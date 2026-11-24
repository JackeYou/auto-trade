(() => {
  'use strict';

  const presets = [
    {id:'trend', name:'中期均线趋势', buyMode:'all', sellMode:'any',
      buy:[rule('close','gt','sma50','metric'), rule('sma20','gt','sma50','metric')],
      sell:[rule('close','lt','sma50','metric')]},
    {id:'momentum', name:'MACD 金叉与死叉', buyMode:'all', sellMode:'all',
      buy:[rule('macd','up','signal','metric')], sell:[rule('macd','down','signal','metric')]},
    {id:'rsi', name:'RSI 区间反转', buyMode:'all', sellMode:'all',
      buy:[rule('rsi','up',30)], sell:[rule('rsi','down',70)]}
  ];
  const saved = readList('trade-strategies').filter(s => s && typeof s.id === 'string' &&
    typeof s.name === 'string' && Array.isArray(s.buy) && Array.isArray(s.sell));
  const library = () => [...presets, ...saved];
  const strategyById = id => library().find(s => s.id === id);
  const cloneRules = rules => rules.map(r => ({...r}));
  const warmup = 250;
  const selectionWindow = 250;
  const historyCache = new Map();

  function validateRules(rules, defs) {
    for (const r of rules) {
      if (!r || !defs.has(r.left) || !Object.hasOwn(screenOps,r.op) ||
          !['number','metric'].includes(r.rhs) ||
          (r.rhs === 'metric' ? !defs.has(r.right) : String(r.num).trim() === '' || !Number.isFinite(Number(r.num)))) {
        throw Error('条件中有缺失的指标或无效阈值，请重新选择。');
      }
    }
  }
  function validateStrategy(s, defs) {
    if (!s || !s.buy.length || !s.sell.length) throw Error('买入、卖出各需要至少一个条件。');
    validateRules([...s.buy, ...s.sell], defs);
  }
  function bindRule(r, ctx) {
    const left = ctx.get(r.left), right = r.rhs === 'metric' ? ctx.get(r.right) : null, value = Number(r.num);
    return i => compareMetric(r.op, left[i-1], left[i], right ? right[i-1] : value, right ? right[i] : value);
  }
  function bindGroup(rules, mode, ctx) {
    const conditions = rules.map(r => bindRule(r,ctx)), any = mode === 'any';
    return i => {
      let missing = false;
      for (const test of conditions) {
        const value = test(i);
        if (value === any) return any;
        if (value === null) missing = true;
      }
      return missing ? null : !any;
    };
  }
  // One state machine for simulated fills and the screener's position signal.
  // Orders decided on bar i are first eligible at the open of i+1.
  function replay(s, ctx, start, onBar) {
    const entry = bindGroup(s.buy,s.buyMode,ctx), exit = bindGroup(s.sell,s.sellMode,ctx);
    let held = false, pending = '', usable = 0, lastBuy = null;
    for (let i = start; i < ctx.bars.length; i++) {
      const fill = pending;
      if (fill) held = fill === 'buy';
      if (onBar) onBar(i,fill);
      const buy = entry(i), sell = exit(i);
      if (buy !== null && sell !== null) usable++;
      lastBuy = held || sell === true || buy === false ? false :
        buy === null || sell === null ? null : true;
      pending = held && sell === true ? 'sell' : lastBuy ? 'buy' : '';
    }
    return {held,usable,lastBuy};
  }
  function simulate(s, ctx, options) {
    const {capital, fee, slip, windowSize} = options, bars = ctx.bars;
    const start = Math.max(0,bars.length-windowSize);
    if (bars.length-start < 2) throw Error('已收盘 K 线不足两根，无法回测。');
    const equity = [], benchmark = [], fills = [];
    let cash = capital, units = 0, costBasis = 0, peak = capital, maxDrawdown = 0, closed = 0, wins = 0;
    const holdUnits = capital / (bars[start].open*(1+slip)*(1+fee));
    const state = replay(s,ctx,start,(i,side) => {
      const bar = bars[i];
      if (side) {
        const price = bar.open*(side === 'buy' ? 1+slip : 1-slip);
        let commission, quantity = units, gain = null;
        if (side === 'buy') {
          costBasis = cash;
          units = cash/(price*(1+fee));
          quantity = units;
          commission = units*price*fee;
          cash = 0;
        } else {
          commission = units*price*fee;
          cash = units*price-commission;
          gain = cash/costBasis-1;
          closed++;
          if (gain > 0) wins++;
          units = 0;
        }
        fills.push({side,signalIndex:i-1,signal:bars[i-1].time,time:bar.time,price,quantity,commission,gain});
      }
      const value = cash+units*bar.close;
      equity.push(value);
      benchmark.push(holdUnits*bar.close);
      peak = Math.max(peak,value);
      maxDrawdown = Math.max(maxDrawdown,1-value/peak);
    });
    if (!state.usable) throw Error('当前历史区间不足以计算所选买卖条件，请调整窗口或指标。');
    const segments = [], parts = Math.min(4,equity.length);
    for (let part = 0; part < parts; part++) {
      const from = Math.floor(part*equity.length/parts), to = Math.floor((part+1)*equity.length/parts)-1;
      segments.push({from:bars[start+from].time,to:bars[start+to].time,gain:equity[to]/(from ? equity[from-1] : capital)-1});
    }
    return {equity,benchmark,fills,segments,closed,wins,maxDrawdown,held:state.held,usable:state.usable,
      preRoll:start,from:bars[start].time,to:bars.at(-1).time,capital};
  }

  async function binanceHistory(a, tf, count, end, signal) {
    const result = [];
    while (result.length < count) {
      const limit = Math.min(1000,count-result.length);
      const rows = await json(binanceUrl(a,'klines',{interval:tf,endTime:end*1000-1,limit}),signal);
      const page = binanceBars(rows,Infinity).filter(b => b.time < end);
      if (!page.length) break;
      result.push(...page);
      end = page[0].time;
      if (a.onboard && end*1000 <= a.onboard) break;
      if (!a.kind && page.length < limit) break;
    }
    return validBars(result,count);
  }
  async function usdHistory(a, tf, count, end, signal) {
    const base = coinBasePeriod[tf] || tf, seconds = periods[base];
    const required = count*periods[tf]/seconds, rows = [], until = end;
    for (let remaining = required; remaining > 0; remaining -= 300) {
      const start = end-Math.min(300,remaining)*seconds;
      const params = new URLSearchParams({granularity:seconds,start:new Date(start*1000).toISOString(),end:new Date((end-1)*1000).toISOString()});
      const page = coinBars(await json('https://api.exchange.coinbase.com/products/'+encodeURIComponent(a.id)+'/candles?'+params,signal));
      if (!page.length) break;
      rows.push(...page.filter(b => b.time >= start && b.time < end));
      end = start;
    }
    const bars = validBars(rows,Infinity);
    if (base === tf || !bars.length) return bars.slice(-count);
    return groupCandles(bars,tf,false,Infinity).filter(b => b.time >= bars[0].time && b.time+periods[tf] <= until).slice(-count);
  }
  function stockClose(time, tf) {
    // Tencent labels the current weekly bar with its most recent trading date.
    return candleBucket(time,tf,true) + (tf === '1w' ? 4*86400 : 0) + 15*3600;
  }
  async function researchBars(a, tf, count, asOf, signal) {
    const stock = a.market === 'stock';
    const end = stock ? Math.floor((asOf+8*3600-15*3600)/86400) : candleBucket(asOf,tf);
    const key = [a.id,tf,end].join('|'), cached = historyCache.get(key);
    if (cached && cached.count >= count) return cached.bars.slice(-count);
    let bars;
    if (stock) {
      const endDate = new Date((asOf+8*3600)*1000-1).toISOString().slice(0,10);
      bars = await candles(a,tf,null,signal,{limit:count+1,adjusted:true,endDate});
      bars = bars.filter(b => stockClose(b.time,tf) <= asOf);
    } else if (binance(a)) {
      bars = await binanceHistory(a,tf,count,end,signal);
    } else {
      bars = await usdHistory(a,tf,count,end,signal);
    }
    signal.throwIfAborted();
    bars = bars.filter(b => b.low > 0 && b.volume >= 0 && b.open >= b.low && b.open <= b.high && b.close >= b.low && b.close <= b.high).slice(-count);
    if (!bars.length) throw Error('行情源没有返回可用的已收盘 K 线。');
    historyCache.set(key,{count,bars});
    if (historyCache.size > 80) historyCache.delete(historyCache.keys().next().value);
    return bars;
  }

  function ruleLabel(r, defs) {
    const other = r.rhs === 'metric' ? defs.get(r.right).label : r.num;
    return defs.get(r.left).label+' '+screenOps[r.op]+' '+other;
  }
  function optionsFor(select, pairs, preferred) {
    select.replaceChildren();
    for (const [value,label] of pairs) scrOpt(select,value,label);
    if (pairs.some(([v]) => v === preferred)) select.value = preferred;
  }
  function barLabel(t, tf) {
    if (periods[tf] >= 86400) {
      const date = new Date((t+28800)*1000).toISOString().slice(0,10);
      return tf === '1w' ? date+' 当周' : date;
    }
    return dt(t,true);
  }
  function percent(value) { return value == null ? '—' : pct(value*100); }
  function gainClass(value) { return value > 0 ? 'up' : value < 0 ? 'down' : ''; }
  function metricCard(label, value, cls='') {
    const card = elm('div');
    card.append(elm('small','',label),elm('strong',cls,value));
    return card;
  }
  function equityCurve(report) {
    const host = $('btCurve');
    host.replaceChildren();
    const capital = report.capital;
    const lines = [report.equity,report.benchmark].map(series => [1,...series.map(x => x/capital)]);
    const lo = Math.min(...lines[0],...lines[1]), hi = Math.max(...lines[0],...lines[1]);
    const ns = 'http://www.w3.org/2000/svg', svg = document.createElementNS(ns,'svg');
    svg.setAttribute('viewBox','0 0 800 150');svg.setAttribute('preserveAspectRatio','none');
    svg.setAttribute('role','img');svg.setAttribute('aria-label','策略与买入持有净值走势，起始净值均为 1');
    for (const [i,series] of lines.entries()) {
      const line = document.createElementNS(ns,'polyline');
      const points = series.map((v,j) => (4+j*792/(series.length-1)).toFixed(2)+','+(hi===lo ? 75 : 142-(v-lo)/(hi-lo)*134).toFixed(2));
      line.setAttribute('points',points.join(' '));line.setAttribute('fill','none');
      line.setAttribute('stroke',i ? '#88a8ce' : '#f5bd58');line.setAttribute('stroke-width',i ? '1.4' : '2');
      line.setAttribute('vector-effect','non-scaling-stroke');svg.prepend(line);
    }
    const scale = elm('div','equityScale');
    scale.append(elm('span','','起始 1.00'),elm('span','','净值范围 '+num(lo,3)+' – '+num(hi,3)));
    host.append(svg,scale);
  }
  function showReport(report, asset, tf, requested, ctx) {
    const r = report, last = r.equity.at(-1), gain = last/r.capital-1, buyHold = r.benchmark.at(-1)/r.capital-1;
    $('btRange').textContent = ticker(asset)+' · '+sourceOf(asset)+' · '+periodNames[tf]+' · '+barLabel(r.from,tf)+' 至 '+barLabel(r.to,tf);
    $('btMetrics').replaceChildren(
      metricCard('策略净收益率',percent(gain),gainClass(gain)),metricCard('最大回撤（收盘净值）',percent(-r.maxDrawdown)),
      metricCard('买入持有收益率',percent(buyHold),gainClass(buyHold)),metricCard('期末权益',num(last)),
      metricCard('已平仓交易',String(r.closed)),metricCard('已平仓胜率',r.closed ? (100*r.wins/r.closed).toFixed(1)+'%' : '—'),
      metricCard('期末仓位',r.held ? '持仓' : '空仓'),metricCard('正收益分段',r.segments.filter(x => x.gain>0).length+' / '+r.segments.length));
    equityCurve(r);
    $('btSegments').replaceChildren(...r.segments.map((segment,i) => {
      const card = metricCard('第 '+(i+1)+' 段',percent(segment.gain),gainClass(segment.gain));
      card.append(elm('small','',barLabel(segment.from,tf)+' 至 '+barLabel(segment.to,tf)));
      return card;
    }));
    $('btFillCount').textContent = '成交明细（'+r.fills.length+' 笔）';
    const triggers = {};
    for (const side of ['buy','sell']) triggers[side] = bt.draft[side].map(r => ({test:bindRule(r,ctx),label:ruleLabel(r,bt.defs)}));
    const rows = [...r.fills].reverse().map(f => {
      const tr = elm('tr');
      const reason = triggers[f.side].filter(r => r.test(f.signalIndex) === true).map(r => r.label).join('、');
      for (const v of [barLabel(f.signal,tf),barLabel(f.time,tf),f.side==='buy'?'买入':'卖出',num(f.price),num(f.quantity,6),num(f.commission,4),percent(f.gain),reason]) tr.append(elm('td','',v));
      return tr;
    });
    $('btFills').replaceChildren(...rows);
    $('btStatus').textContent = '完成 · 回测 '+r.equity.length+'/'+requested+' 根，预热 '+r.preRoll+' 根，可判定买卖条件 '+r.usable+' 根'+(r.fills.length?'':' · 区间内没有成交');
    $('btResult').hidden = false;
  }

  const bt = {defs:null,assets:new Map(),draft:null,job:null};
  function invalidateBacktest() {
    bt.job?.abort();
    bt.job = null;
    $('btRun').disabled = false;
    $('btResult').hidden = true;
    $('btStatus').textContent = '';
    $('btSaved').textContent = '';
  }
  function renderTradeRules() {
    renderRuleRows($('btBuyRules'),bt.draft.buy,bt.defs,invalidateBacktest);
    renderRuleRows($('btSellRules'),bt.draft.sell,bt.defs,invalidateBacktest);
  }
  function loadStrategy(id) {
    const s = strategyById(id) || presets[0];
    bt.draft = {...s,buy:cloneRules(s.buy),sell:cloneRules(s.sell)};
    $('btBuyMode').value = s.buyMode;
    $('btSellMode').value = s.sellMode;
    $('btName').value = saved.some(item => item.id === s.id) ? s.name : '';
    invalidateBacktest();renderTradeRules();
  }
  function refreshTemplates(id) {
    optionsFor($('btTemplate'),library().map(s => [s.id,s.name]),id);
  }
  function backtestPeriods(preferred) {
    const a = bt.assets.get($('btAsset').value), stock = a.market === 'stock';
    const allowed = stock ? ['1d','1w'] : ['1m','5m','15m','1h','4h','1d','1w'];
    optionsFor($('btPeriod'),allowed.map(p => [p,periodNames[p]]),allowed.includes(preferred) ? preferred : '1d');
    const unit = stock ? '人民币' : a.quote || (a.id.endsWith('USDT') ? 'USDT' : 'USD');
    $('btCapitalLabel').textContent = '起始资金（'+unit+'）';
    $('btEnd').max = new Date(Date.now()+(stock ? 28800000 : 0)).toISOString().slice(0,10);
  }
  function openBacktest(asset=active, period=activePeriod, selectedStrategy) {
    bt.defs = screenMetrics();
    bt.assets = new Map([...watch,active,asset].map(a => [a.id,a]));
    optionsFor($('btAsset'),[...bt.assets].map(([id,a]) => [id,a.name+' · '+ticker(a)+' · '+productName(a)]),asset.id);
    backtestPeriods(period);
    refreshTemplates(selectedStrategy || bt.draft?.id || presets[0].id);
    if (bt.draft && !selectedStrategy) { invalidateBacktest();renderTradeRules(); } else loadStrategy($('btTemplate').value);
    $('btDialog').showModal();
  }
  function saveStrategy() {
    try {
      const name = $('btName').value.trim();
      if (!name) throw Error('先为策略填写名称。');
      validateStrategy(bt.draft,bt.defs);
      const index = saved.findIndex(s => s.id === bt.draft.id && s.name === name);
      if (library().some(s => s.name === name && s.id !== saved[index]?.id)) throw Error('该名称已使用，请换一个策略名称。');
      const item = {...bt.draft,name,id:index < 0 ? 'user-'+crypto.randomUUID() : bt.draft.id,
        buy:cloneRules(bt.draft.buy),sell:cloneRules(bt.draft.sell)};
      const next = saved.slice();
      if (index < 0) next.push(item); else next[index] = item;
      localStorage.setItem('candledesk-v1:trade-strategies',JSON.stringify(next));
      saved.splice(0,saved.length,...next);bt.draft.id = item.id;bt.draft.name = name;refreshTemplates(item.id);
      $('btSaved').textContent = '已保存到本机，可在「策略筛选标的」中选择。';
    } catch (e) { $('btSaved').textContent = e.message; }
  }
  async function runBacktest() {
    invalidateBacktest();
    const job = new AbortController();bt.job = job;
    try {
      validateStrategy(bt.draft,bt.defs);
      const capital = $('btCapital').valueAsNumber, fee = $('btFee').valueAsNumber/100, slip = $('btSlip').valueAsNumber/100;
      if (!Number.isFinite(capital) || capital <= 0 || ![fee,slip].every(x => Number.isFinite(x) && x >= 0 && x <= .1)) {
        throw Error('起始资金须大于零，手续费和滑点须在 0% 至 10% 之间。');
      }
      const asset = bt.assets.get($('btAsset').value), tf = $('btPeriod').value, windowSize = Number($('btWindow').value);
      const end = $('btEnd');
      if (!end.validity.valid) throw Error('请选择有效的截至日期。');
      const day = end.value ? Date.parse(end.value+'T00:00:00'+(asset.market==='stock'?'+08:00':'Z'))/1000+86400 : Infinity;
      const asOf = Math.min(Date.now()/1000,day);
      $('btRun').disabled = true;$('btStatus').textContent = '正在获取已收盘行情…';
      const bars = await researchBars(asset,tf,windowSize+warmup,asOf,job.signal);
      if (bt.job !== job) return;
      const ctx = makeScreenContext(bars,bt.defs);
      const report = simulate(bt.draft,ctx,{capital,fee,slip,windowSize});
      showReport(report,asset,tf,windowSize,ctx);
    } catch (e) {
      if (bt.job === job) $('btStatus').textContent = '回测未完成 · '+e.message;
    } finally {
      if (bt.job === job) { bt.job = null;$('btRun').disabled = false; }
    }
  }

  let csi300;
  async function selectionUniverse(scope, codes, signal) {
    if (scope === 'custom') {
      const pool = new Map();
      for (const word of codes.split(/[\s,，、;；]+/u).filter(Boolean)) {
        const a = symbolFrom(word);
        if (!a) throw Error('无法识别代码「'+word+'」。');
        pool.set(a.id,a);
      }
      if (!pool.size) throw Error('请填写至少一个标的代码。');
      return {assets:[...pool.values()],note:''};
    }
    if (scope !== 'hs300') return scrUniverse(scope,signal);
    if (csi300 && csi300.until > Date.now()) return csi300.pool;
    const members = new Map();
    for (let page = 1; ; page++) {
      const key = 'researchIndex'+(++reqId);
      const url = 'https://vip.stock.finance.sina.com.cn/quotes_service/api/jsonp_v2.php/var%20'+key+
        '=/Market_Center.getHQNodeData?node=hs300&sort=symbol&asc=1&num=80&page='+page;
      const [rows] = await remoteVars(url,[key],'gbk',signal);
      if (!Array.isArray(rows)) throw Error('未能取得沪深 300 成分表。');
      const before = members.size;
      for (const row of rows) {
        if (!/^(sh|sz)\d{6}$/i.test(row.symbol)) continue;
        const a = symbolFrom(row.symbol);
        members.set(a.id,{...a,name:row.name || a.name});
      }
      if (rows.length < 80) break;
      if (members.size === before) throw Error('成分表分页未更新，请稍后重试。');
    }
    if (!members.size) throw Error('成分股列表为空。');
    const pool = {assets:[...members.values()],note:' · 新浪当前成分'};
    csi300 = {until:Date.now()+3600000,pool};
    return pool;
  }
  function evaluatePick(plan, bars, defs) {
    const ctx = makeScreenContext(bars,defs), states = new Map(), hits = [];
    let unknown = 0;
    for (const item of plan.items) {
      let value;
      if (item.strategy) {
        const s = item.strategy;
        if (!states.has(s.id)) states.set(s.id,replay(s,ctx,Math.max(0,bars.length-plan.windowSize)));
        const state = states.get(s.id);
        value = !state.usable ? null : item.mode === 'entry' ? state.lastBuy : state.held;
      } else value = bindRule(item.rule,ctx)(bars.length-1);
      if (value === true) hits.push(item.label);
      else if (value === null) unknown++;
    }
    return {hits,unknown,passes:hits.length >= plan.required,
      insufficient:hits.length < plan.required && hits.length+unknown >= plan.required};
  }
  const picker = {defs:null,strategies:[],rules:[],rows:[],page:0,job:null,totalItems:0};
  function pickPlan() {
    const items = [], keys = new Set();
    function add(key,item) {
      if (keys.has(key)) throw Error('存在重复的筛选项，请移除重复项。');
      keys.add(key);items.push(item);
    }
    for (const f of picker.strategies) {
      const s = strategyById(f.id);
      if (!s) throw Error('选中的策略已移除，请重新选择。');
      validateStrategy(s,picker.defs);
      add('s/'+s.id+'/'+f.mode,{strategy:s,mode:f.mode,label:s.name+' · '+(f.mode==='entry'?'买入信号':'持仓中')});
    }
    validateRules(picker.rules,picker.defs);
    for (const r of picker.rules) {
      const key = JSON.stringify([r.left,r.op,r.rhs,r.rhs==='metric'?r.right:Number(r.num)]);
      add(key,{rule:r,label:ruleLabel(r,picker.defs)});
    }
    if (!items.length) throw Error('请至少添加一个策略或指标。');
    const mode = $('pickMode').value;
    const required = mode==='all' ? items.length : mode==='any' ? 1 : $('pickMin').valueAsNumber;
    if (!Number.isInteger(required) || required < 1 || required > items.length) throw Error('最低命中项数应在 1 至 '+items.length+' 之间。');
    return {items,required,windowSize:selectionWindow};
  }
  function resultsTable() {
    const host = $('pickRows');host.replaceChildren();
    const rows = picker.rows, size = scrPageSize, pages = Math.max(1,Math.ceil(rows.length/size));
    picker.page = Math.max(0,Math.min(picker.page,pages-1));
    rows.sort((a,b) => b.hits.length-a.hits.length || a.unknown-b.unknown || a.asset.id.localeCompare(b.asset.id));
    for (const item of rows.slice(picker.page*size,(picker.page+1)*size)) {
      const row = elm('tr'), name = elm('td'), actions = elm('td'), a = item.asset;
      name.append(marketButton(a.name+' · '+ticker(a),() => {
        $('pickDialog').close();choose(a,item.tf);
      },'scrOpen'),elm('small','',productName(a)+' · '+sourceOf(a)));
      const reason = elm('td','',item.hits.join('、'));
      if (item.unknown) reason.append(elm('small','',item.unknown+' 项数据不足'));
      const savedAlready = watch.some(w => w.id === a.id);
      const star = marketButton(savedAlready?'已自选':'加自选',() => {
        if (watch.length >= 40) { star.textContent = '自选已满';return; }
        watch.push(a);storeWrite('symbols',watch.map(w => w.id));renderWatch();star.disabled = true;star.textContent = '已自选';
      },'scrSave');
      star.disabled = savedAlready;
      actions.append(marketButton('回测',() => {
        $('pickDialog').close();
        $('btWindow').value = String(selectionWindow);$('btEnd').value = '';
        const id = picker.strategies.length === 1 ? picker.strategies[0].id : undefined;
        openBacktest(a,item.tf,id);
      },'scrOpen'),document.createTextNode(' '),star);
      row.append(name,elm('td','',item.hits.length+' / '+picker.totalItems),reason,elm('td','',barLabel(item.time,item.tf)),actions);
      host.append(row);
    }
    $('pickTotal').textContent = rows.length+' 个命中';
    $('pickPager').hidden = pages <= 1;$('pickPage').textContent = (picker.page+1)+' / '+pages;
    $('pickPrev').disabled = picker.page === 0;$('pickNext').disabled = picker.page+1 >= pages;
  }
  function scanStatus(job) {
    return job.done+'/'+job.total+' 已查 · '+picker.rows.length+' 个命中'+
      (job.missing?' · '+job.missing+' 个数据不足':'')+(job.failed?' · '+job.failed+' 个行情失败':'')+job.note;
  }
  function stopPick(message='已停止') {
    const job = picker.job;if (!job) return;
    picker.job = null;job.controller.abort();clearTimeout(job.paint);
    $('pickRun').disabled = false;$('pickStop').hidden = true;
    $('pickStatus').textContent = message+' · '+scanStatus(job);resultsTable();
  }
  function clearSelection() {
    stopPick();
    picker.rows = [];picker.page = 0;
    $('pickResult').hidden = true;$('pickStatus').textContent = '';
    $('pickMinLabel').hidden = $('pickMode').value !== 'min';$('pickCodesLabel').hidden = $('pickScope').value !== 'custom';
  }
  function pickChanged() {
    clearSelection();
    storeWrite('strategy-selection',{strategies:picker.strategies,rules:picker.rules,scope:$('pickScope').value,tf:$('pickPeriod').value,
      mode:$('pickMode').value,minimum:$('pickMin').value,codes:$('pickCodes').value});
  }
  function renderPickControls() {
    const host = $('pickStrategies');host.replaceChildren();
    for (const [index,item] of picker.strategies.entries()) {
      const row = elm('div','pickStrategyRow'), select = elm('select'), mode = elm('select');
      const pairs = library().map(s => [s.id,s.name]);
      if (!strategyById(item.id)) pairs.push([item.id,'策略已移除，请重新选择']);
      optionsFor(select,pairs,item.id);
      optionsFor(mode,[['holding','持仓中'],['entry','最新买入信号']],item.mode);
      select.setAttribute('aria-label','叠加策略 '+(index+1));mode.setAttribute('aria-label','策略判定方式');
      select.onchange = () => { item.id = select.value;pickChanged(); };
      mode.onchange = () => { item.mode = mode.value;pickChanged(); };
      const remove = marketButton('移除',() => { picker.strategies.splice(index,1);pickChanged();renderPickControls(); },'scrRemove');
      row.append(select,mode,remove);host.append(row);
    }
    renderRuleRows($('pickRules'),picker.rules,picker.defs,pickChanged,0);
  }
  function openSelection() {
    picker.defs = screenMetrics();
    const prefs = storeRead('strategy-selection',{}) || {};
    picker.strategies = Array.isArray(prefs.strategies) ? prefs.strategies.filter(f => f && typeof f.id === 'string' && ['holding','entry'].includes(f.mode)) : [{id:'trend',mode:'holding'}];
    picker.rules = Array.isArray(prefs.rules) ? prefs.rules.filter(r => r && typeof r.left==='string' && Object.hasOwn(screenOps,r.op) && ['number','metric'].includes(r.rhs)) : [rule('rsi','gte',50)];
    for (const [id,value,defaultValue] of [['pickScope',prefs.scope,'watch'],['pickPeriod',prefs.tf,'1d'],['pickMode',prefs.mode,'all']]) {
      const select = $(id);select.value = [...select.options].some(o => o.value === value) ? value : defaultValue;
    }
    $('pickMin').value = prefs.minimum ?? 2;$('pickCodes').value = prefs.codes || '';
    clearSelection();renderPickControls();$('pickDialog').showModal();
  }
  async function runPick() {
    clearSelection();
    const job = {controller:new AbortController(),done:0,total:0,missing:0,failed:0,note:'',paint:0};
    picker.job = job;
    try {
      const plan = pickPlan(), tf = $('pickPeriod').value, asOf = Date.now()/1000;
      picker.totalItems = plan.items.length;
      $('pickRun').disabled = true;$('pickStop').hidden = false;$('pickStatus').textContent = '正在获取标的池…';
      const pool = await selectionUniverse($('pickScope').value,$('pickCodes').value,job.controller.signal);
      if (picker.job !== job) return;
      job.total = pool.assets.length;job.note = pool.note;
      const defs = picker.defs;let next = 0, nextSlot = 0;
      const paint = () => {
        if (picker.job !== job) return;
        job.paint = 0;resultsTable();$('pickStatus').textContent = scanStatus(job);
      };
      $('pickResult').hidden = false;paint();
      async function worker() {
        while (picker.job === job && next < pool.assets.length) {
          const a = pool.assets[next++];
          const at = Math.max(Date.now(),nextSlot);nextSlot = at+260;
          const wait = at-Date.now();
          if (wait > 0) await new Promise(resolve => setTimeout(resolve,wait));
          if (picker.job !== job) return;
          try {
            const bars = await researchBars(a,tf,plan.windowSize+warmup,asOf,job.controller.signal);
            if (picker.job !== job) return;
            const item = evaluatePick(plan,bars,defs);
            if (item.passes) picker.rows.push({...item,asset:a,tf,time:bars.at(-1).time});
            else if (item.insufficient) job.missing++;
          } catch (e) {
            if (picker.job !== job) return;
            job.failed++;
            if (e.status === 429 || e.status === 418) { job.done++;stopPick('行情源限流，已停止');return; }
          }
          job.done++;
          if (!job.paint) job.paint = setTimeout(paint,220);
        }
      }
      await Promise.all(Array.from({length:Math.min(3,job.total)},worker));
      if (picker.job !== job) return;
      clearTimeout(job.paint);paint();
      $('pickStatus').textContent = !job.total ? '当前标的池为空。' :
        (job.failed===job.total?'未取得可用行情':'筛选完成')+' · '+scanStatus(job);
    } catch (e) {
      if (picker.job === job) $('pickStatus').textContent = '筛选未完成 · '+e.message;
    } finally {
      if (picker.job === job) { picker.job = null;clearTimeout(job.paint);$('pickRun').disabled = false;$('pickStop').hidden = true; }
    }
  }

  $('btOpen').onclick = () => openBacktest();
  $('btTemplate').onchange = () => loadStrategy($('btTemplate').value);
  $('btAsset').onchange = () => { backtestPeriods($('btPeriod').value);invalidateBacktest(); };
  for (const id of ['btWindow','btPeriod','btEnd']) $(id).onchange = invalidateBacktest;
  for (const id of ['btCapital','btFee','btSlip']) $(id).oninput = invalidateBacktest;
  for (const [side,id] of [['buy','Buy'],['sell','Sell']]) {
    $('bt'+id+'Mode').onchange = () => { bt.draft[side+'Mode'] = $('bt'+id+'Mode').value;invalidateBacktest(); };
    $('btAdd'+id).onclick = () => {
      bt.draft[side].push(rule('close',side==='buy'?'gt':'lt','sma20','metric'));
      invalidateBacktest();renderTradeRules();
    };
  }
  $('btSave').onclick = saveStrategy;$('btRun').onclick = runBacktest;
  $('btDialog').addEventListener('close',() => { bt.job?.abort();bt.job = null;$('btRun').disabled = false; });
  $('pickOpen').onclick = openSelection;$('pickRun').onclick = runPick;$('pickStop').onclick = () => stopPick();
  $('pickDialog').addEventListener('close',() => stopPick());
  for (const id of ['pickScope','pickPeriod','pickMode']) $(id).onchange = pickChanged;
  for (const id of ['pickMin','pickCodes']) $(id).oninput = pickChanged;
  $('pickAddStrategy').onclick = () => {
    const s = library().find(candidate => !picker.strategies.some(f => f.id === candidate.id)) || presets[0];
    picker.strategies.push({id:s.id,mode:'holding'});pickChanged();renderPickControls();
  };
  $('pickAddRule').onclick = () => { picker.rules.push(rule('close','gt','sma20','metric'));pickChanged();renderPickControls(); };
  $('pickPrev').onclick = () => { picker.page--;resultsTable(); };
  $('pickNext').onclick = () => { picker.page++;resultsTable(); };
})();
