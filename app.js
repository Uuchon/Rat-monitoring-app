'use strict';
/* USV MONITOR — rat ultrasonic vocalization monitor (no external libraries) */
(() => {
const $ = id => document.getElementById(id);
const DPR = () => Math.min(2, window.devicePixelRatio || 1);

/* ============ config / classes ============ */
const cfg = { thr: 18, margin: 2, minDur: 10, gap: 40, useDur: true };
const CLS = {
  s22: { name: '22 kHz', label: 'ストレス・苦痛', color: 'hsl(360 72% 48%)' },
  s31: { name: '31 kHz', label: '孤立・不平等（嫉妬様）', color: 'hsl(225 72% 48%)' },
  s50: { name: '50 kHz', label: 'うれしい・親和', color: 'hsl(130 70% 38%)' },
  unk: { name: '不明（中間）', label: '判定できない声', color: '#1f2937' },
};
const ORDER = ['s22', 's31', 's50', 'unk'];

/* frequency(kHz) -> hue. Class cores are plateaus, the in-between zones are colour transitions
   (22→31: red→magenta→blue, 31→50: blue→cyan→green) so odd calls get odd colours. */
const ANCH = [[10,360],[24,360],[29,225],[33,225],[45,130],[70,130],[100,70],[130,70]];
function hueF(k) {
  if (k <= ANCH[0][0]) return ANCH[0][1] % 360;
  for (let i = 1; i < ANCH.length; i++) if (k <= ANCH[i][0]) {
    const [a, ha] = ANCH[i-1], [b, hb] = ANCH[i];
    return (((ha + (hb - ha) * (k - a) / (b - a)) % 360) + 360) % 360;
  }
  return 70;
}
const colF = (k, unk, a = 1) => `hsla(${hueF(k).toFixed(0)},${unk ? 95 : 72}%,${unk ? 46 : 46}%,${a})`;

function classify(e) {
  const f = e.fmed, d = e.dur, m = cfg.margin;
  let c;
  if (f > 18 && f <= 26) c = 's22'; else if (f > 26 && f <= 40) c = 's31'; else if (f > 40 && f <= 100) c = 's50'; else c = 'unk';
  if (c === 'unk') return { c, why: f <= 18 ? '18 kHz以下' : '100 kHz超' };
  const why = [];
  if (Math.abs(f - 26) < m) why.push('22/31 kHz の境界付近');
  if (Math.abs(f - 40) < m) why.push('31/50 kHz の境界付近');
  if (f - 18 < m) why.push('18 kHz付近');
  for (const b of [26, 40]) if (e.fmin < b - m / 2 && e.fmax > b + m / 2) why.push(`${b} kHz をまたぐ`);
  if (cfg.useDur) {
    if (c === 's22' && d < 0.5) why.push('22 kHz帯だが0.5 s未満');
    if (c !== 's22' && d >= 0.5) why.push(`${c === 's31' ? '31' : '50'} kHz帯だが0.5 s以上`);
  }
  return why.length ? { c: 'unk', why: why.join('・') } : { c, why: '' };
}

/* ============ time helpers ============ */
const p2 = n => String(n).padStart(2, '0');
function clock(ms, frac = 0) {
  const d = new Date(ms); let s = `${p2(d.getHours())}:${p2(d.getMinutes())}:${p2(d.getSeconds())}`;
  if (frac) s += '.' + String(d.getMilliseconds()).padStart(3, '0').slice(0, frac);
  return s;
}
const dateStr = ms => { const d = new Date(ms); return `${d.getFullYear()}-${p2(d.getMonth()+1)}-${p2(d.getDate())}`; };
const fmtDur = s => s >= 1 ? s.toFixed(2) + ' s' : Math.round(s * 1000) + ' ms';
function toLocalInput(ms) { const d = new Date(ms); return `${dateStr(ms)}T${clock(ms)}`; }

/* ============ FFT / detector ============ */
class FFT {
  constructor(n) {
    this.n = n; this.cs = new Float32Array(n / 2); this.sn = new Float32Array(n / 2); this.rev = new Uint32Array(n);
    for (let i = 0; i < n / 2; i++) { this.cs[i] = Math.cos(2 * Math.PI * i / n); this.sn[i] = -Math.sin(2 * Math.PI * i / n); }
    const bits = Math.log2(n);
    for (let i = 0; i < n; i++) { let r = 0; for (let b = 0; b < bits; b++) if (i & (1 << b)) r |= 1 << (bits - 1 - b); this.rev[i] = r; }
  }
  run(re, im) {
    const n = this.n, rev = this.rev;
    for (let i = 0; i < n; i++) { const j = rev[i]; if (j > i) { let t = re[i]; re[i] = re[j]; re[j] = t; t = im[i]; im[i] = im[j]; im[j] = t; } }
    for (let size = 2; size <= n; size <<= 1) {
      const half = size >> 1, step = n / size;
      for (let i = 0; i < n; i += size) for (let j = 0, k = 0; j < half; j++, k += step) {
        const a = i + j, b = a + half, tr = re[b] * this.cs[k] - im[b] * this.sn[k], ti = re[b] * this.sn[k] + im[b] * this.cs[k];
        re[b] = re[a] - tr; im[b] = im[a] - ti; re[a] += tr; im[a] += ti;
      }
    }
  }
}

class Detector {
  constructor(fs, t0, onEvent, onFrame) {
    this.fs = fs; this.t0 = t0; this.onEvent = onEvent; this.onFrame = onFrame;
    let N = 256; while (N < fs * 0.005) N <<= 1; this.N = N; this.hop = N >> 1;
    this.fft = new FFT(N); this.win = new Float32Array(N);
    for (let i = 0; i < N; i++) this.win[i] = 0.5 - 0.5 * Math.cos(2 * Math.PI * i / (N - 1));
    this.re = new Float64Array(N); this.im = new Float64Array(N); this.db = new Float32Array(N / 2);
    this.df = fs / N; this.kLo = Math.max(2, Math.ceil(15000 / this.df));
    this.kHi = Math.min(N / 2 - 3, Math.floor(Math.min(110000, fs * 0.48) / this.df));
    this.L = Math.ceil(fs * 4); this.ring = new Float32Array(this.L); this.total = 0; this.next = 0;
    this.floor = null; this.warm = 0; this.cur = null; this.nextId = 1;
  }
  feed(x) {
    const L = this.L; if (x.length > L / 2) { for (let o = 0; o < x.length; o += L >> 2) this.feed(x.subarray(o, o + (L >> 2))); return; }
    for (let i = 0; i < x.length; i++) this.ring[(this.total + i) % L] = x[i];
    this.total += x.length;
    while (this.next + this.N <= this.total) { this.frame(this.next); this.next += this.hop; }
  }
  tms(sample) { return this.t0 + sample / this.fs * 1000; }
  frame(s) {
    const { N, ring, L, win, re, im, db, kLo, kHi } = this;
    for (let i = 0; i < N; i++) { re[i] = ring[(s + i) % L] * win[i]; im[i] = 0; }
    this.fft.run(re, im);
    let sum = 0, pk = -1e9, pkK = kLo;
    for (let k = kLo - 1; k <= kHi + 1; k++) {
      const v = 10 * Math.log10(re[k] * re[k] + im[k] * im[k] + 1e-12); db[k] = v;
      if (k >= kLo && k <= kHi) { sum += v; if (v > pk) { pk = v; pkK = k; } }
    }
    const nb = kHi - kLo + 1, mean = sum / nb;
    if (this.floor === null) { this.floor = mean; }
    let cnt = 0; const lvl = this.floor + cfg.thr * 0.6;
    for (let k = kLo; k <= kHi; k++) if (db[k] > lvl) cnt++;
    const snr = pk - this.floor;
    let active = snr > cfg.thr && cnt / nb < 0.35 && this.warm > 10;
    this.warm++;
    if (!active) this.floor += 0.03 * (mean - this.floor);
    // parabolic refinement
    const a = db[pkK - 1], b = db[pkK], c = db[pkK + 1], den = a - 2 * b + c;
    const off = den !== 0 ? Math.max(-0.5, Math.min(0.5, 0.5 * (a - c) / den)) : 0;
    const fk = (pkK + off) * this.df / 1000;
    const tc = this.tms(s + N / 2), hopMs = this.hop / this.fs * 1000;
    if (this.onFrame) this.onFrame(this, fk, active, snr, tc);
    const cur = this.cur;
    if (active) {
      if (!cur) this.cur = { t: tc - hopMs / 2, s0: s, f: [fk], snr, last: tc, ls: s + N, sil: 0 };
      else { cur.f.push(fk); if (snr > cur.snr) cur.snr = snr; cur.last = tc; cur.ls = s + N; cur.sil = 0; }
    } else if (cur) {
      cur.sil += hopMs;
      if (cur.sil >= cfg.gap) this.close();
    }
  }
  close() {
    const c = this.cur; this.cur = null; if (!c) return;
    const dur = (c.last + this.hop / this.fs * 500 - c.t) / 1000;
    if (dur * 1000 < cfg.minDur) return;
    const f = c.f.slice().sort((x, y) => x - y), q = p => f[Math.min(f.length - 1, Math.floor(p * (f.length - 1)))];
    const ev = { id: this.nextId++, t: c.t, dur, fmed: q(0.5), fmin: q(0.1), fmax: q(0.9), snr: c.snr, _s0: c.s0, _s1: c.ls };
    this.onEvent(ev, this);
  }
  flush() { if (this.cur) this.close(); }
  clip(ev) {
    const pad = Math.round(this.fs * 0.2), maxL = Math.round(this.fs * 2.4);
    let a = ev._s0 - pad, b = ev._s1 + pad;
    a = Math.max(a, this.total - this.L + this.N, 0); b = Math.min(b, this.total);
    if (b - a > maxL) a = b - maxL;
    if (b - a < 16) return null;
    const out = new Int16Array(b - a);
    for (let i = 0; i < out.length; i++) out[i] = Math.max(-32768, Math.min(32767, Math.round(this.ring[(a + i) % this.L] * 32767)));
    return out;
  }
}

/* ============ state ============ */
const S = {
  events: [], markers: [], clips: new Map(), clipBytes: 0,
  start: 0, end: 0, live: false, fs: 0, nyq: 0, mode: 'idle', // idle|mic|file|demo
  v0: 0, v1: 1, follow: true, sel: -1, dirty: true, dirtyList: true, maxDur: 1,
};
let det = null, ctx = null, stream = null, node = null, wake = null, specCtx = null;

function addEvent(ev, d) {
  delete ev._s1; delete ev._s0n;
  const k = classify(ev);
  if (k.c === 'unk' && d) { const cl = d.clip(ev); if (cl) { S.clips.set(ev.id, { fs: d.fs, data: cl }); S.clipBytes += cl.byteLength; trimClips(); } }
  delete ev._s0;
  S.events.push(ev); if (ev.dur > S.maxDur) S.maxDur = ev.dur;
  S.dirty = S.dirtyList = true; S.lastEv = ev;
}
function trimClips() {
  while (S.clipBytes > 80e6 && S.clips.size) { const k = S.clips.keys().next().value; S.clipBytes -= S.clips.get(k).data.byteLength; S.clips.delete(k); }
}

/* ============ live mic ============ */
const WORKLET = `class P extends AudioWorkletProcessor{constructor(){super();this.b=new Float32Array(2048);this.n=0}
process(i){const c=i[0]&&i[0][0];if(!c)return true;for(let k=0;k<c.length;k++){this.b[this.n++]=c[k];if(this.n===2048){this.port.postMessage(this.b.slice(0));this.n=0}}return true}}
registerProcessor('cap',P)`;

async function startMic() {
  if (S.events.length && !confirm('いまの記録を消して新しく計測を始めますか？\n（先にCSVを保存してください）')) return;
  stopAll(true); resetData();
  const want = +$('selRate').value, dev = $('selDev').value;
  try {
    const cons = { echoCancellation: false, noiseSuppression: false, autoGainControl: false, channelCount: 1 };
    if (want) cons.sampleRate = { ideal: want };
    if (dev) cons.deviceId = { exact: dev };
    stream = await navigator.mediaDevices.getUserMedia({ audio: cons });
  } catch (e) { setInfo('マイクを開けませんでした：' + e.message, true); return; }
  try { ctx = new (window.AudioContext || window.webkitAudioContext)(want ? { sampleRate: want, latencyHint: 'playback' } : { latencyHint: 'playback' }); }
  catch (e) { ctx = new (window.AudioContext || window.webkitAudioContext)({ latencyHint: 'playback' }); }
  let src;
  try { src = ctx.createMediaStreamSource(stream); }
  catch (e) { // Firefox: rate mismatch
    try { ctx.close(); } catch (_) {}
    ctx = new (window.AudioContext || window.webkitAudioContext)({ latencyHint: 'playback' });
    src = ctx.createMediaStreamSource(stream);
  }
  if (ctx.state === 'suspended') await ctx.resume();
  const trk = stream.getAudioTracks()[0], ts = trk.getSettings ? trk.getSettings() : {};
  const fs = ctx.sampleRate, devRate = ts.sampleRate || fs, eff = Math.min(fs, devRate);
  S.fs = fs; S.nyq = eff / 2; S.live = true; S.mode = 'mic'; S.start = Date.now(); S.end = S.start;
  fillDevices();
  let msg = `サンプリング ${fs / 1000} kHz（マイク側 ${devRate / 1000} kHz）→ 観測できる上限は約 ${(S.nyq / 1000).toFixed(0)} kHz。`;
  const warn = S.nyq < 55000;
  if (S.nyq < 26000) msg += ' ⚠ これでは22 kHz前後までしか見えません。超音波マイクと192 kHz以上の入力設定（OS側も）が必要です。';
  else if (warn) msg += ' ⚠ 50 kHz帯（40〜100 kHz）の上側は見えません。';
  else msg += ' 22/31/50 kHz帯をすべて観測できます。';
  setInfo(msg, warn);
  det = new Detector(fs, Date.now(), addEvent, onFrame);
  let first = true;
  const feed = x => {
    if (first) { det.t0 = Date.now() - x.length / fs * 1000; first = false; }
    det.feed(x);
    if (det.total % (fs * 5) < x.length) { const exp = det.tms(det.total), dif = Date.now() - exp; if (Math.abs(dif) > 1500) det.t0 += dif; }
  };
  const zero = ctx.createGain(); zero.gain.value = 0; zero.connect(ctx.destination);
  let ok = false;
  if (ctx.audioWorklet) {
    try {
      const url = URL.createObjectURL(new Blob([WORKLET], { type: 'application/javascript' }));
      await ctx.audioWorklet.addModule(url);
      node = new AudioWorkletNode(ctx, 'cap'); node.port.onmessage = e => feed(e.data); ok = true;
    } catch (e) { ok = false; }
  }
  if (!ok) { node = ctx.createScriptProcessor(4096, 1, 1); node.onaudioprocess = e => feed(new Float32Array(e.inputBuffer.getChannelData(0))); }
  src.connect(node); node.connect(zero);
  try { if (navigator.wakeLock) wake = await navigator.wakeLock.request('screen'); } catch (_) {}
  S.follow = true; $('follow').checked = true; if (S.v1 - S.v0 > 3600e3 || S.v1 - S.v0 < 1) S.v0 = S.v1 - 300e3;
  setMode('mic'); saveTimer();
}
function stopAll(silent) {
  if (det && S.mode === 'mic') { det.flush(); }
  if (node) { try { node.disconnect(); } catch (_) {} node = null; }
  if (stream) { stream.getTracks().forEach(t => t.stop()); stream = null; }
  if (ctx) { try { ctx.close(); } catch (_) {} ctx = null; }
  if (wake) { try { wake.release(); } catch (_) {} wake = null; }
  fileAbort = true;
  if (S.live) { S.end = Date.now(); S.live = false; }
  if (!silent) { setMode('idle'); persist(); }
  S.dirty = S.dirtyList = true;
}

/* ============ WAV file analysis (streamed) ============ */
let fileAbort = false;
async function analyzeFile(file) {
  if (!file) return;
  if (S.events.length && !confirm('いまの記録を消してファイルを解析しますか？')) return;
  stopAll(true); resetData(); fileAbort = false;
  const head = new DataView(await file.slice(0, Math.min(file.size, 1 << 16)).arrayBuffer());
  const tag = o => String.fromCharCode(head.getUint8(o), head.getUint8(o + 1), head.getUint8(o + 2), head.getUint8(o + 3));
  if (head.byteLength < 44 || tag(0) !== 'RIFF' || tag(8) !== 'WAVE') { setInfo('WAVファイル（PCM）を選んでください。', true); return; }
  let o = 12, fmt = null, dOff = 0, dLen = 0;
  while (o + 8 <= head.byteLength) {
    const id = tag(o), sz = head.getUint32(o + 4, true);
    if (id === 'fmt ') fmt = { tag: head.getUint16(o + 8, true), ch: head.getUint16(o + 10, true), fs: head.getUint32(o + 12, true), bits: head.getUint16(o + 22, true) };
    if (id === 'data') { dOff = o + 8; dLen = sz; break; }
    o += 8 + sz + (sz & 1);
  }
  if (!fmt || !dOff) { setInfo('WAVの形式を読み取れませんでした。', true); return; }
  const bps = fmt.bits / 8, frameB = bps * fmt.ch;
  if (!dLen || dOff + dLen > file.size) dLen = file.size - dOff;
  const total = Math.floor(dLen / frameB), fs = fmt.fs, durS = total / fs;
  if (![16, 24, 32].includes(fmt.bits)) { setInfo(`${fmt.bits}bit のWAVには未対応です（16/24/32bit）。`, true); return; }
  const isFloat = fmt.tag === 3 || (fmt.tag === 0xFFFE && fmt.bits === 32 && false);
  S.fs = fs; S.nyq = fs / 2; S.mode = 'file'; S.live = false;
  let st = $('fileStart').value ? new Date($('fileStart').value).getTime() : NaN;
  if (isNaN(st)) st = (file.lastModified || Date.now()) - durS * 1000;
  $('fileStart').value = toLocalInput(st);
  S.start = st; S.end = st + durS * 1000; S.v0 = S.start; S.v1 = S.end; S.follow = false; $('follow').checked = false;
  let msg = `${file.name}：${(fs / 1000).toFixed(0)} kHz / ${fmt.bits}bit / ${fmt.ch}ch / ${fmtHMS(durS)}。観測できる上限は約 ${(fs / 2000).toFixed(0)} kHz。`;
  const warn = fs / 2 < 55000; if (warn) msg += ' ⚠ 50 kHz帯の上側は含まれていません。';
  setInfo(msg + ' 録音開始時刻は入力欄で修正できます。', warn);
  setMode('file');
  det = new Detector(fs, st, addEvent, null);
  const CH = 2 * 1024 * 1024 - ((2 * 1024 * 1024) % frameB), chunkS = Math.floor(fs * 0.4);
  const t0 = performance.now(); let pos = 0, lastUi = 0;
  while (pos < dLen && !fileAbort) {
    const buf = await file.slice(dOff + pos, dOff + Math.min(dLen, pos + CH)).arrayBuffer();
    const nf = Math.floor(buf.byteLength / frameB), dv = new DataView(buf);
    let x = new Float32Array(Math.min(nf, chunkS)), n = 0;
    for (let i = 0; i < nf; i++) {
      const p = i * frameB; let v;
      if (fmt.bits === 16) v = dv.getInt16(p, true) / 32768;
      else if (fmt.bits === 24) v = ((dv.getUint8(p) | (dv.getUint8(p + 1) << 8) | (dv.getInt8(p + 2) << 16))) / 8388608;
      else v = isFloat ? dv.getFloat32(p, true) : dv.getInt32(p, true) / 2147483648;
      x[n++] = v;
      if (n === x.length) { det.feed(x); n = 0; }
    }
    if (n) det.feed(x.subarray(0, n));
    pos += nf * frameB;
    const now = performance.now();
    if (now - lastUi > 120) {
      lastUi = now; const r = pos / dLen;
      $('progBar').style.width = (r * 100) + '%'; $('progTxt').textContent = `解析中 ${(r * 100).toFixed(0)}%　声 ${S.events.length} 件`;
      S.dirty = S.dirtyList = true; await new Promise(r => setTimeout(r, 0));
    }
  }
  det.flush();
  $('prog').hidden = true; S.dirty = S.dirtyList = true;
  setMode('idle'); persist();
  setInfo($('rateInfo').textContent + `（解析 ${((performance.now() - t0) / 1000).toFixed(1)} 秒で完了）`, warn);
}
const fmtHMS = s => `${Math.floor(s / 3600)}時間${p2(Math.floor(s % 3600 / 60))}分${p2(Math.floor(s % 60))}秒`;

/* ============ demo ============ */
function demo() {
  if (S.events.length && !confirm('いまの記録を消してデモデータを作りますか？')) return;
  stopAll(true); resetData();
  const now = new Date(); const t0 = new Date(now.getFullYear(), now.getMonth(), now.getDate(), 10, 0, 0).getTime();
  S.mode = 'demo'; S.start = t0; S.end = t0 + 3 * 3600e3; S.fs = 250000; S.nyq = 125000;
  let seed = 7; const rnd = () => (seed = (seed * 16807) % 2147483647) / 2147483647, g = () => (rnd() + rnd() + rnd() - 1.5) / 1.5;
  let id = 1;
  const add = (t, dur, f, sp) => { const ev = { id: id++, t, dur, fmed: f, fmin: f - sp, fmax: f + sp, snr: 12 + rnd() * 20 }; S.events.push(ev); if (dur > S.maxDur) S.maxDur = dur; };
  for (let h = 0; h < 180; ) {                      // minutes
    const ph = h < 40 ? 'play' : h < 90 ? 'isolate' : h < 130 ? 'mixed' : 'play2';
    const n = ph === 'isolate' ? 6 : 4;
    const tt = t0 + h * 60e3 + rnd() * 50e3;
    for (let b = 0; b < n; b++) {
      const bt = tt + b * (200 + rnd() * 400);
      if (ph === 'play' || ph === 'play2' || (ph === 'mixed' && rnd() < .5)) add(bt, .03 + rnd() * .12, 55 + g() * 9, 4 + rnd() * 6);
      else add(bt, .03 + rnd() * .06, 31 + g() * 2.2, 1.5);
    }
    if (rnd() < .06) add(tt + 5000, 0.7 + rnd() * 1.5, 22 + g() * 1.6, .8);          // 22 kHz
    if (rnd() < .14) add(tt + 2200, .05 + rnd() * .1, 26 + g() * 1.5, 1.2);           // between 22/31
    if (rnd() < .12) add(tt + 3100, .05 + rnd() * .1, 40 + g() * 2, 2);               // between 31/50
    if (rnd() < .05) add(tt + 4100, .2 + rnd() * .2, 29 + g(), 5);                    // sweeping across
    h += 1 + Math.floor(rnd() * 2);
  }
  S.events.sort((a, b) => a.t - b.t);
  S.v0 = S.start; S.v1 = S.end; S.follow = false; $('follow').checked = false;
  setInfo('これはデモ用の模擬データです（実測ではありません）。', false);
  setMode('idle'); S.dirty = S.dirtyList = true;
}

/* ============ markers / reset / persistence ============ */
function mark() {
  if (S.mode !== 'mic') return;
  const t = Date.now(); const txt = (prompt('メモ（任意）：例「撫でた」「ケージを開けた」', '') || '').slice(0, 60);
  S.markers.push({ t, txt }); S.dirty = S.dirtyList = true;
}
function resetData() {
  S.events = []; S.markers = []; S.clips.clear(); S.clipBytes = 0; S.sel = -1; S.maxDur = 1; S.lastEv = null;
  S.start = S.end = Date.now(); S.v0 = S.start; S.v1 = S.start + 60e3; S.dirty = S.dirtyList = true;
}
const DB = () => new Promise((res, rej) => { const r = indexedDB.open('usvmon', 1); r.onupgradeneeded = () => r.result.createObjectStore('kv'); r.onsuccess = () => res(r.result); r.onerror = () => rej(r.error); });
async function persist() {
  try {
    if (!S.events.length) return;
    const db = await DB(), tx = db.transaction('kv', 'readwrite');
    tx.objectStore('kv').put({ start: S.start, end: S.live ? Date.now() : S.end, fs: S.fs, nyq: S.nyq, events: S.events, markers: S.markers, saved: Date.now() }, 'session');
  } catch (_) {}
}
let saveT = 0; function saveTimer() { clearInterval(saveT); saveT = setInterval(() => { if (S.live) persist(); }, 20000); }
async function checkRestore() {
  try {
    const db = await DB(), r = db.transaction('kv').objectStore('kv').get('session');
    r.onsuccess = () => {
      const d = r.result; if (!d || !d.events || !d.events.length) return;
      const el = $('restore'); el.hidden = false;
      el.innerHTML = `前回の記録が残っています（${dateStr(d.start)} ${clock(d.start)}〜${clock(d.end)}、声 ${d.events.length} 件）。 <button class="btn sm" id="btnRestore">復元する</button>`;
      $('btnRestore').onclick = () => {
        resetData(); S.events = d.events; S.markers = d.markers || []; S.start = d.start; S.end = d.end; S.fs = d.fs; S.nyq = d.nyq;
        S.maxDur = Math.max(1, ...S.events.map(e => e.dur)); S.v0 = S.start; S.v1 = Math.max(S.end, S.start + 60e3); S.follow = false; $('follow').checked = false;
        el.hidden = true; S.dirty = S.dirtyList = true;
      };
    };
  } catch (_) {}
}

/* ============ UI: status, devices ============ */
function setInfo(t, warn) { const e = $('rateInfo'); e.textContent = t; e.classList.toggle('warn', !!warn); }
function setMode(m) {
  const pill = $('statusPill'); S.mode = m === 'idle' ? (S.mode === 'file' || S.mode === 'demo' ? S.mode : 'idle') : m;
  $('btnMic').disabled = m === 'mic' || m === 'file'; $('btnStop').disabled = !(m === 'mic' || m === 'file');
  $('btnMark').disabled = m !== 'mic'; $('prog').hidden = m !== 'file';
  pill.className = 'pill ' + (m === 'mic' ? 'rec' : m === 'file' ? 'busy' : 'idle');
  if (m === 'idle') pill.textContent = S.events.length ? '停止中（記録あり）' : '待機中';
  if (m === 'file') pill.textContent = 'WAV解析中';
}
async function fillDevices() {
  try {
    const list = (await navigator.mediaDevices.enumerateDevices()).filter(d => d.kind === 'audioinput'), cur = $('selDev').value;
    $('selDev').innerHTML = '<option value="">既定のマイク</option>' + list.map(d => `<option value="${d.deviceId}">${(d.label || 'マイク').replace(/</g, '')}</option>`).join('');
    $('selDev').value = cur;
  } catch (_) {}
}

/* ============ live spectrogram ============ */
const SPC = { w: 380, h: 140, off: null, o2: null, acc: null, n: 0, lastCol: 0 };
function initSpec() {
  const c = $('spec'); c.width = SPC.w; c.height = SPC.h; specCtx = c.getContext('2d');
  SPC.off = document.createElement('canvas'); SPC.off.width = SPC.w; SPC.off.height = SPC.h; SPC.o2 = SPC.off.getContext('2d');
  SPC.o2.fillStyle = '#0b1020'; SPC.o2.fillRect(0, 0, SPC.w, SPC.h); S.specDirty = true; S.nyq = S.nyq || 125000;
}
let colMax = null, colFreq = 0, colAct = false, colSnr = 0, colN = 0;
function onFrame(d, fk, active, snr, tc) {
  const bins = SPC.h; if (!colMax) colMax = new Float32Array(bins).fill(-200);
  const kmax = d.N / 2;
  for (let y = 0; y < bins; y++) { // y=0 bottom -> freq 0..nyq (shown up to 110kHz)
    const top = Math.min(S.nyq, 110000), f0 = y / bins * top, f1 = (y + 1) / bins * top;
    let k0 = Math.floor(f0 / d.df), k1 = Math.max(k0, Math.floor(f1 / d.df)); if (k0 < d.kLo - 1 || k1 > d.kHi + 1) continue;
    let m = -200; for (let k = k0; k <= k1; k++) if (d.db[k] > m) m = d.db[k]; if (m > colMax[y]) colMax[y] = m;
  }
  if (active && snr > colSnr) { colFreq = fk; colSnr = snr; S.nowSnr = snr; }
  colAct = colAct || active; colN++;
  S.floorDb = d.floor;
  if (tc - SPC.lastCol >= 40) {
    SPC.lastCol = tc;
    const o = SPC.o2; o.drawImage(SPC.off, -1, 0);
    const img = o.createImageData(1, SPC.h), fl = d.floor;
    for (let y = 0; y < SPC.h; y++) {
      const v = Math.max(0, Math.min(1, (colMax[y] - fl) / 35)), p = (SPC.h - 1 - y) * 4;
      img.data[p] = 11 + v * 230; img.data[p + 1] = 16 + v * 225; img.data[p + 2] = 32 + v * 215; img.data[p + 3] = 255;
    }
    o.putImageData(img, SPC.w - 1, 0);
    if (colAct) {
      const top = Math.min(S.nyq, 110000), y = Math.round(SPC.h - 1 - colFreq * 1000 / top * SPC.h);
      o.fillStyle = colF(colFreq, false); for (let dy = -2; dy <= 2; dy++) o.fillRect(SPC.w - 3, y + dy, 3, 1);
      S.nowF = colFreq; S.nowT = tc; S.nowAct = true;
    } else S.nowAct = false;
    colMax.fill(-200); colAct = false; colSnr = 0; colN = 0; S.specDirty = true;
  }
}
function drawSpec() {
  if (!specCtx || !S.specDirty) return; S.specDirty = false;
  specCtx.drawImage(SPC.off, 0, 0);
  const top = Math.min(S.nyq || 125000, 110000);
  specCtx.font = '10px "JetBrains Mono",monospace'; specCtx.textBaseline = 'middle';
  for (const [k, c, l] of [[22, CLS.s22.color, '22'], [31, CLS.s31.color, '31'], [50, CLS.s50.color, '50']]) {
    const y = SPC.h - k * 1000 / top * SPC.h; if (y < 0) continue;
    specCtx.strokeStyle = c; specCtx.globalAlpha = .7; specCtx.setLineDash([4, 4]); specCtx.beginPath(); specCtx.moveTo(0, y); specCtx.lineTo(SPC.w, y); specCtx.stroke();
    specCtx.setLineDash([]); specCtx.globalAlpha = 1; specCtx.fillStyle = '#fff'; specCtx.fillText(l + 'k', 3, y - 6);
  }
}
function drawNow() {
  const act = S.mode === 'mic' && S.nowAct && Date.now() - S.nowT < 600 + 0;
  const e = S.lastEv;
  $('nowClock').textContent = clock(S.mode === 'mic' ? Date.now() : (e ? e.t : S.start || Date.now()));
  if (act) {
    $('nowSwatch').style.background = colF(S.nowF, false); $('nowFreq').textContent = S.nowF.toFixed(1) + ' kHz'; $('nowCls').textContent = '発声中';
  } else if (e && S.mode !== 'idle') {
    const k = classify(e); $('nowSwatch').style.background = colF(e.fmed, k.c === 'unk');
    $('nowFreq').textContent = `直近: ${e.fmed.toFixed(1)} kHz / ${fmtDur(e.dur)}`; $('nowCls').textContent = `${clock(e.t, 1)} — ${CLS[k.c].name}${k.why ? '（' + k.why + '）' : ''}`;
  } else { $('nowSwatch').style.background = '#e5e7eb'; $('nowFreq').textContent = '— kHz'; $('nowCls').textContent = '声なし'; }
}

/* ============ timeline ============ */
const TL = { c: null, g: null, W: 0, H: 0, pad: 0, hover: null, pts: new Map(), drag: null };
const FMIN = 15, FMAX = 105;
const geom = () => { const H = TL.H; return { ruler: 22, strip: 42, lane0: 22 + 42 + 6, laneH: H - (22 + 42 + 6) - 40 - 6, mini0: H - 40, miniH: 34 }; };
function resizeTL() {
  const c = TL.c, w = c.parentElement.clientWidth, h = w < 600 ? 330 : 360, d = DPR();
  c.style.height = h + 'px'; c.width = w * d; c.height = h * d; TL.W = w; TL.H = h; TL.g = c.getContext('2d'); TL.g.setTransform(d, 0, 0, d, 0, 0);
  const l = $('legend'); l.style.height = '54px'; l.width = w * d; l.height = 54 * d; S.dirty = true;
}
const tx = t => (t - S.v0) / (S.v1 - S.v0) * TL.W;
const ty = (k, G) => G.lane0 + G.laneH - (k - FMIN) / (FMAX - FMIN) * G.laneH;
function firstIdx(t) { let lo = 0, hi = S.events.length; while (lo < hi) { const m = (lo + hi) >> 1; if (S.events[m].t < t) lo = m + 1; else hi = m; } return lo; }
function niceStep(span, px) {
  const steps = [.01,.02,.05,.1,.2,.5,1,2,5,10,15,30,60,120,300,600,900,1800,3600,7200,10800,21600,43200,86400];
  const want = span / (px / 100); return steps.find(s => s >= want) || 86400;
}
function drawTL() {
  const g = TL.g, W = TL.W, H = TL.H, G = geom(); if (!g) return;
  g.clearRect(0, 0, W, H); g.fillStyle = '#fff'; g.fillRect(0, 0, W, H);
  const span = (S.v1 - S.v0) / 1000;
  // lane band shading
  const bands = [[18, 26, 'hsl(360 72% 48% / .06)'], [26, 40, 'hsl(225 72% 48% / .06)'], [40, 100, 'hsl(130 70% 38% / .07)']];
  for (const [a, b, c] of bands) { g.fillStyle = c; g.fillRect(0, ty(b, G), W, ty(a, G) - ty(b, G)); }
  g.font = '10px "JetBrains Mono",monospace'; g.textBaseline = 'middle';
  for (const k of [20, 26, 30, 40, 50, 60, 80, 100]) {
    const y = ty(k, G); g.strokeStyle = [26, 40].includes(k) ? '#9ca3af' : '#e5e7eb'; g.setLineDash([k === 26 || k === 40 ? 4 : 0, 3]); g.beginPath(); g.moveTo(0, y); g.lineTo(W, y); g.stroke(); g.setLineDash([]);
    g.fillStyle = '#6b7280'; g.fillText(k + 'k', 3, y - 6);
  }
  // ruler
  const step = niceStep(span, W), t0s = Math.ceil(S.v0 / 1000 / step) * step;
  g.fillStyle = '#f3f4f0'; g.fillRect(0, 0, W, G.ruler); g.strokeStyle = '#d1d5db'; g.beginPath(); g.moveTo(0, G.ruler); g.lineTo(W, G.ruler); g.stroke();
  g.textBaseline = 'middle'; g.fillStyle = '#374151';
  const frac = step < 1 ? (step < .1 ? 2 : 1) : 0;
  for (let s = t0s; s * 1000 <= S.v1; s += step) {
    const x = tx(s * 1000); g.strokeStyle = '#e5e7eb'; g.beginPath(); g.moveTo(x, G.ruler); g.lineTo(x, G.mini0 - 4); g.stroke();
    g.strokeStyle = '#6b7280'; g.beginPath(); g.moveTo(x, G.ruler - 5); g.lineTo(x, G.ruler); g.stroke();
    g.fillText(clock(s * 1000, frac), x + 3, G.ruler / 2 - 1);
  }
  // events
  const E = S.events; TL.pts.clear(); const vis = [];
  for (let i = firstIdx(S.v0 - S.maxDur * 1000 - 1); i < E.length; i++) {
    const e = E[i]; if (e.t > S.v1) break; if (e.t + e.dur * 1000 < S.v0) continue; vis.push(i);
  }
  const unkL = [];
  g.save(); g.beginPath(); g.rect(0, G.ruler + 1, W, G.mini0 - G.ruler - 2); g.clip();
  const draw = (i, k) => {
    const e = E[i], u = k.c === 'unk' ; const x = tx(e.t), w = Math.max(2, e.dur * 1000 / (S.v1 - S.v0) * W);
    const col = colF(e.fmed, u);
    g.fillStyle = col; g.fillRect(x, G.ruler + 4, w, G.strip - 8);
    const y1 = ty(Math.min(FMAX, e.fmax), G), y2 = ty(Math.max(FMIN, e.fmin), G), yc = ty(e.fmed, G), hh = Math.max(4, y2 - y1);
    g.fillRect(x, yc - hh / 2, w, hh);
    if (u) { g.strokeStyle = '#111'; g.lineWidth = 1.5; g.strokeRect(x - .5, G.ruler + 3.5, w + 1, G.strip - 7); g.strokeRect(x - .5, yc - hh / 2 - .5, w + 1, hh + 1); g.lineWidth = 1; }
    if (i === S.sel) { g.strokeStyle = 'hsl(230 100% 57%)'; g.lineWidth = 2.5; g.strokeRect(x - 3, G.ruler + 1, w + 6, G.mini0 - G.ruler - 4); g.lineWidth = 1; }
    TL.pts.set(i, [x, w, yc, hh]);
  };
  for (const i of vis) { const k = classify(E[i]); if (k.c === 'unk') unkL.push([i, k]); else draw(i, k); }
  for (const [i, k] of unkL) draw(i, k);
  if (S.sel >= 0 && !TL.pts.has(S.sel)) {}
  g.restore();
  // markers
  for (const m of S.markers) if (m.t >= S.v0 && m.t <= S.v1) {
    const x = tx(m.t); g.strokeStyle = 'hsl(265 92% 60%)'; g.setLineDash([5, 3]); g.beginPath(); g.moveTo(x, G.ruler); g.lineTo(x, G.mini0 - 4); g.stroke(); g.setLineDash([]);
    g.fillStyle = 'hsl(265 92% 60%)'; g.beginPath(); g.moveTo(x, G.ruler + 1); g.lineTo(x + 9, G.ruler + 5); g.lineTo(x, G.ruler + 9); g.fill();
    if (m.txt) { g.font = '11px "Zen Kaku Gothic New",sans-serif'; g.fillText(m.txt, x + 11, G.ruler + 14); g.font = '10px "JetBrains Mono",monospace'; }
  }
  // now line
  if (S.live && S.end >= S.v0 && S.end <= S.v1) { const x = tx(S.end); g.strokeStyle = '#dc2626'; g.beginPath(); g.moveTo(x, G.ruler); g.lineTo(x, G.mini0 - 4); g.stroke(); }
  if (!E.length) { g.fillStyle = '#9ca3af'; g.font = '14px "Zen Kaku Gothic New",sans-serif'; g.textAlign = 'center'; g.fillText('まだ声が検出されていません', W / 2, G.lane0 + G.laneH / 2); g.textAlign = 'left'; }
  // minimap
  const S0 = S.start, S1 = Math.max(S.live ? Date.now() : S.end, S0 + 1000), mp = t => (t - S0) / (S1 - S0) * W;
  g.fillStyle = '#f3f4f0'; g.fillRect(0, G.mini0, W, G.miniH); g.strokeStyle = '#d1d5db'; g.strokeRect(.5, G.mini0 + .5, W - 1, G.miniH - 1);
  const px = new Array(Math.ceil(W)).fill(null);
  for (let i = 0; i < E.length; i++) { const x = Math.max(0, Math.min(W - 1, Math.floor(mp(E[i].t)))); const u = classify(E[i]).c === 'unk'; if (!px[x] || (u && !px[x].u)) px[x] = { f: E[i].fmed, u }; }
  px.forEach((p, x) => { if (p) { g.fillStyle = p.u ? '#111' : colF(p.f, false); g.fillRect(x, G.mini0 + (p.u ? 3 : 8), 2, G.miniH - (p.u ? 6 : 16)); } });
  const a = mp(S.v0), b = mp(S.v1); g.fillStyle = 'hsl(230 100% 57% / .15)'; g.fillRect(a, G.mini0, Math.max(3, b - a), G.miniH);
  g.strokeStyle = 'hsl(230 100% 57%)'; g.strokeRect(a + .5, G.mini0 + .5, Math.max(3, b - a), G.miniH - 1);
  g.fillStyle = '#6b7280'; g.font = '10px "JetBrains Mono",monospace'; g.fillText(clock(S0), 3, G.mini0 - 2); g.textAlign = 'right'; g.fillText(clock(S1), W - 3, G.mini0 - 2); g.textAlign = 'left';
  // span label
  g.fillStyle = '#374151'; g.textAlign = 'right'; g.fillText(`表示幅 ${span >= 3600 ? (span / 3600).toFixed(1) + ' h' : span >= 60 ? (span / 60).toFixed(1) + ' min' : span.toFixed(2) + ' s'}`, W - 4, G.ruler + 12); g.textAlign = 'left';
}
function drawLegend() {
  const c = $('legend'), g = c.getContext('2d'), d = DPR(), W = c.width / d; g.setTransform(d, 0, 0, d, 0, 0); g.clearRect(0, 0, W, 54); g.fillStyle = '#fff'; g.fillRect(0, 0, W, 54);
  const x0 = 12, x1 = W - 12, fx = k => x0 + (k - 15) / 90 * (x1 - x0);
  for (let x = x0; x <= x1; x++) { const k = 15 + (x - x0) / (x1 - x0) * 90; g.fillStyle = colF(k, false); g.fillRect(x, 8, 1.5, 16); }
  g.font = '10px "JetBrains Mono",monospace'; g.textAlign = 'center'; g.fillStyle = '#374151';
  for (const k of [18, 22, 26, 31, 40, 50, 70, 100]) { const x = fx(k); g.fillRect(x, 24, 1, 5); g.fillText(k + 'k', x, 36); }
  g.font = '11px "Zen Kaku Gothic New",sans-serif'; g.textAlign = 'left';
  g.fillStyle = CLS.s22.color; g.fillText('22k帯', fx(18), 49); g.fillStyle = CLS.s31.color; g.fillText('31k帯', fx(28.5), 49); g.fillStyle = CLS.s50.color; g.fillText('50k帯', fx(52), 49);
  g.fillStyle = '#6b7280'; g.fillText('26k・40k付近の中間色（紫・水色）＝「不明」', fx(62), 49);
  // fix overlap: draw text in a clearer place
}

/* interactions */
function clampView() {
  const S0 = S.start, S1 = Math.max(S.live ? Date.now() : S.end, S0 + 1000), full = Math.max(S1 - S0, 5000);
  let w = Math.max(200, Math.min(S.v1 - S.v0, Math.max(full, 60e3)));
  if (S.follow && S.live) { S.v1 = S1; S.v0 = S1 - w; return; }
  let a = S.v0; if (a + w > S1 + w * .05) a = S1 + w * .05 - w; if (a < S0 - w * .05) a = S0 - w * .05; S.v0 = a; S.v1 = a + w;
}
function zoomAt(t, f) { const w = (S.v1 - S.v0) * f, r = (t - S.v0) / (S.v1 - S.v0); S.v0 = t - w * r; S.v1 = S.v0 + w; clampView(); S.dirty = true; }
function setWidth(sec) {
  const S1 = Math.max(S.live ? Date.now() : S.end, S.start + 1000);
  if (!sec) { S.v0 = S.start; S.v1 = S1; S.follow = false; $('follow').checked = false; }
  else { const c = S.live && S.follow ? S1 - sec * 500 : (S.v0 + S.v1) / 2; S.v0 = c - sec * 500; S.v1 = c + sec * 500; if (S.live && S.follow) S.v1 = S1, S.v0 = S1 - sec * 1000; }
  clampView(); S.dirty = true;
}
function hit(mx, my) {
  const G = geom(); let best = null, bd = 1e9;
  for (const [i, [x, w, yc, hh]] of TL.pts) {
    if (mx < x - 5 || mx > x + w + 5) continue;
    let d = 0; if (my >= G.ruler && my <= G.ruler + G.strip) d = 0; else if (my >= G.lane0) d = Math.abs(my - yc) > hh / 2 + 6 ? 1e8 : Math.abs(my - yc); else continue;
    if (d < bd) { bd = d; best = i; }
  }
  return best;
}
function initTL() {
  const c = TL.c = $('tl'); resizeTL(); new ResizeObserver(() => { resizeTL(); }).observe(c.parentElement);
  const ptrs = new Map(); let pinch = null;
  const pos = e => { const r = c.getBoundingClientRect(); return [e.clientX - r.left, e.clientY - r.top]; };
  c.addEventListener('wheel', e => { e.preventDefault(); const [mx] = pos(e); zoomAt(S.v0 + mx / TL.W * (S.v1 - S.v0), e.deltaY > 0 ? 1.25 : 0.8); S.follow = S.follow && S.live && false; if (S.live) { /* keep follow only if user says */ } $('follow').checked = S.follow; }, { passive: false });
  c.addEventListener('pointerdown', e => {
    c.setPointerCapture(e.pointerId); const [mx, my] = pos(e); ptrs.set(e.pointerId, [mx, my]); const G = geom();
    if (ptrs.size === 2) { const [a, b] = [...ptrs.values()]; pinch = { d: Math.hypot(a[0] - b[0], a[1] - b[1]), mid: S.v0 + (a[0] + b[0]) / 2 / TL.W * (S.v1 - S.v0), w: S.v1 - S.v0 }; TL.drag = null; return; }
    if (my >= G.mini0) { TL.drag = { mini: true }; miniMove(mx); return; }
    TL.drag = { x: mx, v0: S.v0, moved: false };
  });
  c.addEventListener('pointermove', e => {
    const [mx, my] = pos(e);
    if (ptrs.has(e.pointerId)) ptrs.set(e.pointerId, [mx, my]);
    if (pinch && ptrs.size === 2) { const [a, b] = [...ptrs.values()], d = Math.hypot(a[0] - b[0], a[1] - b[1]); const w = pinch.w * pinch.d / Math.max(10, d); const r = ((a[0] + b[0]) / 2) / TL.W; S.v0 = pinch.mid - w * r; S.v1 = S.v0 + w; clampView(); S.dirty = true; return; }
    if (TL.drag) {
      if (TL.drag.mini) { miniMove(mx); return; }
      const dx = mx - TL.drag.x; if (Math.abs(dx) > 3) TL.drag.moved = true;
      if (TL.drag.moved) { const w = S.v1 - S.v0; S.v0 = TL.drag.v0 - dx / TL.W * w; S.v1 = S.v0 + w; S.follow = false; $('follow').checked = false; clampView(); S.dirty = true; hideTip(); }
      return;
    }
    const i = hit(mx, my); if (i !== TL.hover) { TL.hover = i; if (i === null) hideTip(); }
    if (i !== null) showTip(i, mx, my); c.style.cursor = i !== null ? 'pointer' : 'grab';
  });
  const up = e => {
    const [mx, my] = pos(e); ptrs.delete(e.pointerId); if (ptrs.size < 2) pinch = null;
    if (TL.drag && !TL.drag.moved && !TL.drag.mini && ptrs.size === 0) { const i = hit(mx, my); selectEv(i === null ? -1 : i, false); }
    if (ptrs.size === 0) TL.drag = null;
  };
  c.addEventListener('pointerup', up); c.addEventListener('pointercancel', up); c.addEventListener('pointerleave', () => { hideTip(); });
  c.addEventListener('dblclick', () => setWidth(0));
}
function miniMove(mx) {
  const S0 = S.start, S1 = Math.max(S.live ? Date.now() : S.end, S0 + 1000), t = S0 + mx / TL.W * (S1 - S0), w = S.v1 - S.v0;
  S.v0 = t - w / 2; S.v1 = S.v0 + w; S.follow = false; $('follow').checked = false; clampView(); S.dirty = true;
}
function showTip(i, mx, my) {
  const e = S.events[i], k = classify(e), tip = $('tip');
  tip.innerHTML = `${clock(e.t, 3)} → ${clock(e.t + e.dur * 1000, 3)}<br>長さ ${fmtDur(e.dur)}<br>${e.fmed.toFixed(1)} kHz（${e.fmin.toFixed(1)}–${e.fmax.toFixed(1)}）<br><b>${CLS[k.c].name}</b> ${CLS[k.c].label}${k.why ? '<br>' + k.why : ''}`;
  tip.hidden = false; const w = tip.offsetWidth; tip.style.left = Math.min(TL.W - w - 4, mx + 14) + 'px'; tip.style.top = Math.max(2, Math.min(TL.H - 90, my + 10)) + 'px';
}
const hideTip = () => { $('tip').hidden = true; };
function selectEv(i, zoom) {
  S.sel = i; S.dirty = S.dirtyList = true;
  if (i >= 0 && zoom) { const e = S.events[i], w = Math.max(4000, e.dur * 1000 * 6); S.follow = false; $('follow').checked = false; S.v0 = e.t + e.dur * 500 - w / 2; S.v1 = S.v0 + w; clampView(); }
}

/* ============ summary ============ */
function range() { return $('sumRange').value === 'view' ? [S.v0, S.v1] : [S.start, Math.max(S.live ? Date.now() : S.end, S.start + 1000)]; }
function compute() {
  const [r0, r1] = range(), base = $('sumBase').value === '24h' ? 86400 : (r1 - r0) / 1000;
  const o = {}; for (const k of ORDER) o[k] = { n: 0, d: 0 };
  for (let i = firstIdx(r0); i < S.events.length; i++) { const e = S.events[i]; if (e.t >= r1) break; const k = classify(e).c; o[k].n++; o[k].d += e.dur; }
  const N = ORDER.reduce((a, k) => a + o[k].n, 0), D = ORDER.reduce((a, k) => a + o[k].d, 0);
  return { o, N, D, base, r0, r1 };
}
const pct = (a, b) => b > 0 ? a / b * 100 : 0;
function renderSummary() {
  const s = compute(), { o, N, D, base } = s;
  const bar = (el, items) => { el.innerHTML = items.map(([k, v, label]) => v > 0 ? `<div class="${k === 'unk' ? 'unkbg' : ''}" style="width:${v}%;${k === 'quiet' ? 'background:#e5e7eb;color:#6b7280' : k === 'unk' ? '' : 'background:' + CLS[k].color}" title="${label}">${v >= 6 ? v.toFixed(v < 10 ? 1 : 0) + '%' : ''}</div>` : '').join(''); };
  const used = ORDER.map(k => pct(o[k].d, base)), quiet = Math.max(0, 100 - used.reduce((a, b) => a + b, 0));
  bar($('barTime'), [...ORDER.map((k, i) => [k, used[i], CLS[k].name]), ['quiet', quiet, '声なし']]);
  bar($('barDur'), ORDER.map(k => [k, pct(o[k].d, D), CLS[k].name]));
  const tb = $('sumTbl').tBodies[0];
  tb.innerHTML = ORDER.map(k => `<tr><td><span class="dot ${k === 'unk' ? 'unk' : ''}" style="${k === 'unk' ? '' : 'background:' + CLS[k].color}"></span>${CLS[k].name}<br><small>${CLS[k].label}</small></td><td class="mono">${o[k].n}</td><td class="mono">${o[k].d.toFixed(2)} s</td><td class="mono">${pct(o[k].d, base).toFixed(2)}%</td><td class="mono">${pct(o[k].n, N).toFixed(1)}%</td><td class="mono">${pct(o[k].d, D).toFixed(1)}%</td></tr>`).join('') +
    `<tr><td>合計</td><td class="mono">${N}</td><td class="mono">${D.toFixed(2)} s</td><td class="mono">${pct(D, base).toFixed(2)}%</td><td></td><td></td></tr>`;
  const neg = o.s22.n + o.s31.n;
  $('sumLine').innerHTML = `対象 ${clock(s.r0)}〜${clock(s.r1)}（${$('sumBase').value === '24h' ? '24時間' : fmtHMS((s.r1 - s.r0) / 1000)}）。声 ${N} 回のうち、ポジティブ(50 kHz) ${pct(o.s50.n, N).toFixed(1)}% ／ ネガティブ(22+31 kHz) ${pct(neg, N).toFixed(1)}% ／ <b>不明 ${pct(o.unk.n, N).toFixed(1)}%</b>。`;
  // hourly
  const c = $('hourly'), d = DPR(), W = c.clientWidth, H = 130; c.width = W * d; c.height = H * d; const g = c.getContext('2d'); g.setTransform(d, 0, 0, d, 0, 0);
  g.fillStyle = '#fff'; g.fillRect(0, 0, W, H);
  const bins = Array.from({ length: 24 }, () => ({ s22: 0, s31: 0, s50: 0, unk: 0 }));
  for (let i = firstIdx(s.r0); i < S.events.length; i++) { const e = S.events[i]; if (e.t >= s.r1) break; bins[new Date(e.t).getHours()][classify(e).c]++; }
  const mx = Math.max(1, ...bins.map(b => ORDER.reduce((a, k) => a + b[k], 0))), bw = (W - 40) / 24;
  g.font = '10px "JetBrains Mono",monospace'; g.fillStyle = '#6b7280'; g.textAlign = 'right'; g.fillText(mx, 34, 10); g.fillText('0', 34, H - 16);
  const pat = (() => { const p = document.createElement('canvas'); p.width = p.height = 8; const q = p.getContext('2d'); q.fillStyle = '#1f2937'; q.fillRect(0, 0, 8, 8); q.strokeStyle = '#9ca3af'; q.lineWidth = 2; q.beginPath(); q.moveTo(0, 8); q.lineTo(8, 0); q.stroke(); return g.createPattern(p, 'repeat'); })();
  bins.forEach((b, h) => { let y = H - 16; const x = 40 + h * bw;
    for (const k of ORDER) { const hh = b[k] / mx * (H - 30); g.fillStyle = k === 'unk' ? pat : CLS[k].color; g.fillRect(x + 1, y - hh, bw - 2, hh); y -= hh; }
    g.fillStyle = '#6b7280'; g.textAlign = 'center'; if (h % 3 === 0) g.fillText(p2(h), x + bw / 2, H - 4); });
}

/* ============ events table ============ */
const vstart = () => { const v = $('videoStart').value; if (!v) return null; const [h, m, s] = v.split(':').map(Number); const d = new Date(S.start); d.setHours(h, m, s || 0, 0); return d.getTime(); };
function renderList() {
  const only = $('onlyUnk').checked, vs = vstart(), rows = []; let shown = 0;
  for (let i = S.events.length - 1; i >= 0 && shown < 400; i--) {
    const e = S.events[i], k = classify(e); if (only && k.c !== 'unk') continue; shown++;
    const vp = vs !== null ? (() => { const s = (e.t - vs) / 1000; return s < 0 ? '—' : `${p2(Math.floor(s / 60))}:${p2(Math.floor(s % 60))}`; })() : '—';
    rows.push(`<tr data-i="${i}" class="${k.c === 'unk' ? 'unk' : ''} ${i === S.sel ? 'sel' : ''}"><td class="mono">${clock(e.t, 2)}</td><td class="mono">${vp}</td><td class="mono">${fmtDur(e.dur)}</td><td class="mono">${e.fmed.toFixed(1)} <small>(${e.fmin.toFixed(0)}–${e.fmax.toFixed(0)})</small></td><td><span class="dot ${k.c === 'unk' ? 'unk' : ''}" style="${k.c === 'unk' ? '' : 'background:' + CLS[k.c].color}"></span>${CLS[k.c].name}</td><td><small>${k.why || ''}</small></td><td>${S.clips.has(e.id) ? `<button class="b" data-play="${i}">▶ ×0.1</button> <button class="b" data-wav="${i}">WAV</button>` : ''}</td></tr>`);
  }
  $('evTbl').tBodies[0].innerHTML = rows.join('');
  $('evNote').textContent = `${S.events.length} 件中、新しい順に最大400件を表示。行をクリックすると、その瞬間まで時間履歴が拡大します。▶ は「不明」の声の前後を10倍ゆっくり（聞こえる高さで）再生します。`;
}
let pctx = null;
function playClip(i) {
  const c = S.clips.get(S.events[i].id); if (!c) return;
  pctx = pctx || new (window.AudioContext || window.webkitAudioContext)(); if (pctx.state === 'suspended') pctx.resume();
  const b = pctx.createBuffer(1, c.data.length, c.fs), ch = b.getChannelData(0); for (let k = 0; k < ch.length; k++) ch[k] = c.data[k] / 32768;
  const s = pctx.createBufferSource(); s.buffer = b; s.playbackRate.value = 0.1; s.connect(pctx.destination); s.start();
}
function wavBlob(c) {
  const n = c.data.length, buf = new ArrayBuffer(44 + n * 2), v = new DataView(buf), w = (o, s) => [...s].forEach((ch, k) => v.setUint8(o + k, ch.charCodeAt(0)));
  w(0, 'RIFF'); v.setUint32(4, 36 + n * 2, true); w(8, 'WAVE'); w(12, 'fmt '); v.setUint32(16, 16, true); v.setUint16(20, 1, true); v.setUint16(22, 1, true);
  v.setUint32(24, c.fs, true); v.setUint32(28, c.fs * 2, true); v.setUint16(32, 2, true); v.setUint16(34, 16, true); w(36, 'data'); v.setUint32(40, n * 2, true);
  new Int16Array(buf, 44).set(c.data); return new Blob([buf], { type: 'audio/wav' });
}
function download(name, blob) { const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name; document.body.appendChild(a); a.click(); setTimeout(() => { URL.revokeObjectURL(a.href); a.remove(); }, 500); }
function csvEvents() {
  const vs = vstart(), rows = [['type', 'date', 'clock', 'epoch_ms', 'duration_s', 'f_median_kHz', 'f_min_kHz', 'f_max_kHz', 'snr_dB', 'class', 'label', 'unknown_reason', 'video_pos', 'note']];
  const all = [...S.events.map(e => ({ k: 'call', t: e.t, e })), ...S.markers.map(m => ({ k: 'marker', t: m.t, m }))].sort((a, b) => a.t - b.t);
  for (const x of all) {
    const vp = vs !== null ? (() => { const s = (x.t - vs) / 1000; return s < 0 ? '' : `${p2(Math.floor(s / 60))}:${p2(Math.floor(s % 60))}`; })() : '';
    if (x.k === 'call') { const e = x.e, k = classify(e); rows.push(['call', dateStr(e.t), clock(e.t, 3), Math.round(e.t), e.dur.toFixed(4), e.fmed.toFixed(2), e.fmin.toFixed(2), e.fmax.toFixed(2), e.snr.toFixed(1), CLS[k.c].name, CLS[k.c].label, k.why, vp, '']); }
    else rows.push(['marker', dateStr(x.t), clock(x.t, 3), Math.round(x.t), '', '', '', '', '', '', '', '', vp, x.m.txt]);
  }
  return '﻿' + rows.map(r => r.map(c => /[",\n]/.test(String(c)) ? '"' + String(c).replace(/"/g, '""') + '"' : c).join(',')).join('\r\n');
}
function csvSummary() {
  const s = compute(), rows = [['range_start', 'range_end', 'base_s', 'class', 'label', 'calls', 'total_s', 'pct_of_base', 'pct_calls', 'pct_call_time']];
  for (const k of ORDER) rows.push([clock(s.r0), clock(s.r1), s.base.toFixed(1), CLS[k].name, CLS[k].label, s.o[k].n, s.o[k].d.toFixed(3), pct(s.o[k].d, s.base).toFixed(3), pct(s.o[k].n, s.N).toFixed(2), pct(s.o[k].d, s.D).toFixed(2)]);
  return '﻿' + rows.map(r => r.join(',')).join('\r\n');
}


/* ============ realtime blob ============ */
const B = { f: 31, a: 0, hold: 0, t0: performance.now(), sim: null };
function blobState() {
  const now = Date.now();
  if (B.sim) { // simulated voice sequence
    const p = (performance.now() - B.sim) / 1000, seq = [[55, .6], [31, .5], [22, 1.6], [27, .5], [40.5, .5], [52, .6], [35, .4]];
    let tot = seq.reduce((a, x) => a + x[1] + .6, 0), q = p % tot;
    for (const [f, d] of seq) { if (q < d) return { act: true, f, snr: 28 + 8 * Math.sin(p * 20) }; q -= d + .6; }
    return { act: false };
  }
  if (S.mode === 'mic' && S.nowAct && now - S.nowT < 300) return { act: true, f: S.nowF, snr: S.nowSnr || 25 };
  return { act: false };
}
function drawBlob() {
  const c = $('blob'), d = DPR(), W = c.clientWidth, H = c.clientHeight; if (!W) return;
  if (c.width !== Math.round(W * d)) { c.width = Math.round(W * d); c.height = Math.round(H * d); }
  const g = c.getContext('2d'); g.setTransform(d, 0, 0, d, 0, 0); g.clearRect(0, 0, W, H); g.fillStyle = '#fff'; g.fillRect(0, 0, W, H);
  const st = blobState(), t = (performance.now() - B.t0) / 1000;
  if (st.act) { B.f += (st.f - B.f) * .5; B.hold = 1; B.a += (Math.min(1, Math.max(.35, st.snr / 40)) - B.a) * .3; }
  else { B.a *= .9; B.hold = Math.max(0, B.hold - 1 / 90); }
  const cx = W / 2, cy = H / 2, base = Math.min(W, H) * .27, k = classify({ fmed: B.f, dur: B.f <= 26 ? .6 : .1, fmin: B.f, fmax: B.f });
  const hue = hueF(B.f), vis = B.hold, sat = st.act || vis > 0 ? 80 * vis + 5 : 0;
  const R = base * (1 + .12 * B.a) , pts = 72;
  g.beginPath();
  for (let i = 0; i <= pts; i++) {
    const a = i / pts * Math.PI * 2;
    const w = Math.sin(a * 3 + t * 5) * .5 + Math.sin(a * 5 - t * 7) * .35 + Math.sin(a * 8 + t * 11) * .25;
    const r = R * (1 + .02 * Math.sin(t * 1.5 + a * 2) + B.a * .16 * w);
    const x = cx + Math.cos(a) * r, y = cy + Math.sin(a) * r; i ? g.lineTo(x, y) : g.moveTo(x, y);
  }
  g.closePath();
  const gr = g.createRadialGradient(cx, cy, R * .1, cx, cy, R * 1.2);
  gr.addColorStop(0, `hsl(${hue} ${sat}% ${58 - 6 * vis}%)`); gr.addColorStop(1, `hsl(${hue} ${sat}% ${40 + 20 * (1 - vis)}%)`);
  g.shadowColor = `hsla(${hue},${sat}%,45%,${.5 * vis})`; g.shadowBlur = 30 * vis; g.fillStyle = gr; g.fill(); g.shadowBlur = 0;
  g.lineWidth = 3; g.strokeStyle = `hsla(${hue},${sat}%,35%,${.4 + .5 * vis})`; g.stroke();
  g.textAlign = 'center'; g.textBaseline = 'middle'; g.fillStyle = vis > .15 ? '#fff' : '#6b7280'; g.shadowColor = '#0006'; g.shadowBlur = vis > .15 ? 4 : 0;
  if (vis > .05) {
    g.font = `700 ${Math.round(R * .26)}px "Space Grotesk","Zen Kaku Gothic New",sans-serif`; g.fillText(B.f.toFixed(1) + ' kHz', cx, cy - R * .15);
    g.font = `500 ${Math.round(R * .17)}px "Zen Kaku Gothic New",sans-serif`;
    g.fillText(k.c === 'unk' ? '不明（中間）' : CLS[k.c].label, cx, cy + R * .12);
    if (k.why) { g.font = `400 ${Math.round(R * .11)}px "Zen Kaku Gothic New",sans-serif`; g.fillText(k.why.split('・')[0], cx, cy + R * .34); }
  } else { g.font = `500 ${Math.round(R * .17)}px "Zen Kaku Gothic New",sans-serif`; g.fillText(S.mode === 'mic' || B.sim ? '声を待っています…' : '待機中', cx, cy); }
  g.shadowBlur = 0;
}

/* ============ main loop ============ */
let lastSlow = 0;
function tick() {
  requestAnimationFrame(tick);
  const now = Date.now();
  if (S.live) { S.end = now; S.dirty = true; if (S.follow) clampView(); }
  if (S.mode === 'mic') { $('statusPill').textContent = `REC ${fmtClock(now - S.start)}　声 ${S.events.length}`; }
  drawSpec(); drawBlob();
  if (S.dirty) { S.dirty = false; drawTL(); }
  if (now - lastSlow > 700 || S.dirtyList) {
    if (S.dirtyList || S.live) { renderSummary(); } lastSlow = now; drawNow();
    if (S.dirtyList) { S.dirtyList = false; renderList(); if (S.mode === 'idle' || S.mode === 'demo' || S.mode === 'file') setMode(S.mode === 'file' && !fileAbort && $('prog').hidden === false ? 'file' : 'idle'); }
  }
}
const fmtClock = ms => { const s = Math.floor(ms / 1000); return `${p2(Math.floor(s / 3600))}:${p2(Math.floor(s % 3600 / 60))}:${p2(s % 60)}`; };

/* ============ init ============ */
function init() {
  initSpec(); initTL(); drawLegend();
  $('btnMic').onclick = startMic;
  $('btnStop').onclick = () => { stopAll(false); };
  $('fileIn').onchange = e => { const f = e.target.files[0]; e.target.value = ''; analyzeFile(f); };
  $('btnSim').onclick = () => { B.sim = B.sim ? null : performance.now(); $('btnSim').textContent = B.sim ? '模擬を止める' : '動作確認（模擬の声）'; };
  $('btnDemo').onclick = demo; $('btnMark').onclick = mark;
  $('btnClear').onclick = () => { if (!S.events.length || confirm('記録を全部消しますか？（CSVを保存していない場合は戻せません）')) { stopAll(true); resetData(); S.mode = 'idle'; setMode('idle'); setInfo('記録をクリアしました。', false); } };
  document.querySelectorAll('[data-w]').forEach(b => b.onclick = () => { setWidth(+b.dataset.w); });
  $('zIn').onclick = () => zoomAt((S.v0 + S.v1) / 2, .5); $('zOut').onclick = () => zoomAt((S.v0 + S.v1) / 2, 2);
  $('follow').onchange = e => { S.follow = e.target.checked; if (S.follow) { clampView(); } S.dirty = true; };
  $('sumRange').onchange = $('sumBase').onchange = () => { S.dirtyList = true; };
  $('onlyUnk').onchange = $('videoStart').onchange = () => { S.dirtyList = true; };
  $('csvEv').onclick = () => download(`usv_calls_${dateStr(S.start)}.csv`, new Blob([csvEvents()], { type: 'text/csv' }));
  $('csvSum').onclick = () => download(`usv_summary_${dateStr(S.start)}.csv`, new Blob([csvSummary()], { type: 'text/csv' }));
  $('evTbl').addEventListener('click', e => {
    const p = e.target.closest('[data-play]'); if (p) { playClip(+p.dataset.play); return; }
    const w = e.target.closest('[data-wav]'); if (w) { const i = +w.dataset.wav, ev = S.events[i]; download(`usv_${dateStr(ev.t)}_${clock(ev.t, 0).replace(/:/g, '')}.wav`, wavBlob(S.clips.get(ev.id))); return; }
    const tr = e.target.closest('tr[data-i]'); if (tr) selectEv(+tr.dataset.i, true);
  });
  const sl = (id, out, key, f) => { const el = $(id), up = () => { cfg[key] = +el.value; $(out).textContent = f(+el.value); S.dirty = S.dirtyList = true; }; el.oninput = up; up(); };
  sl('cThr', 'vThr', 'thr', v => v + ' dB'); sl('cMargin', 'vMargin', 'margin', v => v + ' kHz'); sl('cMin', 'vMin', 'minDur', v => v + ' ms');
  $('cDur').onchange = e => { cfg.useDur = e.target.checked; S.dirty = S.dirtyList = true; };
  document.addEventListener('keydown', e => { if ((e.key === 'm' || e.key === 'M') && !/INPUT|SELECT|TEXTAREA/.test(document.activeElement.tagName)) mark(); });
  window.addEventListener('resize', () => { S.dirty = S.dirtyList = true; drawLegend(); });
  resetData(); S.v1 = S.v0 + 300e3; setMode('idle'); checkRestore(); requestAnimationFrame(tick);
  window.__USV = { S, cfg, classify, Detector, hueF };
}
init();
})();
