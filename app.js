(() => {
  const $ = (id) => document.getElementById(id);
  const output = $('console-output');
  const input = $('command-input');
  const vars = Object.create(null);
  const history = [];
  let historyIndex = 0;
  let plotState = null;
  let plotTitle = '';
  let xLabel = '';
  let yLabel = '';

  const isMatrix = (x) => Array.isArray(x);
  const isVector = (x) => isMatrix(x) && !x.some(Array.isArray);
  const matrix = (x) => isVector(x) ? [x] : x;
  const mapDeep = (x, fn) => isMatrix(x) ? x.map((v) => mapDeep(v, fn)) : fn(x);
  const shape = (x) => !isMatrix(x) ? '1×1' : isVector(x) ? `1×${x.length}` : `${x.length}×${(x[0] || []).length}`;
  const formatNum = (x) => Number.isInteger(x) ? String(x) : Number(x.toPrecision(7)).toString();
  const format = (x) => isMatrix(x) ? (isVector(x) ? `[${x.map(format).join('  ')}]` : `[${x.map((r) => r.map(format).join('  ')).join('; ')}]`) : typeof x === 'number' ? formatNum(x) : String(x);
  const sizeValue = (x) => isMatrix(x) ? (isVector(x) ? [1, x.length] : [x.length, (x[0] || []).length]) : [1, 1];
  const numeric = (x) => typeof x === 'number' && Number.isFinite(x);

  function elementwise(a, b, fn) {
    if (!isMatrix(a) && !isMatrix(b)) return fn(a, b);
    const aa = isMatrix(a) ? matrix(a) : null;
    const bb = isMatrix(b) ? matrix(b) : null;
    const rows = aa ? aa.length : bb.length;
    const cols = aa ? aa[0].length : bb[0].length;
    if (aa && bb && (aa.length !== bb.length || aa[0].length !== bb[0].length)) throw Error('Matrix dimensions must agree.');
    const out = Array.from({ length: rows }, (_, r) => Array.from({ length: cols }, (_, c) => fn(aa ? aa[r][c] : a, bb ? bb[r][c] : b)));
    return isVector(a) && isVector(b) || (isVector(a) && !isMatrix(b)) || (!isMatrix(a) && isVector(b)) ? out[0] : out;
  }
  function multiply(a, b) {
    if (!isMatrix(a) || !isMatrix(b)) return elementwise(a, b, (x, y) => x * y);
    const A = matrix(a), B = matrix(b);
    if (A[0].length !== B.length) throw Error('Inner matrix dimensions must agree for multiplication.');
    const out = A.map((row) => B[0].map((_, c) => row.reduce((s, v, k) => s + v * B[k][c], 0)));
    return isVector(a) && isVector(b) ? out[0][0] : isVector(a) ? out[0] : out;
  }

  function determinant(value) {
    if (!isMatrix(value)) throw Error('det expects a square matrix.');
    const A = matrix(value).map((row) => row.slice());
    const n = A.length;
    if (!n || A.some((row) => !Array.isArray(row) || row.length !== n)) throw Error('det expects a square matrix.');
    if (A.some((row) => row.some((v) => !numeric(v)))) throw Error('det requires a numeric matrix.');
    let det = 1;
    for (let col = 0; col < n; col++) {
      let pivot = col;
      for (let row = col + 1; row < n; row++) if (Math.abs(A[row][col]) > Math.abs(A[pivot][col])) pivot = row;
      if (Math.abs(A[pivot][col]) < Number.EPSILON) return 0;
      if (pivot !== col) { [A[pivot], A[col]] = [A[col], A[pivot]]; det = -det; }
      const pivotValue = A[col][col];
      det *= pivotValue;
      for (let row = col + 1; row < n; row++) {
        const factor = A[row][col] / pivotValue;
        for (let j = col + 1; j < n; j++) A[row][j] -= factor * A[col][j];
      }
    }
    return Math.abs(det) < Number.EPSILON ? 0 : det;
  }

  function tokenize(source) {
    const tokens = [];
    const re = /\s+|'(?:\\.|[^'\\])*'|"(?:\\.|[^"\\])*"|(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?|[A-Za-z_]\w*|\.\*|\.\/|\.\^|==|~=|<=|>=|[+\-*\/%^=(),;:\[\]<>]/gy;
    let pos = 0;
    while (pos < source.length) {
      re.lastIndex = pos;
      const m = re.exec(source);
      if (!m) throw Error(`Unexpected character “${source[pos]}”.`);
      pos = re.lastIndex;
      if (!/^\s+$/.test(m[0])) tokens.push(m[0]);
    }
    tokens.push('<eof>');
    return tokens;
  }

  function evaluate(source) {
    const tokens = tokenize(source);
    let i = 0;
    const peek = () => tokens[i];
    const take = () => tokens[i++];
    const expect = (v) => { if (take() !== v) throw Error(`Expected “${v}”.`); };
    const precedence = { '==': 1, '~=': 1, '<': 1, '>': 1, '<=': 1, '>=': 1, '+': 2, '-': 2, '*': 3, '/': 3, '.*': 3, './': 3, '^': 4, '.^': 4 };
    function expression(min = 0) {
      let left = primary();
      while ((precedence[peek()] || 0) > min) {
        const op = take(), p = precedence[op], right = expression(p - (p === 4 ? 1 : 0));
        const ops = {
          '+': (a, b) => elementwise(a, b, (x, y) => x + y), '-': (a, b) => elementwise(a, b, (x, y) => x - y),
          '*': multiply, '.*': (a, b) => elementwise(a, b, (x, y) => x * y), '/': (a, b) => elementwise(a, b, (x, y) => x / y), './': (a, b) => elementwise(a, b, (x, y) => x / y),
          '^': (a, b) => elementwise(a, b, (x, y) => x ** y), '.^': (a, b) => elementwise(a, b, (x, y) => x ** y),
          '==': (a, b) => a === b, '~=': (a, b) => a !== b, '<': (a, b) => a < b, '>': (a, b) => a > b, '<=': (a, b) => a <= b, '>=': (a, b) => a >= b
        };
        left = ops[op](left, right);
      }
      return left;
    }
    function primary() {
      const t = take();
      if ((t.startsWith("'") && t.endsWith("'")) || (t.startsWith('"') && t.endsWith('"'))) return t.slice(1, -1).replace(/\\([\\'"nrt])/g, (_, c) => ({ n: '\n', r: '\r', t: '\t' }[c] || c));
      if (t === '+' || t === '-') { const v = primary(); return t === '-' ? mapDeep(v, (n) => -n) : v; }
      if (t === '(') { const v = expression(); expect(')'); return v; }
      if (t === '[') {
        const rows = [[]];
        while (peek() !== ']' && peek() !== '<eof>') {
          if (peek() === ';') { take(); rows.push([]); continue; }
          if (peek() === ',') { take(); continue; }
          const v = expression();
          if (isMatrix(v)) rows[rows.length - 1].push(...(isVector(v) ? v : v.flat())); else rows[rows.length - 1].push(v);
        }
        expect(']');
        const width = rows[0].length;
        if (rows.some((r) => r.length !== width)) throw Error('Rows in a matrix must have the same number of columns.');
        return rows.length === 1 ? rows[0] : rows;
      }
      if (t === '<eof>') throw Error('Expected an expression.');
      if (/^(?:\d|\.)/.test(t)) return Number(t);
      if (/^[A-Za-z_]/.test(t)) {
        if (t === 'pi') return Math.PI;
        if (t === 'Inf') return Infinity;
        if (peek() === '(') {
          take(); const args = [];
          if (peek() !== ')') { do { args.push(expression()); if (peek() !== ',') break; take(); } while (true); }
          expect(')'); return callFunction(t, args);
        }
        if (!(t in vars)) throw Error(`Undefined variable “${t}”.`);
        return vars[t];
      }
      throw Error(`Unexpected token “${t}”.`);
    }
    const result = expression();
    if (peek() !== '<eof>') throw Error(`Unexpected token “${peek()}”.`);
    return result;
  }

  function callFunction(name, args) {
    const a = args[0];
    const math = { sin: Math.sin, cos: Math.cos, tan: Math.tan, asin: Math.asin, acos: Math.acos, atan: Math.atan, sqrt: Math.sqrt, abs: Math.abs, exp: Math.exp, log10: Math.log10, log2: Math.log2, floor: Math.floor, ceil: Math.ceil, round: Math.round, sign: Math.sign };
    if (math[name]) return mapDeep(a, math[name]);
    switch (name) {
      case 'log': return args.length > 1 ? elementwise(a, args[1], (x, base) => Math.log(x) / Math.log(base)) : mapDeep(a, Math.log);
      case 'linspace': { const start = args[0], end = args[1], n = Math.max(0, Math.floor(args[2] ?? 100)); return n <= 1 ? [start] : Array.from({ length: n }, (_, i) => start + (end - start) * i / (n - 1)); }
      case 'zeros': case 'ones': { const d = isMatrix(a) ? a : args.slice(0, 2); const r = d[0] || 1, c = d[1] || r; return Array.from({ length: r }, () => Array(c).fill(name === 'ones' ? 1 : 0)); }
      case 'eye': { const n = a; return Array.from({ length: n }, (_, r) => Array.from({ length: n }, (_, c) => r === c ? 1 : 0)); }
      case 'size': return sizeValue(a);
      case 'det': return determinant(a);
      case 'sum': case 'mean': { const flat = (isMatrix(a) ? a.flat(Infinity) : [a]); const s = flat.reduce((x, y) => x + y, 0); return name === 'mean' ? s / flat.length : s; }
      case 'min': case 'max': { const flat = args.flatMap((x) => isMatrix(x) ? x.flat(Infinity) : [x]); return Math[name](...flat); }
      case 'plot': drawPlot(args[0], args[1]); return 'Figure updated';
      case 'title': plotTitle = String(a); drawPlot(); return plotTitle;
      case 'xlabel': xLabel = String(a); drawPlot(); return xLabel;
      case 'ylabel': yLabel = String(a); drawPlot(); return yLabel;
      case 'disp': return a;
      default: throw Error(`Unknown function “${name}”. Try help for supported functions.`);
    }
  }

  function appendLine(text, className = '') {
    const line = document.createElement('div'); line.className = `console-line ${className}`; line.textContent = text; output.appendChild(line); output.scrollTop = output.scrollHeight;
  }
  function runLine(raw) {
    const source = raw.replace(/%.*$/, '').trim();
    if (!source) return;
    if (/^help$/i.test(source)) { appendLine('Supported: vectors [1 2 3], matrices [1 2; 3 4], + - * ./ ^, linspace, zeros, ones, eye, size, det, sum, mean, sin, cos, tan, sqrt, abs, exp, log(x[,base]), log2, log10, plot, clear.', 'result-line'); return; }
    if (/^clc$/i.test(source)) { output.innerHTML = ''; return; }
    if (/^clear(?:\s+all)?$/i.test(source)) { Object.keys(vars).forEach((k) => delete vars[k]); renderVars(); appendLine('Workspace cleared.', 'result-line'); return; }
    const suppress = /;\s*$/.test(source);
    const clean = source.replace(/;\s*$/, '').trim();
    try {
      const assignment = clean.match(/^([A-Za-z_]\w*)\s*=\s*(.+)$/s);
      const result = assignment ? evaluate(assignment[2]) : evaluate(clean);
      if (assignment) { vars[assignment[1]] = result; renderVars(); }
      if (!suppress && result !== undefined) appendLine(`${assignment ? assignment[1] + ' = ' : ''}${format(result)}`, 'result-line');
    } catch (err) { appendLine(`Error: ${err.message}`, 'error-line'); }
  }
  function runScript(source) { source.split(/\r?\n/).forEach((line) => { if (line.trim() && !line.trim().startsWith('%')) { appendLine(`>> ${line}`, 'input-line'); runLine(line); } }); }
  function renderVars() {
    const body = $('variable-rows'); const keys = Object.keys(vars).sort();
    $('variable-count').textContent = keys.length;
    if (!keys.length) { body.innerHTML = '<tr class="empty-row"><td colspan="3">Variables you create will show up here.</td></tr>'; return; }
    body.innerHTML = '';
    keys.forEach((key) => { const row = document.createElement('tr'); const n = document.createElement('td'), v = document.createElement('td'), s = document.createElement('td'); n.textContent = key; n.className = 'variable-name'; v.textContent = format(vars[key]); v.title = v.textContent; s.textContent = shape(vars[key]); row.append(n, v, s); body.appendChild(row); });
  }
  function drawPlot(xArg, yArg) {
    if (xArg !== undefined && yArg !== undefined) plotState = { x: isMatrix(xArg) ? xArg.flat(Infinity) : [xArg], y: isMatrix(yArg) ? yArg.flat(Infinity) : [yArg] };
    const canvas = $('plot-canvas'), wrap = canvas.parentElement, ctx = canvas.getContext('2d');
    if (!plotState) return;
    $('plot-empty').hidden = true; canvas.hidden = false;
    const ratio = window.devicePixelRatio || 1; canvas.width = Math.max(1, wrap.clientWidth * ratio); canvas.height = Math.max(1, wrap.clientHeight * ratio); canvas.style.width = `${wrap.clientWidth}px`; canvas.style.height = `${wrap.clientHeight}px`; ctx.scale(ratio, ratio);
    const w = wrap.clientWidth, h = wrap.clientHeight, pad = { l: 48, r: 20, t: plotTitle ? 42 : 24, b: 42 };
    const x = plotState.x, y = plotState.y, count = Math.min(x.length, y.length);
    const xmin = Math.min(...x.slice(0, count)), xmax = Math.max(...x.slice(0, count)), ymin = Math.min(...y.slice(0, count)), ymax = Math.max(...y.slice(0, count));
    const dx = xmax - xmin || 1, dy = ymax - ymin || 1;
    const px = (v) => pad.l + (v - xmin) / dx * (w - pad.l - pad.r), py = (v) => h - pad.b - (v - ymin) / dy * (h - pad.t - pad.b);
    ctx.clearRect(0, 0, w, h); ctx.font = '11px system-ui'; ctx.fillStyle = '#778396'; ctx.strokeStyle = '#293341'; ctx.lineWidth = 1;
    for (let i = 0; i <= 4; i++) { const gy = pad.t + (h - pad.t - pad.b) * i / 4; ctx.beginPath(); ctx.moveTo(pad.l, gy); ctx.lineTo(w - pad.r, gy); ctx.stroke(); const val = ymax - dy * i / 4; ctx.fillText(formatNum(val), 4, gy + 4); }
    for (let i = 0; i <= 4; i++) { const gx = pad.l + (w - pad.l - pad.r) * i / 4; ctx.beginPath(); ctx.moveTo(gx, pad.t); ctx.lineTo(gx, h - pad.b); ctx.stroke(); ctx.fillText(formatNum(xmin + dx * i / 4), gx - 10, h - 16); }
    ctx.strokeStyle = '#47b7a4'; ctx.lineWidth = 2; ctx.beginPath();
    for (let i = 0; i < count; i++) { const xx = px(x[i]), yy = py(y[i]); if (i === 0) ctx.moveTo(xx, yy); else ctx.lineTo(xx, yy); }
    ctx.stroke(); ctx.fillStyle = '#dce5ed'; ctx.textAlign = 'center'; if (plotTitle) ctx.fillText(plotTitle, w / 2, 20); if (xLabel) ctx.fillText(xLabel, w / 2, h - 2); ctx.textAlign = 'left';
    $('plot-caption').textContent = `${count} data points${yLabel ? ` · ${yLabel}` : ''}`;
  }
  $('command-form').addEventListener('submit', (event) => { event.preventDefault(); const command = input.value.trim(); if (!command) return; history.push(command); historyIndex = history.length; appendLine(`>> ${command}`, 'input-line'); runLine(command); input.value = ''; });
  input.addEventListener('keydown', (event) => { if (event.key === 'ArrowUp') { event.preventDefault(); historyIndex = Math.max(0, historyIndex - 1); input.value = history[historyIndex] || ''; } if (event.key === 'ArrowDown') { event.preventDefault(); historyIndex = Math.min(history.length, historyIndex + 1); input.value = history[historyIndex] || ''; } });
  $('run-script').addEventListener('click', () => runScript($('script-editor').value));
  $('script-editor').addEventListener('input', (event) => { $('line-numbers').innerHTML = Array.from({ length: event.target.value.split('\n').length }, (_, i) => i + 1).join('<br>'); });
  $('clear-button').addEventListener('click', () => { output.innerHTML = ''; });
  $('help-button').addEventListener('click', () => $('help-dialog').showModal());
  $('theme-button').addEventListener('click', () => document.body.classList.toggle('light-theme'));
  const formatLatexSource = (source) => {
    const tokens = source.trim().split(/(\\begin\{[^}]+\}|\\end\{[^}]+\}|\\\\)/g).filter(Boolean);
    const lines = [];
    let depth = 0;
    let line = '';
    const flush = () => {
      if (line.trim()) lines.push(`${'  '.repeat(depth)}${line.trim()}`);
      line = '';
    };
    tokens.forEach((token) => {
      if (token.startsWith('\\begin{')) {
        flush();
        lines.push(`${'  '.repeat(depth)}${token}`);
        depth++;
      } else if (token.startsWith('\\end{')) {
        flush();
        depth = Math.max(0, depth - 1);
        lines.push(`${'  '.repeat(depth)}${token}`);
      } else if (token === '\\\\') {
        line = `${line.trimEnd()} \\\\`;
        flush();
      } else {
        line += token;
      }
    });
    flush();
    return lines.join('\n');
  };
  const renderLatex = () => {
    const preview = $('latex-preview');
    const status = $('latex-status');
    const source = $('latex-input').value.trim();
    preview.textContent = source ? `\\[${source}\\]` : 'Enter a LaTeX expression to preview it.';
    if (!source || !window.MathJax?.typesetPromise) {
      if (source) status.textContent = 'Math renderer is still loading. Try Render again shortly.';
      return;
    }
    window.MathJax.typesetClear([preview]);
    window.MathJax.typesetPromise([preview]).then(() => {
      status.textContent = 'Rendered with MathJax';
    }).catch(() => {
      status.textContent = 'Could not render this expression. Check the LaTeX syntax.';
    });
  };
  $('latex-format').addEventListener('click', () => {
    $('latex-input').value = formatLatexSource($('latex-input').value);
    $('latex-status').textContent = 'Formatted environments and line breaks';
    renderLatex();
  });
  $('latex-render').addEventListener('click', renderLatex);
  window.addEventListener('load', () => {
    if (window.MathJax?.startup?.promise) window.MathJax.startup.promise.then(renderLatex);
  });
  $('download-plot').addEventListener('click', () => { if (!plotState) return; const a = document.createElement('a'); a.download = 'figure.png'; a.href = $('plot-canvas').toDataURL('image/png'); a.click(); });
  document.querySelectorAll('.example-link').forEach((button) => button.addEventListener('click', () => {
    const examples = {
      plot: 'x = linspace(0, 2*pi, 100);\ny = sin(x);\nplot(x, y);\ntitle(\'Sine wave\');',
      matrix: 'A = [1 2; 3 4]\nb = [5 6; 7 8]\nC = A + b',
      function: 'x = linspace(0, 2*pi, 100);\ny = cos(x);\nplot(x, y);\ntitle(\'Cosine wave\');',
      logs: 'x = [2 10 100];\nln_x = log(x);\nlog2_x = log2(x);\nlog10_x = log10(x);\nlog_base_3_of_81 = log(81, 3)',
      statistics: 'measurements = [4 7 9 10 15];\ntotal = sum(measurements);\naverage = mean(measurements);\nsmallest = min(measurements);\nlargest = max(measurements)',
      determinant: 'A = [4 7; 2 6]\ndet_A = det(A)'
    };
    $('script-editor').value = examples[button.dataset.example]; $('script-editor').dispatchEvent(new Event('input')); runScript($('script-editor').value);
  }));
  document.querySelectorAll('.side-item').forEach((button) => button.addEventListener('click', () => {
    document.querySelectorAll('.side-item').forEach((item) => {
      const isActive = item === button;
      item.classList.toggle('active', isActive);
      if (isActive) item.setAttribute('aria-current', 'location');
      else item.removeAttribute('aria-current');
    });
    const target = { command: 'command-panel', editor: 'editor-panel', variables: 'variables-panel', plots: 'plot-panel' }[button.dataset.panel];
    document.querySelector(`.${target}`).scrollIntoView({ behavior: 'smooth', block: 'center' });
  }));
  window.addEventListener('resize', () => { if (plotState) drawPlot(); });  
})();
