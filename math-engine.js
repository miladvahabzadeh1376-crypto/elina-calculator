/* ELINA math engine: safe recursive-descent/Pratt parser; no eval or Function. */
(function (root) {
  'use strict';
  const FUNCTIONS = new Set(['sin','cos','tan','asin','acos','atan','ln','log','sqrt','cbrt','abs','exp','floor','ceil','round']);
  const MAX_BITS = 12000;

  function absBig(n) { return n < 0n ? -n : n; }
  function gcd(a,b) { a=absBig(a); b=absBig(b); while(b){const t=a%b;a=b;b=t;} return a||1n; }
  function guard(n,d) {
    if (n.toString(2).length > MAX_BITS || d.toString(2).length > MAX_BITS) throw new Error('اندازه عدد از حد ایمن این نسخه بیشتر است.');
  }
  function rat(n,d=1n) {
    n=BigInt(n); d=BigInt(d);
    if(d===0n) throw new Error('تقسیم بر صفر مجاز نیست.');
    if(d<0n){n=-n;d=-d;}
    const g=gcd(n,d); n/=g; d/=g; guard(n,d);
    return {kind:'r',n,d};
  }
  function fl(x) {
    if(!Number.isFinite(x)) throw new Error('نتیجه خارج از محدوده اعداد قابل نمایش است.');
    return {kind:'f',x};
  }
  function isRat(v){return v.kind==='r';}
  function floorDiv(n,d){let q=n/d,r=n%d;if(r!==0n&&n<0n)q--;return q;}

  function decimalValue(s) {
    const parts=s.toLowerCase().split('e');
    if(parts.length>2) throw new Error('عدد اعشاری نامعتبر است.');
    const exponent=parts.length===2?Number(parts[1]):0;
    if(!Number.isInteger(exponent)||Math.abs(exponent)>1000) throw new Error('توان ده‌دهی خارج از محدوده است.');
    const p=parts[0].split('.');
    const fraction=(p[1]||'').length;
    const digits=(p[0]+(p[1]||''))||'0';
    let n=BigInt(digits), scale=fraction-exponent, d=1n;
    if(Math.abs(scale)>1000) throw new Error('دقت ورودی خارج از محدوده است.');
    if(scale>=0) d=10n**BigInt(scale); else n*=10n**BigInt(-scale);
    return rat(n,d);
  }
  function toNumber(v) {
    if(!isRat(v)) return v.x;
    const x=Number(formatRat(v,17));
    if(!Number.isFinite(x)) throw new Error('این عدد برای تابع علمی خارج از محدوده محاسبات شناور است.');
    return x;
  }
  function add(a,b){return isRat(a)&&isRat(b)?rat(a.n*b.d+b.n*a.d,a.d*b.d):fl(toNumber(a)+toNumber(b));}
  function sub(a,b){return isRat(a)&&isRat(b)?rat(a.n*b.d-b.n*a.d,a.d*b.d):fl(toNumber(a)-toNumber(b));}
  function mul(a,b){return isRat(a)&&isRat(b)?rat(a.n*b.n,a.d*b.d):fl(toNumber(a)*toNumber(b));}
  function div(a,b){if(isRat(b)?b.n===0n:b.x===0)throw new Error('تقسیم بر صفر مجاز نیست.');return isRat(a)&&isRat(b)?rat(a.n*b.d,a.d*b.n):fl(toNumber(a)/toNumber(b));}
  function modulo(a,b){
    if(isRat(b)?b.n===0n:b.x===0) throw new Error('باقیمانده بر صفر تعریف نشده است.');
    if(isRat(a)&&isRat(b)){const q=floorDiv(a.n*b.d,a.d*b.n);return sub(a,mul(rat(q),b));}
    return fl(toNumber(a)%toNumber(b));
  }
  function power(a,b){
    if(isRat(a)&&isRat(b)&&b.d===1n){
      const e=b.n;
      if(absBig(e)>3000n) throw new Error('توان صحیح بیش از محدوده ایمن است.');
      if(a.n===0n&&e<0n) throw new Error('صفر به توان منفی تعریف نشده است.');
      if(e===0n) return rat(1n);
      const p=absBig(e),n=a.n**p,d=a.d**p;
      return e<0n?rat(d,n):rat(n,d);
    }
    const x=Math.pow(toNumber(a),toNumber(b));
    if(Number.isNaN(x)) throw new Error('این توان در مجموعه اعداد حقیقی تعریف نشده است.');
    return fl(x);
  }
  function isqrt(n){if(n<2n)return n;let x=n,y=(x+1n)/2n;while(y<x){x=y;y=(x+n/x)/2n;}return x;}
  function sqrtValue(v){
    if(isRat(v)){
      if(v.n<0n) throw new Error('ریشه دوم عدد منفی در اعداد حقیقی تعریف نشده است.');
      const a=isqrt(v.n),b=isqrt(v.d);
      if(a*a===v.n&&b*b===v.d)return rat(a,b);
    }
    return fl(Math.sqrt(toNumber(v)));
  }
  function factorial(v){
    let n;
    if(isRat(v)){if(v.d!==1n)throw new Error('فاکتوریل فقط برای اعداد صحیح نامنفی تعریف شده است.');n=v.n;}
    else {if(!Number.isInteger(v.x))throw new Error('فاکتوریل فقط برای اعداد صحیح تعریف شده است.');n=BigInt(v.x);}
    if(n<0n||n>1000n)throw new Error('فاکتوریل این نسخه برای اعداد صحیح ۰ تا ۱۰۰۰ پشتیبانی می‌شود.');
    let z=1n;for(let i=2n;i<=n;i++)z*=i;return rat(z);
  }
  function applyFunction(name,v,angleMode){
    if(name==='sqrt')return sqrtValue(v);
    if(name==='abs')return isRat(v)?rat(absBig(v.n),v.d):fl(Math.abs(v.x));
    const x=toNumber(v),rad=angleMode==='DEG'?Math.PI/180:1; let y;
    switch(name){
      case 'sin': y=Math.sin(x*rad);break;
      case 'cos': y=Math.cos(x*rad);break;
      case 'tan': if(Math.abs(Math.cos(x*rad))<1e-14)throw new Error('تانژانت در این زاویه تعریف نشده است.'); y=Math.tan(x*rad);break;
      case 'asin': if(Math.abs(x)>1)throw new Error('دامنه آرک‌سینوس بین ۱- و ۱ است.'); y=Math.asin(x)/rad;break;
      case 'acos': if(Math.abs(x)>1)throw new Error('دامنه آرک‌کسینوس بین ۱- و ۱ است.'); y=Math.acos(x)/rad;break;
      case 'atan': y=Math.atan(x)/rad;break;
      case 'ln': if(x<=0)throw new Error('لگاریتم طبیعی فقط برای عدد مثبت تعریف شده است.'); y=Math.log(x);break;
      case 'log': if(x<=0)throw new Error('لگاریتم فقط برای عدد مثبت تعریف شده است.'); y=Math.log10(x);break;
      case 'cbrt': y=Math.cbrt(x);break;
      case 'exp': y=Math.exp(x);break;
      case 'floor': return isRat(v)?rat(floorDiv(v.n,v.d)):rat(BigInt(Math.floor(x)));
      case 'ceil': return isRat(v)?rat(-floorDiv(-v.n,v.d)):rat(BigInt(Math.ceil(x)));
      case 'round': return rat(BigInt(Math.round(x)));
      default: throw new Error('تابع ناشناخته است: '+name);
    }
    if(!Number.isFinite(y))throw new Error('خروجی تابع در محدوده قابل نمایش نیست.');
    if(['sin','cos','tan'].includes(name)&&Math.abs(y)<1e-15)y=0;
    return fl(y);
  }

  function formatRat(v,precision=15){
    let n=v.n,d=v.d;
    if(n===0n)return '0';
    const neg=n<0n;n=absBig(n);
    let k=n.toString().length-d.toString().length;
    if(k>=0){if(n<d*10n**BigInt(k))k--;}
    else if(n*10n**BigInt(-k)<d)k--;
    const scale=precision-1-k; let a=n,b=d;
    if(scale>=0)a*=10n**BigInt(scale);else b*=10n**BigInt(-scale);
    let q=a/b,r=a%b;if(2n*r>=b)q++;
    if(q>=10n**BigInt(precision)){q/=10n;k++;}
    const digits=q.toString().padStart(precision,'0');let s;
    if(k>=precision||k<=-7){let m=digits[0]+'.'+digits.slice(1).replace(/0+$/,'');if(m.endsWith('.'))m=m.slice(0,-1);s=m+'e'+(k>=0?'+':'')+k;}
    else if(k>=0){const p=k+1;s=p>=digits.length?digits+'0'.repeat(p-digits.length):digits.slice(0,p)+'.'+digits.slice(p);if(s.includes('.'))s=s.replace(/0+$/,'').replace(/\.$/,'');}
    else{s='0.'+'0'.repeat(-k-1)+digits;s=s.replace(/0+$/,'').replace(/\.$/,'');}
    return (neg?'-':'')+s;
  }
  function formatFloat(x){
    if(x===0)return '0';
    let s=x.toPrecision(15);
    if(s.includes('e')){const p=s.split('e');return p[0].replace(/0+$/,'').replace(/\.$/,'')+'e'+(Number(p[1])>=0?'+':'')+Number(p[1]);}
    return s.includes('.')?s.replace(/0+$/,'').replace(/\.$/,''):s;
  }
  function format(v){return isRat(v)?formatRat(v):formatFloat(v.x);}
  function describe(v){
    if(!isRat(v))return 'نتیجه تابع علمی با محاسبات شناور استاندارد؛ نمایش حدود ۱۵ رقم معنادار.';
    if(v.d===1n)return 'نتیجه با حساب صحیح دقیق نگهداری شده است.';
    const s=v.n.toString()+'/'+v.d.toString();return 'کسر دقیق: '+(s.length<=90?s:'مقدار کسری دقیق در حافظه حفظ شده است.');
  }

  function tokenize(source){
    const src=source.replaceAll('×','*').replaceAll('÷','/').replaceAll('−','-').replaceAll('π','pi').replaceAll('√','sqrt');
    const out=[];let i=0;
    while(i<src.length){
      if(/\s/.test(src[i])){i++;continue;}
      const rest=src.slice(i);let m=rest.match(/^(?:\d+(?:\.\d*)?|\.\d+)(?:e[+-]?\d+)?/i);
      if(m){out.push({t:'num',v:m[0]});i+=m[0].length;continue;}
      m=rest.match(/^[a-zA-Z]+/);
      if(m){const s=m[0].toLowerCase();
        if(FUNCTIONS.has(s))out.push({t:'fn',v:s});
        else if(s==='pi'||s==='e')out.push({t:'const',v:s});
        else if(s==='ans')out.push({t:'ans',v:s});
        else if(s==='m')out.push({t:'mem',v:s});
        else if(s==='mod')out.push({t:'op',v:s});
        else throw new Error('نام یا تابع ناشناخته: '+m[0]);
        i+=m[0].length;continue;
      }
      const c=src[i];
      if('+-*/^!%()'.includes(c)){out.push({t:c==='('? 'lp':c===')'?'rp':'op',v:c});i++;continue;}
      throw new Error('نویسه نامعتبر: '+c);
    }
    const ends=t=>['num','const','ans','mem','rp'].includes(t.t)||(t.t==='op'&&(t.v==='!'||t.v==='%'));
    const starts=t=>['num','const','ans','mem','fn','lp'].includes(t.t);
    const expanded=[];
    for(const t of out){const p=expanded[expanded.length-1];if(p&&ends(p)&&starts(t))expanded.push({t:'op',v:'*'});expanded.push(t);}
    return expanded;
  }
  class Parser{
    constructor(source,context){this.tokens=tokenize(source);this.i=0;this.context=context;}
    peek(){return this.tokens[this.i];}
    take(){return this.tokens[this.i++];}
    expression(minBP=0){
      const first=this.take();if(!first)throw new Error('عبارت ناقص است.');let left;
      if(first.t==='num')left=decimalValue(first.v);
      else if(first.t==='const')left=first.v==='pi'?fl(Math.PI):fl(Math.E);
      else if(first.t==='ans'){if(this.context.ans===null)throw new Error('هنوز نتیجه قبلی برای Ans وجود ندارد.');left=this.context.ans;}
      else if(first.t==='mem')left=this.context.memory;
      else if(first.t==='lp'){left=this.expression(0);if(this.peek()?.t!=='rp')throw new Error('پرانتز بسته نشده است.');this.take();}
      else if(first.t==='fn'){
        if(this.peek()?.t!=='lp')throw new Error('تابع را همراه پرانتز بنویس؛ مانند sin(30).');
        this.take();left=this.expression(0);if(this.peek()?.t!=='rp')throw new Error('پرانتز تابع بسته نشده است.');this.take();left=applyFunction(first.v,left,this.context.angleMode);
      }
      else if(first.t==='op'&&(first.v==='+'||first.v==='-')){left=this.expression(25);if(first.v==='-')left=isRat(left)?rat(-left.n,left.d):fl(-left.x);}
      else throw new Error('ساختار عبارت ریاضی معتبر نیست.');

      while(this.i<this.tokens.length){
        const token=this.peek();
        if(token.t==='op'&&(token.v==='!'||token.v==='%')){
          const bp=40;if(bp<minBP)break;this.take();left=token.v==='!'?factorial(left):div(left,rat(100n));continue;
        }
        if(token.t!=='op')break;
        const lbp=({'+':10,'-':10,'*':20,'/':20,'mod':20,'^':30})[token.v];
        if(lbp===undefined||lbp<minBP)break;
        this.take();const rbp=token.v==='^'?lbp:lbp+1;const right=this.expression(rbp);
        switch(token.v){case '+':left=add(left,right);break;case '-':left=sub(left,right);break;case '*':left=mul(left,right);break;case '/':left=div(left,right);break;case 'mod':left=modulo(left,right);break;case '^':left=power(left,right);break;}
      }
      return left;
    }
    parse(){if(!this.tokens.length)throw new Error('ابتدا یک عبارت وارد کن.');const value=this.expression(0);if(this.i<this.tokens.length)throw new Error('بخش اضافی یا ناقص در عبارت وجود دارد.');return value;}
  }
  function calculate(source,context){return new Parser(source,context).parse();}
  const api={calculate,format,describe,rat,fl,isRat,toNumber};
  if(typeof module!=='undefined'&&module.exports)module.exports=api;
  root.ElinaMath=api;
})(typeof window!=='undefined'?window:globalThis);
