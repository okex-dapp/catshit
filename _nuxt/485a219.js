/*!For license information please see LICENSES*/(window.webpackJsonp=window.webpackJsonp||[]).push([[4],{1683:function(t,e,n){"use strict";n(44),n(15),n(29),n(7),n(56),n(17),n(57);var o=n(8),r=n(51);function c(object,t){var e=Object.keys(object);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(object);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(object,t).enumerable}))),e.push.apply(e,n)}return e}var l={computed:function(t){for(var i=1;i<arguments.length;i++){var source=null!=arguments[i]?arguments[i]:{};i%2?c(Object(source),!0).forEach((function(e){Object(o.a)(t,e,source[e])})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(source)):c(Object(source)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(source,e))}))}return t}({},Object(r.c)(["user"])),methods:{login:function(){this.$store.dispatch("modal/login")}}},h=l,f=n(12),component=Object(f.a)(h,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return t.user?n("div",[t._t("default")],2):n("div",{staticClass:"confirm-button"},[n("el-button",{staticClass:"w-100",attrs:{type:"primary"},on:{click:t.login}},[t._v(t._s(t.$t("Connect Wallet")))])],1)}),[],!1,null,null,null);e.a=component.exports},1684:function(t,e,n){"use strict";var o={props:{high:{default:!1,type:Boolean}}},r=(n(1689),n(12)),component=Object(r.a)(o,(function(){var t=this,e=t.$createElement;return(t._self._c||e)("div",{class:["spacer",{high:t.high}]})}),[],!1,null,"2836b060",null);e.a=component.exports},1685:function(t,e,n){var content=n(1690);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("7be39ddd",content,!0,{sourceMap:!1})},1689:function(t,e,n){"use strict";n(1685)},1690:function(t,e,n){var o=n(46)(!1);o.push([t.i,".spacer[data-v-2836b060]{height:8px}.high[data-v-2836b060]{height:14px}",""]),t.exports=o},1717:function(t,e,n){"use strict";n.d(e,"a",(function(){return h}));var o=n(6),r=n(2),c=(n(52),n(7),n(15),n(27),n(28),n(23),n(24),n(33),n(34),n(35),n(36),n(37),n(17),n(16),n(38),n(25),n(95));function l(){l=function(){return t};var t={},e=Object.prototype,n=e.hasOwnProperty,r="function"==typeof Symbol?Symbol:{},c=r.iterator||"@@iterator",h=r.asyncIterator||"@@asyncIterator",f=r.toStringTag||"@@toStringTag";function d(t,e,n){return Object.defineProperty(t,e,{value:n,enumerable:!0,configurable:!0,writable:!0}),t[e]}try{d({},"")}catch(t){d=function(t,e,n){return t[e]=n}}function m(t,e,n,o){var r=e&&e.prototype instanceof w?e:w,c=Object.create(r.prototype),l=new S(o||[]);return c._invoke=function(t,e,n){var o="suspendedStart";return function(r,c){if("executing"===o)throw new Error("Generator is already running");if("completed"===o){if("throw"===r)throw c;return I()}for(n.method=r,n.arg=c;;){var l=n.delegate;if(l){var h=E(l,n);if(h){if(h===y)continue;return h}}if("next"===n.method)n.sent=n._sent=n.arg;else if("throw"===n.method){if("suspendedStart"===o)throw o="completed",n.arg;n.dispatchException(n.arg)}else"return"===n.method&&n.abrupt("return",n.arg);o="executing";var f=v(t,e,n);if("normal"===f.type){if(o=n.done?"completed":"suspendedYield",f.arg===y)continue;return{value:f.arg,done:n.done}}"throw"===f.type&&(o="completed",n.method="throw",n.arg=f.arg)}}}(t,n,l),c}function v(t,e,n){try{return{type:"normal",arg:t.call(e,n)}}catch(t){return{type:"throw",arg:t}}}t.wrap=m;var y={};function w(){}function x(){}function k(){}var _={};d(_,c,(function(){return this}));var O=Object.getPrototypeOf,C=O&&O(O(T([])));C&&C!==e&&n.call(C,c)&&(_=C);var j=k.prototype=w.prototype=Object.create(_);function F(t){["next","throw","return"].forEach((function(e){d(t,e,(function(t){return this._invoke(e,t)}))}))}function L(t,e){function r(c,l,h,f){var d=v(t[c],t,l);if("throw"!==d.type){var m=d.arg,y=m.value;return y&&"object"==Object(o.a)(y)&&n.call(y,"__await")?e.resolve(y.__await).then((function(t){r("next",t,h,f)}),(function(t){r("throw",t,h,f)})):e.resolve(y).then((function(t){m.value=t,h(m)}),(function(t){return r("throw",t,h,f)}))}f(d.arg)}var c;this._invoke=function(t,n){function o(){return new e((function(e,o){r(t,n,e,o)}))}return c=c?c.then(o,o):o()}}function E(t,e){var n=t.iterator[e.method];if(void 0===n){if(e.delegate=null,"throw"===e.method){if(t.iterator.return&&(e.method="return",e.arg=void 0,E(t,e),"throw"===e.method))return y;e.method="throw",e.arg=new TypeError("The iterator does not provide a 'throw' method")}return y}var o=v(n,t.iterator,e.arg);if("throw"===o.type)return e.method="throw",e.arg=o.arg,e.delegate=null,y;var r=o.arg;return r?r.done?(e[t.resultName]=r.value,e.next=t.nextLoc,"return"!==e.method&&(e.method="next",e.arg=void 0),e.delegate=null,y):r:(e.method="throw",e.arg=new TypeError("iterator result is not an object"),e.delegate=null,y)}function A(t){var e={tryLoc:t[0]};1 in t&&(e.catchLoc=t[1]),2 in t&&(e.finallyLoc=t[2],e.afterLoc=t[3]),this.tryEntries.push(e)}function $(t){var e=t.completion||{};e.type="normal",delete e.arg,t.completion=e}function S(t){this.tryEntries=[{tryLoc:"root"}],t.forEach(A,this),this.reset(!0)}function T(t){if(t){var e=t[c];if(e)return e.call(t);if("function"==typeof t.next)return t;if(!isNaN(t.length)){var i=-1,o=function e(){for(;++i<t.length;)if(n.call(t,i))return e.value=t[i],e.done=!1,e;return e.value=void 0,e.done=!0,e};return o.next=o}}return{next:I}}function I(){return{value:void 0,done:!0}}return x.prototype=k,d(j,"constructor",k),d(k,"constructor",x),x.displayName=d(k,f,"GeneratorFunction"),t.isGeneratorFunction=function(t){var e="function"==typeof t&&t.constructor;return!!e&&(e===x||"GeneratorFunction"===(e.displayName||e.name))},t.mark=function(t){return Object.setPrototypeOf?Object.setPrototypeOf(t,k):(t.__proto__=k,d(t,f,"GeneratorFunction")),t.prototype=Object.create(j),t},t.awrap=function(t){return{__await:t}},F(L.prototype),d(L.prototype,h,(function(){return this})),t.AsyncIterator=L,t.async=function(e,n,o,r,c){void 0===c&&(c=Promise);var l=new L(m(e,n,o,r),c);return t.isGeneratorFunction(n)?l:l.next().then((function(t){return t.done?t.value:l.next()}))},F(j),d(j,f,"Generator"),d(j,c,(function(){return this})),d(j,"toString",(function(){return"[object Generator]"})),t.keys=function(object){var t=[];for(var e in object)t.push(e);return t.reverse(),function e(){for(;t.length;){var n=t.pop();if(n in object)return e.value=n,e.done=!1,e}return e.done=!0,e}},t.values=T,S.prototype={constructor:S,reset:function(t){if(this.prev=0,this.next=0,this.sent=this._sent=void 0,this.done=!1,this.delegate=null,this.method="next",this.arg=void 0,this.tryEntries.forEach($),!t)for(var e in this)"t"===e.charAt(0)&&n.call(this,e)&&!isNaN(+e.slice(1))&&(this[e]=void 0)},stop:function(){this.done=!0;var t=this.tryEntries[0].completion;if("throw"===t.type)throw t.arg;return this.rval},dispatchException:function(t){if(this.done)throw t;var e=this;function o(n,o){return c.type="throw",c.arg=t,e.next=n,o&&(e.method="next",e.arg=void 0),!!o}for(var i=this.tryEntries.length-1;i>=0;--i){var r=this.tryEntries[i],c=r.completion;if("root"===r.tryLoc)return o("end");if(r.tryLoc<=this.prev){var l=n.call(r,"catchLoc"),h=n.call(r,"finallyLoc");if(l&&h){if(this.prev<r.catchLoc)return o(r.catchLoc,!0);if(this.prev<r.finallyLoc)return o(r.finallyLoc)}else if(l){if(this.prev<r.catchLoc)return o(r.catchLoc,!0)}else{if(!h)throw new Error("try statement without catch or finally");if(this.prev<r.finallyLoc)return o(r.finallyLoc)}}}},abrupt:function(t,e){for(var i=this.tryEntries.length-1;i>=0;--i){var o=this.tryEntries[i];if(o.tryLoc<=this.prev&&n.call(o,"finallyLoc")&&this.prev<o.finallyLoc){var r=o;break}}r&&("break"===t||"continue"===t)&&r.tryLoc<=e&&e<=r.finallyLoc&&(r=null);var c=r?r.completion:{};return c.type=t,c.arg=e,r?(this.method="next",this.next=r.finallyLoc,y):this.complete(c)},complete:function(t,e){if("throw"===t.type)throw t.arg;return"break"===t.type||"continue"===t.type?this.next=t.arg:"return"===t.type?(this.rval=this.arg=t.arg,this.method="return",this.next="end"):"normal"===t.type&&e&&(this.next=e),y},finish:function(t){for(var i=this.tryEntries.length-1;i>=0;--i){var e=this.tryEntries[i];if(e.finallyLoc===t)return this.complete(e.completion,e.afterLoc),$(e),y}},catch:function(t){for(var i=this.tryEntries.length-1;i>=0;--i){var e=this.tryEntries[i];if(e.tryLoc===t){var n=e.completion;if("throw"===n.type){var o=n.arg;$(e)}return o}}throw new Error("illegal catch attempt")},delegateYield:function(t,e,n){return this.delegate={iterator:T(t),resultName:e,nextLoc:n},"next"===this.method&&(this.arg=void 0),y}},t}function h(t,e){return f.apply(this,arguments)}function f(){return(f=Object(r.a)(l().mark((function t(e,n){var o;return l().wrap((function(t){for(;;)switch(t.prev=t.next){case 0:return o=new c.JsonRpc("".concat(n.protocol,"://").concat(n.host,":").concat(n.port),{fetch:fetch}),t.prev=1,t.next=4,o.get_account(e);case 4:return t.abrupt("return",!0);case 7:return t.prev=7,t.t0=t.catch(1),t.abrupt("return",!1);case 10:case"end":return t.stop()}}),t,null,[[1,7]])})))).apply(this,arguments)}},1718:function(t,e,n){"use strict";n.d(e,"a",(function(){return o}));var o={methods:{showPopupWarning:function(t,e){var n=this;return this.$confirm(t.mess,t.title,{confirmButtonText:"OK",cancelButtonText:"Cancel",type:"warning"}).then((function(){return!1})).catch((function(){return n.$notify({type:"info",title:e,message:"".concat(e," canceled")}),!0}))}}}},1730:function(t,e,n){"use strict";n(44),n(15),n(56),n(17),n(57);var o=n(8),r=(n(397),n(201),n(53),n(29),n(7),n(65),n(76),n(39),n(396),n(112),n(174),n(51));function c(object,t){var e=Object.keys(object);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(object);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(object,t).enumerable}))),e.push.apply(e,n)}return e}function l(t){for(var i=1;i<arguments.length;i++){var source=null!=arguments[i]?arguments[i]:{};i%2?c(Object(source),!0).forEach((function(e){Object(o.a)(t,e,source[e])})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(source)):c(Object(source)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(source,e))}))}return t}var h={components:{TokenImage:n(395).a},props:{value:{type:[String,Number],default:function(){return"0.0000"}},tokens:{type:Array,default:function(){return[]}},token:{type:[Number,Object],default:function(){return""}},readonly:{type:Boolean,default:function(){return!1}},static:{type:Boolean,default:function(){return!1}}},data:function(){return{content:this.value,visible:!1,search:""}},computed:l(l(l(l({},Object(r.e)(["user"])),Object(r.e)("swap",["input","output"])),Object(r.c)({tokens0:"swap/tokens0",tokens1:"swap/tokens1",pair:"swap/current",inputBalance:"swap/inputBalance",outputBalance:"swap/outputBalance",poolOne:"swap/poolOne",poolTwo:"swap/poolTwo"})),{},{isTokenSelected:function(){return this.token&&this.token.contract&&this.token.symbol||0==this.token&&this.input||1==this.token&&this.output||!1},tokensFiltered:function(){var t=this;return this.tokens.filter((function(e){return(e.symbol+"@"+e.contract).toLowerCase().includes(t.search.toLowerCase())})).map((function(e){return e.balance=t.$tokenBalance(e.symbol||e.currency,e.contract),e})).sort((function(a,b){return"0.0000"==a.balance?1:-1})).sort((function(a,b){return parseFloat(a.balance)<parseFloat(b.balance)?1:-1}))}}),watch:{value:function(){this.content=this.value},token:function(){this.fixedInput()}},mounted:function(){this.popupItem=this.$el},methods:{hide:function(){this.visible=!1},toggle:function(){var t=this;this.static||(this.visible=!this.visible,this.visible&&setTimeout((function(){t.$refs.searchInput.focus()}),10))},handleInput:function(content){this.$emit("input",content)},isActiveToken:function(t){return!(0!=this.token||!this.input||this.input.symbol!=t.symbol||this.input.contract!=t.contract)||(!(1!=this.token||!this.output||this.output.symbol!=t.symbol||this.output.contract!=t.contract)||!!(this.token&&this.token.contract&&this.token.symbol&&this.token.symbol==t.symbol&&this.token.contract==t.contract))},inputChange:function(t){this.$emit("inputchange",t),this.fixedInput()},fixedInput:function(){var t=null;0==this.token&&(t=this.input.precision),1==this.token&&(t=this.output.precision),this.token&&this.token.symbol&&this.token.contract&&(t=this.token.precision),t&&(this.content=(parseFloat(this.content)||0).toFixed(t))},setToken:function(t){this.$emit("change",t);var input=this.input,output=this.output;0==this.token&&(this.$store.commit("swap/setInput",t),output&&t.contract==output.contract&&t.symbol==output.symbol?this.$store.commit("swap/setOutput",input):output&&!this.tokens1.filter((function(t){return t.contract==output.contract&&t.symbol==output.symbol}))[0]&&(this.tokens1?this.$store.commit("swap/setOutput",this.tokens1[0]):this.$store.commit("swap/setOutput",null))),1==this.token&&(this.$store.commit("swap/setOutput",t),input&&t.contract==input.contract&&input.symbol==output.symbol?this.$store.commit("swap/setInput",output):input&&!this.tokens0.filter((function(t){return t.contract==input.contract&&t.symbol==input.symbol}))[0]&&(this.tokens0?this.$store.commit("swap/setInput",this.tokens0[0]):this.$store.commit("swap/setInput",null))),this.visible=!1}}},f=(n(1928),n(12)),component=Object(f.a)(h,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"swap-token-select"},[n("div",{staticClass:"row"},[n("div",{directives:[{name:"click-outside",rawName:"v-click-outside",value:t.hide,expression:"hide"}],staticClass:"col"},[n("div",{staticClass:"multi-input-wrapper",style:t.visible?"z-index: 2;":""},[n("el-input",{attrs:{type:"number",clearable:!t.static,placeholder:"0.0",readonly:t.readonly||t.static},on:{input:t.handleInput,change:t.inputChange},model:{value:t.content,callback:function(e){t.content=e},expression:"content"}},[n("template",{slot:"append"},[t.isTokenSelected?n("el-button",{attrs:{type:"text"},on:{click:t.toggle}},[0==t.token?n("div",{staticClass:"d-flex align-items-center"},[n("TokenImage",{attrs:{src:t.$tokenLogo(t.input.symbol,t.input.contract),height:"25"}}),n("span",{staticClass:"ml-2"},[t._v(t._s(t.input.symbol))]),t.static?n("i",{staticClass:"ml-2"}):n("i",{staticClass:"el-icon-bottom ml-1"})],1):1==t.token?n("div",{staticClass:"d-flex align-items-center"},[n("TokenImage",{attrs:{src:t.$tokenLogo(t.output.symbol,t.output.contract),height:"25"}}),n("span",{staticClass:"ml-2"},[t._v(t._s(t.output.symbol))]),t.static?n("i",{staticClass:"ml-2"}):n("i",{staticClass:"el-icon-bottom ml-1"})],1):t.token&&t.token.contract&&t.token.symbol?n("div",{staticClass:"d-flex align-items-center"},[n("TokenImage",{attrs:{src:t.$tokenLogo(t.token.symbol,t.token.contract),height:"25"}}),n("span",{staticClass:"ml-2"},[t._v(t._s(t.token.symbol))]),t.static?n("i",{staticClass:"ml-2"}):n("i",{staticClass:"el-icon-bottom ml-1"})],1):t._e()]):t.static?t._e():n("el-button",{attrs:{type:"text"},on:{click:t.toggle}},[t._v("Select token"),t.static?n("i",{staticClass:"ml-2"}):n("i",{staticClass:"el-icon-bottom ml-1"})])],1)],2)],1),n("div",{directives:[{name:"show",rawName:"v-show",value:t.visible,expression:"visible"}],staticClass:"dropdown"},[n("el-input",{ref:"searchInput",attrs:{placeholder:t.$t("Search by name or contract"),clearable:!t.static,size:"small"},model:{value:t.search,callback:function(e){t.search=e},expression:"search"}}),n("recycle-scroller",{staticClass:"scroller",attrs:{"emit-update":!0,items:t.tokensFiltered,"item-size":"45",keyField:"symbol"},scopedSlots:t._u([{key:"default",fn:function(e){var o=e.item;return[n("div",{key:o.symbol,staticClass:"pair",class:{isActive:t.isActiveToken(o)},on:{click:function(e){return t.setToken(o)}}},[n("TokenImage",{attrs:{src:t.$tokenLogo(o.symbol,o.contract),height:"25"}}),n("span",{staticClass:"ml-2"},[t._v(t._s(o.symbol))]),n("div",{staticClass:"text-muted ml-2 small"},[t._v(t._s(o.contract))]),t.user?n("div",{staticClass:"ml-auto"},[n("span",{staticClass:"text-muted"},[t._v(t._s(t._f("commaFloat")(o.balance)))])]):t._e()],1)]}}])})],1)])])])}),[],!1,null,null,null);e.a=component.exports},1751:function(t,e,n){var content=n(1929);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("08d3f913",content,!0,{sourceMap:!1})},1752:function(t,e,n){var content=n(1931);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("e4460334",content,!0,{sourceMap:!1})},1753:function(t,e,n){var content=n(1933);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("61209612",content,!0,{sourceMap:!1})},1861:function(t,e,n){"use strict";n(15),n(27),n(7),n(28),n(23),n(24),n(33),n(34),n(35),n(36),n(37),n(17),n(38),n(25),n(44),n(29),n(56),n(57);var o=n(6),r=n(8),c=n(2),l=(n(16),n(174),n(52),n(112),n(397),n(176)),h=n.n(l),f=n(54),d=n(51),m=n(151),v=n(1717),y=n(68),w=n.n(y),x=n(1683),k=n(1730),_=n(1684),O=n(113),C=n(1718);function j(object,t){var e=Object.keys(object);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(object);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(object,t).enumerable}))),e.push.apply(e,n)}return e}function F(t){for(var i=1;i<arguments.length;i++){var source=null!=arguments[i]?arguments[i]:{};i%2?j(Object(source),!0).forEach((function(e){Object(r.a)(t,e,source[e])})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(source)):j(Object(source)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(source,e))}))}return t}function L(){L=function(){return t};var t={},e=Object.prototype,n=e.hasOwnProperty,r="function"==typeof Symbol?Symbol:{},c=r.iterator||"@@iterator",l=r.asyncIterator||"@@asyncIterator",h=r.toStringTag||"@@toStringTag";function f(t,e,n){return Object.defineProperty(t,e,{value:n,enumerable:!0,configurable:!0,writable:!0}),t[e]}try{f({},"")}catch(t){f=function(t,e,n){return t[e]=n}}function d(t,e,n,o){var r=e&&e.prototype instanceof y?e:y,c=Object.create(r.prototype),l=new S(o||[]);return c._invoke=function(t,e,n){var o="suspendedStart";return function(r,c){if("executing"===o)throw new Error("Generator is already running");if("completed"===o){if("throw"===r)throw c;return I()}for(n.method=r,n.arg=c;;){var l=n.delegate;if(l){var h=E(l,n);if(h){if(h===v)continue;return h}}if("next"===n.method)n.sent=n._sent=n.arg;else if("throw"===n.method){if("suspendedStart"===o)throw o="completed",n.arg;n.dispatchException(n.arg)}else"return"===n.method&&n.abrupt("return",n.arg);o="executing";var f=m(t,e,n);if("normal"===f.type){if(o=n.done?"completed":"suspendedYield",f.arg===v)continue;return{value:f.arg,done:n.done}}"throw"===f.type&&(o="completed",n.method="throw",n.arg=f.arg)}}}(t,n,l),c}function m(t,e,n){try{return{type:"normal",arg:t.call(e,n)}}catch(t){return{type:"throw",arg:t}}}t.wrap=d;var v={};function y(){}function w(){}function x(){}var k={};f(k,c,(function(){return this}));var _=Object.getPrototypeOf,O=_&&_(_(T([])));O&&O!==e&&n.call(O,c)&&(k=O);var C=x.prototype=y.prototype=Object.create(k);function j(t){["next","throw","return"].forEach((function(e){f(t,e,(function(t){return this._invoke(e,t)}))}))}function F(t,e){function r(c,l,h,f){var d=m(t[c],t,l);if("throw"!==d.type){var v=d.arg,y=v.value;return y&&"object"==Object(o.a)(y)&&n.call(y,"__await")?e.resolve(y.__await).then((function(t){r("next",t,h,f)}),(function(t){r("throw",t,h,f)})):e.resolve(y).then((function(t){v.value=t,h(v)}),(function(t){return r("throw",t,h,f)}))}f(d.arg)}var c;this._invoke=function(t,n){function o(){return new e((function(e,o){r(t,n,e,o)}))}return c=c?c.then(o,o):o()}}function E(t,e){var n=t.iterator[e.method];if(void 0===n){if(e.delegate=null,"throw"===e.method){if(t.iterator.return&&(e.method="return",e.arg=void 0,E(t,e),"throw"===e.method))return v;e.method="throw",e.arg=new TypeError("The iterator does not provide a 'throw' method")}return v}var o=m(n,t.iterator,e.arg);if("throw"===o.type)return e.method="throw",e.arg=o.arg,e.delegate=null,v;var r=o.arg;return r?r.done?(e[t.resultName]=r.value,e.next=t.nextLoc,"return"!==e.method&&(e.method="next",e.arg=void 0),e.delegate=null,v):r:(e.method="throw",e.arg=new TypeError("iterator result is not an object"),e.delegate=null,v)}function A(t){var e={tryLoc:t[0]};1 in t&&(e.catchLoc=t[1]),2 in t&&(e.finallyLoc=t[2],e.afterLoc=t[3]),this.tryEntries.push(e)}function $(t){var e=t.completion||{};e.type="normal",delete e.arg,t.completion=e}function S(t){this.tryEntries=[{tryLoc:"root"}],t.forEach(A,this),this.reset(!0)}function T(t){if(t){var e=t[c];if(e)return e.call(t);if("function"==typeof t.next)return t;if(!isNaN(t.length)){var i=-1,o=function e(){for(;++i<t.length;)if(n.call(t,i))return e.value=t[i],e.done=!1,e;return e.value=void 0,e.done=!0,e};return o.next=o}}return{next:I}}function I(){return{value:void 0,done:!0}}return w.prototype=x,f(C,"constructor",x),f(x,"constructor",w),w.displayName=f(x,h,"GeneratorFunction"),t.isGeneratorFunction=function(t){var e="function"==typeof t&&t.constructor;return!!e&&(e===w||"GeneratorFunction"===(e.displayName||e.name))},t.mark=function(t){return Object.setPrototypeOf?Object.setPrototypeOf(t,x):(t.__proto__=x,f(t,h,"GeneratorFunction")),t.prototype=Object.create(C),t},t.awrap=function(t){return{__await:t}},j(F.prototype),f(F.prototype,l,(function(){return this})),t.AsyncIterator=F,t.async=function(e,n,o,r,c){void 0===c&&(c=Promise);var l=new F(d(e,n,o,r),c);return t.isGeneratorFunction(n)?l:l.next().then((function(t){return t.done?t.value:l.next()}))},j(C),f(C,h,"Generator"),f(C,c,(function(){return this})),f(C,"toString",(function(){return"[object Generator]"})),t.keys=function(object){var t=[];for(var e in object)t.push(e);return t.reverse(),function e(){for(;t.length;){var n=t.pop();if(n in object)return e.value=n,e.done=!1,e}return e.done=!0,e}},t.values=T,S.prototype={constructor:S,reset:function(t){if(this.prev=0,this.next=0,this.sent=this._sent=void 0,this.done=!1,this.delegate=null,this.method="next",this.arg=void 0,this.tryEntries.forEach($),!t)for(var e in this)"t"===e.charAt(0)&&n.call(this,e)&&!isNaN(+e.slice(1))&&(this[e]=void 0)},stop:function(){this.done=!0;var t=this.tryEntries[0].completion;if("throw"===t.type)throw t.arg;return this.rval},dispatchException:function(t){if(this.done)throw t;var e=this;function o(n,o){return c.type="throw",c.arg=t,e.next=n,o&&(e.method="next",e.arg=void 0),!!o}for(var i=this.tryEntries.length-1;i>=0;--i){var r=this.tryEntries[i],c=r.completion;if("root"===r.tryLoc)return o("end");if(r.tryLoc<=this.prev){var l=n.call(r,"catchLoc"),h=n.call(r,"finallyLoc");if(l&&h){if(this.prev<r.catchLoc)return o(r.catchLoc,!0);if(this.prev<r.finallyLoc)return o(r.finallyLoc)}else if(l){if(this.prev<r.catchLoc)return o(r.catchLoc,!0)}else{if(!h)throw new Error("try statement without catch or finally");if(this.prev<r.finallyLoc)return o(r.finallyLoc)}}}},abrupt:function(t,e){for(var i=this.tryEntries.length-1;i>=0;--i){var o=this.tryEntries[i];if(o.tryLoc<=this.prev&&n.call(o,"finallyLoc")&&this.prev<o.finallyLoc){var r=o;break}}r&&("break"===t||"continue"===t)&&r.tryLoc<=e&&e<=r.finallyLoc&&(r=null);var c=r?r.completion:{};return c.type=t,c.arg=e,r?(this.method="next",this.next=r.finallyLoc,v):this.complete(c)},complete:function(t,e){if("throw"===t.type)throw t.arg;return"break"===t.type||"continue"===t.type?this.next=t.arg:"return"===t.type?(this.rval=this.arg=t.arg,this.method="return",this.next="end"):"normal"===t.type&&e&&(this.next=e),v},finish:function(t){for(var i=this.tryEntries.length-1;i>=0;--i){var e=this.tryEntries[i];if(e.finallyLoc===t)return this.complete(e.completion,e.afterLoc),$(e),v}},catch:function(t){for(var i=this.tryEntries.length-1;i>=0;--i){var e=this.tryEntries[i];if(e.tryLoc===t){var n=e.completion;if("throw"===n.type){var o=n.arg;$(e)}return o}}throw new Error("illegal catch attempt")},delegateYield:function(t,e,n){return this.delegate={iterator:T(t),resultName:e,nextLoc:n},"next"===this.method&&(this.arg=void 0),v}},t}var E={components:{SelectToken:k.a,PleaseLoginButton:x.a,SSpacer:_.a,AlcorButton:O.a},mixins:[C.a],data:function(){var t,e=this;return{loading:!1,priceReverse:!1,ibcForm:{transfer:!1,address:"",valid:""},inputAmount:0,outputAmount:0,minOutput:"0.0000",rules:{address:{trigger:"blur",validator:(t=Object(c.a)(L().mark((function t(n,o,r){var c;return L().wrap((function(t){for(;;)switch(t.prev=t.next){case 0:if(""!=o){t.next=2;break}return t.abrupt("return",r());case 2:return e.loading=!0,t.next=5,Object(v.a)(o,w.a.networks[e.ibcChain]);case 5:c=t.sent,e.loading=!1,c?(e.ibcForm.valid=!0,r()):(e.ibcForm.valid=!1,r(new Error("Account does not exist!")));case 8:case"end":return t.stop()}}),t)}))),function(e,n,o){return t.apply(this,arguments)})}}}},computed:F(F(F(F({},Object(d.e)(["network","user","ibcTokens"])),Object(d.e)("swap",["input","output"])),Object(d.c)({pair:"swap/current",inputBalance:"swap/inputBalance",outputBalance:"swap/outputBalance",poolOne:"swap/poolOne",poolTwo:"swap/poolTwo",isReverted:"swap/isReverted",tokens0:"swap/tokens0",tokens1:"swap/tokens1"})),{},{ibcChain:function(){if(!this.output)return"";var t=this.output,e=t.contract,symbol=t.symbol;return"eos"==this.network.name&&"bosibc.io"==e&&"WAX"==symbol?"wax":"wax"==this.network.name&&"bosibc.io"==e&&"EOS"==symbol?"eos":""},price:function(){if(!parseFloat(this.inputAmount)||!parseFloat(this.outputAmount))return"0.0000";if(this.priceReverse){var t=(parseFloat(this.inputAmount)/parseFloat(this.outputAmount)).toFixed(4);return"".concat(t," ").concat(this.input.symbol," per ").concat(this.output.symbol)}var e=(parseFloat(this.outputAmount)/parseFloat(this.inputAmount)).toFixed(4);return"".concat(e," ").concat(this.output.symbol," per ").concat(this.input.symbol)},fee:function(){return this.pair?100*this.pair.fee/1e4:.3},priceImpact:function(){return parseFloat(this.inputAmount)&&parseFloat(this.outputAmount)?parseFloat((.97*parseFloat(this.outputAmount)/parseFloat(this.poolTwo.quantity)*100).toFixed(2)):0},slippageTolerance:{get:function(){return this.$store.state.swap.slippage},set:function(t){this.$store.commit("swap/setSlippage",t)}}}),watch:{input:function(){this.$store.dispatch("swap/updatePairBalances")},output:function(){this.ibcForm.transfer=!1,this.$store.dispatch("swap/updatePairBalances")},inputAmount:function(){this.calcOutput()},pair:function(){this.calcOutput()}},methods:{resetSlippageTolerance:function(){this.slippageTolerance=3},tokenChanged:function(t){this.ibcForm.transfer=!1,0==t&&this.input&&parseFloat(this.inputAmount)&&this.calcOutput(),0==t&&this.input&&parseFloat(this.outputAmount)&&this.calcInput(),1==t&&this.input&&parseFloat(this.inputAmount)&&this.calcOutput(),1!=t||this.input||this.calcInput()},calcOutput:function(){if(this.pair&&this.output&&this.inputAmount&&null!=this.output.precision){var t=this.poolOne.quantity,e=this.poolTwo.quantity,n=Object(f.asset)(parseFloat(this.inputAmount).toFixed(this.input.precision)+" TEXT").amount,o=h.a.min(Object(m.f)(n,t.amount,e.amount,this.pair.fee),e.amount),r=Math.max(10*this.slippageTolerance,1),c=o.minus(o.multiply(r).divide(1e3));this.minOutput=Object(f.asset)(c,Object(f.symbol)(this.output.symbol,this.output.precision)).to_string(),this.outputAmount=parseFloat(Object(f.asset)(o,e.symbol).to_string()).toFixed(this.output.precision)}},calcInput:function(){if(this.pair&&this.output&&this.outputAmount){var t=this.poolOne.quantity,e=this.poolTwo.quantity,n=Object(f.asset)(parseFloat(this.outputAmount).toFixed(this.output.precision)+" TEXT").amount;n>e.amount&&(n=e.amount.minus(1),this.outputAmount=Object(f.asset)(n,e.symbol).to_string());var o=h.a.min(Object(m.e)(n,t.amount,e.amount,this.pair.fee),t.amount),r=Math.max(10*this.slippageTolerance,1),c=o.minus(n.multiply(r).divide(1e3));this.inputAmount=parseFloat(Object(f.asset)(o,t.symbol).to_string()).toFixed(this.input.precision),this.minOutput=Object(f.asset)(c,Object(f.symbol)(this.output.symbol,this.output.precision)).to_string()}},toggleInputs:function(){if(!this.output){var i=Object.assign({},this.input);this.$store.commit("swap/setOutput",i),this.$store.commit("swap/setInput",null);var t=this.inputAmount;return this.inputAmount=0,void(this.outputAmount=parseFloat(t||0).toFixed(this.output.precision))}if(!this.input){var e=Object.assign({},this.output);this.$store.commit("swap/setInput",e),this.$store.commit("swap/setOutput",null);var n=this.outputAmount;return this.outputAmount=0,void(this.inputAmount=parseFloat(n||0).toFixed(this.input.precision))}this.$store.dispatch("swap/toggleInputs"),this.isReverted?(this.outputAmount=this.inputAmount,this.calcInput()):(this.inputAmount=this.outputAmount,this.calcOutput())},processExchange:function(){var t=this;return Object(c.a)(L().mark((function e(){var n,o,r;return L().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:return n="".concat(t.minOutput,"@").concat(t.output.contract),t.ibcChain&&t.ibcForm.transfer&&(n+="|bosibc.io|hub.io@bos >> ".concat(t.ibcForm.address,"@").concat(t.ibcChain," alcor.exchange (IBC swap)")),o=[t.user.authorization],r=[{account:t.input.contract,name:"transfer",authorization:o,data:{from:t.user.name,to:t.network.pools.contract,quantity:parseFloat(t.inputAmount).toFixed(t.input.precision)+" "+t.input.symbol,memo:n}}],t.loading=!0,e.prev=5,e.next=8,t.$store.dispatch("chain/sendTransaction",r);case 8:t.$store.dispatch("swap/updatePair",t.pair.id),setTimeout((function(){return t.$store.dispatch("swap/updatePairBalances")}),1e3),t.inputAmount=Number(0).toFixed(t.input.precision),t.outputAmount=Number(0).toFixed(t.output.precision),t.$notify({title:"Swap",message:"Success",type:"success"}),e.next=18;break;case 15:e.prev=15,e.t0=e.catch(5),t.$notify({title:"Swap error",message:"message"in e.t0?e.t0.message:e.t0,type:"error"});case 18:return e.prev=18,t.loading=!1,e.finish(18);case 21:case"end":return e.stop()}}),e,null,[[5,15,18,21]])})))()},submit:function(){var t=this;return Object(c.a)(L().mark((function e(){var n;return L().wrap((function(e){for(;;)switch(e.prev=e.next){case 0:if(t.inputAmount&&t.outputAmount){e.next=2;break}return e.abrupt("return");case 2:if(!(parseFloat(t.priceImpact)>10)){e.next=10;break}return n={title:"Impact on the price above 10%!",mess:"You are significantly overpaying for the exchange. Try the amount less or do you want to continue?"},e.next=6,t.showPopupWarning(n,"Swap");case 6:e.sent||t.processExchange(),e.next=11;break;case 10:t.processExchange();case 11:case"end":return e.stop()}}),e)})))()}}},A=E,$=(n(1930),n(1932),n(12)),component=Object($.a)(A,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"row mt-4"},[n("div",{staticClass:"col swap-pools"},[n("div",{staticClass:"row"},[n("div",{staticClass:"col"},[n("div",{staticClass:"d-flex mb-1 select-label"},[n("small",{staticClass:"text-muted"},[t._v(t._s(t.$t("Sell")))]),n("el-button",{staticClass:"ml-auto",attrs:{type:"text",size:"mini"},on:{click:function(e){t.inputAmount=parseFloat(t.inputBalance)}}},[t._v(t._s(t._f("commaFloat")(t.inputBalance))),n("i",{staticClass:"el-icon-wallet ml-1"})])],1),n("SelectToken",{attrs:{tokens:t.tokens0,token:0},on:{change:function(e){return t.tokenChanged(0)}},model:{value:t.inputAmount,callback:function(e){t.inputAmount=e},expression:"inputAmount"}},[n("template",{slot:"end"},[n("div",{staticClass:"pair text-muted",on:{click:function(e){return t.$router.push("/swap/create")}}},[n("i",{staticClass:"el-icon-plus mr-2"}),n("span",[t._v(t._s(t.$t("Create pool")))])])])],2)],1)]),n("div",{staticClass:"row mt-3"},[n("div",{staticClass:"col text-center"},[n("i",{staticClass:"el-icon-bottom lead pointer",on:{click:t.toggleInputs}})])]),n("div",{staticClass:"row mt-1"},[n("div",{staticClass:"col"},[n("div",{staticClass:"d-flex mb-1 select-label align-items-center"},[n("small",{staticClass:"text-muted"},[t._v(t._s(t.$t("Buy (Estimated)")))]),n("div",{staticClass:"swap-setting ml-1"},[n("el-dropdown",{attrs:{trigger:"click"}},[n("i",{staticClass:"el-icon-setting"}),n("el-dropdown-menu",{staticClass:"dropdown",attrs:{slot:"dropdown"},slot:"dropdown"},[n("div",{staticClass:"section"},[n("div",{staticClass:"section-label"},[t._v(t._s(t.$t("Transaction Setting")))]),n("label",[t._v(t._s(t.$t("Slippage Tolerance"))+" %")]),n("div",{staticClass:"section-content"},[n("AlcorButton",{attrs:{round:"",compact:""},on:{click:t.resetSlippageTolerance}},[t._v(t._s(t.$t("Auto")))]),n("div",{staticClass:"section-input"},[n("el-input",{attrs:{placeholder:t.$t("Slippage Tolerance %"),size:"small"},model:{value:t.slippageTolerance,callback:function(e){t.slippageTolerance=e},expression:"slippageTolerance"}})],1)],1)])])],1)],1),n("small",{staticClass:"text-mutted small ml-auto with-padding"},[t._v(t._s(t._f("commaFloat")(t.outputBalance))),n("i",{staticClass:"el-icon-wallet ml-1"})])]),n("SelectToken",{attrs:{tokens:t.tokens1,readonly:"",token:1},on:{change:function(e){return t.tokenChanged(1)}},model:{value:t.outputAmount,callback:function(e){t.outputAmount=e},expression:"outputAmount"}},[n("template",{slot:"end"},[n("div",{staticClass:"pair text-muted",on:{click:function(e){return t.$router.push("/swap/create")}}},[n("i",{staticClass:"el-icon-plus mr-2"}),n("span",[t._v(t._s(t.$t("Create pool")))])])])],2)],1)]),n("div",{staticClass:"row mt-4"},[n("div",{staticClass:"col"},[n("PleaseLoginButton",[n("div",{directives:[{name:"loading",rawName:"v-loading",value:t.loading,expression:"loading"}],staticClass:"confirm-button"},[!t.ibcForm.transfer||t.ibcForm.valid&&t.ibcForm.address?t.input&&t.inputAmount&&t.output&&t.outputAmount?n("div",{staticClass:"div"},[n("el-button",{staticClass:"w-100",attrs:{type:"primary"},on:{click:t.submit}},[t._v(t._s(t.$t("Swap"))+" "+t._s(t.input.symbol)+" to "+t._s(t.output.symbol))])],1):n("div",{staticClass:"div"},[n("el-button",{staticClass:"w-100",attrs:{type:"primary",disabled:""}},[t._v(t._s(t.$t("Select amounts")))])],1):n("div",{staticClass:"div"},[n("el-button",{staticClass:"w-100",attrs:{type:"primary",disabled:""}},[t._v(t._s(t.$t("Invalid"))+" "+t._s(this.ibcChain.toUpperCase())+" Account")])],1)])])],1)]),n("div",{staticClass:"row mt-3"},[n("div",{staticClass:"col"},[n("div",{staticClass:"d-flex justify-content-between"},[n("small",[t._v(t._s(t.$t("Minimum Received")))]),n("div",{staticClass:"small"},[t._v(t._s(t._f("commaFloat")(t.minOutput)))])]),n("SSpacer"),n("div",{staticClass:"d-flex justify-content-between"},[n("small",[t._v(t._s(t.$t("Rate")))]),n("div",{staticClass:"small"},[t._v(t._s(t.price)),n("div",{staticClass:"el-icon-refresh ml-1 pointer",on:{click:function(e){t.priceReverse=!t.priceReverse}}})])]),n("SSpacer"),n("div",{staticClass:"d-flex justify-content-between"},[n("small",[t._v(t._s(t.$t("Price Impact")))]),t.priceImpact>=5?n("div",{staticClass:"small text-danger font-weight-bold"},[t._v(t._s(t.priceImpact)+"%")]):t.priceImpact>=2?n("div",{staticClass:"small text-warning font-weight-bold"},[t._v(t._s(t.priceImpact)+"%")]):t.priceImpact<2?n("div",{staticClass:"small text-success font-weight-bold"},[t._v(t._s(t.priceImpact)+"%")]):n("div",{staticClass:"small font-weight-bold"},[t._v(t._s(t.priceImpact)+" %")])]),n("SSpacer"),n("div",{staticClass:"d-flex justify-content-between"},[n("small",[t._v(t._s(t.$t("Slippage")))]),n("div",{staticClass:"small"},[t._v(t._s(t.slippageTolerance)+"%")])]),n("SSpacer"),n("div",{staticClass:"d-flex justify-content-between"},[n("small",[t._v(t._s(t.$t("Liquidity Source Fee")))]),n("div",{staticClass:"small"},[t._v(t._s(t.fee)+"%")])])],1)])])])}),[],!1,null,"40eb568b",null);e.a=component.exports},1928:function(t,e,n){"use strict";n(1751)},1929:function(t,e,n){var o=n(46)(!1);o.push([t.i,".scroller{height:calc(100% - 32px)}.swap-token-select .dropdown{border-radius:var(--radius);position:absolute;padding:20px 10px 10px;right:15px;left:15px;bottom:auto;margin-top:-8px;background:var(--background-color-base);z-index:1;height:310px;overflow:hidden;box-shadow:var(--dropdown-shadow)}.swap-token-select .dropdown .pairs{overflow-y:auto;height:calc(100% - 32px)}.swap-token-select .el-dialog__body{padding:25px 20px}.swap-token-select .el-button.is-round{padding:7px 23px}.pair{display:flex;cursor:pointer;padding:10px 8px;border-radius:5px;align-items:center;margin-top:5px}.isActive,.pair:hover{background-color:var(--background-color-secondary)}.multi-input-wrapper{padding:8px 15px;background:#282828;border-radius:6px;position:relative}.multi-input-wrapper .el-input{font-size:18px}.multi-input-wrapper .el-input .el-input-group__append{border:none;background:transparent}.multi-input-wrapper .el-input__inner{background-color:transparent!important;border:none}.multi-input-wrapper input{font:inherit;color:currentColor;width:100%;border:0;height:1.1876em;margin:0;display:block;padding:6px 0 7px;min-width:0;background:none;box-sizing:content-box;-webkit-animation-name:mui-auto-fill-cancel;animation-name:mui-auto-fill-cancel;letter-spacing:inherit;-webkit-animation-duration:10ms;animation-duration:10ms;-webkit-tap-highlight-color:transparent}.theme-light .multi-input-wrapper{background:var(--btn-active)}.theme-dark .swap-token-select .dropdown .el-input__inner{background-color:#232424;border:none}",""]),t.exports=o},1930:function(t,e,n){"use strict";n(1752)},1931:function(t,e,n){var o=n(46)(!1);o.push([t.i,".confirm-button button[data-v-40eb568b]{padding:20px;border:none;border-radius:var(--radius-2)}.confirm-button button[data-v-40eb568b],.confirm-button button[data-v-40eb568b]:hover{background:rgba(46,46,49,.6)}.theme-dark .confirm-button button[data-v-40eb568b],.theme-dark .confirm-button button[data-v-40eb568b]:hover{background:#161617}.dropdown[data-v-40eb568b]{padding:14px}.swap-setting[data-v-40eb568b]{display:flex;justify-content:flex-end}.swap-setting .el-icon-setting[data-v-40eb568b]{font-size:1rem}.section-label[data-v-40eb568b]{font-weight:700;margin-bottom:8px}.section-content[data-v-40eb568b]{display:flex;align-items:flex-end}.section-content .alcor-button[data-v-40eb568b]{margin-right:4px}label[data-v-40eb568b]{margin-bottom:4px}.section-input[data-v-40eb568b]{width:200px}",""]),t.exports=o},1932:function(t,e,n){"use strict";n(1753)},1933:function(t,e,n){var o=n(46)(!1);o.push([t.i,".swap-pools .el-form-item__error{top:-32px;left:-5px}",""]),t.exports=o}}]);