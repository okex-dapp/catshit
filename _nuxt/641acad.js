(window.webpackJsonp=window.webpackJsonp||[]).push([[41],{1684:function(t,e,n){"use strict";var l={props:{high:{default:!1,type:Boolean}}},o=(n(1689),n(12)),component=Object(o.a)(l,(function(){var t=this,e=t.$createElement;return(t._self._c||e)("div",{class:["spacer",{high:t.high}]})}),[],!1,null,"2836b060",null);e.a=component.exports},1685:function(t,e,n){var content=n(1690);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("7be39ddd",content,!0,{sourceMap:!1})},1689:function(t,e,n){"use strict";n(1685)},1690:function(t,e,n){var l=n(46)(!1);l.push([t.i,".spacer[data-v-2836b060]{height:8px}.high[data-v-2836b060]{height:14px}",""]),t.exports=l},1823:function(t,e,n){var content=n(2082);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("64439236",content,!0,{sourceMap:!1})},1824:function(t,e,n){var content=n(2084);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("acb25ff6",content,!0,{sourceMap:!1})},1825:function(t,e,n){var content=n(2086);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("7a73aeac",content,!0,{sourceMap:!1})},1826:function(t,e,n){var content=n(2088);content.__esModule&&(content=content.default),"string"==typeof content&&(content=[[t.i,content,""]]),content.locals&&(t.exports=content.locals);(0,n(47).default)("f681fdd8",content,!0,{sourceMap:!1})},2081:function(t,e,n){"use strict";n(1823)},2082:function(t,e,n){var l=n(46)(!1);l.push([t.i,".wallet-name[data-v-6288c022]{display:flex;align-items:center}.wallet-name .name[data-v-6288c022]{font-size:1.2rem;font-weight:500}.wallet-name>*[data-v-6288c022]{padding:4px}",""]),t.exports=l},2083:function(t,e,n){"use strict";n(1824)},2084:function(t,e,n){var l=n(46)(!1);l.push([t.i,".main[data-v-57d790da]{font-size:1.1rem;font-weight:500;padding-right:4px}.symbol[data-v-57d790da]{font-size:.86rem}.info[data-v-57d790da],.title[data-v-57d790da],.value[data-v-57d790da]{padding:2px}.wallet-header[data-v-57d790da]{display:flex;justify-content:space-between;flex-wrap:wrap}.line[data-v-57d790da]{margin:0 4px;width:2px}@media only screen and (max-width:840px){.wallet-header[data-v-57d790da]{justify-content:center;background:transparent;padding:0}.item[data-v-57d790da]{background:var(--background-color-secondary);padding:10px;margin:4px;border-radius:var(--radius)}}@media only screen and (max-width:540px){.wallet-header[data-v-57d790da]{flex-direction:column}.item[data-v-57d790da]{background:var(--background-color-secondary);padding:10px;margin:4px;border-radius:var(--radius)}}.green[data-v-57d790da]{color:var(--main-green)!important}.red[data-v-57d790da]{color:var(--main-red)!important}",""]),t.exports=l},2085:function(t,e,n){"use strict";n(1825)},2086:function(t,e,n){var l=n(46)(!1);l.push([t.i,".wallet-tab-bar[data-v-2399d0ad]{display:flex;position:-webkit-sticky;position:sticky;top:0;z-index:4;overflow:auto;padding:4px 0;background:var(--background-color-base)}.wallet-tab-bar[data-v-2399d0ad]::-webkit-scrollbar{height:4px;width:4px;display:block}.wallet-tab-bar[data-v-2399d0ad]::-webkit-scrollbar-thumb{border-radius:5px}.tab-bar-item[data-v-2399d0ad]{flex:1;border-radius:8px;padding:12px;margin:0 8px;white-space:nowrap}.tab-bar-item[data-v-2399d0ad]:first-child{margin-left:0}.tab-bar-item[data-v-2399d0ad]:last-child{margin-right:0}.tab-bar-item.active[data-v-2399d0ad]{background:var(--btn-active)}@media only screen and (max-width:940px){.tab-bar-item[data-v-2399d0ad]{border-radius:4px;margin:2px;padding:6px 12px;font-size:.86rem}}",""]),t.exports=l},2087:function(t,e,n){"use strict";n(1826)},2088:function(t,e,n){var l=n(46)(!1);l.push([t.i,".wallet-layout[data-v-4fb8e3fa]{padding-top:25px}.content[data-v-4fb8e3fa]{padding:25px 0}",""]),t.exports=l},2199:function(t,e,n){"use strict";n.r(e);n(16);var l={name:"WalletName",methods:{copyUserName:function(){navigator.clipboard.writeText(this.$store.state.user.name),this.$notify({title:"Clipboard",message:"Account name copyed to Clipboard",type:"info"})}}},o=(n(2081),n(12)),r=Object(o.a)(l,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return this.$store.state.user?n("div",{staticClass:"wallet-name"},[n("i",{staticClass:"el-icon-wallet"}),n("div",{staticClass:"name"},[t._v(t._s(this.$store.state.user.name))]),n("div",{staticClass:"actions"},[n("i",{staticClass:"el-icon-copy-document pointer",on:{click:t.copyUserName}})])]):t._e()}),[],!1,null,"6288c022",null).exports,c=(n(44),n(15),n(29),n(7),n(56),n(17),n(57),n(8)),d=n(51);function v(object,t){var e=Object.keys(object);if(Object.getOwnPropertySymbols){var n=Object.getOwnPropertySymbols(object);t&&(n=n.filter((function(t){return Object.getOwnPropertyDescriptor(object,t).enumerable}))),e.push.apply(e,n)}return e}var f={name:"WalletHeader",computed:function(t){for(var i=1;i<arguments.length;i++){var source=null!=arguments[i]?arguments[i]:{};i%2?v(Object(source),!0).forEach((function(e){Object(c.a)(t,e,source[e])})):Object.getOwnPropertyDescriptors?Object.defineProperties(t,Object.getOwnPropertyDescriptors(source)):v(Object(source)).forEach((function(e){Object.defineProperty(t,e,Object.getOwnPropertyDescriptor(source,e))}))}return t}({},Object(d.c)({buyPositionsCount:"wallet/buyPositionsCount",sellPositionsCount:"wallet/sellPositionsCount",pairsCount:"wallet/pairsCount",systemBalance:"systemBalance",network:"network"}))},m=f,_=(n(2083),Object(o.a)(m,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"wallet-header alcor-card"},[n("div",{staticClass:"item"},[n("div",{staticClass:"title cancel"},[t._v(t._s(t.$t("Portfolio value")))]),n("div",{staticClass:"value"},[n("span",{staticClass:"main"},[t._v(t._s(t._f("commaFloat")(t.systemBalance.split(" ")[0],4)))]),n("span",{staticClass:"symbol cancel"},[t._v(t._s(this.$store.state.network.baseToken.symbol))])]),n("div",{staticClass:"info cancel"},[t._v("= $"+t._s(t.$systemToUSD(t.systemBalance)))])]),n("div",{staticClass:"item"},[n("div",{staticClass:"title cancel"},[t._v(t._s(t.$t("Active positions"))),t.$store.state.userOrdersLoading?n("el-tooltip",{staticClass:"item",attrs:{effect:"dark",content:"Scanning for active positions might take some time",placement:"right-start"}},[n("i",{staticClass:"el-icon-loading ml-1 pointer"})]):t._e()],1),n("div",{staticClass:"value"},[n("span",{staticClass:"main"},[n("span",{staticClass:"buy green"},[t._v(t._s(t.buyPositionsCount)+" "+t._s(t.$t("Buy")))]),n("span",{staticClass:"cancel line"},[t._v("|")]),n("span",{staticClass:"sell red"},[t._v(t._s(t.sellPositionsCount)+" "+t._s(t.$t("Sell")))])])]),n("div",{staticClass:"info cancel"},[t._v(t._s(t.pairsCount)+" "+t._s(t.$t("Pairs")))])]),n("div",{staticClass:"item"},[n("div",{staticClass:"title cancel"},[t._v(t._s(t.$t("Available funds")))]),n("div",{staticClass:"value"},[n("span",{staticClass:"main"},[t._v(t._s(t._f("commaFloat")(t.systemBalance.split(" ")[0])))]),n("span",{staticClass:"symbol cancel"},[t._v(t._s(this.$store.state.network.baseToken.symbol))])]),n("div",{staticClass:"info cancel"},[t._v("= $"+t._s(t.$systemToUSD(t.systemBalance)))])]),n("div",{staticClass:"item"},[n("div",{staticClass:"title cancel"},[t._v(t._s(t.$t("Staking rewards")))]),t._m(0),n("div",{staticClass:"info cancel"},[t._v(t._s(t.$t("Last Claim"))+": 0.00000")])]),n("div",{staticClass:"item"},[n("div",{staticClass:"title cancel"},[t._v(t._s(t.$t("LP rewards")))]),t._m(1),n("div",{staticClass:"info cancel"},[t._v("0 "+t._s(t.$t("Liquidity Pools")))])])])}),[function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"value"},[n("span",{staticClass:"main"},[t._v("0.0000")]),n("span",{staticClass:"symbol cancel"},[t._v("WAX")])])},function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"value"},[n("span",{staticClass:"main green"},[t._v("+0.0000")]),n("span",{staticClass:"symbol cancel"},[t._v("WAX")])])}],!1,null,"57d790da",null).exports),h=n(1684),y={name:"WalletTabBar",components:{AlcorLink:n(294).a},data:function(){return{urls:[{name:"Tokens",to:"/wallet",exact:!0},{name:"Open Orders",to:"/wallet/positions"},{name:"History",to:"/wallet/history"},{name:"NFT’s",to:"/wallet/nfts",isNFT:!0},{name:"Liquidity Pools",to:"/wallet/liquidity_pools"},{name:"Resources",to:"/wallet/resources"}]}},watch:{$route:function(){var t=this;this.$nextTick((function(){t.funcScrollTo()}))}},mounted:function(){this.funcScrollTo()},methods:{funcScrollTo:function(){this.$scrollTo(".wallet-tab-bar .active",{container:".wallet-tab-bar",offset:-100,x:!0})}}},w=(n(2085),Object(o.a)(y,(function(){var t=this,e=t.$createElement,n=t._self._c||e;return n("div",{staticClass:"wallet-tab-bar"},t._l(t.urls,(function(e){var l=e.name,o=e.to,r=e.exact;return n("AlcorLink",{key:l,staticClass:"tab-bar-item",attrs:{to:o,exact:r}},[t._v(t._s(t.$t(l)))])})),1)}),[],!1,null,"2399d0ad",null).exports),x={components:{WalletName:r,WalletHeader:_,SSpacer:h.a,WalletTabBar:w}},C=(n(2087),Object(o.a)(x,(function(){var t=this.$createElement,e=this._self._c||t;return e("div",{staticClass:"wallet-layout"},[e("WalletName"),e("WalletHeader",{staticClass:"mt-3"}),e("WalletTabBar",{staticClass:"mt-3"}),e("div",{staticClass:"content"},[e("nuxt-child")],1)],1)}),[],!1,null,"4fb8e3fa",null));e.default=C.exports}}]);