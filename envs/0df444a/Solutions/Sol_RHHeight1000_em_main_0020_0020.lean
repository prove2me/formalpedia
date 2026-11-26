-- Prove2me | solution 1 for RHHeight1000.em_main_0020_0020
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:17:46.757764+00:00
-- url     : https://prove2.me/submissions/6c16c808-fab5-4c0a-83a3-14a9176574a7

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow20.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow20.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow20.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow20.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow20.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 3906250001249 624500000000000000 4138529546116343 2251799813685248 3906250001249 624500000000000000 481788 262144

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 159872 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 3906250001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000319744 159872000000000000000 4138529546116343 2251799813685248 3906250001249 624500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 159872 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 3906250001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000319744 159872000000000000000 4138529546116343 2251799813685248 3906250001249 624500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow20.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 159872 600168 524288 1 159872 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 159872 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 159872 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 159872 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 159872 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 159872 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 159872 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow20.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz537 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 76170 1000)))

noncomputable abbrev qz512 := qz537

noncomputable abbrev qz272 := qz512

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz538 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz513 := qz538

noncomputable abbrev qz273 := qz513

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz514 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz514

noncomputable abbrev qz515 := (@Neg.neg Complex Complex.instNeg qz537)

noncomputable abbrev qz275 := qz515

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 8) qz275)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.true 108906003625 274877906944 1122909400493 343322505773056 Bool.true 23060115999 137438953472 561901655521 171661252886528

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.true 66915234347 137438953472 502731568159 171661252886528 Bool.false 47812653615 274877906944 1005892059155 343322505773056 Bool.false

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 7) qz275)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.true 66915234347 137438953472 502731568159 171661252886528 Bool.false 47812653615 274877906944 1005892059155 343322505773056

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.true 23037190235 137438953472 439642867421 171661252886528 Bool.true 7800999683 274877906944 879917247977 343322505773056 Bool.true

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 6) qz275)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.true 23037190235 137438953472 439642867421 171661252886528 Bool.true 7800999683 274877906944 879917247977 343322505773056

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.true 12934977513 137438953472 371739551299 171661252886528 Bool.true 118185192763 274877906944 743584382057 343322505773056 Bool.true

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 5) qz275)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.true 12934977513 137438953472 371739551299 171661252886528 Bool.true 118185192763 274877906944 743584382057 343322505773056

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 96769758831 274877906944 594478516161 343322505773056 Bool.true 126614822251 274877906944 595192184769 343322505773056 Bool.true

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 4) qz275)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 96769758831 274877906944 594478516161 343322505773056 Bool.true 126614822251 274877906944 595192184769 343322505773056

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 24791091915 137438953472 214034928957 171661252886528 Bool.true 127849245941 137438953472 13387291451 10728828305408 Bool.false

noncomputable abbrev qz516 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz276 := qz516

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz274 qz276 qz275)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 24791091915 137438953472 214034928957 171661252886528 Bool.true 127849245941 137438953472 13387291451 10728828305408

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 7223922403 17179869184 58907812699 85830626443264 Bool.true 13921624197 34359738368 117654173413 171661252886528 Bool.true

noncomputable abbrev qz517 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz277 := qz517

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz274 qz277 qz275)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 7223922403 17179869184 58907812699 85830626443264 Bool.true 13921624197 34359738368 117654173413 171661252886528

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz278

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz279))

noncomputable abbrev qz539 := (Enclosure.sfrac Bool.false 76170 1000)

noncomputable abbrev qz518 := qz539

noncomputable abbrev qz280 := qz518

noncomputable abbrev qz281 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log qz281))

noncomputable abbrev qz16 := qz280

noncomputable abbrev qz282 := (@Eq.refl Real qz518)

noncomputable abbrev qz17 := qz282

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.true 9955946781 17179869184 58907812699 85830626443264 Bool.true 13921624197 34359738368 117654173413 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz279) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz279) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 79936 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 4551264237242333018493251132945151594739234326697522241934382390708728299520

noncomputable def ep57 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep58 := nat_lit 1281318213564031748674467109020802801019913219258586747812299474814959616

noncomputable def ep59 := nat_lit 11917903249003197092270184782394125257877295758043282445569781586039826087936

noncomputable def ep60 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz283 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz284 := (BSN.sinOddQ 1073741824)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 1031471244 1073741824 3 2 524288 160029 ep56 ep57 ep58 ep59 ep60 ep58 429682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1031471244) qz283 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1031471244) qz284 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz20 := (Real.log qz281)

noncomputable abbrev qz21 := (Enclosure.Real.IsNear.const Bool.false 76170 1000)

noncomputable abbrev qz22 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27680787) qz19)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 79936 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 79936 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz15 qz285 Bool.false 27680787 524288 125 131072 Bool.true 429682 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 173004921 3276800 7617 7993600 27680787 524288 125 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 76170 1000 0 1 181704 262144 1 79936 173004921 3276800 7617 7993600 qz21 qz286 rfl) rfl) (Enclosure.sfrac_false_div 27680787 524288) (BSN.cos_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72583336155232226770944) qz22) 226375608064910080 72057594037927936 Bool.false 429682 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 27680787 524288 226375608064910080 72057594037927936 8 72583336155232226770944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429682 524288 72583336155232226770944 75557863725914323419136 1031471244 1073741824 160029 159872 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 2529049606562880135495661503684649020544472365151627284073684572382544592896

noncomputable def ep64 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep65 := nat_lit 7584586183261512342989635576835905456031377269016364678725429118198003859456

noncomputable def ep66 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz287 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz288 := (BSN.cosOddQ 1073741824)

noncomputable def ep67 := BSN.cos_dyadic_bound_f 1031471244 1073741824 3 2 524288 160029 ep63 ep64 ep58 ep65 ep66 ep58 300417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1031471244) qz287 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1031471244) qz288 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz15 qz285 Bool.false 27680787 524288 125 131072 Bool.false 300417 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 173004921 3276800 7617 7993600 27680787 524288 125 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz20 76170 1000 0 1 181704 262144 1 79936 173004921 3276800 7617 7993600 qz21 qz286 rfl) rfl) (Enclosure.sfrac_false_div 27680787 524288) (BSN.sin_reduce1 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72583336155232226770944) qz22) 226375608064910080 72057594037927936 Bool.false 300417 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 27680787 524288 226375608064910080 72057594037927936 8 72583336155232226770944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 300417 524288 72583336155232226770944 75557863725914323419136 1031471244 1073741824 160029 159872 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.true 9955946781 17179869184 58907812699 85830626443264 Bool.true 13921624197 34359738368 117654173413 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz14 (Real.cos qz15) 46341 65536 1 262144 214841 262144 158173 163708928 9955946781 17179869184 58907812699 85830626443264 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.true 429682 524288 10123072 10477371392 214841 262144 158173 163708928 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 46341 65536 1 262144 300417 524288 158173 163708928 13921624197 34359738368 117654173413 171661252886528 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.false 300417 524288 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.false 300417 524288 10123072 10477371392 300417 524288 158173 163708928 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz290 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz23 := qz290

noncomputable def ep70 := @ep51 9955946781 17179869184 58907812699 85830626443264 Bool.true 13921624197 34359738368 117654173413 171661252886528 Bool.false 7223922403 7223922403 17179869184 58907812699 85830626443264 Bool.true 13921624197 13921624197 34359738368 117654173413 171661252886528 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep53 ep69) rfl rfl

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz291))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 33000287309 137438953472 96219303559 171661252886528 Bool.true 72162749153 137438953472 96542489803 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 3 qz17 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz291) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz291) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz18)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz291 qz18)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 79936 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 44984960199189578639010663504824481

noncomputable def ep75 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep76 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep77 := BSN.sin_dyadic_bound_f 460539447 1073741824 2 1 524288 160029 ep74 ep75 ep74 ep74 ep76 ep74 218041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 460539447) qz283 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 460539447) qz284 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz292 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43873005) qz19)

noncomputable abbrev qz293 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 79936 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 79936 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz25 qz292 Bool.false 43873005 524288 501 524288 Bool.true 218041 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 1096825149 13107200 7617 7993600 43873005 524288 501 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz26 76170 1000 0 1 287994 262144 1 79936 1096825149 13107200 7617 7993600 qz21 qz293 rfl) rfl) (Enclosure.sfrac_false_div 43873005 524288) (BSN.cos_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32407582567779522314240) qz22) 226375608064910080 72057594037927936 Bool.false 218041 524288 13 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 43873005 524288 226375608064910080 72057594037927936 13 32407582567779522314240 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 218041 524288 32407582567779522314240 75557863725914323419136 460539447 1073741824 160029 159872 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep80 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep81 := BSN.cos_dyadic_bound_f 460539447 1073741824 2 1 524288 160029 ep74 ep79 ep74 ep74 ep80 ep74 476797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 460539447) qz287 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 460539447) qz288 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz25 qz292 Bool.false 43873005 524288 501 524288 Bool.false 476797 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 1096825149 13107200 7617 7993600 43873005 524288 501 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz26 76170 1000 0 1 287994 262144 1 79936 1096825149 13107200 7617 7993600 qz21 qz293 rfl) rfl) (Enclosure.sfrac_false_div 43873005 524288) (BSN.sin_reduce1 qz292 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32407582567779522314240) qz22) 226375608064910080 72057594037927936 Bool.false 476797 524288 13 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 43873005 524288 226375608064910080 72057594037927936 13 32407582567779522314240 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 476797 524288 32407582567779522314240 75557863725914323419136 460539447 1073741824 160029 159872 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 33000287309 137438953472 96219303559 171661252886528 Bool.true 72162749153 137438953472 96542489803 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 151349 262144 1 262144 218041 524288 633941 654835712 33000287309 137438953472 96219303559 171661252886528 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 218041 524288 40572224 41909485568 218041 524288 633941 654835712 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 151349 262144 1 262144 476797 524288 633941 654835712 72162749153 137438953472 96542489803 171661252886528 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.false 476797 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.false 476797 524288 40572224 41909485568 476797 524288 633941 654835712 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 33000287309 137438953472 96219303559 171661252886528 Bool.true 72162749153 137438953472 96542489803 171661252886528 Bool.false 425907716028220047360 24791091915 137438953472 214034928957 171661252886528 Bool.true 4392866641078845964288 127849245941 137438953472 13387291451 10728828305408 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 47187575001 274877906944 166408658247 343322505773056 Bool.false 129083669631 274877906944 166798858337 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 4 qz17 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz18)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz18)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 79936 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 20053761811661608668067936326782976

noncomputable def ep91 := BSN.sin_dyadic_bound_f 376312776 1073741824 2 1 524288 160029 ep90 ep75 ep90 ep90 ep76 ep90 180007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 376312776) qz283 0 1 ep90 ep75 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 376312776) qz284 0 1 ep90 ep76 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz29 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27680787) qz29)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 79936 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 79936 rfl rfl rfl (ep89 rfl)))

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz28 qz296 Bool.false 27680787 262144 501 524288 Bool.false 180007 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 173004921 1638400 7617 7993600 27680787 262144 501 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz30 76170 1000 0 1 363408 262144 1 79936 173004921 1638400 7617 7993600 qz21 qz297 rfl) rfl) (Enclosure.sfrac_false_div 27680787 262144) (BSN.cos_reduce3 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13240328754664438759424) qz298) 226375608064910080 72057594037927936 Bool.false 180007 524288 16 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 27680787 262144 226375608064910080 72057594037927936 16 13240328754664438759424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 180007 524288 13240328754664438759424 37778931862957161709568 376312776 1073741824 160029 159872 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := BSN.cos_dyadic_bound_f 376312776 1073741824 2 1 524288 160029 ep90 ep79 ep90 ep90 ep80 ep90 492417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 376312776) qz287 0 1 ep90 ep79 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 376312776) qz288 0 1 ep90 ep80 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz28 qz296 Bool.false 27680787 262144 501 524288 Bool.true 492417 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 173004921 1638400 7617 7993600 27680787 262144 501 524288 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz30 76170 1000 0 1 363408 262144 1 79936 173004921 1638400 7617 7993600 qz21 qz297 rfl) rfl) (Enclosure.sfrac_false_div 27680787 262144) (BSN.sin_reduce3 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13240328754664438759424) qz298) 226375608064910080 72057594037927936 Bool.false 492417 524288 16 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 27680787 262144 226375608064910080 72057594037927936 16 13240328754664438759424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 492417 524288 13240328754664438759424 37778931862957161709568 376312776 1073741824 160029 159872 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 47187575001 274877906944 166408658247 343322505773056 Bool.false 129083669631 274877906944 166798858337 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz28) 262143 524288 1 524288 180007 524288 633941 654835712 47187575001 274877906944 166408658247 343322505773056 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 180007 524288 40572224 41909485568 180007 524288 633941 654835712 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 262143 524288 1 524288 492417 524288 633941 654835712 129083669631 274877906944 166798858337 343322505773056 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 492417 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 492417 524288 40572224 41909485568 492417 524288 633941 654835712 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 47187575001 274877906944 166408658247 343322505773056 Bool.false 129083669631 274877906944 166798858337 343322505773056 Bool.false 13299934381470470111232 96769758831 274877906944 594478516161 343322505773056 Bool.true 17401808664220739305472 126614822251 274877906944 595192184769 343322505773056 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep95) rfl rfl

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz300))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 122639713857 274877906944 149000586437 343322505773056 Bool.false 526851843 17179869184 18549024661 42915313221632 (BSN.cpow_neg_s_mk qz16 76170 1000 5 qz17 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz300) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz300) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz300 qz18)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz300 qz18)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 39510257877627786146545168145625

noncomputable def ep100 := nat_lit 8181717556663416291180905432700

noncomputable def ep101 := nat_lit 6646766139202842132480000

noncomputable def ep102 := BSN.log_dyadic_bound 2 3 16 15 ep99 262144 79936 ep100 ep101 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep100 ep99 ep101 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep103 := BSN.cos_dyadic_bound_f 73689420 1073741824 1 0 524288 160029 0 1 1 0 1 1 523053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 73689420) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 73689420) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz33 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64272855) qz19)

noncomputable abbrev qz302 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 79936 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 79936 rfl rfl rfl (ep102 rfl)))

noncomputable def ep104 := @Enclosure.Real.IsNear.cos_image qz32 qz301 Bool.false 64272855 524288 125 131072 Bool.true 523053 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 200852673 1638400 7617 7993600 64272855 524288 125 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz33 76170 1000 0 1 421904 262144 1 79936 200852673 1638400 7617 7993600 qz21 qz302 rfl) rfl) (Enclosure.sfrac_false_div 64272855 524288) (BSN.cos_reduce2 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5185432008638532157440) qz22) 226375608064910080 72057594037927936 Bool.false 523053 524288 19 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 64272855 524288 226375608064910080 72057594037927936 19 5185432008638532157440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523053 524288 5185432008638532157440 75557863725914323419136 73689420 1073741824 160029 159872 (ep103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep105 := BSN.sin_dyadic_bound_f 73689420 1073741824 1 0 524288 160029 0 1 1 0 1 1 35952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 73689420) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 73689420) qz284 0 0 rfl) rfl rfl

noncomputable def ep106 := @Enclosure.Real.IsNear.sin_image qz32 qz301 Bool.false 64272855 524288 125 131072 Bool.true 35952 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 200852673 1638400 7617 7993600 64272855 524288 125 131072 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz33 76170 1000 0 1 421904 262144 1 79936 200852673 1638400 7617 7993600 qz21 qz302 rfl) rfl) (Enclosure.sfrac_false_div 64272855 524288) (BSN.sin_reduce2 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5185432008638532157440) qz22) 226375608064910080 72057594037927936 Bool.false 35952 524288 19 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 64272855 524288 226375608064910080 72057594037927936 19 5185432008638532157440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 35952 524288 5185432008638532157440 75557863725914323419136 73689420 1073741824 160029 159872 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep98 rfl rfl) rfl)

noncomputable def ep107 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 122639713857 274877906944 149000586437 343322505773056 Bool.false 526851843 17179869184 18549024661 42915313221632 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz32) 234469 524288 1 524288 523053 524288 158173 163708928 122639713857 274877906944 149000586437 343322505773056 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 523053 524288 10123072 10477371392 523053 524288 158173 163708928 (ep104 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 234469 524288 1 524288 2247 32768 158173 163708928 526851843 17179869184 18549024661 42915313221632 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 2247 32768 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 35952 524288 10123072 10477371392 2247 32768 158173 163708928 (ep106 rfl rfl) rfl)) rfl)

noncomputable def ep108 := @ep45 122639713857 274877906944 149000586437 343322505773056 Bool.false 526851843 17179869184 18549024661 42915313221632 Bool.true 7111079090282293100544 12934977513 137438953472 371739551299 171661252886528 Bool.true 2030406151154163515392 118185192763 274877906944 743584382057 343322505773056 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep107) rfl rfl

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz304))

noncomputable abbrev qz305 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz280 qz305)

noncomputable def ep109 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 5051106361 68719476736 33951658061 85830626443264 Bool.false 13798024135 34359738368 1065100515 2682207076352 (BSN.cpow_neg_s_mk qz16 76170 1000 6 qz17 rfl)

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep110 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz304) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz304) (Real.sqrt qz306) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz306) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep111 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 79936 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep112 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz305 76170 1000 0 1 4034681531866359 2251799813685248 7812500001249 624500000000000000 30732169228226056503 225179981368524800 59507812509513633 62450000000000000000 qz21 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 7812500001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz306) Bool.false 16922680887833197019136 9444732965739290427392 1000000000159872 79936000000000000000 4034681531866359 2251799813685248 7812500001249 624500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep113 := nat_lit 11097725771402764493510574844692658513966904040376123538066149488024029822976

noncomputable def ep114 := nat_lit 24588038305016783118752679189371841594078454624035891154544137680673898496

noncomputable def ep115 := nat_lit 33244001237598259914294219175699231858712555211880298831889360188710741671936

noncomputable def ep116 := BSN.cos_dyadic_bound_f 1492246212 1073741824 3 2 524288 160029 ep113 ep64 ep114 ep115 ep66 ep114 94396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1492246212) qz287 0 2 ep113 ep64 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1492246212) qz288 0 2 ep115 ep66 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71553907) qz19)

noncomputable def ep117 := @Enclosure.Real.IsNear.cos_image qz35 qz307 Bool.false 71553907 524288 501 524288 Bool.true 94396 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 30732169228226056503 225179981368524800 59507812509513633 62450000000000000000 71553907 524288 501 524288 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 71553907 524288) (BSN.cos_reduce2 qz307 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105007491969640472510464) qz22) 226375608064910080 72057594037927936 Bool.false 94396 524288 21 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 71553907 524288 226375608064910080 72057594037927936 21 105007491969640472510464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94396 524288 105007491969640472510464 75557863725914323419136 1492246212 1073741824 160029 159872 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep118 := nat_lit 19956235957880962661824032577095287851865164508977793655595433768298714562560

noncomputable def ep119 := nat_lit 52226523065765827417823057173704866154208827644598163369452112217870780399616

noncomputable def ep120 := BSN.sin_dyadic_bound_f 1492246212 1073741824 3 2 524288 160029 ep118 ep57 ep114 ep119 ep60 ep114 515720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1492246212) qz283 0 2 ep118 ep57 ep114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1492246212) qz284 0 2 ep119 ep60 ep114 rfl rfl rfl rfl) rfl rfl

noncomputable def ep121 := @Enclosure.Real.IsNear.sin_image qz35 qz307 Bool.false 71553907 524288 501 524288 Bool.true 515720 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 30732169228226056503 225179981368524800 59507812509513633 62450000000000000000 71553907 524288 501 524288 (ep112 rfl) rfl) (Enclosure.sfrac_false_div 71553907 524288) (BSN.sin_reduce2 qz307 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105007491969640472510464) qz22) 226375608064910080 72057594037927936 Bool.false 515720 524288 21 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 71553907 524288 226375608064910080 72057594037927936 21 105007491969640472510464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515720 524288 105007491969640472510464 75557863725914323419136 1492246212 1073741824 160029 159872 (ep120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep110 rfl rfl) rfl)

noncomputable def ep122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 5051106361 68719476736 33951658061 85830626443264 Bool.false 13798024135 34359738368 1065100515 2682207076352 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 214039 524288 1 524288 23599 131072 633941 654835712 5051106361 68719476736 33951658061 85830626443264 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 94396 524288 40572224 41909485568 23599 131072 633941 654835712 (ep117 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 214039 524288 1 524288 64465 65536 633941 654835712 13798024135 34359738368 1065100515 2682207076352 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 64465 65536 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 515720 524288 40572224 41909485568 64465 65536 633941 654835712 (ep121 rfl rfl) rfl)) rfl)

noncomputable def ep123 := @ep43 5051106361 68719476736 33951658061 85830626443264 Bool.false 13798024135 34359738368 1065100515 2682207076352 Bool.true 1583103658416888872960 23037190235 137438953472 439642867421 171661252886528 Bool.true 268040308116730937344 7800999683 274877906944 879917247977 343322505773056 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep108 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep109 ep122) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz310 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz280 qz310)

noncomputable def ep124 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 2742377757 8589934592 31544350369 85830626443264 Bool.false 27806826649 137438953472 62987405589 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 7 qz17 rfl)

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep125 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz311) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz311) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep126 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 79936 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz310 76170 1000 0 1 4381792198794487 2251799813685248 7812500001249 624500000000000000 33376111178217607479 225179981368524800 59507812509513633 62450000000000000000 qz21 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 7812500001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 18378568546572512002048 9444732965739290427392 1000000000159872 79936000000000000000 4381792198794487 2251799813685248 7812500001249 624500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep128 := nat_lit 135313313650018717312534069277586801

noncomputable def ep129 := BSN.cos_dyadic_bound_f 606506043 1073741824 2 1 524288 160029 ep128 ep79 ep128 ep128 ep80 ep128 442848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 606506043) qz287 0 1 ep128 ep79 ep128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 606506043) qz288 0 1 ep128 ep80 ep128 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38854907) qz29)

noncomputable def ep130 := @Enclosure.Real.IsNear.cos_image qz37 qz312 Bool.false 38854907 262144 501 524288 Bool.true 442848 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 33376111178217607479 225179981368524800 59507812509513633 62450000000000000000 38854907 262144 501 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 38854907 262144) (BSN.cos_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21339534321516778881024) qz298) 226375608064910080 72057594037927936 Bool.false 442848 524288 23 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 38854907 262144 226375608064910080 72057594037927936 23 21339534321516778881024 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 442848 524288 21339534321516778881024 37778931862957161709568 606506043 1073741824 160029 159872 (ep129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep131 := BSN.sin_dyadic_bound_f 606506043 1073741824 2 1 524288 160029 ep128 ep75 ep128 ep128 ep76 ep128 280646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 606506043) qz283 0 1 ep128 ep75 ep128 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 606506043) qz284 0 1 ep128 ep76 ep128 rfl rfl rfl rfl) rfl rfl

noncomputable def ep132 := @Enclosure.Real.IsNear.sin_image qz37 qz312 Bool.false 38854907 262144 501 524288 Bool.true 280646 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 33376111178217607479 225179981368524800 59507812509513633 62450000000000000000 38854907 262144 501 524288 (ep127 rfl) rfl) (Enclosure.sfrac_false_div 38854907 262144) (BSN.sin_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21339534321516778881024) qz298) 226375608064910080 72057594037927936 Bool.false 280646 524288 23 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 38854907 262144 226375608064910080 72057594037927936 23 21339534321516778881024 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 280646 524288 21339534321516778881024 37778931862957161709568 606506043 1073741824 160029 159872 (ep131 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep125 rfl rfl) rfl)

noncomputable def ep133 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 2742377757 8589934592 31544350369 85830626443264 Bool.false 27806826649 137438953472 62987405589 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 198163 524288 1 524288 13839 16384 633941 654835712 2742377757 8589934592 31544350369 85830626443264 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 442848 524288 40572224 41909485568 13839 16384 633941 654835712 (ep130 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 198163 524288 1 524288 140323 262144 633941 654835712 27806826649 137438953472 62987405589 171661252886528 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 140323 262144 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 280646 524288 40572224 41909485568 140323 262144 633941 654835712 (ep132 rfl rfl) rfl)) rfl)

noncomputable def ep134 := @ep41 2742377757 8589934592 31544350369 85830626443264 Bool.false 27806826649 137438953472 62987405589 171661252886528 Bool.true 574797486249081831424 66915234347 137438953472 502731568159 171661252886528 Bool.false 6571321075564837601280 47812653615 274877906944 1005892059155 343322505773056 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep124 ep133) rfl rfl

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz314))

noncomputable abbrev qz315 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz267 qz280 qz315)

noncomputable def ep135 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 24924465069 274877906944 117446264175 343322505773056 Bool.true 93932885613 274877906944 117911251887 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 8 qz17 rfl)

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep136 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz314) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz314) (Real.sqrt qz316) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep137 := BSN.log_dyadic_bound 0 16 1 0 1 262144 79936 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz315 76170 1000 0 1 9364972152248037 4503599627370496 15625000003747 1249000000000000000 71332992883673297829 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 19639770079031275290624 9444732965739290427392 1000000000239808 79936000000000000000 9364972152248037 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep137 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep139 := nat_lit 8795316511046697665663956671631606154411141849968372507702001884425811403361

noncomputable def ep140 := nat_lit 15458149276609760457334643576387713722531702094100323519846106386719056481

noncomputable def ep141 := nat_lit 26355033234586873476077200727742043035788362145716916876066313440503996097121

noncomputable def ep142 := BSN.cos_dyadic_bound_f 1408136277 1073741824 3 2 524288 160029 ep139 ep64 ep140 ep141 ep66 ep140 134463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1408136277) qz287 0 2 ep139 ep64 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1408136277) qz288 0 2 ep141 ep66 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83042533) qz19)

noncomputable def ep143 := @Enclosure.Real.IsNear.cos_image qz39 qz317 Bool.false 83042533 524288 125 131072 Bool.false 134463 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 71332992883673297829 450359962737049600 119015625028540899 124900000000000000000 83042533 524288 125 131072 (ep138 rfl) rfl) (Enclosure.sfrac_false_div 83042533 524288) (BSN.cos_reduce0 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99088781476910151499776) qz22) 226375608064910080 72057594037927936 Bool.false 134463 524288 25 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 83042533 524288 226375608064910080 72057594037927936 25 99088781476910151499776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 134463 524288 99088781476910151499776 75557863725914323419136 1408136277 1073741824 160029 159872 (ep142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep144 := nat_lit 15819203200462767989829254294075780906962029968267790255047726506857085280865

noncomputable def ep145 := nat_lit 41406218997621309885002838490122417505540265256358526334664294774285297263201

noncomputable def ep146 := BSN.sin_dyadic_bound_f 1408136277 1073741824 3 2 524288 160029 ep144 ep57 ep140 ep145 ep60 ep140 506751 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1408136277) qz283 0 2 ep144 ep57 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1408136277) qz284 0 2 ep145 ep60 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep147 := @Enclosure.Real.IsNear.sin_image qz39 qz317 Bool.false 83042533 524288 125 131072 Bool.false 506751 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 71332992883673297829 450359962737049600 119015625028540899 124900000000000000000 83042533 524288 125 131072 (ep138 rfl) rfl) (Enclosure.sfrac_false_div 83042533 524288) (BSN.sin_reduce0 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99088781476910151499776) qz22) 226375608064910080 72057594037927936 Bool.false 506751 524288 25 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 83042533 524288 226375608064910080 72057594037927936 25 99088781476910151499776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 506751 524288 99088781476910151499776 75557863725914323419136 1408136277 1073741824 160029 159872 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep136 rfl rfl) rfl)

noncomputable def ep148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 24924465069 274877906944 117446264175 343322505773056 Bool.true 93932885613 274877906944 117911251887 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 185363 524288 1 524288 134463 524288 158173 163708928 24924465069 274877906944 117446264175 343322505773056 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 134463 524288 10123072 10477371392 134463 524288 158173 163708928 (ep143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 185363 524288 1 524288 506751 524288 158173 163708928 93932885613 274877906944 117911251887 343322505773056 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.false 506751 524288 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.false 506751 524288 10123072 10477371392 506751 524288 158173 163708928 (ep147 rfl rfl) rfl)) rfl)

noncomputable def ep149 := @ep39 24924465069 274877906944 117446264175 343322505773056 Bool.true 93932885613 274877906944 117911251887 343322505773056 Bool.true 14967927165037838336000 108906003625 274877906944 1122909400493 343322505773056 Bool.true 12677432839381935194112 23060115999 137438953472 561901655521 171661252886528 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep134 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep135 ep148) rfl rfl

theorem EMRow20.d6 : Enclosure.Complex.IsNear qz3 Bool.true 108906003625 274877906944 1122909400493 343322505773056 Bool.true 23060115999 137438953472 561901655521 171661252886528 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz40 := (BSN.headSumC qz272 17)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep150 := @Enclosure.Complex.IsNear.of_eq qz40 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz41) Bool.false 155238507281 274877906944 1888557586917 343322505773056 Bool.false 44700829083 274877906944 1888355748517 343322505773056

noncomputable def ep151 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz41 Bool.false 207736637053 274877906944 1804965407697 343322505773056 Bool.false 358723357 274877906944 1804841289571 343322505773056 Bool.true

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep152 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz42) Bool.false 207736637053 274877906944 1804965407697 343322505773056 Bool.false 358723357 274877906944 1804841289571 343322505773056

noncomputable def ep153 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz42 Bool.false 86930631321 137438953472 6714859669 1341103538176 Bool.true 31004228083 137438953472 859308538805 171661252886528 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep154 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz43) Bool.false 86930631321 137438953472 6714859669 1341103538176 Bool.true 31004228083 137438953472 859308538805 171661252886528

noncomputable def ep155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz43 Bool.false 50236304325 137438953472 814760414107 171661252886528 Bool.true 2041497583 8589934592 814879203999 171661252886528 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz44) Bool.false 50236304325 137438953472 814760414107 171661252886528 Bool.true 2041497583 8589934592 814879203999 171661252886528

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz44 Bool.false 37258811675 274877906944 1536795227997 343322505773056 Bool.true 22712175475 274877906944 1537209733627 343322505773056 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz45) Bool.false 37258811675 274877906944 1536795227997 343322505773056 Bool.true 22712175475 274877906944 1537209733627 343322505773056

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz45 Bool.true 1198049209 17179869184 90023911983 21457656610816 Bool.false 8269182691 68719476736 720401184069 171661252886528 Bool.false

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz46) Bool.true 1198049209 17179869184 90023911983 21457656610816 Bool.false 8269182691 68719476736 720401184069 171661252886528

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz46 Bool.true 2947683347 8589934592 20930865217 5364414152704 Bool.false 68009818579 274877906944 1340312964593 343322505773056 Bool.false

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz47) Bool.true 2947683347 8589934592 20930865217 5364414152704 Bool.false 68009818579 274877906944 1340312964593 343322505773056

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz47 Bool.true 168814410499 274877906944 1233909339883 343322505773056 Bool.false 5801800381 68719476736 154358820817 42915313221632 Bool.false

noncomputable abbrev qz48 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 9) qz275)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz48) Bool.true 168814410499 274877906944 1233909339883 343322505773056 Bool.false 5801800381 68719476736 154358820817 42915313221632

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP qz3 qz48 Bool.true 108906003625 274877906944 1122909400493 343322505773056 Bool.true 23060115999 137438953472 561901655521 171661252886528 Bool.true

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz319))

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz280 qz320)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 29954203437 137438953472 55499969695 171661252886528 Bool.false 34663716761 137438953472 55533627747 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 9 qz17 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep167 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz319) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz319) (Real.sqrt qz321) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep168 := BSN.log_dyadic_bound 1 17 2 1 867 262144 79936 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep169 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz320 76170 1000 0 1 9895417793173221 4503599627370496 15625000003747 1249000000000000000 75373397330600424357 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 20752195215788806766592 9444732965739290427392 1000000000239808 79936000000000000000 9895417793173221 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep170 := nat_lit 1610290964783169991591200579476219093774977610103697341849850887829309438081

noncomputable def ep171 := nat_lit 519649897228882430733554825230126550158158671393542114846206749763254401

noncomputable def ep172 := nat_lit 4829833594555052209912134628778197028224616512968304941319860249988401805441

noncomputable def ep173 := BSN.cos_dyadic_bound_f 921433199 1073741824 3 2 524288 160029 ep170 ep64 ep171 ep172 ep66 ep171 342798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 921433199) qz287 0 2 ep170 ep64 ep171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 921433199) qz288 0 2 ep172 ep66 ep171 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87746183) qz19)

noncomputable def ep174 := @Enclosure.Real.IsNear.cos_image qz50 qz322 Bool.false 87746183 524288 125 131072 Bool.true 342798 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 75373397330600424357 450359962737049600 119015625028540899 124900000000000000000 87746183 524288 125 131072 (ep169 rfl) rfl) (Enclosure.sfrac_false_div 87746183 524288) (BSN.cos_reduce2 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64840097063096167694336) qz22) 226375608064910080 72057594037927936 Bool.false 342798 524288 26 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 87746183 524288 226375608064910080 72057594037927936 26 64840097063096167694336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 342798 524288 64840097063096167694336 75557863725914323419136 921433199 1073741824 160029 159872 (ep173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep175 := nat_lit 720867461624453147111611056815707201

noncomputable def ep176 := BSN.sin_dyadic_bound_f 921433199 1073741824 2 1 524288 160029 ep175 ep75 ep175 ep175 ep76 ep175 396694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 921433199) qz283 0 1 ep175 ep75 ep175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 921433199) qz284 0 1 ep175 ep76 ep175 rfl rfl rfl rfl) rfl rfl

noncomputable def ep177 := @Enclosure.Real.IsNear.sin_image qz50 qz322 Bool.false 87746183 524288 125 131072 Bool.true 396694 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 75373397330600424357 450359962737049600 119015625028540899 124900000000000000000 87746183 524288 125 131072 (ep169 rfl) rfl) (Enclosure.sfrac_false_div 87746183 524288) (BSN.sin_reduce2 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64840097063096167694336) qz22) 226375608064910080 72057594037927936 Bool.false 396694 524288 26 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 87746183 524288 226375608064910080 72057594037927936 26 64840097063096167694336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 396694 524288 64840097063096167694336 75557863725914323419136 921433199 1073741824 160029 159872 (ep176 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep167 rfl rfl) rfl)

noncomputable def ep178 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 29954203437 137438953472 55499969695 171661252886528 Bool.false 34663716761 137438953472 55533627747 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 174763 524288 1 524288 171399 262144 158173 163708928 29954203437 137438953472 55499969695 171661252886528 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 342798 524288 10123072 10477371392 171399 262144 158173 163708928 (ep174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 174763 524288 1 524288 198347 262144 158173 163708928 34663716761 137438953472 55533627747 171661252886528 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 198347 262144 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 396694 524288 10123072 10477371392 198347 262144 158173 163708928 (ep177 rfl rfl) rfl)) rfl)

noncomputable def ep179 := @ep165 29954203437 137438953472 55499969695 171661252886528 Bool.false 34663716761 137438953472 55533627747 171661252886528 Bool.true 23201675909975169302528 168814410499 274877906944 1233909339883 343322505773056 Bool.false 1594786745236181745664 5801800381 68719476736 154358820817 42915313221632 EMRow20.d6 (ep166 ep178) rfl rfl

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz324))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep180 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 74488543395 274877906944 105666034005 343322505773056 Bool.false 44802617055 274877906944 105442398057 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 10 qz17 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep181 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz324) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz324) (Real.sqrt qz325) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep182 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 79936 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz53 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep183 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz53 76170 1000 0 1 10369908600166117 4503599627370496 15625000003747 1249000000000000000 78987593807465313189 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 21747274560655572598784 9444732965739290427392 1000000000239808 79936000000000000000 10369908600166117 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep182 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep184 := nat_lit 5999364887971624350563264625265298049502391108158385217322282815896050134465

noncomputable def ep185 := nat_lit 2226002666290607882234508733340559482480178694063757067781080108931935681

noncomputable def ep186 := nat_lit 15709018321323117076808741956793229223820342136814905676781952292884717694401

noncomputable def ep187 := BSN.sin_dyadic_bound_f 1105199577 1073741824 3 2 524288 160029 ep184 ep57 ep185 ep186 ep60 ep185 449281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1105199577) qz283 0 2 ep184 ep57 ep185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1105199577) qz284 0 2 ep186 ep60 ep185 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91953661) qz19)

noncomputable def ep188 := @Enclosure.Real.IsNear.cos_image qz52 qz326 Bool.false 91953661 524288 501 524288 Bool.false 449281 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 78987593807465313189 450359962737049600 119015625028540899 124900000000000000000 91953661 524288 501 524288 (ep183 rfl) rfl) (Enclosure.sfrac_false_div 91953661 524288) (BSN.cos_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77771506352444200189952) qz22) 226375608064910080 72057594037927936 Bool.false 449281 524288 27 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 91953661 524288 226375608064910080 72057594037927936 27 77771506352444200189952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449281 524288 77771506352444200189952 75557863725914323419136 1105199577 1073741824 160029 159872 (ep187 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep189 := nat_lit 3333969827835920464927251240139983609493541806174242346098059822212886490561

noncomputable def ep190 := nat_lit 9997457478175180179017284702953269709515665061134599524158617306420795600321

noncomputable def ep191 := BSN.cos_dyadic_bound_f 1105199577 1073741824 3 2 524288 160029 ep189 ep64 ep185 ep190 ep66 ep185 270229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1105199577) qz287 0 2 ep189 ep64 ep185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1105199577) qz288 0 2 ep190 ep66 ep185 rfl rfl rfl rfl) rfl rfl

noncomputable def ep192 := @Enclosure.Real.IsNear.sin_image qz52 qz326 Bool.false 91953661 524288 501 524288 Bool.true 270229 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 78987593807465313189 450359962737049600 119015625028540899 124900000000000000000 91953661 524288 501 524288 (ep183 rfl) rfl) (Enclosure.sfrac_false_div 91953661 524288) (BSN.sin_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77771506352444200189952) qz22) 226375608064910080 72057594037927936 Bool.false 270229 524288 27 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 91953661 524288 226375608064910080 72057594037927936 27 77771506352444200189952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270229 524288 77771506352444200189952 75557863725914323419136 1105199577 1073741824 160029 159872 (ep191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep181 rfl rfl) rfl)

noncomputable def ep193 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 74488543395 274877906944 105666034005 343322505773056 Bool.false 44802617055 274877906944 105442398057 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 165795 524288 1 524288 449281 524288 633941 654835712 74488543395 274877906944 105666034005 343322505773056 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 449281 524288 40572224 41909485568 449281 524288 633941 654835712 (ep188 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 165795 524288 1 524288 270229 524288 633941 654835712 44802617055 274877906944 105442398057 343322505773056 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 270229 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 270229 524288 40572224 41909485568 270229 524288 633941 654835712 (ep192 rfl rfl) rfl)) rfl)

noncomputable def ep194 := @ep163 74488543395 274877906944 105666034005 343322505773056 Bool.false 44802617055 274877906944 105442398057 343322505773056 Bool.true 25928096920225422770176 2947683347 8589934592 20930865217 5364414152704 Bool.false 4673599145659171078144 68009818579 274877906944 1340312964593 343322505773056 (ep164 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep179 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep180 ep193) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz329 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz280 qz329)

noncomputable def ep195 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 4697317485 17179869184 6300451115 21457656610816 Bool.true 34933087815 274877906944 100489403545 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 11 qz17 rfl)

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep196 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz330) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep197 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 79936 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep198 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz329 76170 1000 0 1 10799147631728357 4503599627370496 15625000003747 1249000000000000000 82257107510874895269 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 22647454054174387339264 9444732965739290427392 1000000000239808 79936000000000000000 10799147631728357 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep197 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep199 := nat_lit 47635912122855278284507792244818176

noncomputable def ep200 := BSN.cos_dyadic_bound_f 467179332 1073741824 2 1 524288 160029 ep199 ep79 ep199 ep199 ep80 ep199 475440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 467179332) qz287 0 1 ep199 ep79 ep199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 467179332) qz288 0 1 ep199 ep80 ep199 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz519 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23939969) qz519)

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep201 := @Enclosure.Real.IsNear.cos_image qz55 qz331 Bool.false 23939969 131072 501 524288 Bool.false 475440 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 82257107510874895269 450359962737049600 119015625028540899 124900000000000000000 23939969 131072 501 524288 (ep198 rfl) rfl) (Enclosure.sfrac_false_div 23939969 131072) (BSN.cos_reduce0 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8218705732227519479808) qz332) 226375608064910080 72057594037927936 Bool.false 475440 524288 29 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 23939969 131072 226375608064910080 72057594037927936 29 8218705732227519479808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 475440 524288 8218705732227519479808 18889465931478580854784 467179332 1073741824 160029 159872 (ep200 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep202 := BSN.sin_dyadic_bound_f 467179332 1073741824 2 1 524288 160029 ep199 ep75 ep199 ep199 ep76 ep199 220985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 467179332) qz283 0 1 ep199 ep75 ep199 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 467179332) qz284 0 1 ep199 ep76 ep199 rfl rfl rfl rfl) rfl rfl

noncomputable def ep203 := @Enclosure.Real.IsNear.sin_image qz55 qz331 Bool.false 23939969 131072 501 524288 Bool.false 220985 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 82257107510874895269 450359962737049600 119015625028540899 124900000000000000000 23939969 131072 501 524288 (ep198 rfl) rfl) (Enclosure.sfrac_false_div 23939969 131072) (BSN.sin_reduce0 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8218705732227519479808) qz332) 226375608064910080 72057594037927936 Bool.false 220985 524288 29 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 23939969 131072 226375608064910080 72057594037927936 29 8218705732227519479808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 220985 524288 8218705732227519479808 18889465931478580854784 467179332 1073741824 160029 159872 (ep202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep196 rfl rfl) rfl)

noncomputable def ep204 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 4697317485 17179869184 6300451115 21457656610816 Bool.true 34933087815 274877906944 100489403545 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 158079 524288 1 524288 29715 32768 633941 654835712 4697317485 17179869184 6300451115 21457656610816 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 475440 524288 40572224 41909485568 29715 32768 633941 654835712 (ep201 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 158079 524288 1 524288 220985 524288 633941 654835712 34933087815 274877906944 100489403545 343322505773056 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 220985 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 220985 524288 40572224 41909485568 220985 524288 633941 654835712 (ep203 rfl rfl) rfl)) rfl)

noncomputable def ep205 := @ep161 4697317485 17179869184 6300451115 21457656610816 Bool.true 34933087815 274877906944 100489403545 343322505773056 Bool.true 10291164343307337728 1198049209 17179869184 90023911983 21457656610816 Bool.false 9092062520958534025216 8269182691 68719476736 720401184069 171661252886528 (ep162 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep194 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep195 ep204) rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz334))

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz280 qz335)

noncomputable def ep206 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 56427599019 274877906944 96412636269 343322505773056 Bool.true 55788906239 274877906944 96407365489 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 12 qz17 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep207 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz336) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep208 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 79936 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep209 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz335 76170 1000 0 1 11191020447815397 4503599627370496 15625000003747 1249000000000000000 85242002751009878949 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 23469270914176955449344 9444732965739290427392 1000000000239808 79936000000000000000 11191020447815397 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep208 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep210 := nat_lit 1097312860352250462332015845028028124738544410970734665980858596117708800000

noncomputable def ep211 := nat_lit 241352804224122516836975673447281086301386019186959754645313945600000000

noncomputable def ep212 := nat_lit 3291455875448303141962373583737189812043030460873830078433285160461926400000

noncomputable def ep213 := BSN.cos_dyadic_bound_f 837204480 1073741824 3 2 524288 160029 ep210 ep64 ep211 ep212 ep66 ep211 372831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 837204480) qz287 0 2 ep210 ep64 ep211 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 837204480) qz288 0 2 ep212 ep66 ep211 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99234751) qz19)

noncomputable def ep214 := @Enclosure.Real.IsNear.cos_image qz57 qz337 Bool.false 99234751 524288 501 524288 Bool.false 372831 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 85242002751009878949 450359962737049600 119015625028540899 124900000000000000000 99234751 524288 501 524288 (ep209 rfl) rfl) (Enclosure.sfrac_false_div 99234751 524288) (BSN.cos_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58913027889457447043072) qz22) 226375608064910080 72057594037927936 Bool.false 372831 524288 30 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 99234751 524288 226375608064910080 72057594037927936 30 58913027889457447043072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 372831 524288 58913027889457447043072 75557863725914323419136 837204480 1073741824 160029 159872 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep215 := nat_lit 491276708407922099851083550556160000

noncomputable def ep216 := BSN.sin_dyadic_bound_f 837204480 1073741824 2 1 524288 160029 ep215 ep75 ep215 ep215 ep76 ep215 368611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 837204480) qz283 0 1 ep215 ep75 ep215 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 837204480) qz284 0 1 ep215 ep76 ep215 rfl rfl rfl rfl) rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.sin_image qz57 qz337 Bool.false 99234751 524288 501 524288 Bool.false 368611 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 85242002751009878949 450359962737049600 119015625028540899 124900000000000000000 99234751 524288 501 524288 (ep209 rfl) rfl) (Enclosure.sfrac_false_div 99234751 524288) (BSN.sin_reduce0 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58913027889457447043072) qz22) 226375608064910080 72057594037927936 Bool.false 368611 524288 30 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 99234751 524288 226375608064910080 72057594037927936 30 58913027889457447043072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 368611 524288 58913027889457447043072 75557863725914323419136 837204480 1073741824 160029 159872 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep207 rfl rfl) rfl)

noncomputable def ep218 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 56427599019 274877906944 96412636269 343322505773056 Bool.true 55788906239 274877906944 96407365489 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 151349 524288 1 524288 372831 524288 633941 654835712 56427599019 274877906944 96412636269 343322505773056 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 372831 524288 40572224 41909485568 372831 524288 633941 654835712 (ep214 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 151349 524288 1 524288 368611 524288 633941 654835712 55788906239 274877906944 96407365489 343322505773056 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 368611 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 368611 524288 40572224 41909485568 368611 524288 633941 654835712 (ep217 rfl rfl) rfl)) rfl)

noncomputable def ep219 := @ep159 56427599019 274877906944 96412636269 343322505773056 Bool.true 55788906239 274877906944 96407365489 343322505773056 Bool.false 640101510527791923200 37258811675 274877906944 1536795227997 343322505773056 Bool.true 1560768814178212249600 22712175475 274877906944 1537209733627 343322505773056 (ep160 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep205 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep206 ep218) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz340 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz280 qz340)

noncomputable def ep220 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 63213796975 274877906944 92725600217 343322505773056 Bool.true 42615747181 274877906944 92548674371 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 13 qz17 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep221 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz341) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep222 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 79936 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz340 76170 1000 0 1 11551488463034085 4503599627370496 15625000003747 1249000000000000000 17597537524586125089 90071992547409920 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 24225227133228857425920 9444732965739290427392 1000000000239808 79936000000000000000 11551488463034085 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep224 := nat_lit 164554138674037601722545673449790321

noncomputable def ep225 := BSN.cos_dyadic_bound_f 636908731 1073741824 2 1 524288 160029 ep224 ep79 ep224 ep224 ep80 ep224 434725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 636908731) qz287 0 1 ep224 ep79 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 636908731) qz288 0 1 ep224 ep80 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102431149) qz19)

noncomputable def ep226 := @Enclosure.Real.IsNear.cos_image qz59 qz342 Bool.false 102431149 524288 501 524288 Bool.false 434725 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 17597537524586125089 90071992547409920 119015625028540899 124900000000000000000 102431149 524288 501 524288 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 102431149 524288) (BSN.cos_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44818467620204700499968) qz22) 226375608064910080 72057594037927936 Bool.false 434725 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 102431149 524288 226375608064910080 72057594037927936 31 44818467620204700499968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 434725 524288 44818467620204700499968 75557863725914323419136 636908731 1073741824 160029 159872 (ep225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep227 := BSN.sin_dyadic_bound_f 636908731 1073741824 2 1 524288 160029 ep224 ep75 ep224 ep224 ep76 ep224 293071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 636908731) qz283 0 1 ep224 ep75 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 636908731) qz284 0 1 ep224 ep76 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.sin_image qz59 qz342 Bool.false 102431149 524288 501 524288 Bool.false 293071 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 17597537524586125089 90071992547409920 119015625028540899 124900000000000000000 102431149 524288 501 524288 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 102431149 524288) (BSN.sin_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44818467620204700499968) qz22) 226375608064910080 72057594037927936 Bool.false 293071 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 102431149 524288 226375608064910080 72057594037927936 31 44818467620204700499968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 293071 524288 44818467620204700499968 75557863725914323419136 636908731 1073741824 160029 159872 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep221 rfl rfl) rfl)

noncomputable def ep229 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 63213796975 274877906944 92725600217 343322505773056 Bool.true 42615747181 274877906944 92548674371 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 145411 524288 1 524288 434725 524288 633941 654835712 63213796975 274877906944 92725600217 343322505773056 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 434725 524288 40572224 41909485568 434725 524288 633941 654835712 (ep226 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 145411 524288 1 524288 293071 524288 633941 654835712 42615747181 274877906944 92548674371 343322505773056 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 293071 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 293071 524288 40572224 41909485568 293071 524288 633941 654835712 (ep228 rfl rfl) rfl)) rfl)

noncomputable def ep230 := @ep157 63213796975 274877906944 92725600217 343322505773056 Bool.true 42615747181 274877906944 92548674371 343322505773056 Bool.false 27617700370915629465600 50236304325 137438953472 814760414107 171661252886528 Bool.true 17957202644680797323264 2041497583 8589934592 814879203999 171661252886528 (ep158 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep220 ep229) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz345 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz280 qz345)

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 9173581749 34359738368 44741623525 171661252886528 Bool.false 1659733245 137438953472 22214667403 85830626443264 (BSN.cpow_neg_s_mk qz16 76170 1000 14 qz17 rfl)

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep232 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz346) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz346) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep233 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 79936 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz345 76170 1000 0 1 11885241781671653 4503599627370496 15625000003747 1249000000000000000 90529886650992980901 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 24925158572916270432256 9444732965739290427392 1000000000239808 79936000000000000000 11885241781671653 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep235 := nat_lit 28994380656571484997756311386598760120180749233083543838147341223013751193600

noncomputable def ep236 := nat_lit 51845445139590399150927979239762688907392505427408649541505036690890162176

noncomputable def ep237 := nat_lit 75853723379842171490736455950894279770813802982622048429223456953250764292096

noncomputable def ep238 := BSN.sin_dyadic_bound_f 1638094024 1073741824 3 2 524288 160029 ep235 ep57 ep236 ep237 ep60 ep236 523752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1638094024) qz283 0 2 ep235 ep57 ep236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1638094024) qz284 0 2 ep237 ep60 ep236 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52695329) qz29)

noncomputable def ep239 := @Enclosure.Real.IsNear.cos_image qz61 qz347 Bool.false 52695329 262144 501 524288 Bool.false 523752 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 90529886650992980901 450359962737049600 119015625028540899 124900000000000000000 52695329 262144 501 524288 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 52695329 262144) (BSN.cos_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57635309681993054158848) qz298) 226375608064910080 72057594037927936 Bool.false 523752 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 52695329 262144 226375608064910080 72057594037927936 31 57635309681993054158848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523752 524288 57635309681993054158848 37778931862957161709568 1638094024 1073741824 160029 159872 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep240 := nat_lit 16131031673712865176153918761105872372948146243014150420989191806870257401856

noncomputable def ep241 := nat_lit 48289404130859414730159900324838091741029653718187633963884565347228991881216

noncomputable def ep242 := BSN.cos_dyadic_bound_f 1638094024 1073741824 3 2 524288 160029 ep240 ep64 ep236 ep241 ep66 ep236 23690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1638094024) qz287 0 2 ep240 ep64 ep236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1638094024) qz288 0 2 ep241 ep66 ep236 rfl rfl rfl rfl) rfl rfl

noncomputable def ep243 := @Enclosure.Real.IsNear.sin_image qz61 qz347 Bool.false 52695329 262144 501 524288 Bool.true 23690 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 90529886650992980901 450359962737049600 119015625028540899 124900000000000000000 52695329 262144 501 524288 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 52695329 262144) (BSN.sin_reduce3 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57635309681993054158848) qz298) 226375608064910080 72057594037927936 Bool.false 23690 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 52695329 262144 226375608064910080 72057594037927936 31 57635309681993054158848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23690 524288 57635309681993054158848 37778931862957161709568 1638094024 1073741824 160029 159872 (ep242 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep232 rfl rfl) rfl)

noncomputable def ep244 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 9173581749 34359738368 44741623525 171661252886528 Bool.false 1659733245 137438953472 22214667403 85830626443264 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 140121 524288 1 524288 65469 65536 633941 654835712 9173581749 34359738368 44741623525 171661252886528 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 523752 524288 40572224 41909485568 65469 65536 633941 654835712 (ep239 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 140121 524288 1 524288 11845 262144 633941 654835712 1659733245 137438953472 22214667403 85830626443264 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 11845 262144 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 23690 524288 40572224 41909485568 11845 262144 633941 654835712 (ep243 rfl rfl) rfl)) rfl)

noncomputable def ep245 := @ep155 9173581749 34359738368 44741623525 171661252886528 Bool.false 1659733245 137438953472 22214667403 85830626443264 Bool.false 2986913748354626224128 86930631321 137438953472 6714859669 1341103538176 Bool.true 266324291308419547136 31004228083 137438953472 859308538805 171661252886528 (ep156 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep231 ep244) rfl rfl

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt qz349))

noncomputable abbrev qz350 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz267 qz280 qz350)

noncomputable def ep246 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 33875374411 274877906944 85961332433 343322505773056 Bool.false 62367179523 274877906944 86224211961 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 15 qz17 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep247 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz349) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz349) (Real.sqrt qz351) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep248 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 79936 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz350 76170 1000 0 1 12195956895733477 4503599627370496 15625000003747 1249000000000000000 92896603674801894309 450359962737049600 119015625028540899 124900000000000000000 qz21 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 25576775395801252757504 9444732965739290427392 1000000000239808 79936000000000000000 12195956895733477 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep250 := nat_lit 81478419350628020075439062023373056

noncomputable def ep251 := BSN.sin_dyadic_bound_f 534269828 1073741824 2 1 524288 160029 ep250 ep75 ep250 ep250 ep76 ep250 250241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 534269828) qz283 0 1 ep250 ep75 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 534269828) qz284 0 1 ep250 ep76 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13518235) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz353 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep252 := @Enclosure.Real.IsNear.cos_image qz63 qz352 Bool.false 13518235 65536 125 131072 Bool.false 250241 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 92896603674801894309 450359962737049600 119015625028540899 124900000000000000000 13518235 65536 125 131072 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 13518235 65536) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4699487110022446448640) qz353) 226375608064910080 72057594037927936 Bool.false 250241 524288 32 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 13518235 65536 226375608064910080 72057594037927936 32 4699487110022446448640 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 250241 524288 4699487110022446448640 9444732965739290427392 534269828 1073741824 160029 159872 (ep251 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep253 := BSN.cos_dyadic_bound_f 534269828 1073741824 2 1 524288 160029 ep250 ep79 ep250 ep250 ep80 ep250 460713 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 534269828) qz287 0 1 ep250 ep79 ep250 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 534269828) qz288 0 1 ep250 ep80 ep250 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz63 qz352 Bool.false 13518235 65536 125 131072 Bool.true 460713 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 92896603674801894309 450359962737049600 119015625028540899 124900000000000000000 13518235 65536 125 131072 (ep249 rfl) rfl) (Enclosure.sfrac_false_div 13518235 65536) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4699487110022446448640) qz353) 226375608064910080 72057594037927936 Bool.false 460713 524288 32 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 13518235 65536 226375608064910080 72057594037927936 32 4699487110022446448640 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 460713 524288 4699487110022446448640 9444732965739290427392 534269828 1073741824 160029 159872 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep247 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 33875374411 274877906944 85961332433 343322505773056 Bool.false 62367179523 274877906944 86224211961 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 135371 524288 1 524288 250241 524288 158173 163708928 33875374411 274877906944 85961332433 343322505773056 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 250241 524288 10123072 10477371392 250241 524288 158173 163708928 (ep252 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 135371 524288 1 524288 460713 524288 158173 163708928 62367179523 274877906944 86224211961 343322505773056 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.true 460713 524288 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.true 460713 524288 10123072 10477371392 460713 524288 158173 163708928 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep153 33875374411 274877906944 85961332433 343322505773056 Bool.false 62367179523 274877906944 86224211961 343322505773056 Bool.false 28551105994357018198016 207736637053 274877906944 1804965407697 343322505773056 Bool.false 49302562772042645504 358723357 274877906944 1804841289571 343322505773056 (ep154 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep245 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep246 ep255) rfl rfl

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt qz355))

noncomputable abbrev qz356 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz267 qz280 qz356)

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.true 13124532443 68719476736 20898044805 85830626443264 Bool.false 22171052863 137438953472 41757229473 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 16 qz17 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz355) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz355) (Real.sqrt qz357) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 0 32 1 0 1 262144 79936 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz356 76170 1000 0 1 3121657384082679 1125899906842624 3906250001249 312250000000000000 23777664294557765943 112589990684262400 29753906259513633 31225000000000000000 qz21 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 26186360105375033720832 9444732965739290427392 1000000000319744 79936000000000000000 3121657384082679 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 321660703385785517556908170486850625

noncomputable def ep262 := BSN.cos_dyadic_bound_f 753094545 1073741824 2 1 524288 160029 ep261 ep79 ep261 ep261 ep80 ep261 400532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 753094545) qz287 0 1 ep261 ep79 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 753094545) qz288 0 1 ep261 ep80 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110723377) qz19)

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz65 qz358 Bool.false 110723377 524288 501 524288 Bool.true 400532 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 23777664294557765943 112589990684262400 29753906259513633 31225000000000000000 110723377 524288 501 524288 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 110723377 524288) (BSN.cos_reduce2 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52994317396727126032384) qz22) 226375608064910080 72057594037927936 Bool.false 400532 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 110723377 524288 226375608064910080 72057594037927936 33 52994317396727126032384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400532 524288 52994317396727126032384 75557863725914323419136 753094545 1073741824 160029 159872 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := BSN.sin_dyadic_bound_f 753094545 1073741824 2 1 524288 160029 ep261 ep75 ep261 ep261 ep76 ep261 338306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 753094545) qz283 0 1 ep261 ep75 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 753094545) qz284 0 1 ep261 ep76 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz65 qz358 Bool.false 110723377 524288 501 524288 Bool.true 338306 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 23777664294557765943 112589990684262400 29753906259513633 31225000000000000000 110723377 524288 501 524288 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 110723377 524288) (BSN.sin_reduce2 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52994317396727126032384) qz22) 226375608064910080 72057594037927936 Bool.false 338306 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 110723377 524288 226375608064910080 72057594037927936 33 52994317396727126032384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338306 524288 52994317396727126032384 75557863725914323419136 753094545 1073741824 160029 159872 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep258 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.true 13124532443 68719476736 20898044805 85830626443264 Bool.false 22171052863 137438953472 41757229473 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz64 (Real.cos qz65) 131071 524288 1 524288 100133 131072 633941 654835712 13124532443 68719476736 20898044805 85830626443264 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.true 400532 524288 40572224 41909485568 100133 131072 633941 654835712 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 131071 524288 1 524288 169153 262144 633941 654835712 22171052863 137438953472 41757229473 171661252886528 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.true 169153 262144 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.true 338306 524288 40572224 41909485568 169153 262144 633941 654835712 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep151 13124532443 68719476736 20898044805 85830626443264 Bool.false 22171052863 137438953472 41757229473 171661252886528 Bool.false 10667908989628046114816 155238507281 274877906944 1888557586917 343322505773056 Bool.false 6143635168498261426176 44700829083 274877906944 1888355748517 343322505773056 (ep152 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep266) rfl rfl

theorem EMRow20.d7 : Enclosure.Complex.IsNear qz40 Bool.false 155238507281 274877906944 1888557586917 343322505773056 Bool.false 44700829083 274877906944 1888355748517 343322505773056 := ep150 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow20.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow20.d9 : @Eq Nat (Nat.pow 20 1) 20 := @Eq.refl Nat 20

noncomputable def ep268 := nat_lit 5446461814444766308246478719

noncomputable def ep269 := nat_lit 10034081478143735863286169600

noncomputable def ep270 := nat_lit 342708959465943544975129443095873

noncomputable def ep271 := nat_lit 52177257133285686968207626207232000

noncomputable abbrev qz540 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz520 := qz540

noncomputable abbrev qz360 := qz520

noncomputable abbrev qz66 := qz360

noncomputable abbrev qz521 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz361 := qz521

noncomputable abbrev qz67 := qz361

noncomputable abbrev qz541 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz542 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz538 (@HAdd.hAdd Complex Complex Complex qz538 qz541 (@HMul.hMul Complex Complex Complex qz540 Complex.I (@HDiv.hDiv Complex Complex Complex qz542 (↑qz539) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz362 := qz522

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 1 qz362)

noncomputable abbrev qz523 := (@HAdd.hAdd Complex Complex Complex qz538 qz541 (@HMul.hMul Complex Complex Complex qz540 Complex.I (@HDiv.hDiv Complex Complex Complex qz542 (↑qz539) (2 : Complex))))

noncomputable abbrev qz363 := qz523

noncomputable abbrev qz69 := qz363

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz364 := (@instHSub Real Real.instSub)

noncomputable def ep272 := Complex.re (@HMul.hMul Complex Complex Complex qz66 (Complex.exp (@HMul.hMul Complex Complex Complex qz66 Complex.I ↑(@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70))) (zetaApproximant qz5 1 20))

noncomputable def ep273 := @Enclosure.Real.IsNear.of_eq ep272 (@HSub.hSub Real Real Real qz364 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20))))

noncomputable def ep274 := nat_lit 21785517822235326691408524581

noncomputable def ep275 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20))) ep274

noncomputable def ep276 := nat_lit 40136325912574943453144678400

noncomputable def ep277 := nat_lit 2052244712955446252393896399411283

noncomputable def ep278 := nat_lit 313063542799714121809245757243392000

noncomputable def ep279 := nat_lit 8027265182514988690628935680

noncomputable def ep280 := nat_lit 801808768043003491376051832791

noncomputable def ep281 := nat_lit 62612708559942824361849151448678400

noncomputable def ep282 := nat_lit 174880773163959533946780182153738020204515107242959175680

noncomputable def ep283 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20)) 524287 524288 73241

noncomputable def ep284 := nat_lit 3016545400317326665945309

noncomputable def ep285 := nat_lit 478079519889889758806016000

noncomputable def ep286 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) Bool.false 524287 524288 4687424

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14823741) qz29)

noncomputable def ep287 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) qz365 Bool.false 14823741 262144 57

noncomputable def ep288 := nat_lit 3274178560000000000000000

noncomputable def ep289 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) Bool.false 50933987531736565603 900719925474099200 1418173056165513208963 ep288

noncomputable def ep290 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70 18040539753087045191 180143985094819840 466809756165513208963 ep288 571434957 13107200

noncomputable def ep291 := nat_lit 133520392275195502534328320

noncomputable def ep292 := nat_lit 8185446400000000000000000

noncomputable def ep293 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 26938190803813007399 450359962737049600 2077179859043479342447 ep292 Bool.false 18040539753087045191 180143985094819840

noncomputable def ep294 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 23659480209610955599 450359962737049600 2025979858961624878447 ep292 Bool.false 18599386236055397831 180143985094819840 425849756162239030403

noncomputable def ep295 := nat_lit 60659413033043791119967072081149952

noncomputable def ep296 := nat_lit 5077960506847839789817467603255296

noncomputable abbrev qz543 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz524 := qz543

noncomputable abbrev qz366 := (@HSub.hSub Complex Complex Complex qz521 qz522 qz524)

noncomputable abbrev qz367 := (Complex.log qz522)

noncomputable abbrev qz71 := (@HSub.hSub Complex Complex Complex qz361 (@HMul.hMul Complex Complex Complex qz360 qz366 qz367) qz362)

noncomputable abbrev qz368 := qz524

noncomputable abbrev qz72 := (@HMul.hMul Complex Complex Complex qz360 qz368 ↑(Real.log qz271))

noncomputable abbrev qz525 := qz542

noncomputable abbrev qz369 := qz525

noncomputable abbrev qz73 := qz369

noncomputable abbrev qz74 := (@instHMul Nat instMulNat)

noncomputable abbrev qz526 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz370 := qz526

noncomputable abbrev qz75 := qz370

noncomputable abbrev qz76 := qz362

noncomputable abbrev qz371 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz77 := qz371

noncomputable abbrev qz372 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz78 := qz372

noncomputable abbrev qz373 := (@instHSub Int Int.instSub)

noncomputable abbrev qz374 := (@instHMul Int Int.instMul)

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz71 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k)))))) Bool.true 23659480209610955599

noncomputable def ep298 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz71 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) Bool.true 23659538224542309199 450359962737049600

noncomputable def ep299 := nat_lit 203233387481276558362026180608

noncomputable def ep300 := nat_lit 39941877804765234864207167488000

noncomputable def ep301 := @ep298 123655822767791383 499600000000000000000 Bool.false 92998895179086413027 900719925474099200 1624414064889337 12490000000000000000 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600 Bool.true ep299 23659480209610955599 450359962737049600 2025979858961624878447 ep292 Bool.false ep300

noncomputable def ep302 := @Enclosure.Complex.IsNear.addLitP qz71 qz72 Bool.true 24073390965263358799 450359962737049600 121750000013885133 499600000000000000000

noncomputable def ep303 := nat_lit 3101102994167209551331328

noncomputable def ep304 := @ep302 Bool.false 92998895179086413027 900719925474099200 1624414064889337 12490000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep303 23659538224542309199 450359962737049600 123655822767791383 499600000000000000000 Bool.false 92998895179086413027 92998895179086413027 900719925474099200

noncomputable abbrev qz79 := (@HMul.hMul Complex Complex Complex qz360 qz366 qz367)

noncomputable def ep305 := @Enclosure.Complex.IsNear.subLitP qz79 qz76 Bool.true 23060081049104997199 450359962737049600 121750000013885133 499600000000000000000 Bool.false 127302813540767481059

noncomputable def ep306 := @ep305 900719925474099200 1624414064889337 12490000000000000000 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 Bool.true 96293563861053435196000 24073390965263358799 450359962737049600 121750000013885133 499600000000000000000 Bool.false 371995580716345652108000 92998895179086413027 900719925474099200 1624414064889337 12490000000000000000

noncomputable abbrev qz80 := qz366

noncomputable abbrev qz81 := qz367

noncomputable def ep307 := @Enclosure.Complex.IsNear.mul qz80 qz81 Bool.true 23060081049104997199 450359962737049600 121750000013885133 499600000000000000000 Bool.false 127302813540767481059 900719925474099200 1624414064889337

noncomputable abbrev qz82 := (Complex.re qz366)

noncomputable abbrev qz83 := (Complex.re qz367)

noncomputable abbrev qz84 := (Complex.im qz366)

noncomputable abbrev qz85 := (Complex.im qz367)

noncomputable def ep308 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz82 qz83) (@HMul.hMul Real Real Real qz0 qz84 qz85) 114800960091125189 18014398509481984 5468750008743 999200000000000000 6482526262845781731 112589990684262400

noncomputable def ep309 := nat_lit 103853372419882701857621649815240704

noncomputable def ep310 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz83 7000 4000 0 1 16400137155875027 4503599627370496 781250001249 249800000000000000

noncomputable def ep311 := @Enclosure.Complex.IsNear.re_isNear qz80 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable abbrev qz375 := (Enclosure.sfrac Bool.false 152340 4000)

noncomputable abbrev qz86 := qz375

noncomputable def ep312 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz86) Bool.false 7000 4000 0 1 Bool.false 152340 4000 0

noncomputable abbrev qz376 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz87 := qz376

noncomputable abbrev qz377 := (Complex.log (Complex.mk qz87 qz86))

noncomputable def ep313 := @Enclosure.Complex.IsNear.of_eq qz81 qz377 Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000

noncomputable def ep314 := nat_lit 409378574406279186293566994665881280282967105773178880000000000000

noncomputable def ep315 := nat_lit 4209941226640533764950290595157096262339387021848576000000000000

noncomputable def ep316 := nat_lit 1625082651902046509034027775944390023961253539840000000000000

noncomputable def ep317 := BSN.log_dyadic_bound 6904475600 39672475600 4 3 ep314 524288 159872 ep315 ep316 184367 46576951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6904475600) (BSN.artanhQ 39672475600) 0 3 ep315 ep314 ep316 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz88 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz378 := (Real.log (Enclosure.sfrac Bool.false 23288475600 16000000))

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz380 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep318 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz378 1 2 0 1 16400137155875027 2251799813685248 781250001249 124900000000000000 16400137155875027 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 23288475600 16000000 16400137155875027 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23288475600) qz380)) Bool.false 137574321746870498492416 18889465931478580854784 1000000001598720 159872000000000000000 16400137155875027 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 23288475600 16000000 10 46576951200 32768000000 184367 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep319 := BSN.arctan_dyadic_bound_f 9000 152340 1 0 524288 159872 0 1 1 0 1 1 30938 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz89 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz90 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz379 BSN.pi_near_15 rfl)

noncomputable abbrev qz381 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 152340)))

noncomputable def ep320 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz381 884279719003555 562949953421312 1 2000000000000000 30938 524288 1 159872 446200699657987293184 851060294452643 562949953421312 15625000001249 2498000000000000000 qz90 (ep319 rfl) rfl rfl

noncomputable abbrev qz382 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152340) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep321 := @Enclosure.Complex.IsNear.re_isNear qz81 Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (ep313 (@congrArg Complex Complex qz76 (Complex.mk qz87 qz86) Complex.log (BSN.w_shift_mk qz16 Bool.false 76170 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz377 Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz377) (@HMul.hMul Real Real Real qz0 qz88 qz378) Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 9000 152340 4000 23288475600 16000000 rfl rfl rfl) (ep318 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz377) qz382 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 9000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz382 (@HSub.hSub Real Real Real qz364 qz89 qz381) Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 152340 9000 rfl rfl) ep320))))

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz85 152340 4000 0 1 851060294452643 562949953421312 15625000001249 2498000000000000000

noncomputable def ep323 := @Enclosure.Complex.IsNear.im_isNear qz80 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable def ep324 := @Enclosure.Complex.IsNear.im_isNear qz81 Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (ep313 (@congrArg Complex Complex qz76 (Complex.mk qz87 qz86) Complex.log (BSN.w_shift_mk qz16 Bool.false 76170 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz377 Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz377) (@HMul.hMul Real Real Real qz0 qz88 qz378) Bool.false 16400137155875027 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 9000 152340 4000 23288475600 16000000 rfl rfl rfl) (ep318 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz377) qz382 Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 9000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz382 (@HSub.hSub Real Real Real qz364 qz89 qz381) Bool.false 851060294452643 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 152340 9000 rfl rfl) ep320))))

noncomputable abbrev qz383 := (Enclosure.Real.IsNear.const Bool.false 152340 4000)

noncomputable abbrev qz91 := (@ep312 1 (BSN.w_sub_half_mk qz280 Bool.false 76170 1000 2 qz282 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz375 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz383))

noncomputable def ep325 := @ep308 119015625009513633 499600000000000000000 ep309 23060081049104997199 450359962737049600 121750000013885133 499600000000000000000 (@ep310 114800960091125189 18014398509481984 5468750008743 999200000000000000 (ep311 qz91) ep321 rfl) (@ep322 6482526262845781731 112589990684262400 119015625009513633 499600000000000000000 (ep323 qz91) ep324 rfl) rfl

noncomputable def ep326 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz82 qz85) (@HMul.hMul Real Real Real qz0 qz84 qz83) 5957422061168501 2251799813685248 109375000008743 9992000000000000000 124919844716300080659 900719925474099200

noncomputable def ep327 := nat_lit 286660451812708080098321076827717632

noncomputable def ep328 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz85 7000 4000 0 1 851060294452643 562949953421312 15625000001249 2498000000000000000

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz83 152340 4000 0 1 16400137155875027 4503599627370496 781250001249 249800000000000000

noncomputable def ep330 := @ep326 5950781259513633 49960000000000000000 ep327 127302813540767481059 900719925474099200 1624414064889337 12490000000000000000 (@ep328 5957422061168501 2251799813685248 109375000008743 9992000000000000000 (ep311 qz91) ep324 rfl) (@ep329 124919844716300080659 900719925474099200 5950781259513633 49960000000000000000 (ep323 qz91) ep321 rfl) rfl

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk qz87 qz86) Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 76170 1000 2 qz17 rfl)

noncomputable abbrev qz384 := (ep331 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 152340 4000) Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 152340 4000)))

noncomputable abbrev qz92 := qz384

noncomputable def ep332 := ep306 (@ep307 12490000000000000000 (ep325 rfl) (ep330 rfl)) qz92 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz93 := qz368

noncomputable def ep333 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz93) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz93) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz93) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz94 := (@Enclosure.Complex.IsNear.of_eq qz368 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz278) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz278 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz379 qz290))

noncomputable def ep335 := ep334 (@Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow20.d4)

noncomputable def ep336 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz93) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep337 := ep336 (@Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep338 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz93) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz93) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz93) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep340 := ep339 (@Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz23)

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz93) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep342 := ep341 (@Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow20.d4)

noncomputable def ep343 := @ep304 1624414064889337 12490000000000000000 (ep332 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz93 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep333 131072 1 262144 (ep335 rfl) (ep337 rfl) rfl rfl) (@ep338 1 0 1 (ep340 rfl) (ep342 rfl) rfl rfl))

noncomputable abbrev qz95 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz385 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz96 := (@HMul.hMul Complex Complex Complex qz360 (@HMul.hMul Complex Complex Complex qz360 (2 : Complex) qz385) (@HSub.hSub Complex Complex Complex qz361 (@HMul.hMul Complex Complex Complex qz360 (2 : Complex) qz385) (1 : Complex)))

noncomputable abbrev qz386 := (@HPow.hPow Complex Int Complex qz526 qz522 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz97 := qz386

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97)) Bool.false 1106547 8589934592 3 8589934592

noncomputable def ep345 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97) Bool.false 0 1 0 1 Bool.false

noncomputable def ep346 := @ep345 0 1 0 1 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600 Bool.false 1106547 1106547 8589934592 3 8589934592 Bool.true 936507611 936507611 429496729600 2539

noncomputable def ep347 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep348 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600

noncomputable abbrev qz98 := (Complex.re qz386)

noncomputable abbrev qz99 := (Complex.im qz386)

noncomputable def ep349 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99) 1106547 8589934592 3 8589934592 0 1 0

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98 1 12 0 1 3319641 2147483648 9 2147483648 1106547

noncomputable def ep351 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz387 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz23)

noncomputable def ep352 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep351 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz387)

noncomputable def ep353 := @Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617 107374182400

noncomputable abbrev qz527 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz388 := (@HPow.hPow Complex Nat Complex qz527 qz522 1)

noncomputable abbrev qz100 := (@Inv.inv Complex Complex.instInv qz388)

noncomputable def ep354 := @Enclosure.Complex.IsNear.of_eq qz97 qz100 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617

noncomputable def ep355 := @Enclosure.Complex.IsNear.of_parts qz100 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617

noncomputable abbrev qz101 := (Complex.re qz388)

noncomputable abbrev qz102 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz103 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz104 := qz388

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz101 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) 9000 4000 0 1 368849 536870912 1 536870912

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear qz104 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable def ep358 := @Enclosure.Complex.IsNear.of_eq qz104 qz76 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0

noncomputable def ep359 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) Bool.false 368849 536870912 1 536870912 368849 536870912 1

noncomputable abbrev qz105 := (Complex.im qz388)

noncomputable abbrev qz389 := (@instHAdd Real Real.instAdd)

noncomputable def ep360 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104) (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 qz101 qz101) (@HMul.hMul Real Real Real qz0 qz105 qz105)) Bool.false 58221189 40000 0 1

noncomputable def ep361 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz101 qz101) (@HMul.hMul Real Real Real qz0 qz105 qz105) 81 16 0 1 58018689 40000

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 9000 4000 0 1 9000 4000 0 1

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 152340 4000 0 1 152340 4000 0 1

noncomputable def ep364 := @Enclosure.Complex.IsNear.im_isNear qz104 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable abbrev qz106 := (ep357 (@ep358 1 (BSN.pow_one_c qz362) qz384))

noncomputable abbrev qz107 := (ep364 (@ep358 1 (BSN.pow_one_c qz362) qz384))

noncomputable def ep365 := @ep361 0 1 931539024 58221189 40000 0 1 (@ep362 81 16 0 1 qz106 qz106 rfl) (@ep363 58018689 40000 0 1 qz107 qz107 rfl)

noncomputable def ep366 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104) 58221189 40000 0 1 184424 184425 268435456 (ep360 (Enclosure.Complex.normSq_eq_mul_add_mul qz104) (ep365 rfl rfl)) rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.of_eq (Complex.re qz100) (@HMul.hMul Real Real Real qz0 qz101 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104))) Bool.false 3319641 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz104) (@ep356 3319641 2147483648 9 2147483648 qz106 (@ep359 536870912 (ep366 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep368 := @Enclosure.Real.IsNear.of_eq (Complex.im qz100) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz105) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104))) Bool.true 2809522833 107374182400 7617 107374182400 (Enclosure.Complex.inv_im_eq_mul qz104)

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz105) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) 152340 4000 0 1 368849 536870912 1

noncomputable def ep370 := @ep369 536870912 2809522833 107374182400 7617 107374182400 (@Enclosure.Real.IsNear.neg qz105 Bool.false 152340 4000 0 1 qz107) (@ep359 536870912 (ep366 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99 0 1 0 1 2809522833 107374182400 7617 107374182400 0

noncomputable def ep372 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep351 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz387)

noncomputable def ep373 := @Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617 107374182400

noncomputable abbrev qz108 := (@ep354 107374182400 (BSN.zpow_one_sub_two_mul qz362 1 1 rfl rfl) (@ep355 107374182400 ep367 (ep368 ep370)))

noncomputable def ep374 := @ep349 1 1106547 1106547 8589934592 3 8589934592 (@ep350 8589934592 3 8589934592 ep352 (ep353 qz108) rfl) (@ep371 1 0 1 ep372 (ep373 qz108) rfl) rfl

noncomputable def ep375 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98) 936507611 429496729600 2539 429496729600 0 1 0

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99 1 12 0 1 2809522833 107374182400 7617 107374182400 936507611

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98 0 1 0 1 3319641 2147483648 9 2147483648 0

noncomputable def ep378 := @ep375 1 936507611 936507611 429496729600 2539 429496729600 (@ep376 429496729600 2539 429496729600 ep352 (ep373 qz108) rfl) (@ep377 1 0 1 ep372 (ep353 qz108) rfl) rfl

noncomputable abbrev qz109 := (@Enclosure.Complex.IsNear.mk qz278 qz278 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz290 qz290)

noncomputable def ep379 := @ep346 429496729600 (@ep347 0 1 0 1 (BSN.stirling_sum_base qz76) qz109) (ep348 (ep374 rfl) (ep378 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep380 := @ep301 18599386236055397831 180143985094819840 425849756162239030403 ep288 (ep343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep344 Bool.true 936507611 429496729600 2539 429496729600 (BSN.stirling_sum_succ qz76 0 1 rfl) (ep379 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 16393552971010259 2251799813685248 781250001249 124900000000000000 Bool.false 873197629638051 281474976710656

noncomputable abbrev qz110 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz363 qz385))

noncomputable def ep382 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz110) Bool.false 16393552971010259 2251799813685248 781250001249 124900000000000000 Bool.false 873197629638051 281474976710656 15625000001249 1249000000000000000

noncomputable def ep383 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz110 Bool.false 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000 Bool.false

noncomputable def ep384 := nat_lit 147659998103040580094241619836928

noncomputable def ep385 := nat_lit 983133129864681714399339085824

noncomputable abbrev qz111 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz363 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz111) Bool.false 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000

noncomputable def ep387 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz111 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz390 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz86))

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq qz111 qz390 Bool.false 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000

noncomputable def ep389 := nat_lit 404450377909545333017942743071634904783995666669178880000000000000

noncomputable def ep390 := nat_lit 4078423902544044669261707384808128600453312961048576000000000000

noncomputable def ep391 := nat_lit 1515329126926870048685187821818510608841381539840000000000000

noncomputable def ep392 := BSN.log_dyadic_bound 6824475600 39592475600 4 3 ep389 524288 159872 ep390 ep391 182563 46416951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6824475600) (BSN.artanhQ 39592475600) 0 3 ep390 ep389 ep391 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep393 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 23208475600 16000000)) 1 2 0 1 16392389034873043 2251799813685248 781250001249 124900000000000000 16392389034873043 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 23208475600 16000000 16392389034873043 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23208475600) qz380)) Bool.false 137509325797048287494144 18889465931478580854784 1000000001598720 159872000000000000000 16392389034873043 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 23208475600 16000000 10 46416951200 32768000000 182563 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep392 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep394 := BSN.arctan_dyadic_bound_f 1000 152340 1 0 524288 159872 0 1 1 0 1 1 3441 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 152340)

noncomputable def ep395 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz391 qz392)) 884279719003555 562949953421312 1 2000000000000000 3441 524288 1 159872 461680134527213109248 880584973387171 562949953421312 15625000001249 2498000000000000000 qz90 (ep394 rfl) rfl rfl

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz273 qz363 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz393 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz86)

noncomputable def ep396 := @ep387 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000 Bool.false 16392389034873043 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 880584973387171 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz109) (ep388 (@congrArg Complex Complex qz112 qz393 Complex.log (BSN.w_shift_mk qz16 Bool.false 76170 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz390 Bool.false 16392389034873043 4503599627370496 781250001249 249800000000000000 Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz390) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 23208475600 16000000))) Bool.false 16392389034873043 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 1000 152340 4000 23208475600 16000000 rfl rfl rfl) (ep393 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz390) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz391)) Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 1000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz391)) (@HSub.hSub Real Real Real qz364 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz391 qz392))) Bool.false 880584973387171 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 152340 1000 rfl rfl) ep395)))) rfl rfl

noncomputable abbrev qz394 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz86))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz110 qz394 Bool.false 16394716907147475 4503599627370496 781250001249 249800000000000000 Bool.false 865810285888931 562949953421312 15625000001249 2498000000000000000

noncomputable def ep398 := nat_lit 405923617089258979443600241174590665952629818400378880000000000000

noncomputable def ep399 := nat_lit 4117565499606241841277565156322818940650879179288576000000000000

noncomputable def ep400 := nat_lit 1547585798464563283482169137918359082337343139840000000000000

noncomputable def ep401 := BSN.log_dyadic_bound 6848475600 39616475600 4 3 ep398 524288 159872 ep399 ep400 183105 46464951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6848475600) (BSN.artanhQ 39616475600) 0 3 ep399 ep398 ep400 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep402 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 23232475600 16000000)) 1 2 0 1 16394716907147475 2251799813685248 781250001249 124900000000000000 16394716907147475 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 23232475600 16000000 16394716907147475 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23232475600) qz380)) Bool.false 137528853405032565964800 18889465931478580854784 1000000001598720 159872000000000000000 16394716907147475 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 23232475600 16000000 10 46464951200 32768000000 183105 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep401 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep403 := BSN.arctan_dyadic_bound_f 5000 152340 1 0 524288 159872 0 1 1 0 1 1 17201 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz395 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep404 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz395 qz392)) 884279719003555 562949953421312 1 2000000000000000 17201 524288 1 159872 453933943168135856128 865810285888931 562949953421312 15625000001249 2498000000000000000 qz90 (ep403 rfl) rfl rfl

noncomputable abbrev qz113 := (@HAdd.hAdd Complex Complex Complex qz273 qz363 qz385)

noncomputable abbrev qz396 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz86)

noncomputable def ep405 := @ep383 16394716907147475 4503599627370496 781250001249 249800000000000000 Bool.false 865810285888931 562949953421312 15625000001249 2498000000000000000 Bool.false ep384 16393552971010259 2251799813685248 781250001249 124900000000000000 Bool.false ep385 873197629638051 281474976710656 15625000001249 1249000000000000000 (ep386 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep396 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep397 (@congrArg Complex Complex qz113 qz396 Complex.log (BSN.w_shift_mk qz16 Bool.false 76170 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz394 Bool.false 16394716907147475 4503599627370496 781250001249 249800000000000000 Bool.false 865810285888931 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz394) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 23232475600 16000000))) Bool.false 16394716907147475 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 5000 152340 4000 23232475600 16000000 rfl rfl rfl) (ep402 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz394) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz395)) Bool.false 865810285888931 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 5000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz395)) (@HSub.hSub Real Real Real qz364 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz395 qz392))) Bool.false 865810285888931 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 152340 5000 rfl rfl) ep404)))) rfl rfl

noncomputable def ep406 := @ep294 ep288 Bool.false 16393552971010259 2251799813685248 781250001249 124900000000000000 Bool.false 873197629638051 281474976710656 15625000001249 1249000000000000000 Bool.true ep295 26938190803813007399 450359962737049600 2077179859043479342447 ep292 Bool.false ep296 18040539753087045191 180143985094819840 466809756165513208963 ep288 (@ep297 450359962737049600 2025979858961624878447 ep292 Bool.false 18599386236055397831 180143985094819840 425849756162239030403 ep288 (BSN.logGammaStirling_unfold 1 qz76) (ep380 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep381 15625000001249 1249000000000000000 (BSN.log_sum_c_eq qz16 2) (ep382 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz114 := (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real))

noncomputable def ep407 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Real.log Real.pi) 76170 2000 0 1 75021 65536 1 131072 571434957 13107200 7617 26214400 (@Enclosure.Real.IsNear.of_eq qz114 (Enclosure.sfrac Bool.false 76170 2000) Bool.false 76170 2000 0 1 (BSN.t_half_eq qz16 Bool.false 76170 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 76170 2000)) EMRow20.d5 rfl

noncomputable def ep408 := @ep290 7617 26214400 ep291 50933987531736565603 900719925474099200 1418173056165513208963 ep288 (@ep293 466809756165513208963 ep288 (ep406 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep407 rfl rfl

noncomputable def ep409 := nat_lit 32545203444316372922907570641384943032050113043371499677817907164593798734080

noncomputable def ep410 := nat_lit 65293073331563102297057780531986707634822512428156002774573556139788820736

noncomputable def ep411 := nat_lit 85131724997339398346753162892289729462055821522041675151697590149709814784256

noncomputable def ep412 := BSN.sin_dyadic_bound_f 1686003178 1073741824 3 2 524288 160029 ep409 ep57 ep410 ep411 ep60 ep410 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686003178) qz283 0 2 ep409 ep57 ep410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686003178) qz284 0 2 ep411 ep60 ep410 rfl rfl rfl rfl) rfl rfl

noncomputable def ep413 := @ep287 131072 Bool.false 524287 524288 1 79936 (@ep289 14823741 262144 57 131072 ep408 rfl) (Enclosure.sfrac_false_div 14823741 262144) (BSN.cos_reduce3 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59320963182903219453952) qz298) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 14823741 262144 226375608064910080 72057594037927936 8 59320963182903219453952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 59320963182903219453952 37778931862957161709568 1686003178 1073741824 160029 159872 (ep412 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep414 := nat_lit 31871967992659317253734400

noncomputable abbrev qz115 := qz274

noncomputable abbrev qz116 := qz275

noncomputable abbrev qz528 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable abbrev qz397 := (@HPow.hPow Complex Complex Complex qz514 qz528 qz515)

noncomputable abbrev qz117 := qz397

noncomputable abbrev qz398 := qz528

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz369 qz398 (@HSub.hSub Complex Complex Complex qz361 qz272 (1 : Complex))) qz368)

noncomputable abbrev qz119 := (@instHSub Nat instSubNat)

noncomputable abbrev qz399 := qz527

noncomputable abbrev qz120 := qz399

noncomputable abbrev qz121 := qz398

noncomputable def ep415 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (@HMul.hMul Complex Complex Complex qz66 qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) Bool.false 41552656888756209273563 76553966355466734796800 ep284

noncomputable def ep416 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (@HMul.hMul Complex Complex Complex qz66 qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) Bool.false 79321238485 137438953472 531209968751 85830626443264

noncomputable def ep417 := nat_lit 5710953676771744926300320076660736

noncomputable def ep418 := nat_lit 296900172904291388774309781569536

noncomputable def ep419 := @ep416 Bool.false 33340950115 274877906944 2124722562679 343322505773056 Bool.true 2629543781825473910437 76553966355466734796800 57687736741083631801309 ep285 Bool.true 8205394989849859025081 76553966355466734796800 3859563050934394571141 ep414 Bool.false ep417 41552656888756209273563 76553966355466734796800 ep284 ep285 Bool.false ep418 1080116536847677302919 76553966355466734796800

noncomputable def ep420 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (BSN.headSumC qz5 20) Bool.false 79321238485 137438953472 531209968751 85830626443264 Bool.false 33340950115 274877906944 2124722562679

noncomputable abbrev qz122 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz275)

noncomputable def ep421 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz122) Bool.false 79321238485 137438953472 531209968751 85830626443264 Bool.false 33340950115 274877906944 2124722562679 343322505773056

noncomputable def ep422 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz122 Bool.false 22504382419 34359738368 1024258768301 171661252886528 Bool.true 3247536481 34359738368 1024003182933 171661252886528 Bool.true

noncomputable abbrev qz123 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz123) Bool.false 22504382419 34359738368 1024258768301 171661252886528 Bool.true 3247536481 34359738368 1024003182933 171661252886528

noncomputable def ep424 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz123 Bool.false 117229919227 274877906944 1969542858071 343322505773056 Bool.true 10070875623 274877906944 1969505672843 343322505773056 Bool.false

noncomputable abbrev qz124 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz40 qz124) Bool.false 117229919227 274877906944 1969542858071 343322505773056 Bool.true 10070875623 274877906944 1969505672843 343322505773056

noncomputable def ep426 := @Enclosure.Complex.IsNear.addLitP qz40 qz124 Bool.false 155238507281 274877906944 1888557586917 343322505773056 Bool.false 44700829083 274877906944 1888355748517 343322505773056 Bool.true

noncomputable abbrev qz400 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz400))

noncomputable abbrev qz401 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz280 qz401)

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.true 19004294027 137438953472 40492635577 171661252886528 Bool.true 27385852353 137438953472 40574962163 171661252886528 (BSN.cpow_neg_s_mk qz16 76170 1000 17 qz17 rfl)

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep428 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz400) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz400) (Real.sqrt qz402) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz402) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep429 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 79936 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep430 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz401 76170 1000 0 1 3189913004350711 1125899906842624 3906250001249 312250000000000000 24297567354139365687 112589990684262400 29753906259513633 31225000000000000000 qz21 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 26758929747600409100288 9444732965739290427392 1000000000319744 79936000000000000000 3189913004350711 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep431 := nat_lit 180034512186463519433114692227394576

noncomputable def ep432 := BSN.sin_dyadic_bound_f 651386782 1073741824 2 1 524288 160029 ep431 ep75 ep431 ep431 ep76 ep431 298906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 651386782) qz283 0 1 ep431 ep75 ep431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 651386782) qz284 0 1 ep431 ep76 ep431 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28286091) qz519)

noncomputable def ep433 := @Enclosure.Real.IsNear.cos_image qz126 qz403 Bool.false 28286091 131072 501 524288 Bool.true 298906 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 24297567354139365687 112589990684262400 29753906259513633 31225000000000000000 28286091 131072 501 524288 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 28286091 131072) (BSN.cos_reduce1 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11459317456880619487232) qz332) 226375608064910080 72057594037927936 Bool.false 298906 524288 34 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 28286091 131072 226375608064910080 72057594037927936 34 11459317456880619487232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298906 524288 11459317456880619487232 18889465931478580854784 651386782 1073741824 160029 159872 (ep432 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep434 := BSN.cos_dyadic_bound_f 651386782 1073741824 2 1 524288 160029 ep431 ep79 ep431 ep431 ep80 ep431 430734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 651386782) qz287 0 1 ep431 ep79 ep431 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 651386782) qz288 0 1 ep431 ep80 ep431 rfl rfl rfl rfl) rfl rfl

noncomputable def ep435 := @Enclosure.Real.IsNear.sin_image qz126 qz403 Bool.false 28286091 131072 501 524288 Bool.false 430734 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 24297567354139365687 112589990684262400 29753906259513633 31225000000000000000 28286091 131072 501 524288 (ep430 rfl) rfl) (Enclosure.sfrac_false_div 28286091 131072) (BSN.sin_reduce1 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11459317456880619487232) qz332) 226375608064910080 72057594037927936 Bool.false 430734 524288 34 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 28286091 131072 226375608064910080 72057594037927936 34 11459317456880619487232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 430734 524288 11459317456880619487232 18889465931478580854784 651386782 1073741824 160029 159872 (ep434 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz404 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep428 rfl rfl) rfl)

noncomputable def ep436 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.true 19004294027 137438953472 40492635577 171661252886528 Bool.true 27385852353 137438953472 40574962163 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz125 (Real.cos qz126) 127159 524288 1 524288 149453 262144 633941 654835712 19004294027 137438953472 40492635577 171661252886528 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.true 298906 524288 40572224 41909485568 149453 262144 633941 654835712 (ep433 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 127159 524288 1 524288 215367 262144 633941 654835712 27385852353 137438953472 40574962163 171661252886528 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 215367 262144 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 430734 524288 40572224 41909485568 215367 262144 633941 654835712 (ep435 rfl rfl) rfl)) rfl)

noncomputable def ep437 := @ep426 19004294027 137438953472 40492635577 171661252886528 Bool.true 27385852353 137438953472 40574962163 171661252886528 Bool.false 16111957414165971206144 117229919227 274877906944 1969542858071 343322505773056 Bool.true 1384130606171796013056 10070875623 274877906944 1969505672843 343322505773056 EMRow20.d7 (ep427 ep436) rfl rfl

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz405))

noncomputable abbrev qz406 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz280 qz406)

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 62805140125 274877906944 78974678531 343322505773056 Bool.true 15909416225 274877906944 78500693023 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 18 qz17 rfl)

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz18)

noncomputable def ep439 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz405) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz405) (Real.sqrt qz407) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz407) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep440 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 79936 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep441 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz406 76170 1000 0 1 3254268794313975 1125899906842624 3906250001249 312250000000000000 991510616251581903 4503599627370496 29753906259513633 31225000000000000000 qz21 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz407) Bool.false 27298785242132565196800 9444732965739290427392 1000000000319744 79936000000000000000 3254268794313975 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep440 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep442 := nat_lit 5035947934806690079297806821272336

noncomputable def ep443 := BSN.cos_dyadic_bound_f 266391466 1073741824 2 1 524288 160029 ep442 ep79 ep442 ep442 ep80 ep442 508235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 266391466) qz287 0 1 ep442 ep79 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 266391466) qz288 0 1 ep442 ep80 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115427027) qz19)

noncomputable def ep444 := @Enclosure.Real.IsNear.cos_image qz128 qz408 Bool.false 115427027 524288 501 524288 Bool.false 508235 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 991510616251581903 4503599627370496 29753906259513633 31225000000000000000 115427027 524288 501 524288 (ep441 rfl) rfl) (Enclosure.sfrac_false_div 115427027 524288) (BSN.cos_reduce0 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18745632982913142226944) qz22) 226375608064910080 72057594037927936 Bool.false 508235 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 115427027 524288 226375608064910080 72057594037927936 35 18745632982913142226944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508235 524288 18745632982913142226944 75557863725914323419136 266391466 1073741824 160029 159872 (ep443 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep445 := BSN.sin_dyadic_bound_f 266391466 1073741824 2 1 524288 160029 ep442 ep75 ep442 ep442 ep76 ep442 128743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 266391466) qz283 0 1 ep442 ep75 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 266391466) qz284 0 1 ep442 ep76 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable def ep446 := @Enclosure.Real.IsNear.sin_image qz128 qz408 Bool.false 115427027 524288 501 524288 Bool.false 128743 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 991510616251581903 4503599627370496 29753906259513633 31225000000000000000 115427027 524288 501 524288 (ep441 rfl) rfl) (Enclosure.sfrac_false_div 115427027 524288) (BSN.sin_reduce0 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18745632982913142226944) qz22) 226375608064910080 72057594037927936 Bool.false 128743 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 115427027 524288 226375608064910080 72057594037927936 35 18745632982913142226944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 128743 524288 18745632982913142226944 75557863725914323419136 266391466 1073741824 160029 159872 (ep445 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz409 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep439 rfl rfl) rfl)

noncomputable def ep447 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 62805140125 274877906944 78974678531 343322505773056 Bool.true 15909416225 274877906944 78500693023 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 123575 524288 1 524288 508235 524288 633941 654835712 62805140125 274877906944 78974678531 343322505773056 qz409 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 508235 524288 40572224 41909485568 508235 524288 633941 654835712 (ep444 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 123575 524288 1 524288 128743 524288 633941 654835712 15909416225 274877906944 78500693023 343322505773056 qz409 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.false 128743 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.false 128743 524288 40572224 41909485568 128743 524288 633941 654835712 (ep446 rfl rfl) rfl)) rfl)

noncomputable def ep448 := @ep424 62805140125 274877906944 78974678531 343322505773056 Bool.true 15909416225 274877906944 78500693023 343322505773056 Bool.false 49487660291216572940288 22504382419 34359738368 1024258768301 171661252886528 Bool.true 7141408244972505792512 3247536481 34359738368 1024003182933 171661252886528 (ep425 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep437 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep438 ep447) rfl rfl

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz410))

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz280 qz411)

noncomputable def ep449 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.true 10696291191 137438953472 38161169201 171661252886528 Bool.false 59321241963 274877906944 76716196813 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 19 qz17 rfl)

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18)

noncomputable def ep450 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz410) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz410) (Real.sqrt qz412) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz412) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep451 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 79936 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz411 76170 1000 0 1 3315141365800183 1125899906842624 3906250001249 312250000000000000 25251431783299993911 112589990684262400 29753906259513633 31225000000000000000 qz21 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 27809421382282341515264 9444732965739290427392 1000000000319744 79936000000000000000 3315141365800183 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep451 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep453 := nat_lit 6686399791894222901199223856036496166549601798550727193399698201300172800000

noncomputable def ep454 := nat_lit 8941386335349207062010101278024665478339503057985940628169562521600000000

noncomputable def ep455 := nat_lit 20041316603011970289473651365553439168692126389536209698942755478857318400000

noncomputable def ep456 := BSN.cos_dyadic_bound_f 1314999560 1073741824 3 2 524288 160029 ep453 ep64 ep454 ep455 ep66 ep454 177858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1314999560) qz287 0 2 ep453 ep64 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1314999560) qz288 0 2 ep455 ep66 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58793071) qz29)

noncomputable def ep457 := @Enclosure.Real.IsNear.cos_image qz130 qz413 Bool.false 58793071 262144 125 131072 Bool.true 177858 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 25251431783299993911 112589990684262400 29753906259513633 31225000000000000000 58793071 262144 125 131072 (ep452 rfl) rfl) (Enclosure.sfrac_false_div 58793071 262144) (BSN.cos_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46267433841521770627072) qz298) 226375608064910080 72057594037927936 Bool.false 177858 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 58793071 262144 226375608064910080 72057594037927936 35 46267433841521770627072 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 177858 524288 46267433841521770627072 37778931862957161709568 1314999560 1073741824 160029 159872 (ep456 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep458 := nat_lit 12028366516341321856508994859843273367406611634944920195616921112323031040000

noncomputable def ep459 := nat_lit 31488388155398610907994589230853676027671433181809480417979661716763443200000

noncomputable def ep460 := BSN.sin_dyadic_bound_f 1314999560 1073741824 3 2 524288 160029 ep458 ep57 ep454 ep459 ep60 ep454 493197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1314999560) qz283 0 2 ep458 ep57 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1314999560) qz284 0 2 ep459 ep60 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep461 := @Enclosure.Real.IsNear.sin_image qz130 qz413 Bool.false 58793071 262144 125 131072 Bool.true 493197 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 25251431783299993911 112589990684262400 29753906259513633 31225000000000000000 58793071 262144 125 131072 (ep452 rfl) rfl) (Enclosure.sfrac_false_div 58793071 262144) (BSN.sin_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46267433841521770627072) qz298) 226375608064910080 72057594037927936 Bool.false 493197 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 58793071 262144 226375608064910080 72057594037927936 35 46267433841521770627072 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493197 524288 46267433841521770627072 37778931862957161709568 1314999560 1073741824 160029 159872 (ep460 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep450 rfl rfl) rfl)

noncomputable def ep462 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.true 10696291191 137438953472 38161169201 171661252886528 Bool.false 59321241963 274877906944 76716196813 343322505773056 (@Enclosure.Real.IsNear.mulLit_ft qz129 (Real.cos qz130) 120279 524288 1 524288 88929 262144 158173 163708928 10696291191 137438953472 38161169201 171661252886528 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.true 177858 524288 10123072 10477371392 88929 262144 158173 163708928 (ep457 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 120279 524288 1 524288 493197 524288 158173 163708928 59321241963 274877906944 76716196813 343322505773056 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 493197 524288 158173 163708928 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 493197 524288 10123072 10477371392 493197 524288 158173 163708928 (ep461 rfl rfl) rfl)) rfl)

noncomputable def ep463 := @ep422 10696291191 137438953472 38161169201 171661252886528 Bool.false 59321241963 274877906944 76716196813 343322505773056 Bool.false 2725457001370332692480 79321238485 137438953472 531209968751 85830626443264 Bool.false 1145586322891939512320 33340950115 274877906944 2124722562679 343322505773056 (ep423 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep448 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep449 ep462) rfl rfl

noncomputable def ep464 := @Enclosure.Complex.IsNear.mul qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.true 2629543781825473910437 76553966355466734796800 57687736741083631801309 ep285 Bool.true

noncomputable abbrev qz131 := (Complex.re qz397)

noncomputable abbrev qz132 := (Complex.im qz397)

noncomputable def ep465 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 69732418455797942663 1531079327109334695936 207876310665039221569

noncomputable def ep466 := nat_lit 1912318079559559035224064

noncomputable def ep467 := nat_lit 159359839963296586268672000

noncomputable def ep468 := nat_lit 1342013374693960598694742649638576763961344

noncomputable def ep469 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 25020410935 274877906944 74587269905 343322505773056 13935106549

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz415))

noncomputable abbrev qz416 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz518 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz134 := (Real.cos qz416)

noncomputable abbrev qz135 := (Real.sin qz416)

noncomputable abbrev qz417 := (@Neg.neg Real Real.instNeg qz135)

noncomputable def ep470 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz417)) Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (BSN.cpow_neg_s_mk qz16 76170 1000 20 qz17 rfl)

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz18)

noncomputable def ep471 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz415) 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz415) (Real.sqrt qz418) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz418) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep472 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 79936 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz419 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz136 := qz419

noncomputable abbrev qz420 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz18))

noncomputable def ep473 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz136 76170 1000 0 1 3372891496062199 1125899906842624 3906250001249 312250000000000000 25691314525505769783 112589990684262400 29753906259513633 31225000000000000000 qz21 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 28293864586999331028992 9444732965739290427392 1000000000319744 79936000000000000000 3372891496062199 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep472 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep474 := nat_lit 41063814781357998357845792688200625

noncomputable def ep475 := BSN.sin_dyadic_bound_f 450157845 1073741824 2 1 524288 160029 ep474 ep75 ep474 ep474 ep76 ep474 213421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 450157845) qz283 0 1 ep474 ep75 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 450157845) qz284 0 1 ep474 ep76 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz137 := qz416

noncomputable abbrev qz421 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119634505) qz19)

noncomputable def ep476 := @Enclosure.Real.IsNear.cos_image qz137 qz421 Bool.false 119634505 524288 501 524288 Bool.true 213421 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 25691314525505769783 112589990684262400 29753906259513633 31225000000000000000 119634505 524288 501 524288 (ep473 rfl) rfl) (Enclosure.sfrac_false_div 119634505 524288) (BSN.cos_reduce1 qz421 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31677042272261174722560) qz22) 226375608064910080 72057594037927936 Bool.false 213421 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 119634505 524288 226375608064910080 72057594037927936 36 31677042272261174722560 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213421 524288 31677042272261174722560 75557863725914323419136 450157845 1073741824 160029 159872 (ep475 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep477 := BSN.cos_dyadic_bound_f 450157845 1073741824 2 1 524288 160029 ep474 ep79 ep474 ep474 ep80 ep474 478883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 450157845) qz287 0 1 ep474 ep79 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 450157845) qz288 0 1 ep474 ep80 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable def ep478 := @Enclosure.Real.IsNear.sin_image qz137 qz421 Bool.false 119634505 524288 501 524288 Bool.false 478883 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 25691314525505769783 112589990684262400 29753906259513633 31225000000000000000 119634505 524288 501 524288 (ep473 rfl) rfl) (Enclosure.sfrac_false_div 119634505 524288) (BSN.sin_reduce1 qz421 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31677042272261174722560) qz22) 226375608064910080 72057594037927936 Bool.false 478883 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 119634505 524288 226375608064910080 72057594037927936 36 31677042272261174722560 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478883 524288 31677042272261174722560 75557863725914323419136 450157845 1073741824 160029 159872 (ep477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz422 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep471 rfl rfl) rfl)

noncomputable def ep479 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz417) Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (@Enclosure.Real.IsNear.mulLit_ft qz133 qz134 117235 524288 1 524288 213421 524288 633941 654835712 25020410935 274877906944 74587269905 343322505773056 qz422 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 213421 524288 40572224 41909485568 213421 524288 633941 654835712 (ep476 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz133 qz417 117235 524288 1 524288 478883 524288 633941 654835712 56141848505 274877906944 74918831943 343322505773056 qz422 (@Enclosure.Real.IsNear.neg qz135 Bool.false 478883 524288 633941 654835712 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 478883 524288 40572224 41909485568 478883 524288 633941 654835712 (ep478 rfl rfl) rfl)) rfl)

noncomputable def ep480 := @ep469 27850170720 0 1 69732418455797942663 1531079327109334695936 207876310665039221569 ep466 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (ep470 ep479))

noncomputable def ep481 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 13935106549 27850170720 0 1 Bool.false

noncomputable def ep482 := @Enclosure.Complex.IsNear.addLitP qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) Bool.false 57821189 116042378 0 1 Bool.true 15234000

noncomputable def ep483 := @ep482 58021189 0 1 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1 Bool.false 27870213098 13935106549 27850170720 0 1 Bool.false 25443798871 25443798871 464169512000 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz369 qz398 (@HSub.hSub Complex Complex Complex qz361 qz272 (1 : Complex)))

noncomputable def ep484 := @Enclosure.Complex.IsNear.addLitP qz138 qz93 Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1

noncomputable def ep485 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 40000000 23208475600) (Enclosure.sfrac Bool.true 6093600000 23208475600)) Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1

noncomputable def ep486 := @ep484 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 23128475600 57821189 116042378 0 1 Bool.true 6093600000 15234000 58021189 0 1 (ep485 (BSN.N_div_s_sub_one_mk qz16 76170 1000 20 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 23208475600) (Enclosure.sfrac Bool.true 6093600000 23208475600) Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 23208475600) (Enclosure.Real.IsNear.const Bool.true 6093600000 23208475600))) qz94 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz423 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz527 qz528 1))

noncomputable abbrev qz140 := qz423

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 480 0 1

noncomputable def ep488 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep489 := @ep488 0 1 0 1 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1 Bool.false 1 1 480 0 1 Bool.false 2539 2539 8000 0

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep491 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1

noncomputable abbrev qz141 := (Complex.re qz423)

noncomputable abbrev qz142 := (Complex.im qz423)

noncomputable def ep492 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 480 0 1 0 1 0

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 20 0 1 1

noncomputable def ep494 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep495 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep496 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow20.d8 rfl) qz387

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep498 := ep497 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz88 qz16) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 76170 1000 qz17) (@Enclosure.Complex.IsNear.mk qz88 qz16 Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 qz379 qz21))

noncomputable def ep499 := @ep495 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep500 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 76170 1000 0 1 0 1 0

noncomputable def ep501 := @ep500 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep502 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 2539 400 0 1 0 1 0 1 2539

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 76170 1000 0 1 2539 400 0

noncomputable def ep504 := @ep503 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep506 := @ep505 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep507 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 (@ep494 1 24 0 1 (ep499 rfl) (ep501 rfl) rfl rfl) (@ep502 2539 400 0 1 (ep504 rfl) (ep506 rfl) rfl rfl)

noncomputable def ep508 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 ep507

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.re_isNear qz423 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz423 (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz278) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow20.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz278 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz290)))

noncomputable def ep509 := @ep493 480 0 1 ep508 qz143

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 2539 400 0 1 0 1 0 1 0

noncomputable def ep511 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 ep507

noncomputable abbrev qz144 := (@Enclosure.Complex.IsNear.im_isNear qz423 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz423 (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz278) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow20.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz278 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz290)))

noncomputable def ep512 := @ep510 1 0 1 ep511 qz144

noncomputable def ep513 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 2539 8000 0

noncomputable def ep514 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep515 := @ep514 1 0 1 ep508 qz144

noncomputable def ep516 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 2539 400 0 1 1 20 0 1 2539

noncomputable def ep517 := @ep516 8000 0 1 ep511 qz143

noncomputable def ep518 := @ep489 1 (@ep490 0 1 0 1 (BSN.bern_sum_base qz5 20) qz109) (ep491 (@ep492 1 1 1 480 0 1 (ep509 rfl) (ep512 rfl) rfl rfl) (@ep513 1 2539 2539 8000 0 1 (ep515 rfl) (ep517 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep519 := ep483 (ep486 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep487 Bool.false 2539 8000 0 1 (BSN.bern_sum_succ qz5 20 0 1 1 rfl rfl) (ep518 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 56141848505 274877906944 74918831943 343322505773056 25443798871

noncomputable def ep521 := @ep520 464169512000 0 1 285692380321474407571 25517988785155578265600 1906219691607942136353 ep467 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (ep470 ep479))

noncomputable def ep522 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 13935106549 27850170720 0 1 Bool.false

noncomputable def ep523 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 127322860699981810877 25517988785155578265600 379556698759962255451

noncomputable def ep524 := nat_lit 3187196799265931725373440

noncomputable def ep525 := nat_lit 4187703546575209451138635247762232177590272

noncomputable def ep526 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 25020410935 274877906944 74587269905 343322505773056 25443798871

noncomputable def ep527 := @ep526 464169512000 0 1 127322860699981810877 25517988785155578265600 379556698759962255451 ep414 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (ep470 ep479))

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 56141848505 274877906944 74918831943 343322505773056 13935106549

noncomputable def ep529 := @ep528 27850170720 0 1 156468528154998271849 1531079327109334695936 348000635217443231569 ep524 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.true 25020410935 274877906944 74587269905 343322505773056 Bool.true 56141848505 274877906944 74918831943 343322505773056 (ep470 ep479))

noncomputable abbrev qz424 := (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep530 := @ep464 8205394989849859025081 76553966355466734796800 3859563050934394571141 ep414 (@ep465 ep466 285692380321474407571 25517988785155578265600 1906219691607942136353 ep467 ep468 2629543781825473910437 76553966355466734796800 57687736741083631801309 ep285 (ep480 (@ep481 25443798871 464169512000 0 1 qz424) rfl) (ep521 (@ep522 25443798871 464169512000 0 1 qz424) rfl) rfl rfl) (@ep523 ep414 156468528154998271849 1531079327109334695936 348000635217443231569 ep524 ep525 8205394989849859025081 76553966355466734796800 3859563050934394571141 ep414 (ep527 (@ep522 25443798871 464169512000 0 1 qz424) rfl) (ep529 (@ep481 25443798871 464169512000 0 1 qz424) rfl) rfl rfl)

noncomputable def ep531 := @ep419 201105850061754563100741 ep414 (@ep420 343322505773056 (BSN.head_sum_c_eq qz5 20) (ep421 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep463 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep530 rfl rfl rfl

noncomputable def ep532 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 20) Bool.false 41552656888756209273563 76553966355466734796800 ep284 ep285 Bool.false 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 (@ep415 ep285 Bool.false 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep531 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep533 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20)) 305 524288 73241

noncomputable def ep534 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) Bool.true 305 524288 4687424

noncomputable def ep535 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) qz365 Bool.false 14823741 262144 57

noncomputable def ep536 := nat_lit 18109687723878679669302898258783629110087761696285569155576425560836460994816

noncomputable def ep537 := nat_lit 54198477024972912803314579215286913914993640064000395461180129570229805342976

noncomputable def ep538 := BSN.cos_dyadic_bound_f 1686003178 1073741824 3 2 524288 160029 ep536 ep64 ep410 ep537 ep66 ep410 305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686003178) qz287 0 2 ep536 ep64 ep410 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686003178) qz288 0 2 ep537 ep66 ep410 rfl rfl rfl rfl) rfl rfl

noncomputable def ep539 := @ep535 131072 Bool.true 305 524288 1 79936 (@ep289 14823741 262144 57 131072 ep408 rfl) (Enclosure.sfrac_false_div 14823741 262144) (BSN.sin_reduce3 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59320963182903219453952) qz298) 226375608064910080 72057594037927936 Bool.false 305 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 14823741 262144 226375608064910080 72057594037927936 8 59320963182903219453952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 305 524288 59320963182903219453952 37778931862957161709568 1686003178 1073741824 160029 159872 (ep538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep540 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 20) Bool.false 41552656888756209273563 76553966355466734796800 ep284 ep285 Bool.false 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 (@ep415 ep285 Bool.false 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep531 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow20.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz16) Bool.false ep268 ep269 ep270 ep271 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz16) ep272 Bool.false ep268 ep269 ep270 ep271 (@Eq.refl Real ep272) (@ep273 Bool.false ep268 ep269 ep270 ep271 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) (zetaApproximant qz5 1 20)) (@ep275 ep276 ep277 ep278 65887108747708315478059 ep279 ep280 ep281 ep282 ep268 ep269 ep270 ep271 (@ep283 163708928 41552656888756209273563 76553966355466734796800 ep284 ep285 ep274 ep276 ep277 ep278 (@ep286 10477371392 524287 524288 73241 163708928 (ep413 rfl rfl) rfl) ep532 rfl) (@ep533 163708928 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 65887108747708315478059 ep279 ep280 ep281 (@ep534 10477371392 305 524288 73241 163708928 (ep539 rfl rfl) rfl) ep540 rfl) rfl rfl))

noncomputable abbrev qz544 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 78672 1000)))

noncomputable abbrev qz529 := qz544

noncomputable abbrev qz425 := qz529

noncomputable abbrev qz145 := (BSN.headSumC qz425 9)

noncomputable abbrev qz146 := qz425

noncomputable abbrev qz530 := (@Neg.neg Complex Complex.instNeg qz544)

noncomputable abbrev qz426 := qz530

noncomputable abbrev qz147 := qz426

noncomputable abbrev qz427 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 8) qz147)

noncomputable def ep541 := @Enclosure.Complex.IsNear.of_eq qz145 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 8) qz427) Bool.false 104720946353 274877906944 1158958145907 343322505773056 Bool.true 18526874065 274877906944 1160323068095 343322505773056

noncomputable def ep542 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 8) qz427 Bool.false 5059450155 137438953472 518553275659 171661252886528 Bool.false 930978773 68719476736 259739746421 85830626443264 Bool.false

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 7) qz147)

noncomputable def ep543 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 7) qz428) Bool.false 5059450155 137438953472 518553275659 171661252886528 Bool.false 930978773 68719476736 259739746421 85830626443264

noncomputable def ep544 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 7) qz428 Bool.false 78712824597 274877906944 907089817517 343322505773056 Bool.false 40877676127 137438953472 454441384129 171661252886528 Bool.true

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 6) qz147)

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 6) qz429) Bool.false 78712824597 274877906944 907089817517 343322505773056 Bool.false 40877676127 137438953472 454441384129 171661252886528

noncomputable def ep546 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 6) qz429 Bool.false 181610361535 274877906944 766523263759 343322505773056 Bool.false 126532097015 274877906944 768655371707 343322505773056 Bool.true

noncomputable abbrev qz430 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 5) qz147)

noncomputable def ep547 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 5) qz430) Bool.false 181610361535 274877906944 766523263759 343322505773056 Bool.false 126532097015 274877906944 768655371707 343322505773056

noncomputable def ep548 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 5) qz430 Bool.false 27622395793 68719476736 306409306793 171661252886528 Bool.false 56699694723 68719476736 153698865835 85830626443264 Bool.false

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 4) qz147)

noncomputable def ep549 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 4) qz431) Bool.false 27622395793 68719476736 306409306793 171661252886528 Bool.false 56699694723 68719476736 153698865835 85830626443264

noncomputable def ep550 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 4) qz431 Bool.false 98314624343 137438953472 110246419871 85830626443264 Bool.false 166946553627 137438953472 221431344587 171661252886528 Bool.true

noncomputable abbrev qz148 := qz276

noncomputable def ep551 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz115 qz148 qz147)) Bool.false 98314624343 137438953472 110246419871 85830626443264 Bool.false 166946553627 137438953472 221431344587 171661252886528

noncomputable def ep552 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz115 qz148 qz147) Bool.false 5965968149 8589934592 121497696133 171661252886528 Bool.false 21911924781 34359738368 60902693017 85830626443264 Bool.false

noncomputable abbrev qz149 := qz277

noncomputable def ep553 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz115 qz149 qz147)) Bool.false 5965968149 8589934592 121497696133 171661252886528 Bool.false 21911924781 34359738368 60902693017 85830626443264

noncomputable def ep554 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz115 qz149 qz147) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep555 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz146)

noncomputable abbrev qz545 := (Enclosure.sfrac Bool.false 78672 1000)

noncomputable abbrev qz531 := qz545

noncomputable abbrev qz432 := qz531

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz432 (Real.log qz281))

noncomputable abbrev qz151 := qz432

noncomputable abbrev qz433 := (@Eq.refl Real qz531)

noncomputable abbrev qz152 := qz433

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz115 qz149 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 2623966443 8589934592 121497696133 171661252886528 Bool.false 21911924781 34359738368 60902693017 85830626443264 (BSN.cpow_neg_s_mk qz151 78672 1000 2 qz152 rfl)

noncomputable def ep557 := nat_lit 4743738241151225826305256340073738455365987625474498758200694143620104184801

noncomputable def ep558 := nat_lit 4504004602580614743898884737188217070343889835905979875236420040430052321

noncomputable def ep559 := nat_lit 14222206714248516249427971250746838931957275096751684314851609590779452449761

noncomputable def ep560 := BSN.cos_dyadic_bound_f 1206979387 1073741824 3 2 524288 160029 ep557 ep64 ep558 ep559 ep66 ep558 226492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1206979387) qz287 0 2 ep557 ep64 ep558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1206979387) qz288 0 2 ep559 ep66 ep558 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz153 := (Enclosure.Real.IsNear.const Bool.false 78672 1000)

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14295017) qz29)

noncomputable def ep561 := @Enclosure.Real.IsNear.cos_image qz150 qz434 Bool.false 14295017 262144 517 524288 Bool.true 226492 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 111679821 2048000 4917 4996000 14295017 262144 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz20 78672 1000 0 1 181704 262144 1 79936 111679821 2048000 4917 4996000 qz153 qz286 rfl) rfl) (Enclosure.sfrac_false_div 14295017 262144) (BSN.cos_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42466811883252187398144) qz298) 226375608064910080 72057594037927936 Bool.false 226492 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 14295017 262144 226375608064910080 72057594037927936 8 42466811883252187398144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 226492 524288 42466811883252187398144 37778931862957161709568 1206979387 1073741824 160029 159872 (ep560 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep562 := nat_lit 8535125630390141995554342304342978646002502613985372980861060322483843490785

noncomputable def ep563 := nat_lit 22346608262617622326390298317038067911892664357846414791980965688344608105441

noncomputable def ep564 := BSN.sin_dyadic_bound_f 1206979387 1073741824 3 2 524288 160029 ep562 ep57 ep558 ep563 ep60 ep558 472841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1206979387) qz283 0 2 ep562 ep57 ep558 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1206979387) qz284 0 2 ep563 ep60 ep558 rfl rfl rfl rfl) rfl rfl

noncomputable def ep565 := @Enclosure.Real.IsNear.sin_image qz150 qz434 Bool.false 14295017 262144 517 524288 Bool.true 472841 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 111679821 2048000 4917 4996000 14295017 262144 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz20 78672 1000 0 1 181704 262144 1 79936 111679821 2048000 4917 4996000 qz153 qz286 rfl) rfl) (Enclosure.sfrac_false_div 14295017 262144) (BSN.sin_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42466811883252187398144) qz298) 226375608064910080 72057594037927936 Bool.false 472841 524288 8 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 14295017 262144 226375608064910080 72057594037927936 8 42466811883252187398144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 472841 524288 42466811883252187398144 37778931862957161709568 1206979387 1073741824 160029 159872 (ep564 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep566 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 2623966443 8589934592 121497696133 171661252886528 Bool.false 21911924781 34359738368 60902693017 85830626443264 (@Enclosure.Real.IsNear.mulLit_ft qz14 (Real.cos qz150) 46341 65536 1 262144 56623 131072 653925 654835712 2623966443 8589934592 121497696133 171661252886528 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 226492 524288 41851200 41909485568 56623 131072 653925 654835712 (ep561 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 46341 65536 1 262144 472841 524288 653925 654835712 21911924781 34359738368 60902693017 85830626443264 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 472841 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 472841 524288 41851200 41909485568 472841 524288 653925 654835712 (ep565 rfl rfl) rfl)) rfl)

noncomputable def ep567 := @ep554 2623966443 8589934592 121497696133 171661252886528 Bool.false 21911924781 34359738368 60902693017 85830626443264 Bool.false 5965968149 5965968149 8589934592 121497696133 171661252886528 Bool.false 21911924781 21911924781 34359738368 60902693017 85830626443264 (ep555 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz23)) (ep556 ep566) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz432 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep568 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz115 qz148 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 2859133959 137438953472 98995143609 171661252886528 Bool.false 79298854503 137438953472 99625958553 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 3 qz152 rfl)

noncomputable def ep569 := BSN.sin_dyadic_bound_f 38697877 1073741824 1 0 524288 160029 0 1 1 0 1 1 18891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 38697877) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 38697877) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45314127) qz19)

noncomputable def ep570 := @Enclosure.Real.IsNear.cos_image qz154 qz435 Bool.false 45314127 524288 517 524288 Bool.false 18891 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 708033249 8192000 4917 4996000 45314127 524288 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz26 78672 1000 0 1 287994 262144 1 79936 708033249 8192000 4917 4996000 qz153 qz293 rfl) rfl) (Enclosure.sfrac_false_div 45314127 524288) (BSN.cos_reduce3 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2723121035761936236544) qz22) 226375608064910080 72057594037927936 Bool.false 18891 524288 13 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 45314127 524288 226375608064910080 72057594037927936 13 2723121035761936236544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 18891 524288 2723121035761936236544 75557863725914323419136 38697877 1073741824 160029 159872 (ep569 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep571 := BSN.cos_dyadic_bound_f 38697877 1073741824 1 0 524288 160029 0 1 1 0 1 1 523947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 38697877) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 38697877) qz288 0 0 rfl) rfl rfl

noncomputable def ep572 := @Enclosure.Real.IsNear.sin_image qz154 qz435 Bool.false 45314127 524288 517 524288 Bool.true 523947 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 708033249 8192000 4917 4996000 45314127 524288 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz26 78672 1000 0 1 287994 262144 1 79936 708033249 8192000 4917 4996000 qz153 qz293 rfl) rfl) (Enclosure.sfrac_false_div 45314127 524288) (BSN.sin_reduce3 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2723121035761936236544) qz22) 226375608064910080 72057594037927936 Bool.false 523947 524288 13 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 45314127 524288 226375608064910080 72057594037927936 13 2723121035761936236544 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523947 524288 2723121035761936236544 75557863725914323419136 38697877 1073741824 160029 159872 (ep571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep573 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 2859133959 137438953472 98995143609 171661252886528 Bool.false 79298854503 137438953472 99625958553 171661252886528 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz154) 151349 262144 1 262144 18891 524288 653925 654835712 2859133959 137438953472 98995143609 171661252886528 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 18891 524288 41851200 41909485568 18891 524288 653925 654835712 (ep570 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 151349 262144 1 262144 523947 524288 653925 654835712 79298854503 137438953472 99625958553 171661252886528 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 523947 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 523947 524288 41851200 41909485568 523947 524288 653925 654835712 (ep572 rfl rfl) rfl)) rfl)

noncomputable def ep574 := @ep552 2859133959 137438953472 98995143609 171661252886528 Bool.false 79298854503 137438953472 99625958553 171661252886528 Bool.false 844516192543420973056 98314624343 137438953472 110246419871 85830626443264 Bool.false 5736239904063001460736 166946553627 137438953472 221431344587 171661252886528 (ep553 (BSN.head_sum_c_succ qz146 2 3 rfl rfl) (ep567 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep568 ep573) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz432 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq qz431 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 43069832757 137438953472 85916467051 171661252886528 Bool.true 53547164181 137438953472 85966387083 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 4 qz152 rfl)

noncomputable def ep576 := nat_lit 279849003223948833148767937902424336

noncomputable def ep577 := BSN.sin_dyadic_bound_f 727329062 1073741824 2 1 524288 160029 ep576 ep75 ep576 ep576 ep76 ep576 328598 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 727329062) qz283 0 1 ep576 ep75 ep576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 727329062) qz284 0 1 ep576 ep76 ep576 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14295017) qz519)

noncomputable def ep578 := @Enclosure.Real.IsNear.cos_image qz155 qz436 Bool.false 14295017 131072 517 524288 Bool.true 328598 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 111679821 1024000 4917 4996000 14295017 131072 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz30 78672 1000 0 1 363408 262144 1 79936 111679821 1024000 4917 4996000 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 14295017 131072) (BSN.cos_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12795308182968293392384) qz332) 226375608064910080 72057594037927936 Bool.false 328598 524288 17 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 14295017 131072 226375608064910080 72057594037927936 17 12795308182968293392384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 328598 524288 12795308182968293392384 18889465931478580854784 727329062 1073741824 160029 159872 (ep577 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep579 := BSN.cos_dyadic_bound_f 727329062 1073741824 2 1 524288 160029 ep576 ep79 ep576 ep576 ep80 ep576 408534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 727329062) qz287 0 1 ep576 ep79 ep576 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 727329062) qz288 0 1 ep576 ep80 ep576 rfl rfl rfl rfl) rfl rfl

noncomputable def ep580 := @Enclosure.Real.IsNear.sin_image qz155 qz436 Bool.false 14295017 131072 517 524288 Bool.false 408534 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 111679821 1024000 4917 4996000 14295017 131072 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz30 78672 1000 0 1 363408 262144 1 79936 111679821 1024000 4917 4996000 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 14295017 131072) (BSN.sin_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12795308182968293392384) qz332) 226375608064910080 72057594037927936 Bool.false 408534 524288 17 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 14295017 131072 226375608064910080 72057594037927936 17 12795308182968293392384 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 408534 524288 12795308182968293392384 18889465931478580854784 727329062 1073741824 160029 159872 (ep579 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep581 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 43069832757 137438953472 85916467051 171661252886528 Bool.true 53547164181 137438953472 85966387083 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz155) 262143 524288 1 524288 164299 262144 653925 654835712 43069832757 137438953472 85916467051 171661252886528 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 328598 524288 41851200 41909485568 164299 262144 653925 654835712 (ep578 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 262143 524288 1 524288 204267 262144 653925 654835712 53547164181 137438953472 85966387083 171661252886528 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 204267 262144 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 408534 524288 41851200 41909485568 204267 262144 653925 654835712 (ep580 rfl rfl) rfl)) rfl)

noncomputable def ep582 := @ep550 43069832757 137438953472 85916467051 171661252886528 Bool.true 53547164181 137438953472 85966387083 171661252886528 Bool.false 7592786340358591086592 27622395793 68719476736 306409306793 171661252886528 Bool.false 15585493409822001856512 56699694723 68719476736 153698865835 85830626443264 (ep551 (BSN.head_sum_c_succ qz146 3 4 rfl rfl) (ep574 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep575 ep581) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz432 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep583 := @Enclosure.Complex.IsNear.of_eq qz430 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 71120778363 274877906944 153704650173 343322505773056 Bool.true 100266681877 274877906944 153859908367 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 5 qz152 rfl)

noncomputable def ep584 := nat_lit 2458278770597228361681318958483370216657897243881129290521200132214576800000

noncomputable def ep585 := nat_lit 1210645168742867216076516685334952313310954446234599978406958400100000000

noncomputable def ep586 := nat_lit 7372415021454199350611803842079440745347069822750918671606786479843530400000

noncomputable def ep587 := BSN.cos_dyadic_bound_f 1024181930 1073741824 3 2 524288 160029 ep584 ep64 ep585 ep586 ep66 ep585 303327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1024181930) qz287 0 2 ep584 ep64 ep585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1024181930) qz288 0 2 ep586 ep66 ep585 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33192031) qz29)

noncomputable def ep588 := @Enclosure.Real.IsNear.cos_image qz156 qz437 Bool.false 33192031 262144 517 524288 Bool.false 303327 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 129656373 1024000 4917 4996000 33192031 262144 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz33 78672 1000 0 1 421904 262144 1 79936 129656373 1024000 4917 4996000 qz153 qz302 rfl) rfl) (Enclosure.sfrac_false_div 33192031 262144) (BSN.cos_reduce0 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36035198139215414034432) qz298) 226375608064910080 72057594037927936 Bool.false 303327 524288 20 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 33192031 262144 226375608064910080 72057594037927936 20 36035198139215414034432 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 303327 524288 36035198139215414034432 37778931862957161709568 1024181930 1073741824 160029 159872 (ep587 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep589 := nat_lit 4423933270940016757253512911921798428133566275429045042955434671266158240000

noncomputable def ep590 := nat_lit 11584531807903031626837933742304644055652074890353595283965860492096919200000

noncomputable def ep591 := BSN.sin_dyadic_bound_f 1024181930 1073741824 3 2 524288 160029 ep589 ep57 ep585 ep590 ep60 ep585 427633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1024181930) qz283 0 2 ep589 ep57 ep585 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1024181930) qz284 0 2 ep590 ep60 ep585 rfl rfl rfl rfl) rfl rfl

noncomputable def ep592 := @Enclosure.Real.IsNear.sin_image qz156 qz437 Bool.false 33192031 262144 517 524288 Bool.false 427633 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 129656373 1024000 4917 4996000 33192031 262144 517 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz33 78672 1000 0 1 421904 262144 1 79936 129656373 1024000 4917 4996000 qz153 qz302 rfl) rfl) (Enclosure.sfrac_false_div 33192031 262144) (BSN.sin_reduce0 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36035198139215414034432) qz298) 226375608064910080 72057594037927936 Bool.false 427633 524288 20 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 33192031 262144 226375608064910080 72057594037927936 20 36035198139215414034432 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 427633 524288 36035198139215414034432 37778931862957161709568 1024181930 1073741824 160029 159872 (ep591 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep593 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 71120778363 274877906944 153704650173 343322505773056 Bool.true 100266681877 274877906944 153859908367 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz156) 234469 524288 1 524288 303327 524288 653925 654835712 71120778363 274877906944 153704650173 343322505773056 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 303327 524288 41851200 41909485568 303327 524288 653925 654835712 (ep588 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 234469 524288 1 524288 427633 524288 653925 654835712 100266681877 274877906944 153859908367 343322505773056 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 427633 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 427633 524288 41851200 41909485568 427633 524288 653925 654835712 (ep592 rfl rfl) rfl)) rfl)

noncomputable def ep594 := @ep548 71120778363 274877906944 153704650173 343322505773056 Bool.true 100266681877 274877906944 153859908367 343322505773056 Bool.false 12480169014520981749760 181610361535 274877906944 766523263759 343322505773056 Bool.false 8695219497179587543040 126532097015 274877906944 768655371707 343322505773056 (ep549 (BSN.head_sum_c_succ qz146 4 5 rfl rfl) (ep582 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep583 ep593) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz432 qz305)

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq qz429 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 51448768469 137438953472 70283276879 171661252886528 Bool.true 44776744761 274877906944 140227396551 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 6 qz152 rfl)

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz305 78672 1000 0 1 4034681531866359 2251799813685248 7812500001249 624500000000000000 19838529092186887203 140737488355328000 38414062506141333 39031250000000000000 qz153 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 7812500001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz306) Bool.false 16922680887833197019136 9444732965739290427392 1000000000159872 79936000000000000000 4034681531866359 2251799813685248 7812500001249 624500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep111 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep597 := nat_lit 9691715955780961250171675529378391028183666427175427889340272420720097931905

noncomputable def ep598 := nat_lit 5806551365801621078697756515820503359574729423342702448037154253748613761

noncomputable def ep599 := nat_lit 25373664515310267316322210971155886163613148223535946763356272375951330161281

noncomputable def ep600 := BSN.sin_dyadic_bound_f 1245918929 1073741824 3 2 524288 160029 ep597 ep57 ep598 ep599 ep60 ep598 480742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1245918929) qz283 0 2 ep597 ep57 ep598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1245918929) qz284 0 2 ep599 ep60 ep598 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73904279) qz19)

noncomputable def ep601 := @Enclosure.Real.IsNear.cos_image qz157 qz438 Bool.false 73904279 524288 517 524288 Bool.true 480742 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 19838529092186887203 140737488355328000 38414062506141333 39031250000000000000 73904279 524288 517 524288 (ep596 rfl) rfl) (Enclosure.sfrac_false_div 73904279 524288) (BSN.cos_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87673750394459262025728) qz22) 226375608064910080 72057594037927936 Bool.false 480742 524288 22 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 73904279 524288 226375608064910080 72057594037927936 22 87673750394459262025728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 480742 524288 87673750394459262025728 75557863725914323419136 1245918929 1073741824 160029 159872 (ep600 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep602 := nat_lit 5386867331596445859463685408106137461595181228174501139610390080068387123841

noncomputable def ep603 := nat_lit 16148988892057734336233660711286771378066394225676818013935095931697664144001

noncomputable def ep604 := BSN.cos_dyadic_bound_f 1245918929 1073741824 3 2 524288 160029 ep602 ep64 ep598 ep603 ep66 ep598 209199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1245918929) qz287 0 2 ep602 ep64 ep598 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1245918929) qz288 0 2 ep603 ep66 ep598 rfl rfl rfl rfl) rfl rfl

noncomputable def ep605 := @Enclosure.Real.IsNear.sin_image qz157 qz438 Bool.false 73904279 524288 517 524288 Bool.false 209199 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 19838529092186887203 140737488355328000 38414062506141333 39031250000000000000 73904279 524288 517 524288 (ep596 rfl) rfl) (Enclosure.sfrac_false_div 73904279 524288) (BSN.sin_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87673750394459262025728) qz22) 226375608064910080 72057594037927936 Bool.false 209199 524288 22 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 73904279 524288 226375608064910080 72057594037927936 22 87673750394459262025728 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 209199 524288 87673750394459262025728 75557863725914323419136 1245918929 1073741824 160029 159872 (ep604 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep606 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 51448768469 137438953472 70283276879 171661252886528 Bool.true 44776744761 274877906944 140227396551 343322505773056 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz157) 214039 524288 1 524288 240371 262144 653925 654835712 51448768469 137438953472 70283276879 171661252886528 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 480742 524288 41851200 41909485568 240371 262144 653925 654835712 (ep601 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 214039 524288 1 524288 209199 524288 653925 654835712 44776744761 274877906944 140227396551 343322505773056 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 209199 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 209199 524288 41851200 41909485568 209199 524288 653925 654835712 (ep605 rfl rfl) rfl)) rfl)

noncomputable def ep607 := @ep546 51448768469 137438953472 70283276879 171661252886528 Bool.true 44776744761 274877906944 140227396551 343322505773056 Bool.false 10818208237436780150784 78712824597 274877906944 907089817517 343322505773056 Bool.false 22472740109048952651776 40877676127 137438953472 454441384129 171661252886528 (ep547 (BSN.head_sum_c_succ qz146 5 6 rfl rfl) (ep594 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep595 ep606) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz432 qz310)

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq qz428 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 68593924287 274877906944 130016733801 343322505773056 Bool.true 39015718581 137438953472 65038108713 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 7 qz152 rfl)

noncomputable def ep609 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz310 78672 1000 0 1 4381792198794487 2251799813685248 7812500001249 624500000000000000 21545272241472492579 140737488355328000 38414062506141333 39031250000000000000 qz153 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 7812500001249 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 18378568546572512002048 9444732965739290427392 1000000000159872 79936000000000000000 4381792198794487 2251799813685248 7812500001249 624500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep126 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep610 := nat_lit 359446377762122363671512851913773056

noncomputable def ep611 := BSN.sin_dyadic_bound_f 774298696 1073741824 2 1 524288 160029 ep610 ep75 ep610 ep610 ep76 ep610 346149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 774298696) qz283 0 1 ep610 ep75 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 774298696) qz284 0 1 ep610 ep76 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80262393) qz19)

noncomputable def ep612 := @Enclosure.Real.IsNear.cos_image qz158 qz439 Bool.false 80262393 524288 517 524288 Bool.true 346149 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 21545272241472492579 140737488355328000 38414062506141333 39031250000000000000 80262393 524288 517 524288 (ep609 rfl) rfl) (Enclosure.sfrac_false_div 80262393 524288) (BSN.cos_reduce1 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54486426903106935586816) qz22) 226375608064910080 72057594037927936 Bool.false 346149 524288 24 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 80262393 524288 226375608064910080 72057594037927936 24 54486426903106935586816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 346149 524288 54486426903106935586816 75557863725914323419136 774298696 1073741824 160029 159872 (ep611 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep613 := nat_lit 802809998050707665509788690967763573812222165680971519955978064496705929216

noncomputable def ep614 := nat_lit 129201698486310374485633922666940175180553321654271557838066509871579136

noncomputable def ep615 := nat_lit 2408171590755150375780394805057956841086305390399606016752258060470374629376

noncomputable def ep616 := BSN.cos_dyadic_bound_f 774298696 1073741824 3 2 524288 160029 ep613 ep64 ep614 ep615 ep66 ep614 393774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 774298696) qz287 0 2 ep613 ep64 ep614 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 774298696) qz288 0 2 ep615 ep66 ep614 rfl rfl rfl rfl) rfl rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.sin_image qz158 qz439 Bool.false 80262393 524288 517 524288 Bool.false 393774 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 21545272241472492579 140737488355328000 38414062506141333 39031250000000000000 80262393 524288 517 524288 (ep609 rfl) rfl) (Enclosure.sfrac_false_div 80262393 524288) (BSN.sin_reduce1 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54486426903106935586816) qz22) 226375608064910080 72057594037927936 Bool.false 393774 524288 24 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 80262393 524288 226375608064910080 72057594037927936 24 54486426903106935586816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 393774 524288 54486426903106935586816 75557863725914323419136 774298696 1073741824 160029 159872 (ep616 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep618 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 68593924287 274877906944 130016733801 343322505773056 Bool.true 39015718581 137438953472 65038108713 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz158) 198163 524288 1 524288 346149 524288 653925 654835712 68593924287 274877906944 130016733801 343322505773056 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 346149 524288 41851200 41909485568 346149 524288 653925 654835712 (ep612 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 198163 524288 1 524288 196887 262144 653925 654835712 39015718581 137438953472 65038108713 171661252886528 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 196887 262144 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 393774 524288 41851200 41909485568 196887 262144 653925 654835712 (ep617 rfl rfl) rfl)) rfl)

noncomputable def ep619 := @ep544 68593924287 274877906944 130016733801 343322505773056 Bool.true 39015718581 137438953472 65038108713 171661252886528 Bool.false 2781462137787792752640 5059450155 137438953472 518553275659 171661252886528 Bool.false 255905496531533299712 930978773 68719476736 259739746421 85830626443264 (ep545 (BSN.head_sum_c_succ qz146 6 7 rfl rfl) (ep607 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep608 ep618) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz432 qz315)

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 94602046043 274877906944 121851594589 343322505773056 Bool.true 22250789157 274877906944 121364082411 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 8 qz152 rfl)

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz315 78672 1000 0 1 9364972152248037 4503599627370496 15625000003747 1249000000000000000 46047568072603597929 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 19639770079031275290624 9444732965739290427392 1000000000239808 79936000000000000000 9364972152248037 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep137 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep622 := nat_lit 3785258349946039266003774596563521

noncomputable def ep623 := BSN.cos_dyadic_bound_f 248041233 1073741824 2 1 524288 160029 ep622 ep79 ep622 ep622 ep80 ep622 510361 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 248041233) qz287 0 1 ep622 ep79 ep622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 248041233) qz288 0 1 ep622 ep80 ep622 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85770279) qz19)

noncomputable def ep624 := @Enclosure.Real.IsNear.cos_image qz159 qz440 Bool.false 85770279 524288 517 524288 Bool.false 510361 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 46047568072603597929 281474976710656000 76828125018423999 78062500000000000000 85770279 524288 517 524288 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 85770279 524288) (BSN.cos_reduce0 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17454350085531398832128) qz22) 226375608064910080 72057594037927936 Bool.false 510361 524288 26 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 85770279 524288 226375608064910080 72057594037927936 26 17454350085531398832128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510361 524288 17454350085531398832128 75557863725914323419136 248041233 1073741824 160029 159872 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := BSN.sin_dyadic_bound_f 248041233 1073741824 2 1 524288 160029 ep622 ep75 ep622 ep622 ep76 ep622 120039 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 248041233) qz283 0 1 ep622 ep75 ep622 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 248041233) qz284 0 1 ep622 ep76 ep622 rfl rfl rfl rfl) rfl rfl

noncomputable def ep626 := @Enclosure.Real.IsNear.sin_image qz159 qz440 Bool.false 85770279 524288 517 524288 Bool.false 120039 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 46047568072603597929 281474976710656000 76828125018423999 78062500000000000000 85770279 524288 517 524288 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 85770279 524288) (BSN.sin_reduce0 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17454350085531398832128) qz22) 226375608064910080 72057594037927936 Bool.false 120039 524288 26 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 85770279 524288 226375608064910080 72057594037927936 26 17454350085531398832128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120039 524288 17454350085531398832128 75557863725914323419136 248041233 1073741824 160029 159872 (ep625 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep627 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 94602046043 274877906944 121851594589 343322505773056 Bool.true 22250789157 274877906944 121364082411 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz159) 185363 524288 1 524288 510361 524288 653925 654835712 94602046043 274877906944 121851594589 343322505773056 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 510361 524288 41851200 41909485568 510361 524288 653925 654835712 (ep624 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz38 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 185363 524288 1 524288 120039 524288 653925 654835712 22250789157 274877906944 121364082411 343322505773056 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 120039 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 120039 524288 41851200 41909485568 120039 524288 653925 654835712 (ep626 rfl rfl) rfl)) rfl)

noncomputable def ep628 := @ep542 94602046043 274877906944 121851594589 343322505773056 Bool.true 22250789157 274877906944 121364082411 343322505773056 Bool.false 14392737273353775087616 104720946353 274877906944 1158958145907 343322505773056 Bool.true 1273157091300569251840 18526874065 274877906944 1160323068095 343322505773056 (ep543 (BSN.head_sum_c_succ qz146 7 8 rfl rfl) (ep619 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep620 ep627) rfl rfl

theorem EMRow20.d11 : Enclosure.Complex.IsNear qz145 Bool.false 104720946353 274877906944 1158958145907 343322505773056 Bool.true 18526874065 274877906944 1160323068095 343322505773056 := ep541 (BSN.head_sum_c_succ qz146 8 9 rfl rfl) (ep628 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz160 := (BSN.headSumC qz425 17)

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz426)

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq qz160 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 16) qz161) Bool.false 369749615355 274877906944 1948875478969 343322505773056 Bool.false 17548081099 137438953472 121817454035 21457656610816

noncomputable def ep630 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 16) qz161 Bool.false 192225072751 137438953472 465756034319 85830626443264 Bool.true 8007962613 68719476736 931364165805 171661252886528 Bool.true

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz426)

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 15) qz162) Bool.false 192225072751 137438953472 465756034319 85830626443264 Bool.true 8007962613 68719476736 931364165805 171661252886528

noncomputable def ep632 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 15) qz162 Bool.false 162558788843 137438953472 221744196309 42915313221632 Bool.true 17744657159 68719476736 886922927107 171661252886528 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz426)

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 14) qz163) Bool.false 162558788843 137438953472 221744196309 42915313221632 Bool.true 17744657159 68719476736 886922927107 171661252886528

noncomputable def ep634 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 14) qz163 Bool.false 254404814431 274877906944 1681693977527 343322505773056 Bool.true 51063371027 274877906944 1682039056243 343322505773056 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz426)

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 13) qz164) Bool.false 254404814431 274877906944 1681693977527 343322505773056 Bool.true 51063371027 274877906944 1682039056243 343322505773056

noncomputable def ep636 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 13) qz164 Bool.false 98733332697 137438953472 396529092061 85830626443264 Bool.true 366698343 274877906944 1586515057787 343322505773056 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz426)

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 12) qz165) Bool.false 98733332697 137438953472 396529092061 85830626443264 Bool.true 366698343 274877906944 1586515057787 343322505773056

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 12) qz165 Bool.false 137485089157 274877906944 1486649824557 343322505773056 Bool.false 51582332417 274877906944 1487114802277 343322505773056 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz426)

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 11) qz166) Bool.false 137485089157 274877906944 1486649824557 343322505773056 Bool.false 51582332417 274877906944 1487114802277 343322505773056

noncomputable def ep640 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 11) qz166 Bool.false 13888699621 68719476736 691315010047 171661252886528 Bool.false 64085116685 274877906944 1383643552369 343322505773056 Bool.false

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz426)

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 10) qz167) Bool.false 13888699621 68719476736 691315010047 171661252886528 Bool.false 64085116685 274877906944 1383643552369 343322505773056

noncomputable def ep642 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 10) qz167 Bool.false 6667550867 137438953472 79618363309 21457656610816 Bool.true 2974309915 68719476736 637326498805 171661252886528 Bool.false

noncomputable abbrev qz441 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 9) qz147)

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 10) (@HAdd.hAdd Complex Complex Complex qz4 qz145 qz441) Bool.false 6667550867 137438953472 79618363309 21457656610816 Bool.true 2974309915 68719476736 637326498805 171661252886528

noncomputable def ep644 := @Enclosure.Complex.IsNear.addLitP qz145 qz441 Bool.false 104720946353 274877906944 1158958145907 343322505773056 Bool.true 18526874065 274877906944 1160323068095 343322505773056 Bool.true

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz432 qz320)

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq qz441 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 91385844619 274877906944 114935667037 343322505773056 Bool.false 6629634405 274877906944 114329929515 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 9 qz152 rfl)

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz320 78672 1000 0 1 9895417793173221 4503599627370496 15625000003747 1249000000000000000 48655769289032727657 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 20752195215788806766592 9444732965739290427392 1000000000239808 79936000000000000000 9895417793173221 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep168 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep647 := BSN.cos_dyadic_bound_f 77760298 1073741824 1 0 524288 160029 0 1 1 0 1 1 522913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 77760298) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 77760298) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5664277) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep648 := @Enclosure.Real.IsNear.cos_image qz168 qz442 Bool.false 5664277 32768 517 524288 Bool.true 522913 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 48655769289032727657 281474976710656000 76828125018423999 78062500000000000000 5664277 32768 517 524288 (ep646 rfl) rfl) (Enclosure.sfrac_false_div 5664277 32768) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 341993410937585926144) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 522913 524288 27 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 5664277 32768 226375608064910080 72057594037927936 27 341993410937585926144 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522913 524288 341993410937585926144 4722366482869645213696 77760298 1073741824 160029 159872 (ep647 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep649 := BSN.sin_dyadic_bound_f 77760298 1073741824 1 0 524288 160029 0 1 1 0 1 1 37935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 77760298) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 77760298) qz284 0 0 rfl) rfl rfl

noncomputable def ep650 := @Enclosure.Real.IsNear.sin_image qz168 qz442 Bool.false 5664277 32768 517 524288 Bool.true 37935 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 48655769289032727657 281474976710656000 76828125018423999 78062500000000000000 5664277 32768 517 524288 (ep646 rfl) rfl) (Enclosure.sfrac_false_div 5664277 32768) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 341993410937585926144) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 37935 524288 27 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 5664277 32768 226375608064910080 72057594037927936 27 341993410937585926144 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37935 524288 341993410937585926144 4722366482869645213696 77760298 1073741824 160029 159872 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 91385844619 274877906944 114935667037 343322505773056 Bool.false 6629634405 274877906944 114329929515 343322505773056 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz168) 174763 524288 1 524288 522913 524288 653925 654835712 91385844619 274877906944 114935667037 343322505773056 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 522913 524288 41851200 41909485568 522913 524288 653925 654835712 (ep648 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 174763 524288 1 524288 37935 524288 653925 654835712 6629634405 274877906944 114329929515 343322505773056 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 37935 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 37935 524288 41851200 41909485568 37935 524288 653925 654835712 (ep650 rfl rfl) rfl)) rfl)

noncomputable def ep652 := @ep644 91385844619 274877906944 114935667037 343322505773056 Bool.false 6629634405 274877906944 114329929515 343322505773056 Bool.false 3665524853527225040896 6667550867 137438953472 79618363309 21457656610816 Bool.true 3270288336151946199040 2974309915 68719476736 637326498805 171661252886528 EMRow20.d11 (ep645 ep651) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz432 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep653 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 21109848375 137438953472 54368103575 171661252886528 Bool.false 75982356345 274877906944 108990554759 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 10 qz152 rfl)

noncomputable def ep654 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz53 78672 1000 0 1 10369908600166117 4503599627370496 15625000003747 1249000000000000000 50988840587016797289 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 21747274560655572598784 9444732965739290427392 1000000000239808 79936000000000000000 10369908600166117 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep182 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep655 := nat_lit 87947405694499351054446708846600625

noncomputable def ep656 := BSN.sin_dyadic_bound_f 544572565 1073741824 2 1 524288 160029 ep655 ep75 ep655 ep655 ep76 ep655 254650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 544572565) qz283 0 1 ep655 ep75 ep655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 544572565) qz284 0 1 ep655 ep76 ep655 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23743529) qz519)

noncomputable def ep657 := @Enclosure.Real.IsNear.cos_image qz169 qz443 Bool.false 23743529 131072 517 524288 Bool.false 254650 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 50988840587016797289 281474976710656000 76828125018423999 78062500000000000000 23743529 131072 517 524288 (ep654 rfl) rfl) (Enclosure.sfrac_false_div 23743529 131072) (BSN.cos_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9580221886890285989888) qz332) 226375608064910080 72057594037927936 Bool.false 254650 524288 28 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 23743529 131072 226375608064910080 72057594037927936 28 9580221886890285989888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254650 524288 9580221886890285989888 18889465931478580854784 544572565 1073741824 160029 159872 (ep656 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep658 := BSN.cos_dyadic_bound_f 544572565 1073741824 2 1 524288 160029 ep655 ep79 ep655 ep655 ep80 ep655 458291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 544572565) qz287 0 1 ep655 ep79 ep655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 544572565) qz288 0 1 ep655 ep80 ep655 rfl rfl rfl rfl) rfl rfl

noncomputable def ep659 := @Enclosure.Real.IsNear.sin_image qz169 qz443 Bool.false 23743529 131072 517 524288 Bool.true 458291 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 50988840587016797289 281474976710656000 76828125018423999 78062500000000000000 23743529 131072 517 524288 (ep654 rfl) rfl) (Enclosure.sfrac_false_div 23743529 131072) (BSN.sin_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9580221886890285989888) qz332) 226375608064910080 72057594037927936 Bool.false 458291 524288 28 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 23743529 131072 226375608064910080 72057594037927936 28 9580221886890285989888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 458291 524288 9580221886890285989888 18889465931478580854784 544572565 1073741824 160029 159872 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 21109848375 137438953472 54368103575 171661252886528 Bool.false 75982356345 274877906944 108990554759 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz169) 165795 524288 1 524288 127325 262144 653925 654835712 21109848375 137438953472 54368103575 171661252886528 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 254650 524288 41851200 41909485568 127325 262144 653925 654835712 (ep657 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 165795 524288 1 524288 458291 524288 653925 654835712 75982356345 274877906944 108990554759 343322505773056 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 458291 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 458291 524288 41851200 41909485568 458291 524288 653925 654835712 (ep659 rfl rfl) rfl)) rfl)

noncomputable def ep661 := @ep642 21109848375 137438953472 54368103575 171661252886528 Bool.false 75982356345 274877906944 108990554759 343322505773056 Bool.false 3817696681994406068224 13888699621 68719476736 691315010047 171661252886528 Bool.false 4403895685158702940160 64085116685 274877906944 1383643552369 343322505773056 (ep643 (BSN.head_sum_c_succ qz146 9 10 rfl rfl) (ep652 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep653 ep660) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz432 qz329)

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 81930290673 274877906944 104019804463 343322505773056 Bool.true 3125696067 68719476736 25867812477 85830626443264 (BSN.cpow_neg_s_mk qz151 78672 1000 11 qz152 rfl)

noncomputable def ep663 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz329 78672 1000 0 1 10799147631728357 4503599627370496 15625000003747 1249000000000000000 53099408905208331369 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 22647454054174387339264 9444732965739290427392 1000000000239808 79936000000000000000 10799147631728357 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep197 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep664 := nat_lit 699068561411803318258405212160000

noncomputable def ep665 := BSN.cos_dyadic_bound_f 162603520 1073741824 2 1 524288 160029 ep664 ep79 ep664 ep664 ep80 ep664 518287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 162603520) qz287 0 1 ep664 ep79 ep664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 162603520) qz288 0 1 ep664 ep80 ep664 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24726339) qz519)

noncomputable def ep666 := @Enclosure.Real.IsNear.cos_image qz170 qz444 Bool.false 24726339 131072 517 524288 Bool.false 518287 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 53099408905208331369 281474976710656000 76828125018423999 78062500000000000000 24726339 131072 517 524288 (ep663 rfl) rfl) (Enclosure.sfrac_false_div 24726339 131072) (BSN.cos_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860551378302725521408) qz332) 226375608064910080 72057594037927936 Bool.false 518287 524288 30 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 24726339 131072 226375608064910080 72057594037927936 30 2860551378302725521408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518287 524288 2860551378302725521408 18889465931478580854784 162603520 1073741824 160029 159872 (ep665 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep667 := BSN.sin_dyadic_bound_f 162603520 1073741824 1 0 524288 160029 0 1 1 0 1 1 79092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 162603520) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 162603520) qz284 0 0 rfl) rfl rfl

noncomputable def ep668 := @Enclosure.Real.IsNear.sin_image qz170 qz444 Bool.false 24726339 131072 517 524288 Bool.false 79092 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 53099408905208331369 281474976710656000 76828125018423999 78062500000000000000 24726339 131072 517 524288 (ep663 rfl) rfl) (Enclosure.sfrac_false_div 24726339 131072) (BSN.sin_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860551378302725521408) qz332) 226375608064910080 72057594037927936 Bool.false 79092 524288 30 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 24726339 131072 226375608064910080 72057594037927936 30 2860551378302725521408 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79092 524288 2860551378302725521408 18889465931478580854784 162603520 1073741824 160029 159872 (ep667 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep669 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 81930290673 274877906944 104019804463 343322505773056 Bool.true 3125696067 68719476736 25867812477 85830626443264 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz170) 158079 524288 1 524288 518287 524288 653925 654835712 81930290673 274877906944 104019804463 343322505773056 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 518287 524288 41851200 41909485568 518287 524288 653925 654835712 (ep666 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 158079 524288 1 524288 19773 131072 653925 654835712 3125696067 68719476736 25867812477 85830626443264 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 19773 131072 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 79092 524288 41851200 41909485568 19773 131072 653925 654835712 (ep668 rfl rfl) rfl)) rfl)

noncomputable def ep670 := @ep640 81930290673 274877906944 104019804463 343322505773056 Bool.true 3125696067 68719476736 25867812477 85830626443264 Bool.false 9447903385871347351552 137485089157 274877906944 1486649824557 343322505773056 Bool.false 3544710892518650150912 51582332417 274877906944 1487114802277 343322505773056 (ep641 (BSN.head_sum_c_succ qz146 10 11 rfl rfl) (ep661 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep662 ep669) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz432 qz335)

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 59981576237 274877906944 99466543687 343322505773056 Bool.true 6493628845 34359738368 49700127755 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 12 qz152 rfl)

noncomputable def ep672 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz335 78672 1000 0 1 11191020447815397 4503599627370496 15625000003747 1249000000000000000 55026247541908307049 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 23469270914176955449344 9444732965739290427392 1000000000239808 79936000000000000000 11191020447815397 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep208 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep673 := nat_lit 770510441335267017047833376038771811492369449827224282467126160537331402721

noncomputable def ep674 := nat_lit 119016002149751401647364345675458314858112547928115954099222880594921441

noncomputable def ep675 := nat_lit 2311293292001501548340205399424964517847392124385816615493180035850804365281

noncomputable def ep676 := BSN.cos_dyadic_bound_f 766391483 1073741824 3 2 524288 160029 ep673 ep64 ep674 ep675 ep66 ep674 396313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 766391483) qz287 0 2 ep673 ep64 ep674 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 766391483) qz288 0 2 ep675 ep66 ep674 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102494373) qz19)

noncomputable def ep677 := @Enclosure.Real.IsNear.cos_image qz171 qz445 Bool.false 102494373 524288 517 524288 Bool.false 396313 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 55026247541908307049 281474976710656000 76828125018423999 78062500000000000000 102494373 524288 517 524288 (ep672 rfl) rfl) (Enclosure.sfrac_false_div 102494373 524288) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53930006271112612151296) qz22) 226375608064910080 72057594037927936 Bool.false 396313 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 102494373 524288 226375608064910080 72057594037927936 31 53930006271112612151296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 396313 524288 53930006271112612151296 75557863725914323419136 766391483 1073741824 160029 159872 (ep676 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep678 := nat_lit 344986959390860746267501987955825521

noncomputable def ep679 := BSN.sin_dyadic_bound_f 766391483 1073741824 2 1 524288 160029 ep678 ep75 ep678 ep678 ep76 ep678 343240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 766391483) qz283 0 1 ep678 ep75 ep678 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 766391483) qz284 0 1 ep678 ep76 ep678 rfl rfl rfl rfl) rfl rfl

noncomputable def ep680 := @Enclosure.Real.IsNear.sin_image qz171 qz445 Bool.false 102494373 524288 517 524288 Bool.false 343240 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 55026247541908307049 281474976710656000 76828125018423999 78062500000000000000 102494373 524288 517 524288 (ep672 rfl) rfl) (Enclosure.sfrac_false_div 102494373 524288) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53930006271112612151296) qz22) 226375608064910080 72057594037927936 Bool.false 343240 524288 31 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 102494373 524288 226375608064910080 72057594037927936 31 53930006271112612151296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343240 524288 53930006271112612151296 75557863725914323419136 766391483 1073741824 160029 159872 (ep679 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep681 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 59981576237 274877906944 99466543687 343322505773056 Bool.true 6493628845 34359738368 49700127755 171661252886528 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz171) 151349 524288 1 524288 396313 524288 653925 654835712 59981576237 274877906944 99466543687 343322505773056 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 396313 524288 41851200 41909485568 396313 524288 653925 654835712 (ep677 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 151349 524288 1 524288 42905 65536 653925 654835712 6493628845 34359738368 49700127755 171661252886528 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 42905 65536 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 343240 524288 41851200 41909485568 42905 65536 653925 654835712 (ep680 rfl rfl) rfl)) rfl)

noncomputable def ep682 := @ep638 59981576237 274877906944 99466543687 343322505773056 Bool.true 6493628845 34359738368 49700127755 171661252886528 Bool.false 54279223674713917095936 98733332697 137438953472 396529092061 85830626443264 Bool.true 12599659125459124224 366698343 274877906944 1586515057787 343322505773056 (ep639 (BSN.head_sum_c_succ qz146 11 12 rfl rfl) (ep670 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep671 ep681) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz432 qz340)

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 56938149037 274877906944 95577609283 343322505773056 Bool.true 12674168171 68719476736 11940499807 42915313221632 (BSN.cpow_neg_s_mk qz151 78672 1000 13 qz152 rfl)

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz340 78672 1000 0 1 11551488463034085 4503599627370496 15625000003747 1249000000000000000 11359733754547719189 56294995342131200 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 24225227133228857425920 9444732965739290427392 1000000000239808 79936000000000000000 11551488463034085 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep685 := nat_lit 831486685849542473425417034231617719829283182723587284623164188870668188481

noncomputable def ep686 := nat_lit 138595230320711772727267235488610951853276160405711269666301601549908801

noncomputable def ep687 := nat_lit 2494182867087985996730796568223875937584142995849950431330159963408904747841

noncomputable def ep688 := BSN.cos_dyadic_bound_f 781121399 1073741824 3 2 524288 160029 ep685 ep64 ep686 ep687 ep66 ep686 391567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 781121399) qz287 0 2 ep685 ep64 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 781121399) qz288 0 2 ep687 ep66 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26448941) qz519)

noncomputable def ep689 := @Enclosure.Real.IsNear.cos_image qz172 qz446 Bool.false 26448941 131072 517 524288 Bool.false 391567 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 11359733754547719189 56294995342131200 76828125018423999 78062500000000000000 26448941 131072 517 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 26448941 131072) (BSN.cos_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13741632985877050294272) qz332) 226375608064910080 72057594037927936 Bool.false 391567 524288 32 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 26448941 131072 226375608064910080 72057594037927936 32 13741632985877050294272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391567 524288 13741632985877050294272 18889465931478580854784 781121399 1073741824 160029 159872 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep690 := nat_lit 372283803462777269298906934327274401

noncomputable def ep691 := BSN.sin_dyadic_bound_f 781121399 1073741824 2 1 524288 160029 ep690 ep75 ep690 ep690 ep76 ep690 348644 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 781121399) qz283 0 1 ep690 ep75 ep690 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 781121399) qz284 0 1 ep690 ep76 ep690 rfl rfl rfl rfl) rfl rfl

noncomputable def ep692 := @Enclosure.Real.IsNear.sin_image qz172 qz446 Bool.false 26448941 131072 517 524288 Bool.false 348644 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 11359733754547719189 56294995342131200 76828125018423999 78062500000000000000 26448941 131072 517 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 26448941 131072) (BSN.sin_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13741632985877050294272) qz332) 226375608064910080 72057594037927936 Bool.false 348644 524288 32 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 26448941 131072 226375608064910080 72057594037927936 32 13741632985877050294272 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 348644 524288 13741632985877050294272 18889465931478580854784 781121399 1073741824 160029 159872 (ep691 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep693 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 56938149037 274877906944 95577609283 343322505773056 Bool.true 12674168171 68719476736 11940499807 42915313221632 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz172) 145411 524288 1 524288 391567 524288 653925 654835712 56938149037 274877906944 95577609283 343322505773056 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 391567 524288 41851200 41909485568 391567 524288 653925 654835712 (ep689 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 145411 524288 1 524288 87161 131072 653925 654835712 12674168171 68719476736 11940499807 42915313221632 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 87161 131072 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 348644 524288 41851200 41909485568 87161 131072 653925 654835712 (ep692 rfl rfl) rfl)) rfl)

noncomputable def ep694 := @ep636 56938149037 274877906944 95577609283 343322505773056 Bool.true 12674168171 68719476736 11940499807 42915313221632 Bool.false 34965131453635003154432 254404814431 274877906944 1681693977527 343322505773056 Bool.true 3509048137351662927872 51063371027 274877906944 1682039056243 343322505773056 (ep637 (BSN.head_sum_c_succ qz146 12 13 rfl rfl) (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep683 ep693) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz432 qz345)

noncomputable def ep695 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 70712763255 274877906944 92259592945 343322505773056 Bool.true 19915257609 274877906944 91806797971 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 14 qz152 rfl)

noncomputable def ep696 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz345 78672 1000 0 1 11885241781671653 4503599627370496 15625000003747 1249000000000000000 58439733840479517801 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 24925158572916270432256 9444732965739290427392 1000000000239808 79936000000000000000 11885241781671653 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep697 := nat_lit 7549677995461815993271044597633681

noncomputable def ep698 := BSN.cos_dyadic_bound_f 294769203 1073741824 2 1 524288 160029 ep697 ep79 ep697 ep697 ep80 ep697 504655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 294769203) qz287 0 1 ep697 ep79 ep697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 294769203) qz288 0 1 ep697 ep80 ep697 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54426243) qz29)

noncomputable def ep699 := @Enclosure.Real.IsNear.cos_image qz173 qz447 Bool.false 54426243 262144 517 524288 Bool.false 504655 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 58439733840479517801 281474976710656000 76828125018423999 78062500000000000000 54426243 262144 517 524288 (ep696 rfl) rfl) (Enclosure.sfrac_false_div 54426243 262144) (BSN.cos_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10371269332286104928256) qz298) 226375608064910080 72057594037927936 Bool.false 504655 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 54426243 262144 226375608064910080 72057594037927936 33 10371269332286104928256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 504655 524288 10371269332286104928256 37778931862957161709568 294769203 1073741824 160029 159872 (ep698 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep700 := BSN.sin_dyadic_bound_f 294769203 1073741824 2 1 524288 160029 ep697 ep75 ep697 ep697 ep76 ep697 142129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 294769203) qz283 0 1 ep697 ep75 ep697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 294769203) qz284 0 1 ep697 ep76 ep697 rfl rfl rfl rfl) rfl rfl

noncomputable def ep701 := @Enclosure.Real.IsNear.sin_image qz173 qz447 Bool.false 54426243 262144 517 524288 Bool.false 142129 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 58439733840479517801 281474976710656000 76828125018423999 78062500000000000000 54426243 262144 517 524288 (ep696 rfl) rfl) (Enclosure.sfrac_false_div 54426243 262144) (BSN.sin_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10371269332286104928256) qz298) 226375608064910080 72057594037927936 Bool.false 142129 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 54426243 262144 226375608064910080 72057594037927936 33 10371269332286104928256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 142129 524288 10371269332286104928256 37778931862957161709568 294769203 1073741824 160029 159872 (ep700 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep702 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 70712763255 274877906944 92259592945 343322505773056 Bool.true 19915257609 274877906944 91806797971 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz173) 140121 524288 1 524288 504655 524288 653925 654835712 70712763255 274877906944 92259592945 343322505773056 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 504655 524288 41851200 41909485568 504655 524288 653925 654835712 (ep699 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 140121 524288 1 524288 142129 524288 653925 654835712 19915257609 274877906944 91806797971 343322505773056 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 142129 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 142129 524288 41851200 41909485568 142129 524288 653925 654835712 (ep701 rfl rfl) rfl)) rfl)

noncomputable def ep703 := @ep634 70712763255 274877906944 92259592945 343322505773056 Bool.true 19915257609 274877906944 91806797971 343322505773056 Bool.false 89367639265030998851584 162558788843 137438953472 221744196309 42915313221632 Bool.true 19510456877219141648384 17744657159 68719476736 886922927107 171661252886528 (ep635 (BSN.head_sum_c_succ qz146 13 14 rfl rfl) (ep694 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep695 ep702) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz432 qz350)

noncomputable def ep704 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 7416570977 34359738368 22267641701 85830626443264 Bool.false 4868347273 34359738368 22220619349 85830626443264 (BSN.cpow_neg_s_mk qz151 78672 1000 15 qz152 rfl)

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz350 78672 1000 0 1 12195956895733477 4503599627370496 15625000003747 1249000000000000000 59967520056321506409 281474976710656000 76828125018423999 78062500000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 15625000003747 1249000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 25576775395801252757504 9444732965739290427392 1000000000239808 79936000000000000000 12195956895733477 4503599627370496 15625000003747 1249000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep248 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep706 := nat_lit 5132465950139312706470786397372228118283953311276805382763384577173131100160

noncomputable def ep707 := nat_lit 1629347938455691150390894926621219574992902703489695434285238157045661696

noncomputable def ep708 := nat_lit 13439534734654985969370474353712734525717508258490745067010497792722983714816

noncomputable def ep709 := BSN.sin_dyadic_bound_f 1062922816 1073741824 3 2 524288 160029 ep706 ep57 ep707 ep708 ep60 ep707 438296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1062922816) qz283 0 2 ep706 ep57 ep707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1062922816) qz284 0 2 ep708 ep60 ep707 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55849105) qz29)

noncomputable def ep710 := @Enclosure.Real.IsNear.cos_image qz174 qz448 Bool.false 55849105 262144 517 524288 Bool.false 438296 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 59967520056321506409 281474976710656000 76828125018423999 78062500000000000000 55849105 262144 517 524288 (ep705 rfl) rfl) (Enclosure.sfrac_false_div 55849105 262144) (BSN.cos_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37398271866571178639360) qz298) 226375608064910080 72057594037927936 Bool.false 438296 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 55849105 262144 226375608064910080 72057594037927936 33 37398271866571178639360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 438296 524288 37398271866571178639360 37778931862957161709568 1062922816 1073741824 160029 159872 (ep709 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep711 := nat_lit 2852094126938931810772832840729736163302193129688665077283784870943759794176

noncomputable def ep712 := nat_lit 8553023684939884050017716732335966050756593583659015840982784136517188059136

noncomputable def ep713 := BSN.cos_dyadic_bound_f 1062922816 1073741824 3 2 524288 160029 ep711 ep64 ep707 ep712 ep66 ep707 287704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1062922816) qz287 0 2 ep711 ep64 ep707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1062922816) qz288 0 2 ep712 ep66 ep707 rfl rfl rfl rfl) rfl rfl

noncomputable def ep714 := @Enclosure.Real.IsNear.sin_image qz174 qz448 Bool.false 55849105 262144 517 524288 Bool.true 287704 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 59967520056321506409 281474976710656000 76828125018423999 78062500000000000000 55849105 262144 517 524288 (ep705 rfl) rfl) (Enclosure.sfrac_false_div 55849105 262144) (BSN.sin_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37398271866571178639360) qz298) 226375608064910080 72057594037927936 Bool.false 287704 524288 33 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 55849105 262144 226375608064910080 72057594037927936 33 37398271866571178639360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 287704 524288 37398271866571178639360 37778931862957161709568 1062922816 1073741824 160029 159872 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep715 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 7416570977 34359738368 22267641701 85830626443264 Bool.false 4868347273 34359738368 22220619349 85830626443264 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz174) 135371 524288 1 524288 54787 65536 653925 654835712 7416570977 34359738368 22267641701 85830626443264 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 438296 524288 41851200 41909485568 54787 65536 653925 654835712 (ep710 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 135371 524288 1 524288 35963 65536 653925 654835712 4868347273 34359738368 22220619349 85830626443264 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 35963 65536 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 287704 524288 41851200 41909485568 35963 65536 653925 654835712 (ep714 rfl rfl) rfl)) rfl)

noncomputable def ep716 := @ep632 7416570977 34359738368 22267641701 85830626443264 Bool.false 4868347273 34359738368 22220619349 85830626443264 Bool.false 6604803207494126010368 192225072751 137438953472 465756034319 85830626443264 Bool.true 275151500243405635584 8007962613 68719476736 931364165805 171661252886528 (ep633 (BSN.head_sum_c_succ qz146 14 15 rfl rfl) (ep703 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep704 ep715) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz432 qz356)

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 14700530147 274877906944 85851341693 343322505773056 Bool.false 33564006325 137438953472 43175466475 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 16 qz152 rfl)

noncomputable def ep718 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz356 78672 1000 0 1 3121657384082679 1125899906842624 3906250001249 312250000000000000 15349189357534532643 70368744177664000 19207031256141333 19515625000000000000 qz153 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 26186360105375033720832 9444732965739290427392 1000000000319744 79936000000000000000 3121657384082679 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep719 := nat_lit 10032304300130568577478545766300818943538578059038873090994535264436250279936

noncomputable def ep720 := nat_lit 20102112522016131255651158754561533745319480419242148544147097236820525056

noncomputable def ep721 := nat_lit 30056708675347673469924334981393333763125095216278134975895311598835109789696

noncomputable def ep722 := BSN.cos_dyadic_bound_f 1455141452 1073741824 3 2 524288 160029 ep719 ep64 ep720 ep721 ep66 ep720 112157 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1455141452) qz287 0 2 ep719 ep64 ep720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1455141452) qz288 0 2 ep721 ep66 ep720 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28590093) qz519)

noncomputable def ep723 := @Enclosure.Real.IsNear.cos_image qz175 qz449 Bool.false 28590093 131072 517 524288 Bool.true 112157 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 15349189357534532643 70368744177664000 19207031256141333 19515625000000000000 28590093 131072 517 524288 (ep718 rfl) rfl) (Enclosure.sfrac_false_div 28590093 131072) (BSN.cos_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25599119162033062281216) qz332) 226375608064910080 72057594037927936 Bool.false 112157 524288 34 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 28590093 131072 226375608064910080 72057594037927936 34 25599119162033062281216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112157 524288 25599119162033062281216 18889465931478580854784 1455141452 1073741824 160029 159872 (ep722 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep724 := nat_lit 18042066050217410534456861452337824871373184921934577844954845798195794083840

noncomputable def ep725 := nat_lit 47220483854105191949163582880044060751342109922483216591524548456891275083776

noncomputable def ep726 := BSN.sin_dyadic_bound_f 1455141452 1073741824 3 2 524288 160029 ep724 ep57 ep720 ep725 ep60 ep720 512150 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1455141452) qz283 0 2 ep724 ep57 ep720 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1455141452) qz284 0 2 ep725 ep60 ep720 rfl rfl rfl rfl) rfl rfl

noncomputable def ep727 := @Enclosure.Real.IsNear.sin_image qz175 qz449 Bool.false 28590093 131072 517 524288 Bool.true 512150 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 15349189357534532643 70368744177664000 19207031256141333 19515625000000000000 28590093 131072 517 524288 (ep718 rfl) rfl) (Enclosure.sfrac_false_div 28590093 131072) (BSN.sin_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25599119162033062281216) qz332) 226375608064910080 72057594037927936 Bool.false 512150 524288 34 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 28590093 131072 226375608064910080 72057594037927936 34 25599119162033062281216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 512150 524288 25599119162033062281216 18889465931478580854784 1455141452 1073741824 160029 159872 (ep726 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep728 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 14700530147 274877906944 85851341693 343322505773056 Bool.false 33564006325 137438953472 43175466475 171661252886528 (@Enclosure.Real.IsNear.mulLit_ft qz64 (Real.cos qz175) 131071 524288 1 524288 112157 524288 653925 654835712 14700530147 274877906944 85851341693 343322505773056 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 112157 524288 41851200 41909485568 112157 524288 653925 654835712 (ep723 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 131071 524288 1 524288 256075 262144 653925 654835712 33564006325 137438953472 43175466475 171661252886528 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 256075 262144 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 512150 524288 41851200 41909485568 256075 262144 653925 654835712 (ep727 rfl rfl) rfl)) rfl)

noncomputable def ep729 := @ep630 14700530147 274877906944 85851341693 343322505773056 Bool.false 33564006325 137438953472 43175466475 171661252886528 Bool.false 50818000181065741762560 369749615355 274877906944 1948875478969 343322505773056 Bool.false 1205894950844171812864 17548081099 137438953472 121817454035 21457656610816 (ep631 (BSN.head_sum_c_succ qz146 15 16 rfl rfl) (ep716 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep717 ep728) rfl rfl

theorem EMRow20.d12 : Enclosure.Complex.IsNear qz160 Bool.false 369749615355 274877906944 1948875478969 343322505773056 Bool.false 17548081099 137438953472 121817454035 21457656610816 := ep629 (BSN.head_sum_c_succ qz146 16 17 rfl rfl) (ep729 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep730 := nat_lit 825158393191152589615323558869

noncomputable def ep731 := nat_lit 669004347419989694465703936000

noncomputable def ep732 := nat_lit 12367453303747161742070753951681181

noncomputable def ep733 := nat_lit 1739412418299218905593654343106560000

noncomputable abbrev qz532 := (@HAdd.hAdd Complex Complex Complex qz538 (@HAdd.hAdd Complex Complex Complex qz538 qz541 (@HMul.hMul Complex Complex Complex qz540 Complex.I (@HDiv.hDiv Complex Complex Complex qz542 (↑qz545) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz450 := qz532

noncomputable abbrev qz176 := (Complex.Stirling.logGammaStirling 1 qz450)

noncomputable abbrev qz533 := (@HAdd.hAdd Complex Complex Complex qz538 qz541 (@HMul.hMul Complex Complex Complex qz540 Complex.I (@HDiv.hDiv Complex Complex Complex qz542 (↑qz545) (2 : Complex))))

noncomputable abbrev qz451 := qz533

noncomputable abbrev qz177 := qz451

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz432 (2 : Real)) (Real.log Real.pi))

noncomputable def ep734 := Complex.re (@HMul.hMul Complex Complex Complex qz66 (Complex.exp (@HMul.hMul Complex Complex Complex qz66 Complex.I ↑(@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178))) (zetaApproximant qz146 1 20))

noncomputable def ep735 := @Enclosure.Real.IsNear.of_eq ep734 (@HSub.hSub Real Real Real qz364 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20))))

noncomputable def ep736 := nat_lit 137524664314453343135116451813

noncomputable def ep737 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20))) ep736

noncomputable def ep738 := nat_lit 111500724569998282410950656000

noncomputable def ep739 := nat_lit 474312793382433598804366355854131

noncomputable def ep740 := nat_lit 66900477626893034830525167042560000

noncomputable def ep741 := nat_lit 10407304432530804624847991

noncomputable def ep742 := nat_lit 1412827032155526926289147978951

noncomputable def ep743 := nat_lit 69576496731968756223746173724262400

noncomputable def ep744 := nat_lit 92005758725829050972520314974545680683971867227470168064000

noncomputable def ep745 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20)) 524287 524288 75739

noncomputable def ep746 := nat_lit 8654352330567299030262217

noncomputable def ep747 := nat_lit 1328128862265852496445440000

noncomputable def ep748 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.true 524287 524288 4847296

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3911827) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep749 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz452 Bool.false 3911827 65536 59

noncomputable def ep750 := nat_lit 2046361600000000000000000

noncomputable def ep751 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) Bool.false 33602339024902562689 562949953421312000 913896194980289936863 ep750

noncomputable def ep752 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178 58951459825230291841 562949953421312000 299762894980289936863 ep750 368878257 8192000

noncomputable def ep753 := nat_lit 275270361292001793548288000

noncomputable def ep754 := nat_lit 40927232000000000000000000

noncomputable def ep755 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 139134128752343920359 2251799813685248000 10706155295242996695851 ep754 Bool.false 58951459825230291841 562949953421312000

noncomputable def ep756 := @Enclosure.Complex.IsNear.subLitP qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 122595100944050845359 2251799813685248000 10450155294833724375851 ep754 Bool.false 60698559459142937841 562949953421312000 274162894978243575263

noncomputable def ep757 := nat_lit 313302205201787346635369259605164032

noncomputable def ep758 := nat_lit 16593360781365869223977329094557696

noncomputable abbrev qz453 := (@HSub.hSub Complex Complex Complex qz521 qz532 qz524)

noncomputable abbrev qz454 := (Complex.log qz532)

noncomputable abbrev qz179 := (@HSub.hSub Complex Complex Complex qz361 (@HMul.hMul Complex Complex Complex qz360 qz453 qz454) qz450)

noncomputable abbrev qz180 := qz450

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq qz176 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k)))))) Bool.true 122595100944050845359

noncomputable def ep760 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) Bool.true 122595372921334429359 2251799813685248000

noncomputable def ep761 := nat_lit 1053083898409034213156116758528

noncomputable def ep762 := nat_lit 16293645486958147888528490496000

noncomputable def ep763 := @ep760 318912994420259707 1249000000000000000000 Bool.false 60699748181190388977 562949953421312000 33465625049349239 249800000000000000000 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000 Bool.true ep761 122595100944050845359 2251799813685248000 10450155294833724375851 ep754 Bool.false ep762

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP qz179 qz72 Bool.true 124664636624939677359 2251799813685248000 157074218767747041 624500000000000000000

noncomputable def ep765 := nat_lit 16068820719545146324942848

noncomputable def ep766 := @ep764 Bool.false 60699748181190388977 562949953421312000 33465625049349239 249800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep765 122595372921334429359 2251799813685248000 318912994420259707 1249000000000000000000 Bool.false 60699748181190388977 60699748181190388977 562949953421312000

noncomputable abbrev qz181 := (@HMul.hMul Complex Complex Complex qz360 qz453 qz454)

noncomputable def ep767 := @Enclosure.Complex.IsNear.subLitP qz181 qz180 Bool.true 119598087044147869359 2251799813685248000 157074218767747041 624500000000000000000 Bool.false 82843947548971117809

noncomputable def ep768 := @ep767 562949953421312000 33465625049349239 249800000000000000000 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 Bool.true 498658546499758709436000 124664636624939677359 2251799813685248000 157074218767747041 624500000000000000000 Bool.false 242798992724761555908000 60699748181190388977 562949953421312000 33465625049349239 249800000000000000000

noncomputable abbrev qz182 := qz453

noncomputable abbrev qz183 := qz454

noncomputable def ep769 := @Enclosure.Complex.IsNear.mul qz182 qz183 Bool.true 119598087044147869359 2251799813685248000 157074218767747041 624500000000000000000 Bool.false 82843947548971117809 562949953421312000 33465625049349239

noncomputable abbrev qz184 := (Complex.re qz453)

noncomputable abbrev qz185 := (Complex.re qz454)

noncomputable abbrev qz186 := (Complex.im qz453)

noncomputable abbrev qz187 := (Complex.im qz454)

noncomputable def ep770 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz184 qz185) (@HMul.hMul Real Real Real qz0 qz186 qz187) 115816397734081989 18014398509481984 5468750008743 999200000000000000 4189848023778378687 70368744177664000

noncomputable def ep771 := nat_lit 67327737530781061229443217262379008

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz185 7000 4000 0 1 16545199676297427 4503599627370496 781250001249 249800000000000000

noncomputable def ep773 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable abbrev qz455 := (Enclosure.sfrac Bool.false 157344 4000)

noncomputable abbrev qz188 := qz455

noncomputable def ep774 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz188) Bool.false 7000 4000 0 1 Bool.false 157344 4000 0

noncomputable abbrev qz456 := (Complex.log (Complex.mk qz87 qz188))

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz183 qz456 Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000

noncomputable def ep776 := nat_lit 515195599164907312686954817741596432600235171191174447500655329280

noncomputable def ep777 := nat_lit 7410940563828121579666243652431663793006729267897581486689222656

noncomputable def ep778 := nat_lit 5476538258104101385965370783545498029091634184213683545047040

noncomputable def ep779 := BSN.log_dyadic_bound 8454134336 41222134336 4 3 ep776 524288 159872 ep777 ep778 218142 49676268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8454134336) (BSN.artanhQ 41222134336) 0 3 ep777 ep776 ep778 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz457 := (Real.log (Enclosure.sfrac Bool.false 24838134336 16000000))

noncomputable def ep780 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz457 1 2 0 1 16545199676297427 2251799813685248 781250001249 124900000000000000 16545199676297427 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 24838134336 16000000 16545199676297427 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24838134336) qz380)) Bool.false 138791194366186006511616 18889465931478580854784 1000000001598720 159872000000000000000 16545199676297427 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 24838134336 16000000 10 49676268672 32768000000 218142 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep779 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep781 := BSN.arctan_dyadic_bound_f 9000 157344 1 0 524288 159872 0 1 1 0 1 1 29956 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz458 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 157344)))

noncomputable def ep782 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz458 884279719003555 562949953421312 1 2000000000000000 29956 524288 1 159872 446753516512247021568 852114708923811 562949953421312 15625000001249 2498000000000000000 qz90 (ep781 rfl) rfl rfl

noncomputable abbrev qz459 := (Complex.mk qz87 qz188)

noncomputable abbrev qz460 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157344) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep783 := @Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (ep775 (@congrArg Complex Complex qz180 qz459 Complex.log (BSN.w_shift_mk qz151 Bool.false 78672 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz456 Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz456) (@HMul.hMul Real Real Real qz0 qz88 qz457) Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 9000 157344 4000 24838134336 16000000 rfl rfl rfl) (ep780 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz456) qz460 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 9000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz460 (@HSub.hSub Real Real Real qz364 qz89 qz458) Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 157344 9000 rfl rfl) ep782))))

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 157344 4000 0 1 852114708923811 562949953421312 15625000001249 2498000000000000000

noncomputable def ep785 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable def ep786 := @Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (ep775 (@congrArg Complex Complex qz180 qz459 Complex.log (BSN.w_shift_mk qz151 Bool.false 78672 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz456 Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz456) (@HMul.hMul Real Real Real qz0 qz88 qz457) Bool.false 16545199676297427 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 9000 157344 4000 24838134336 16000000 rfl rfl rfl) (ep780 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz456) qz460 Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 9000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz460 (@HSub.hSub Real Real Real qz364 qz89 qz458) Bool.false 852114708923811 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 157344 9000 rfl rfl) ep782))))

noncomputable abbrev qz461 := (Enclosure.Real.IsNear.const Bool.false 157344 4000)

noncomputable abbrev qz189 := (@ep774 1 (BSN.w_sub_half_mk qz432 Bool.false 78672 1000 2 qz433 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz455 Bool.false 7000 4000 0 1 Bool.false 157344 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz461))

noncomputable def ep787 := @ep770 76828125006141333 312250000000000000000 ep771 119598087044147869359 2251799813685248000 157074218767747041 624500000000000000000 (@ep772 115816397734081989 18014398509481984 5468750008743 999200000000000000 (ep773 qz189) ep783 rfl) (@ep784 4189848023778378687 70368744177664000 76828125006141333 312250000000000000000 (ep785 qz189) ep786 rfl) rfl

noncomputable def ep788 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz184 qz187) (@HMul.hMul Real Real Real qz0 qz186 qz185) 5964802962466677 2251799813685248 109375000008743 9992000000000000000 81352746808354448559 562949953421312000

noncomputable def ep789 := nat_lit 186547985655723620794744530253381632

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz187 7000 4000 0 1 852114708923811 562949953421312 15625000001249 2498000000000000000

noncomputable def ep791 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz185 157344 4000 0 1 16545199676297427 4503599627370496 781250001249 249800000000000000

noncomputable def ep792 := @ep788 3841406256141333 31225000000000000000 ep789 82843947548971117809 562949953421312000 33465625049349239 249800000000000000000 (@ep790 5964802962466677 2251799813685248 109375000008743 9992000000000000000 (ep773 qz189) ep786 rfl) (@ep791 81352746808354448559 562949953421312000 3841406256141333 31225000000000000000 (ep785 qz189) ep783 rfl) rfl

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq qz180 qz459 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 (BSN.w_shift_mk qz151 Bool.false 78672 1000 2 qz152 rfl)

noncomputable abbrev qz462 := (ep793 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 157344 4000) Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 157344 4000)))

noncomputable abbrev qz190 := qz462

noncomputable def ep794 := ep768 (@ep769 249800000000000000000 (ep787 rfl) (ep792 rfl)) qz190 rfl rfl rfl rfl rfl rfl

noncomputable def ep795 := @ep766 33465625049349239 249800000000000000000 (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz93 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep333 131072 1 262144 (ep335 rfl) (ep337 rfl) rfl rfl) (@ep338 1 0 1 (ep340 rfl) (ep342 rfl) rfl rfl))

noncomputable abbrev qz463 := (@HPow.hPow Complex Int Complex qz526 qz532 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz191 := qz463

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191)) Bool.false 1037511 8589934592 3 8589934592

noncomputable def ep797 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191) Bool.false 0 1 0 1 Bool.false

noncomputable def ep798 := @ep797 0 1 0 1 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000 Bool.false 1037511 1037511 8589934592 3 8589934592 Bool.true 566826843 566826843 268435456000 1639

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz373 qz77 (@HMul.hMul Int Int Int qz374 qz78 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep800 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191 Bool.false 1037511 8589934592 3 8589934592 Bool.true 566826843 268435456000 1639 268435456000

noncomputable abbrev qz192 := (Complex.re qz463)

noncomputable abbrev qz193 := (Complex.im qz463)

noncomputable def ep801 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193) 1037511 8589934592 3 8589934592 0 1 0

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192 1 12 0 1 3112533 2147483648 9 2147483648 1037511

noncomputable def ep803 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917 67108864000

noncomputable abbrev qz464 := (@HPow.hPow Complex Nat Complex qz527 qz532 1)

noncomputable abbrev qz194 := (@Inv.inv Complex Complex.instInv qz464)

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz191 qz194 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_parts qz194 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917

noncomputable abbrev qz195 := (Complex.re qz464)

noncomputable abbrev qz196 := qz464

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) 9000 4000 0 1 345837 536870912 1 536870912

noncomputable def ep807 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz196 qz180 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0

noncomputable def ep809 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) Bool.false 345837 536870912 1 536870912 345837 536870912 1

noncomputable abbrev qz197 := (Complex.im qz464)

noncomputable def ep810 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196) (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197)) Bool.false 388095849 250000 0 1

noncomputable def ep811 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197) 81 16 0 1 24176889 15625

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz195 9000 4000 0 1 9000 4000 0 1

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 157344 4000 0 1 157344 4000 0 1

noncomputable def ep814 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 157344 4000 0 1

noncomputable abbrev qz198 := (ep807 (@ep808 1 (BSN.pow_one_c qz450) qz462))

noncomputable abbrev qz199 := (ep814 (@ep808 1 (BSN.pow_one_c qz450) qz462))

noncomputable def ep815 := @ep811 0 1 388095849 388095849 250000 0 1 (@ep812 81 16 0 1 qz198 qz198 rfl) (@ep813 24176889 15625 0 1 qz199 qz199 rfl)

noncomputable def ep816 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196) 388095849 250000 0 1 172918 172919 268435456 (ep810 (Enclosure.Complex.normSq_eq_mul_add_mul qz196) (ep815 rfl rfl)) rfl

noncomputable def ep817 := @Enclosure.Real.IsNear.of_eq (Complex.re qz194) (@HMul.hMul Real Real Real qz0 qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196))) Bool.false 3112533 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz196) (@ep806 3112533 2147483648 9 2147483648 qz198 (@ep809 536870912 (ep816 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep818 := @Enclosure.Real.IsNear.of_eq (Complex.im qz194) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196))) Bool.true 1700480529 67108864000 4917 67108864000 (Enclosure.Complex.inv_im_eq_mul qz196)

noncomputable def ep819 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) 157344 4000 0 1 345837 536870912 1

noncomputable def ep820 := @ep819 536870912 1700480529 67108864000 4917 67108864000 (@Enclosure.Real.IsNear.neg qz197 Bool.false 157344 4000 0 1 qz199) (@ep809 536870912 (ep816 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193 0 1 0 1 1700480529 67108864000 4917 67108864000 0

noncomputable def ep822 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 3112533 2147483648 9 2147483648 Bool.true 1700480529 67108864000 4917 67108864000

noncomputable abbrev qz200 := (@ep804 67108864000 (BSN.zpow_one_sub_two_mul qz450 1 1 rfl rfl) (@ep805 67108864000 ep817 (ep818 ep820)))

noncomputable def ep823 := @ep801 1 1037511 1037511 8589934592 3 8589934592 (@ep802 8589934592 3 8589934592 ep352 (ep803 qz200) rfl) (@ep821 1 0 1 ep372 (ep822 qz200) rfl) rfl

noncomputable def ep824 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192) 566826843 268435456000 1639 268435456000 0 1 0

noncomputable def ep825 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193 1 12 0 1 1700480529 67108864000 4917 67108864000 566826843

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192 0 1 0 1 3112533 2147483648 9 2147483648 0

noncomputable def ep827 := @ep824 1 566826843 566826843 268435456000 1639 268435456000 (@ep825 268435456000 1639 268435456000 ep352 (ep822 qz200) rfl) (@ep826 1 0 1 ep372 (ep803 qz200) rfl) rfl

noncomputable def ep828 := @ep798 268435456000 (@ep799 0 1 0 1 (BSN.stirling_sum_base qz180) qz109) (ep800 (ep823 rfl) (ep827 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep829 := @ep763 60698559459142937841 562949953421312000 274162894978243575263 ep750 (ep795 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep796 Bool.true 566826843 268435456000 1639 268435456000 (BSN.stirling_sum_succ qz180 0 1 rfl) (ep828 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz151 2) Bool.false 16539027808293075 2251799813685248 781250001249 124900000000000000 Bool.false 873549816956323 281474976710656

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz451 qz385))

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 1) qz201) Bool.false 16539027808293075 2251799813685248 781250001249 124900000000000000 Bool.false 873549816956323 281474976710656 15625000001249 1249000000000000000

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 1) qz201 Bool.false 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000 Bool.false

noncomputable def ep833 := nat_lit 148970318948997927447088752230400

noncomputable def ep834 := nat_lit 983529657533515312768642711552

noncomputable abbrev qz202 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz451 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 0) qz202) Bool.false 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000

noncomputable def ep836 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 0) qz202 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz465 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188))

noncomputable def ep837 := @Enclosure.Complex.IsNear.of_eq qz202 qz465 Bool.false 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000

noncomputable def ep838 := nat_lit 509225574067709119253138159435368783924692926416333134630255329280

noncomputable def ep839 := nat_lit 7212241311210533700336651561118682449475426019029874688609222656

noncomputable def ep840 := nat_lit 5172860895428033378821720347418384966803515117740416345047040

noncomputable def ep841 := BSN.log_dyadic_bound 8374134336 41142134336 4 3 ep838 524288 159872 ep839 ep840 216451 49516268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8374134336) (BSN.artanhQ 41142134336) 0 3 ep839 ep838 ep840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 24758134336 16000000)) 1 2 0 1 16537936886599891 2251799813685248 781250001249 124900000000000000 16537936886599891 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 24758134336 16000000 16537936886599891 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24758134336) qz380)) Bool.false 138730269670426938441728 18889465931478580854784 1000000001598720 159872000000000000000 16537936886599891 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 24758134336 16000000 10 49516268672 32768000000 216451 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep841 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep843 := BSN.arctan_dyadic_bound_f 1000 157344 1 0 524288 159872 0 1 1 0 1 1 3332 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz466 := (@Nat.cast Real Real.instNatCast 157344)

noncomputable def ep844 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz391 qz466)) 884279719003555 562949953421312 1 2000000000000000 3332 524288 1 159872 461741496072136032256 880702011245987 562949953421312 15625000001249 2498000000000000000 qz90 (ep843 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz451 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz467 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188)

noncomputable def ep845 := @ep836 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000 Bool.false 16537936886599891 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 880702011245987 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz151) qz109) (ep837 (@congrArg Complex Complex qz203 qz467 Complex.log (BSN.w_shift_mk qz151 Bool.false 78672 1000 0 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz465 Bool.false 16537936886599891 4503599627370496 781250001249 249800000000000000 Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz465) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 24758134336 16000000))) Bool.false 16537936886599891 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 1000 157344 4000 24758134336 16000000 rfl rfl rfl) (ep842 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz465) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz391)) Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 1000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz391)) (@HSub.hSub Real Real Real qz364 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz391 qz466))) Bool.false 880702011245987 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 157344 1000 rfl rfl) ep844)))) rfl rfl

noncomputable abbrev qz468 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188))

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq qz201 qz468 Bool.false 16540118729986259 4503599627370496 781250001249 249800000000000000 Bool.false 866397622666659 562949953421312 15625000001249 2498000000000000000

noncomputable def ep847 := nat_lit 511010496175253048548903849671054810328408001951876728491375329280

noncomputable def ep848 := nat_lit 7271433606898626709663952503323994164585133295780426728033222656

noncomputable def ep849 := nat_lit 5262452185517083339184648712131299804367051279282396505047040

noncomputable def ep850 := BSN.log_dyadic_bound 8398134336 41166134336 4 3 ep847 524288 159872 ep848 ep849 216959 49564268672 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8398134336) (BSN.artanhQ 41166134336) 0 3 ep848 ep847 ep849 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 24782134336 16000000)) 1 2 0 1 16540118729986259 2251799813685248 781250001249 124900000000000000 16540118729986259 4503599627370496 781250001249 249800000000000000 qz379 (BSN.isNear_log_sfrac 24782134336 16000000 16540118729986259 2251799813685248 781250001249 124900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24782134336) qz380)) Bool.false 138748572299312572137472 18889465931478580854784 1000000001598720 159872000000000000000 16540118729986259 2251799813685248 781250001249 124900000000000000 (BSN.log_rat_reduce_isNear 24782134336 16000000 10 49564268672 32768000000 216959 524288 24973259072661432 36028797018963968 159872 1000000000000000 rfl rfl rfl rfl (ep850 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep852 := BSN.arctan_dyadic_bound_f 5000 157344 1 0 524288 159872 0 1 1 0 1 1 16654 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 157344) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 157344) 0 0 rfl) rfl rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz395 qz466)) 884279719003555 562949953421312 1 2000000000000000 16654 524288 1 159872 454241876792657313792 866397622666659 562949953421312 15625000001249 2498000000000000000 qz90 (ep852 rfl) rfl rfl

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz273 qz451 qz385)

noncomputable abbrev qz469 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188)

noncomputable def ep854 := @ep832 16540118729986259 4503599627370496 781250001249 249800000000000000 Bool.false 866397622666659 562949953421312 15625000001249 2498000000000000000 Bool.false ep833 16539027808293075 2251799813685248 781250001249 124900000000000000 Bool.false ep834 873549816956323 281474976710656 15625000001249 1249000000000000000 (ep835 (BSN.log_sum_c_succ qz151 0 1 rfl) (ep845 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep846 (@congrArg Complex Complex qz204 qz469 Complex.log (BSN.w_shift_mk qz151 Bool.false 78672 1000 1 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz468 Bool.false 16540118729986259 4503599627370496 781250001249 249800000000000000 Bool.false 866397622666659 562949953421312 15625000001249 2498000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz468) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 24782134336 16000000))) Bool.false 16540118729986259 4503599627370496 781250001249 249800000000000000 (Enclosure.clog_re_eq 5000 157344 4000 24782134336 16000000 rfl rfl rfl) (ep851 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz468) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz395)) Bool.false 866397622666659 562949953421312 15625000001249 2498000000000000000 (Enclosure.clog_im_eq 5000 157344 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz466 qz395)) (@HSub.hSub Real Real Real qz364 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz395 qz466))) Bool.false 866397622666659 562949953421312 15625000001249 2498000000000000000 (BSN.arctan_recip 157344 5000 rfl rfl) ep853)))) rfl rfl

noncomputable def ep855 := @ep756 ep750 Bool.false 16539027808293075 2251799813685248 781250001249 124900000000000000 Bool.false 873549816956323 281474976710656 15625000001249 1249000000000000000 Bool.true ep757 139134128752343920359 2251799813685248000 10706155295242996695851 ep754 Bool.false ep758 58951459825230291841 562949953421312000 299762894980289936863 ep750 (@ep759 2251799813685248000 10450155294833724375851 ep754 Bool.false 60698559459142937841 562949953421312000 274162894978243575263 ep750 (BSN.logGammaStirling_unfold 1 qz180) (ep829 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep830 15625000001249 1249000000000000000 (BSN.log_sum_c_eq qz151 2) (ep831 (BSN.log_sum_c_succ qz151 1 2 rfl) (ep854 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz205 := (@HDiv.hDiv Real Real Real qz270 qz432 (2 : Real))

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff qz205 (Real.log Real.pi) 78672 2000 0 1 75021 65536 1 131072 368878257 8192000 4917 16384000 (@Enclosure.Real.IsNear.of_eq qz205 (Enclosure.sfrac Bool.false 78672 2000) Bool.false 78672 2000 0 1 (BSN.t_half_eq qz151 Bool.false 78672 1000 qz152) (Enclosure.Real.IsNear.const Bool.false 78672 2000)) EMRow20.d5 rfl

noncomputable def ep857 := @ep752 4917 16384000 ep753 33602339024902562689 562949953421312000 913896194980289936863 ep750 (@ep755 299762894980289936863 ep750 (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep856 rfl rfl

noncomputable def ep858 := nat_lit 32550697355620047140042237762604488541043605199518538049266878872677420892160

noncomputable def ep859 := nat_lit 65315075109354681604733012467389478406872153365733984620088367526703005696

noncomputable def ep860 := nat_lit 85146078190732596834655340691397887023407839655194506534885492071492868898816

noncomputable def ep861 := BSN.sin_dyadic_bound_f 1686074184 1073741824 3 2 524288 160029 ep858 ep57 ep859 ep860 ep60 ep859 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686074184) qz283 0 2 ep858 ep57 ep859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686074184) qz284 0 2 ep860 ep60 ep859 rfl rfl rfl rfl) rfl rfl

noncomputable def ep862 := @ep749 131072 Bool.true 524287 524288 1 79936 (@ep751 3911827 65536 59 131072 ep857 rfl) (Enclosure.sfrac_false_div 3911827 65536) (BSN.cos_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14830865369959009091584) qz353) 226375608064910080 72057594037927936 Bool.false 524287 524288 9 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 3911827 65536 226375608064910080 72057594037927936 9 14830865369959009091584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 14830865369959009091584 9444732965739290427392 1686074184 1073741824 160029 159872 (ep861 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep863 := nat_lit 1276024527397136105472000

noncomputable def ep864 := nat_lit 51921770336288635240469443

noncomputable def ep865 := nat_lit 7968773173595114978672640000

noncomputable abbrev qz470 := (@HPow.hPow Complex Complex Complex qz514 qz528 qz530)

noncomputable abbrev qz206 := qz470

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz369 qz398 (@HSub.hSub Complex Complex Complex qz361 qz425 (1 : Complex))) qz368)

noncomputable def ep866 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz146 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz66 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) Bool.false 262307980770939090870299 212670754566189350912000 ep746

noncomputable def ep867 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz66 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) Bool.false 370012824885 274877906944 2192818504809 343322505773056

noncomputable def ep868 := nat_lit 72102668729022736799738008495456256

noncomputable def ep869 := nat_lit 10556229001265982435728453506433024

noncomputable def ep870 := @ep867 Bool.false 10925462587 274877906944 2192893464793 343322505773056 Bool.true 23967869996113213859701 212670754566189350912000 171524968609817151852217 ep747 Bool.true 12314300812816453164679 ep863 1023066287024653585049443 ep865 Bool.false ep868 262307980770939090870299 212670754566189350912000 ep746 ep747 Bool.false ep869 38403337389412563191321 ep863

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (BSN.headSumC qz146 20) Bool.false 370012824885 274877906944 2192818504809 343322505773056 Bool.false 10925462587 274877906944 2192893464793

noncomputable abbrev qz208 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz426)

noncomputable def ep872 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 19) qz208) Bool.false 370012824885 274877906944 2192818504809 343322505773056 Bool.false 10925462587 274877906944 2192893464793 343322505773056

noncomputable def ep873 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 19) qz208 Bool.false 163799721255 137438953472 66053874287 10728828305408 Bool.true 35741105507 274877906944 2113754771279 343322505773056 Bool.false

noncomputable abbrev qz209 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz426)

noncomputable def ep874 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 18) qz209) Bool.false 163799721255 137438953472 66053874287 10728828305408 Bool.true 35741105507 274877906944 2113754771279 343322505773056

noncomputable def ep875 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 18) qz209 Bool.false 75979691315 68719476736 1016337597757 171661252886528 Bool.false 12282426909 137438953472 508083952435 85830626443264 Bool.false

noncomputable abbrev qz210 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz426)

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 18) (@HAdd.hAdd Complex Complex Complex qz4 qz160 qz210) Bool.false 75979691315 68719476736 1016337597757 171661252886528 Bool.false 12282426909 137438953472 508083952435 85830626443264

noncomputable def ep877 := @Enclosure.Complex.IsNear.addLitP qz160 qz210 Bool.false 369749615355 274877906944 1948875478969 343322505773056 Bool.false 17548081099 137438953472 121817454035 21457656610816 Bool.true

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz432 qz401)

noncomputable def ep878 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.true 65830850095 274877906944 83799716545 343322505773056 Bool.true 2632827095 68719476736 20814136295 85830626443264 (BSN.cpow_neg_s_mk qz151 78672 1000 17 qz152 rfl)

noncomputable def ep879 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz401 78672 1000 0 1 3189913004350711 1125899906842624 3906250001249 312250000000000000 15684802242392445987 70368744177664000 19207031256141333 19515625000000000000 qz153 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 26758929747600409100288 9444732965739290427392 1000000000319744 79936000000000000000 3189913004350711 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep429 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep880 := nat_lit 21276061789786706682255686038475364911078706249936378286182619539145023656385

noncomputable def ep881 := nat_lit 27943347018001330041327596248190525170606413614240132393983478320847491521

noncomputable def ep882 := nat_lit 55677777363793182014412266373509837726358486937315078154221363637622261256641

noncomputable def ep883 := BSN.sin_dyadic_bound_f 1516298841 1073741824 3 2 524288 160029 ep880 ep57 ep881 ep882 ep60 ep881 517705 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1516298841) qz283 0 2 ep880 ep57 ep881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1516298841) qz284 0 2 ep882 ep60 ep881 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116860883) qz19)

noncomputable def ep884 := @Enclosure.Real.IsNear.cos_image qz211 qz471 Bool.false 116860883 524288 517 524288 Bool.true 517705 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 15684802242392445987 70368744177664000 19207031256141333 19515625000000000000 116860883 524288 517 524288 (ep879 rfl) rfl) (Enclosure.sfrac_false_div 116860883 524288) (BSN.cos_reduce1 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106700045295471963406336) qz22) 226375608064910080 72057594037927936 Bool.false 517705 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 116860883 524288 226375608064910080 72057594037927936 35 106700045295471963406336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 517705 524288 106700045295471963406336 75557863725914323419136 1516298841 1073741824 160029 159872 (ep883 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep885 := nat_lit 11832453593000615414604860064152176295119550767126539106721003512112056472001

noncomputable def ep886 := nat_lit 35441474084965843583731924999960147835017439474151137055375043579694474432961

noncomputable def ep887 := BSN.cos_dyadic_bound_f 1516298841 1073741824 3 2 524288 160029 ep885 ep64 ep881 ep886 ep66 ep881 82820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1516298841) qz287 0 2 ep885 ep64 ep881 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1516298841) qz288 0 2 ep886 ep66 ep881 rfl rfl rfl rfl) rfl rfl

noncomputable def ep888 := @Enclosure.Real.IsNear.sin_image qz211 qz471 Bool.false 116860883 524288 517 524288 Bool.false 82820 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 15684802242392445987 70368744177664000 19207031256141333 19515625000000000000 116860883 524288 517 524288 (ep879 rfl) rfl) (Enclosure.sfrac_false_div 116860883 524288) (BSN.sin_reduce1 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106700045295471963406336) qz22) 226375608064910080 72057594037927936 Bool.false 82820 524288 35 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 116860883 524288 226375608064910080 72057594037927936 35 106700045295471963406336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 82820 524288 106700045295471963406336 75557863725914323419136 1516298841 1073741824 160029 159872 (ep887 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep889 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.true 65830850095 274877906944 83799716545 343322505773056 Bool.true 2632827095 68719476736 20814136295 85830626443264 (@Enclosure.Real.IsNear.mulLit_ft qz125 (Real.cos qz211) 127159 524288 1 524288 517705 524288 653925 654835712 65830850095 274877906944 83799716545 343322505773056 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.true 517705 524288 41851200 41909485568 517705 524288 653925 654835712 (ep884 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 127159 524288 1 524288 20705 131072 653925 654835712 2632827095 68719476736 20814136295 85830626443264 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 20705 131072 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 82820 524288 41851200 41909485568 20705 131072 653925 654835712 (ep888 rfl rfl) rfl)) rfl)

noncomputable def ep890 := @ep877 65830850095 274877906944 83799716545 343322505773056 Bool.true 2632827095 68719476736 20814136295 85830626443264 Bool.false 83540554075673659965440 75979691315 68719476736 1016337597757 171661252886528 Bool.false 844041950234645889024 12282426909 137438953472 508083952435 85830626443264 EMRow20.d12 (ep878 ep889) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz432 qz406)

noncomputable def ep891 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 11840338625 137438953472 40524390835 171661252886528 Bool.true 60305959325 274877906944 81418961539 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 18 qz152 rfl)

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz406 78672 1000 0 1 3254268794313975 1125899906842624 3906250001249 312250000000000000 640049586465672603 2814749767106560 19207031256141333 19515625000000000000 qz153 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz407) Bool.false 27298785242132565196800 9444732965739290427392 1000000000319744 79936000000000000000 3254268794313975 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep440 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep893 := nat_lit 6093438093317871725714709715986414052976722035167513976761239314972939264256

noncomputable def ep894 := nat_lit 7427589136938945956830531504611438119726808207013104553831711657112248576

noncomputable def ep895 := nat_lit 18265459101679737285230468084950019282690712489088515721176054521604593295616

noncomputable def ep896 := BSN.cos_dyadic_bound_f 1284860518 1073741824 3 2 524288 160029 ep893 ep64 ep894 ep895 ep66 ep894 191630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1284860518) qz287 0 2 ep893 ep64 ep894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1284860518) qz288 0 2 ep895 ep66 ep894 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119218525) qz19)

noncomputable def ep897 := @Enclosure.Real.IsNear.cos_image qz212 qz472 Bool.false 119218525 524288 517 524288 Bool.false 191630 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 640049586465672603 2814749767106560 19207031256141333 19515625000000000000 119218525 524288 517 524288 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 119218525 524288) (BSN.cos_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90414021137602225111040) qz22) 226375608064910080 72057594037927936 Bool.false 191630 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 119218525 524288 226375608064910080 72057594037927936 36 90414021137602225111040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 191630 524288 90414021137602225111040 75557863725914323419136 1284860518 1073741824 160029 159872 (ep896 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep898 := nat_lit 10962246496662617949521013063571856144862318216735914674527165397625600876800

noncomputable def ep899 := nat_lit 28698619965989907764815403829775966622445561449592231502103038984431725322496

noncomputable def ep900 := BSN.sin_dyadic_bound_f 1284860518 1073741824 3 2 524288 160029 ep898 ep57 ep894 ep899 ep60 ep894 488011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1284860518) qz283 0 2 ep898 ep57 ep894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1284860518) qz284 0 2 ep899 ep60 ep894 rfl rfl rfl rfl) rfl rfl

noncomputable def ep901 := @Enclosure.Real.IsNear.sin_image qz212 qz472 Bool.false 119218525 524288 517 524288 Bool.false 488011 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 640049586465672603 2814749767106560 19207031256141333 19515625000000000000 119218525 524288 517 524288 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 119218525 524288) (BSN.sin_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90414021137602225111040) qz22) 226375608064910080 72057594037927936 Bool.false 488011 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q0 119218525 524288 226375608064910080 72057594037927936 36 90414021137602225111040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488011 524288 90414021137602225111040 75557863725914323419136 1284860518 1073741824 160029 159872 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 11840338625 137438953472 40524390835 171661252886528 Bool.true 60305959325 274877906944 81418961539 343322505773056 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz212) 123575 524288 1 524288 95815 262144 653925 654835712 11840338625 137438953472 40524390835 171661252886528 qz409 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 191630 524288 41851200 41909485568 95815 262144 653925 654835712 (ep897 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 123575 524288 1 524288 488011 524288 653925 654835712 60305959325 274877906944 81418961539 343322505773056 qz409 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 488011 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 488011 524288 41851200 41909485568 488011 524288 653925 654835712 (ep901 rfl rfl) rfl)) rfl)

noncomputable def ep903 := @ep875 11840338625 137438953472 40524390835 171661252886528 Bool.true 60305959325 274877906944 81418961539 343322505773056 Bool.false 11256231134146257223680 163799721255 137438953472 66053874287 10728828305408 Bool.true 4912220136814415970304 35741105507 274877906944 2113754771279 343322505773056 (ep876 (BSN.head_sum_c_succ qz146 17 18 rfl rfl) (ep890 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep891 ep902) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz432 qz411)

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 42413382375 274877906944 79094527625 343322505773056 Bool.false 23333284047 137438953472 39569346757 171661252886528 (BSN.cpow_neg_s_mk qz151 78672 1000 19 qz152 rfl)

noncomputable def ep905 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz411 78672 1000 0 1 3315141365800183 1125899906842624 3906250001249 312250000000000000 16300550095639499811 70368744177664000 19207031256141333 19515625000000000000 qz153 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 27809421382282341515264 9444732965739290427392 1000000000319744 79936000000000000000 3315141365800183 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep451 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep906 := nat_lit 393633346292597501710825663835700625

noncomputable def ep907 := BSN.sin_dyadic_bound_f 792087155 1073741824 2 1 524288 160029 ep906 ep75 ep906 ep906 ep76 ep906 352625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 792087155) qz283 0 1 ep906 ep75 ep906 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 792087155) qz284 0 1 ep906 ep76 ep906 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60724281) qz29)

noncomputable def ep908 := @Enclosure.Real.IsNear.cos_image qz213 qz473 Bool.false 60724281 262144 517 524288 Bool.false 352625 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 16300550095639499811 70368744177664000 19207031256141333 19515625000000000000 60724281 262144 517 524288 (ep905 rfl) rfl) (Enclosure.sfrac_false_div 60724281 262144) (BSN.cos_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27869089202656449134592) qz298) 226375608064910080 72057594037927936 Bool.false 352625 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 60724281 262144 226375608064910080 72057594037927936 36 27869089202656449134592 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 352625 524288 27869089202656449134592 37778931862957161709568 792087155 1073741824 160029 159872 (ep907 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep909 := nat_lit 879178766675233633196001166815104356409009258420274989157077556920606190625

noncomputable def ep910 := nat_lit 154947211313507983344959358964052689821339779285740721368674284625390625

noncomputable def ep911 := nat_lit 2637226405603073883621313581727384963847385095702253486028495322192567790625

noncomputable def ep912 := BSN.cos_dyadic_bound_f 792087155 1073741824 3 2 524288 160029 ep909 ep64 ep910 ep911 ep66 ep910 387986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 792087155) qz287 0 2 ep909 ep64 ep910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 792087155) qz288 0 2 ep911 ep66 ep910 rfl rfl rfl rfl) rfl rfl

noncomputable def ep913 := @Enclosure.Real.IsNear.sin_image qz213 qz473 Bool.false 60724281 262144 517 524288 Bool.true 387986 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 16300550095639499811 70368744177664000 19207031256141333 19515625000000000000 60724281 262144 517 524288 (ep905 rfl) rfl) (Enclosure.sfrac_false_div 60724281 262144) (BSN.sin_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27869089202656449134592) qz298) 226375608064910080 72057594037927936 Bool.false 387986 524288 36 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q3 60724281 262144 226375608064910080 72057594037927936 36 27869089202656449134592 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 387986 524288 27869089202656449134592 37778931862957161709568 792087155 1073741824 160029 159872 (ep912 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep914 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 42413382375 274877906944 79094527625 343322505773056 Bool.false 23333284047 137438953472 39569346757 171661252886528 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz213) 120279 524288 1 524288 352625 524288 653925 654835712 42413382375 274877906944 79094527625 343322505773056 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 352625 524288 41851200 41909485568 352625 524288 653925 654835712 (ep908 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 120279 524288 1 524288 193993 262144 653925 654835712 23333284047 137438953472 39569346757 171661252886528 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 193993 262144 653925 654835712 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 387986 524288 41851200 41909485568 193993 262144 653925 654835712 (ep913 rfl rfl) rfl)) rfl)

noncomputable def ep915 := @ep873 42413382375 274877906944 79094527625 343322505773056 Bool.false 23333284047 137438953472 39569346757 171661252886528 Bool.false 50854175423412798750720 370012824885 274877906944 2192818504809 343322505773056 Bool.false 1501584144154769752064 10925462587 274877906944 2192893464793 343322505773056 (ep874 (BSN.head_sum_c_succ qz146 18 19 rfl rfl) (ep903 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep904 ep914) rfl rfl

noncomputable def ep916 := @Enclosure.Complex.IsNear.mul qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.true 23967869996113213859701 212670754566189350912000 171524968609817151852217 ep747 Bool.true

noncomputable abbrev qz214 := (Complex.re qz470)

noncomputable abbrev qz215 := (Complex.im qz470)

noncomputable def ep917 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 190048120675669272283 1701366036529514807296 1197512403048329896611

noncomputable def ep918 := nat_lit 10625030898126819971563520

noncomputable def ep919 := nat_lit 664064431132926248222720000

noncomputable def ep920 := nat_lit 20389059989670908066993609610577405697589248

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 30676061805 137438953472 38658592737 171661252886528 92929849609

noncomputable abbrev qz474 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz531 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz216 := (Real.cos qz474)

noncomputable abbrev qz217 := (Real.sin qz474)

noncomputable abbrev qz475 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 qz216) (@HMul.hMul Real Real Real qz0 qz133 qz475)) Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (BSN.cpow_neg_s_mk qz151 78672 1000 20 qz152 rfl)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz136 78672 1000 0 1 3372891496062199 1125899906842624 3906250001249 312250000000000000 16584507486137832483 70368744177664000 19207031256141333 19515625000000000000 qz153 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 3906250001249 312250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz420 Bool.false 28293864586999331028992 9444732965739290427392 1000000000319744 79936000000000000000 3372891496062199 1125899906842624 3906250001249 312250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 79936 1000000000000000 rfl rfl rfl rfl (ep472 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep924 := BSN.cos_dyadic_bound_f 65043072 1073741824 1 0 524288 160029 0 1 1 0 1 1 523326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65043072) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65043072) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz218 := qz474

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 123564209) qz19)

noncomputable def ep925 := @Enclosure.Real.IsNear.cos_image qz218 qz476 Bool.false 123564209 524288 517 524288 Bool.true 523326 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 16584507486137832483 70368744177664000 19207031256141333 19515625000000000000 123564209 524288 517 524288 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 123564209 524288) (BSN.cos_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4576999309026418229248) qz22) 226375608064910080 72057594037927936 Bool.false 523326 524288 37 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 123564209 524288 226375608064910080 72057594037927936 37 4576999309026418229248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523326 524288 4576999309026418229248 75557863725914323419136 65043072 1073741824 160029 159872 (ep924 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep926 := BSN.sin_dyadic_bound_f 65043072 1073741824 1 0 524288 160029 0 1 1 0 1 1 31739 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 65043072) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 65043072) qz284 0 0 rfl) rfl rfl

noncomputable def ep927 := @Enclosure.Real.IsNear.sin_image qz218 qz476 Bool.false 123564209 524288 517 524288 Bool.true 31739 524288 1 79936 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 16584507486137832483 70368744177664000 19207031256141333 19515625000000000000 123564209 524288 517 524288 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 123564209 524288) (BSN.sin_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4576999309026418229248) qz22) 226375608064910080 72057594037927936 Bool.false 31739 524288 37 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q2 123564209 524288 226375608064910080 72057594037927936 37 4576999309026418229248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 31739 524288 4576999309026418229248 75557863725914323419136 65043072 1073741824 160029 159872 (ep926 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep928 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 qz216) (@HMul.hMul Real Real Real qz0 qz133 qz475) Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (@Enclosure.Real.IsNear.mulLit_ft qz133 qz216 117235 524288 1 524288 261663 262144 653925 654835712 30676061805 137438953472 38658592737 171661252886528 qz422 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 523326 524288 41851200 41909485568 261663 262144 653925 654835712 (ep925 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 qz475 117235 524288 1 524288 31739 524288 653925 654835712 3720921665 274877906944 76703193311 343322505773056 qz422 (@Enclosure.Real.IsNear.neg qz217 Bool.true 31739 524288 653925 654835712 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 31739 524288 41851200 41909485568 31739 524288 653925 654835712 (ep927 rfl rfl) rfl)) rfl)

noncomputable def ep929 := @ep921 185686007520 0 1 190048120675669272283 1701366036529514807296 1197512403048329896611 ep918 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (ep922 ep928))

noncomputable def ep930 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 92929849609 185686007520 0 1 Bool.false

noncomputable def ep931 := @Enclosure.Complex.IsNear.addLitP qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) Bool.false 385595849 773691698 0 1 Bool.true 98340000

noncomputable def ep932 := @ep931 386845849 0 1 Bool.false 1 480 0 1 Bool.false 1639 5000 0 1 Bool.false 185859699218 92929849609 185686007520 0 1 Bool.false 142340346511 142340346511 1934229245000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz369 qz398 (@HSub.hSub Complex Complex Complex qz361 qz425 (1 : Complex)))

noncomputable def ep933 := @Enclosure.Complex.IsNear.addLitP qz219 qz93 Bool.true 40000000 24758134336 0 1 Bool.true 6293760000 24758134336 0 1

noncomputable def ep934 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 40000000 24758134336) (Enclosure.sfrac Bool.true 6293760000 24758134336)) Bool.true 40000000 24758134336 0 1 Bool.true 6293760000 24758134336 0 1

noncomputable def ep935 := @ep933 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 24678134336 385595849 773691698 0 1 Bool.true 6293760000 98340000 386845849 0 1 (ep934 (BSN.N_div_s_sub_one_mk qz151 78672 1000 20 qz152 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 24758134336) (Enclosure.sfrac Bool.true 6293760000 24758134336) Bool.true 40000000 24758134336 0 1 Bool.true 6293760000 24758134336 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 24758134336) (Enclosure.Real.IsNear.const Bool.true 6293760000 24758134336))) qz94 rfl

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 480 0 1

noncomputable def ep937 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep938 := @ep937 0 1 0 1 Bool.false 1 480 0 1 Bool.false 1639 5000 0 1 Bool.false 1 1 480 0 1 Bool.false 1639 1639 5000 0

noncomputable def ep939 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep940 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 480 0 1 Bool.false 1639 5000 0 1

noncomputable def ep941 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 480 0 1 0 1 0

noncomputable def ep942 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 20 0 1 1

noncomputable def ep943 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep945 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz146 Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 (BSN.ascPochhammer_one_eval qz146)

noncomputable def ep946 := ep945 (@Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk qz88 qz151) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_crit_mk qz151 Bool.false 78672 1000 qz152) (@Enclosure.Complex.IsNear.mk qz88 qz151 Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 qz379 qz153))

noncomputable def ep947 := @ep944 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 78672 1000 0 1 0 1 0

noncomputable def ep949 := @ep948 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep950 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1639 250 0 1 0 1 0 1 1639

noncomputable def ep951 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 78672 1000 0 1 1639 250 0

noncomputable def ep952 := @ep951 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep954 := @ep953 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep496) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep955 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 (@ep943 1 24 0 1 (ep947 rfl) (ep949 rfl) rfl rfl) (@ep950 1639 250 0 1 (ep952 rfl) (ep954 rfl) rfl rfl)

noncomputable def ep956 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 ep955

noncomputable def ep957 := @ep942 480 0 1 ep956 qz143

noncomputable def ep958 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1639 250 0 1 0 1 0 1 0

noncomputable def ep959 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1639 250 0 1 ep955

noncomputable def ep960 := @ep958 1 0 1 ep959 qz144

noncomputable def ep961 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 1639 5000 0

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep963 := @ep962 1 0 1 ep956 qz144

noncomputable def ep964 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1639 250 0 1 1 20 0 1 1639

noncomputable def ep965 := @ep964 5000 0 1 ep959 qz143

noncomputable def ep966 := @ep938 1 (@ep939 0 1 0 1 (BSN.bern_sum_base qz146 20) qz109) (ep940 (@ep941 1 1 1 480 0 1 (ep957 rfl) (ep960 rfl) rfl rfl) (@ep961 1 1639 1639 5000 0 1 (ep963 rfl) (ep965 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep967 := ep932 (ep935 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep936 Bool.false 1639 5000 0 1 (BSN.bern_sum_succ qz146 20 0 1 1 rfl rfl) (ep966 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 3720921665 274877906944 76703193311 343322505773056 142340346511

noncomputable def ep969 := @ep968 1934229245000 0 1 105927455827277412163 106335377283094675456000 10917959114387957387921 ep919 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (ep922 ep928))

noncomputable def ep970 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 92929849609 185686007520 0 1 Bool.false

noncomputable def ep971 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 873288253383310422471 53167688641547337728000 5502677485812207890607

noncomputable def ep972 := nat_lit 332032215566463124111360000

noncomputable def ep973 := nat_lit 63750185388760919829381120

noncomputable def ep974 := nat_lit 5237783291633427884563261451739302509674496

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 30676061805 137438953472 38658592737 171661252886528 142340346511

noncomputable def ep976 := @ep975 1934229245000 0 1 873288253383310422471 53167688641547337728000 5502677485812207890607 ep972 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (ep922 ep928))

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 3720921665 274877906944 76703193311 343322505773056 92929849609

noncomputable def ep978 := @ep977 185686007520 0 1 69156938147063975797 10208196219177088843776 7128016218921284765399 ep973 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 30676061805 137438953472 38658592737 171661252886528 Bool.false 3720921665 274877906944 76703193311 343322505773056 (ep922 ep928))

noncomputable abbrev qz477 := (ep967 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep979 := @ep916 12314300812816453164679 ep863 1023066287024653585049443 ep865 (@ep917 ep918 105927455827277412163 106335377283094675456000 10917959114387957387921 ep919 ep920 23967869996113213859701 212670754566189350912000 171524968609817151852217 ep747 (ep929 (@ep930 142340346511 1934229245000 0 1 qz477) rfl) (ep969 (@ep970 142340346511 1934229245000 0 1 qz477) rfl) rfl rfl) (@ep971 ep972 69156938147063975797 10208196219177088843776 7128016218921284765399 ep973 ep974 12314300812816453164679 ep863 1023066287024653585049443 ep865 (ep976 (@ep970 142340346511 1934229245000 0 1 qz477) rfl) (ep978 (@ep930 142340346511 1934229245000 0 1 qz477) rfl) rfl rfl)

noncomputable def ep980 := @ep870 ep864 ep865 (@ep871 343322505773056 (BSN.head_sum_c_eq qz146 20) (ep872 (BSN.head_sum_c_succ qz146 19 20 rfl rfl) (ep915 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep979 rfl rfl rfl

noncomputable def ep981 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz146 1 20) Bool.false 262307980770939090870299 212670754566189350912000 ep746 ep747 Bool.false 38403337389412563191321 ep863 ep864 ep865 (@ep866 ep747 Bool.false 38403337389412563191321 ep863 ep864 ep865 (BSN.zetaApproximant_eq_folded' qz146 1 20 rfl) (ep980 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep982 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20)) 271 524288 75739

noncomputable def ep983 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 271 524288 4847296

noncomputable def ep984 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz452 Bool.false 3911827 65536 59

noncomputable def ep985 := nat_lit 18112749675393072714070013429210222290982834956783958464979416425943768498176

noncomputable def ep986 := nat_lit 54207618875960508779000574262695887916134760563620407425698072542777899483136

noncomputable def ep987 := BSN.cos_dyadic_bound_f 1686074184 1073741824 3 2 524288 160029 ep985 ep64 ep859 ep986 ep66 ep859 271 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686074184) qz287 0 2 ep985 ep64 ep859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686074184) qz288 0 2 ep986 ep66 ep859 rfl rfl rfl rfl) rfl rfl

noncomputable def ep988 := @ep984 131072 Bool.false 271 524288 1 79936 (@ep751 3911827 65536 59 131072 ep857 rfl) (Enclosure.sfrac_false_div 3911827 65536) (BSN.sin_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14830865369959009091584) qz353) 226375608064910080 72057594037927936 Bool.false 271 524288 9 1000000000000000 159872 79936 (BSN.sin_reduce_arg_pos_rat_q1 3911827 65536 226375608064910080 72057594037927936 9 14830865369959009091584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 271 524288 14830865369959009091584 9444732965739290427392 1686074184 1073741824 160029 159872 (ep987 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep989 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz146 1 20) Bool.false 262307980770939090870299 212670754566189350912000 ep746 ep747 Bool.false 38403337389412563191321 ep863 ep864 ep865 (@ep866 ep747 Bool.false 38403337389412563191321 ep863 ep864 ep865 (BSN.zetaApproximant_eq_folded' qz146 1 20 rfl) (ep980 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow20.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz151) Bool.true ep730 ep731 ep732 ep733 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz151) ep734 Bool.true ep730 ep731 ep732 ep733 (@Eq.refl Real ep734) (@ep735 Bool.true ep730 ep731 ep732 ep733 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz364 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) (zetaApproximant qz146 1 20)) (@ep737 ep738 ep739 ep740 ep741 ep731 ep742 ep743 ep744 ep730 ep731 ep732 ep733 (@ep745 163708928 262307980770939090870299 212670754566189350912000 ep746 ep747 ep736 ep738 ep739 ep740 (@ep748 10477371392 524287 524288 75739 163708928 (ep862 rfl rfl) rfl) ep981 rfl) (@ep982 163708928 38403337389412563191321 ep863 ep864 ep865 ep741 ep731 ep742 ep743 (@ep983 10477371392 271 524288 75739 163708928 (ep988 rfl rfl) rfl) ep989 rfl) rfl rfl))

theorem EMRow20.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow20.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow20.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow20.d17 : @Eq Nat (Nat.pow 20 (Nat.succ (Nat.mul 2 3))) 1280000000 := @Eq.refl Nat 1280000000

noncomputable abbrev qz534 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz478 := qz534

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz478) (@HAdd.hAdd Real Real Real qz389 (Complex.re qz272) qz291))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz479 := (@HPow.hPow Complex Complex Complex qz514 qz528 (@HSub.hSub Complex Complex Complex qz521 qz515 qz516))

noncomputable abbrev qz223 := qz479

noncomputable def ep990 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 1260158831 154618822656 45881759 463856467968 47166457941964173 126100789566373888 27204962595

noncomputable def ep991 := nat_lit 7451729219408379921003708416

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) 4427 294912 1 884736 284653 524288 3433 524288 1260158831 154618822656

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz535 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz480 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz535 qz224 2))

noncomputable def ep993 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz480 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep994 := nat_lit 781950621441006189802102638025

noncomputable def ep995 := nat_lit 19807040628566084398385987584

noncomputable def ep996 := nat_lit 26986075409044041160201671

noncomputable def ep997 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz481 := (@HPow.hPow Real Nat Real qz535 qz224 1)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff qz481 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep994 ep995 ep996 ep997

noncomputable def ep999 := ep998 (@Enclosure.Real.IsNear.of_eq qz481 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz482 := (@HPow.hPow Real Nat Real qz535 qz224 2)

noncomputable def ep1000 := @Enclosure.Real.IsNear.inv_image qz482 ep994 ep995 ep996 ep997 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz482 (@HMul.hMul Real Real Real qz0 qz481 qz224) Bool.false ep994 ep995 ep996 ep997 (BSN.pow_succ_r qz224 1 2 rfl) ep999) rfl rfl rfl

noncomputable def ep1001 := ep993 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz480 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep1000 rfl rfl rfl) rfl)

noncomputable def ep1002 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 284653 524288 3433 524288

noncomputable def ep1003 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 284653 524288 3433 524288

noncomputable def ep1004 := nat_lit 2977860288674661033480740857820688077

noncomputable def ep1005 := nat_lit 10100637139225004137517912231510016000

noncomputable def ep1006 := nat_lit 270743348238349438086739180488992568791736616782031

noncomputable def ep1007 := nat_lit 38093337889691249582986011666739555169652965376000000

noncomputable def ep1008 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)))) ep1004 ep1005 ep1006 ep1007 140610 144043

noncomputable def ep1009 := nat_lit 1726623294514698853504345988969310680170714969

noncomputable def ep1010 := nat_lit 5860509764753932785887087764698543937290240000

noncomputable def ep1011 := nat_lit 524888180500452821782088204093545567073815459344437

noncomputable def ep1012 := nat_lit 76186675779382499165972023333479110339305930752000000

noncomputable def ep1013 := nat_lit 1166651733171819840867942747052030085920561

noncomputable def ep1014 := nat_lit 44262709269989478377040418358505521359087397919

noncomputable def ep1015 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))) ep1009 ep1010 ep1011 ep1012 ep1013 ep1010 ep1014

noncomputable def ep1016 := nat_lit 203164468745019997775925395555944294238149148672000

noncomputable def ep1017 := nat_lit 10125729851429318732951239547853196325225692576380553772917501794954672496525167506227200000

noncomputable def ep1018 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20)) 41552656888756209273563 76553966355466734796800 ep284 ep285 41552656888756209273563 76553966355466734796800 ep284 ep285 ep1009

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)) 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 1080116536847677302919 76553966355466734796800 201105850061754563100741 ep414 ep1013

noncomputable def ep1020 := @ep990 126100789566373888 ep991 433747727622300149 1134907106097364992 337508113266353 3404721318292094976 (@ep992 45881759 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz480) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow20.d14 EMRow20.d15 rfl) (ep1001 rfl)) (ep1002 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 20)) (@ep1003 284653 524288 3433 524288 (@ep1008 262144 (@ep1015 ep1016 ep1017 ep1004 ep1005 ep1006 ep1007 (@ep1018 ep1010 ep1011 ep1012 ep532 ep532 rfl) (@ep1019 ep1010 ep1014 ep1016 ep540 ep540 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz478)

noncomputable abbrev qz483 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1021 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz483) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 47166457941964173 126100789566373888 27204962595 126100789566373888 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz16 3)

noncomputable def ep1022 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz483) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 39977153 1835008 1 1835008 1179835341 68719476736 651 68719476736

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz483 39977153 524288 1 524288 2 7 0 1 39977153 1835008

noncomputable abbrev qz484 := (Complex.re qz534)

noncomputable abbrev qz485 := (Complex.im qz534)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz267 qz484 qz484) (@HMul.hMul Real Real Real qz267 qz485 qz485))

noncomputable abbrev qz227 := qz478

noncomputable def ep1024 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 39977153 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1025 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 39977153 524288 1 524288 39977153

noncomputable def ep1026 := @Enclosure.Real.IsNear.sqrt_image qz226 58141189 10000 0 1 19988576 19988577 262144

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz484 qz484)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz485 qz485)

noncomputable def ep1027 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 58018689 10000 0 1

noncomputable abbrev qz230 := qz484

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz486 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1029 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz486 qz16) Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 76170 1000 3 qz17)

noncomputable abbrev qz487 := (ep1029 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz21))

noncomputable def ep1030 := @ep1028 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz487)

noncomputable def ep1031 := ep1030 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz487)

noncomputable abbrev qz231 := qz485

noncomputable def ep1032 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 76170 1000 0 1 76170 1000 0 1 58018689 10000

noncomputable def ep1033 := @ep1032 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz487)

noncomputable def ep1034 := ep1033 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz487)

noncomputable def ep1035 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1179835341 68719476736

noncomputable def ep1036 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1179835341 68719476736

noncomputable def ep1037 := nat_lit 3029109408833544487847140442009345346220945963994404997

noncomputable def ep1038 := nat_lit 10276183387482911143619658980036364981955775692800000000000

noncomputable def ep1039 := nat_lit 84830199189257606549215407425727505840869211004588849606056021

noncomputable def ep1040 := nat_lit 260918886078397279735641465307872874482682162053120000000000000000000000

noncomputable def ep1041 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1037 ep1038 ep1039 ep1040

noncomputable def ep1042 := nat_lit 5179777031410518460132352900936723187144908606518449

noncomputable def ep1043 := nat_lit 22300745198530623141535718272648361505980416000000000000

noncomputable def ep1044 := nat_lit 12636777413348971344647987442672452456466604113968126072711209

noncomputable def ep1045 := nat_lit 48922291139699489950432774745226163965502905384960000000000000000000000

noncomputable def ep1046 := nat_lit 3211340763797887907090761126288516507922860390553518489

noncomputable def ep1047 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1042 ep1043 ep1044 ep1045 ep1046

noncomputable def ep1048 := nat_lit 51380916937414555718098294900181824909778878464000000000000

noncomputable def ep1049 := nat_lit 52302158954189278133278423194423278219141967190276531654788719

noncomputable def ep1050 := nat_lit 782756658235191839206924395923618623448046486159360000000000000000000000

noncomputable def ep1051 := nat_lit 337756985524343007846235721763196988084114474695308680996871759051521426771803241888349895272693760000000000000

noncomputable def ep1052 := nat_lit 71970667854414957208243143

noncomputable def ep1053 := nat_lit 4722366482869645213696000000

noncomputable def ep1054 := nat_lit 1874377146908045608122963953

noncomputable def ep1055 := nat_lit 221183840141407007696486400000000000

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1052 ep1053 ep1054 ep1055 ep1052 ep1053 ep1054

noncomputable def ep1057 := nat_lit 1792021418342394675266522683

noncomputable def ep1058 := nat_lit 226673591177742970257408000000

noncomputable def ep1059 := nat_lit 3738813898063767553286208937

noncomputable def ep1060 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1052 ep1053 ep1054 ep1055 Bool.true ep1057 ep1058 ep1059

noncomputable def ep1061 := nat_lit 884735360565628030785945600000000000

noncomputable def ep1062 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1052 ep1053 ep1054 ep1055 Bool.true ep1057 ep1058 ep1059 ep1061

noncomputable def ep1063 := nat_lit 1871207554821514879032791

noncomputable def ep1064 := nat_lit 4533471823554859405148160000

noncomputable def ep1065 := nat_lit 3911073994730062509366749

noncomputable def ep1066 := nat_lit 17694707211312560615718912000000000

noncomputable def ep1067 := nat_lit 1774076217376496844973655207

noncomputable def ep1068 := nat_lit 113336795588871485128704000000

noncomputable def ep1069 := nat_lit 3650977443947839653511759181

noncomputable abbrev qz232 := (Complex.re qz479)

noncomputable abbrev qz233 := (Complex.im qz479)

noncomputable def ep1070 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1063 ep1064 ep1065 ep1066 ep1067 ep1068 ep1069

noncomputable def ep1071 := nat_lit 442367680282814015392972800000000000

noncomputable def ep1072 := nat_lit 7830647876169976238571300385258465451526797257605120000

noncomputable def ep1073 := nat_lit 3686397335690116794941440000

noncomputable def ep1074 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 174043567 4800000 0 1 53756872117586365 4722366482869645213696 22471810145847347 ep1073 ep1063

noncomputable def ep1075 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 174043567 4800000 0 1 0 1 0 1 174043567

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 522130701 20000 0 1 174043567 4800000 0

noncomputable def ep1077 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow20.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz23)

noncomputable abbrev qz488 := (@HAdd.hAdd Complex Complex Complex qz513 qz512 qz517)

noncomputable abbrev qz234 := qz488

noncomputable def ep1078 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1

noncomputable abbrev qz235 := (Complex.re qz488)

noncomputable abbrev qz236 := (Complex.im qz488)

noncomputable def ep1079 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 58011189 4000 0 1 58018689 5000 0 1

noncomputable def ep1080 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 58011189 10000 0 1 5 2 0 1 58011189 4000

noncomputable abbrev qz489 := (@HAdd.hAdd Complex Complex Complex qz513 qz512 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz489

noncomputable def ep1081 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1

noncomputable abbrev qz238 := (Complex.re qz489)

noncomputable abbrev qz239 := (Complex.im qz489)

noncomputable def ep1082 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 58018689 10000 0 1

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1084 := @ep1083 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable abbrev qz490 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1085 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz490 qz16) Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 76170 1000 1 qz17)

noncomputable abbrev qz491 := (ep1085 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz21))

noncomputable def ep1086 := ep1084 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz491)

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 76170 1000 0 1 76170 1000 0 1 58018689 10000

noncomputable def ep1088 := @ep1087 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep1089 := ep1088 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz491)

noncomputable def ep1090 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 (@ep1082 232044756 58011189 10000 0 1 (ep1086 rfl) (ep1089 rfl) rfl rfl)

noncomputable def ep1091 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 7617 200 0 1 22851 200 0 1

noncomputable def ep1092 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 76170 1000 0 1 7617 200

noncomputable def ep1093 := @ep1092 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep1094 := ep1093 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz491)

noncomputable def ep1095 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 76170 1000 0 1 3 2 0 1 22851 200

noncomputable def ep1096 := @ep1095 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep498)

noncomputable def ep1097 := ep1096 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz491)

noncomputable abbrev qz240 := (ep1081 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1090 (@ep1091 6093600 7617 50 0 1 (ep1094 rfl) (ep1097 rfl) rfl rfl)))

noncomputable def ep1098 := @ep1080 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz240)

noncomputable abbrev qz492 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz492 qz16) Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 76170 1000 2 qz17)

noncomputable abbrev qz493 := (ep1099 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz21))

noncomputable def ep1100 := ep1098 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz493)

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 7617 50 0 1 76170 1000 0 1 58018689 5000

noncomputable def ep1102 := @ep1101 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz240)

noncomputable def ep1103 := ep1102 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz493)

noncomputable def ep1104 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 (@ep1079 522130701000 522130701 20000 0 1 (ep1100 rfl) (ep1103 rfl) rfl rfl)

noncomputable def ep1105 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 441871226613 1000000 0 1 7617 20 0 1

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 58011189 10000 0 1 76170 1000 0 1 441871226613 1000000

noncomputable def ep1107 := @ep1106 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz240)

noncomputable def ep1108 := ep1107 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz493)

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 7617 50 0 1 5 2 0 1 7617 20

noncomputable def ep1110 := @ep1109 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz240)

noncomputable def ep1111 := ep1110 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz493)

noncomputable abbrev qz241 := (ep1078 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1104 (@ep1105 8829807532260 441490376613 1000000 0 1 (ep1108 rfl) (ep1111 rfl) rfl rfl)))

noncomputable def ep1112 := @ep1076 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz241)

noncomputable def ep1113 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 441490376613 1000000 0 1 0 1 0

noncomputable def ep1114 := @ep1113 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz241)

noncomputable def ep1115 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 147163458871 240000000 0 1 0 1 0 1 147163458871

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 441490376613 1000000 0 1 147163458871 240000000 0

noncomputable def ep1117 := @ep1116 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz241)

noncomputable def ep1118 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 522130701 20000 0 1 0 1 0

noncomputable def ep1119 := @ep1118 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz241)

noncomputable def ep1120 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 (@ep1075 174043567 4800000 0 1 (ep1112 rfl) (ep1114 rfl) rfl rfl) (@ep1115 147163458871 240000000 0 1 (ep1117 rfl) (ep1119 rfl) rfl rfl)

noncomputable def ep1121 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 ep1120

noncomputable def ep1122 := nat_lit 1843198667845058397470720000

noncomputable def ep1123 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 53756872117586365 4722366482869645213696 22471810145847347 ep1073 Bool.true 60275704002432085 2361183241434822606848 24808994515059611 ep1122

noncomputable abbrev qz494 := (@Nat.cast Real Real.instNatCast 1280000000)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz494))

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz134) (@HMul.hMul Real Real Real qz0 qz242 qz417)) Bool.true 53756872117586365 4722366482869645213696 22471810145847347 ep1073 Bool.true 60275704002432085 2361183241434822606848 24808994515059611

noncomputable def ep1125 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz494) 2458582741758581 68719476736 1 68719476736 960383 960384 34359738368 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz494) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz494 qz18)) Bool.false 2458582741758581 68719476736 1 68719476736 (BSN.sqrt_natCast_div_one 1280000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz494 qz18)) Bool.false 2458582741758581 68719476736 1 68719476736 2458582741758581 68719476736 1 68719476736 (BSN.sqrt_enclosure 1280000000 1 1229291370879290 1229291370879291 34359738368 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1126 := nat_lit 3708536928388034760741486592

noncomputable def ep1127 := nat_lit 1237940039285380274899124224

noncomputable def ep1128 := nat_lit 12789760000000000000000000

noncomputable def ep1129 := BSN.log_dyadic_bound 4 36 6 5 38005766984454635520 34359738368 12789760000 157571184526884864 990904320 7667154041 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 36) 0 5 157571184526884864 38005766984454635520 990904320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz136 76170 1000 0 1 3372894687698167 1125899906842624 48830623 624500000000000000 25691338836196938039 112589990684262400 371942855391 62450000000000000000 qz21 (BSN.isNear_log_sfrac 20 1 3372894687698167 1125899906842624 48830623 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz420 Bool.false ep1126 ep1127 1000051159040000 ep1128 3372894687698167 1125899906842624 48830623 624500000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 7667154041 34359738368 24973259072661432 36028797018963968 12789760000 1000000000000000 rfl rfl rfl rfl (ep1129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1131 := nat_lit 4154129540333148102992068608

noncomputable def ep1132 := nat_lit 9903520314283042199192993792

noncomputable def ep1133 := nat_lit 14408751664996540782413514403909921068151046336395070838407948271702961137751557480543224879858009588018082129289825

noncomputable def ep1134 := nat_lit 55852343783389174283405539341953572568700530415884770651816705900518310611097296041679722416299367920843395176259911680

noncomputable def ep1135 := nat_lit 147503347860969887420648617983291349761589878409968886935714417143317695838936995348220961407568170047243723361

noncomputable def ep1136 := nat_lit 37736967926713450955074809055334963182972174021231569389061016221594285227365577979620739470452508096343471944016481

noncomputable def ep1137 := nat_lit 1023959636028801528529101554602482163759509724291220795283306274842835694536783760764128244298821745215462244898098380800

noncomputable def ep1138 := BSN.sin_dyadic_bound_f 59033731365803 140737488355328 3 2 68719476736 25604500001 ep1133 ep1134 ep1135 ep1136 ep1137 ep1135 27987190595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59033731365803) (BSN.sinEvenQ 140737488355328) 0 2 ep1133 ep1134 ep1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59033731365803) (BSN.sinOddQ 140737488355328) 0 2 ep1136 ep1137 ep1135 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15680748801389) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1139 := @Enclosure.Real.IsNear.cos_image qz137 qz495 Bool.false 15680748801389 68719476736 411 68719476736 Bool.true 27987190595 68719476736 1 12789760000 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 25691338836196938039 112589990684262400 371942855391 62450000000000000000 15680748801389 68719476736 411 68719476736 (ep1130 rfl) rfl) (Enclosure.sfrac_false_div 15680748801389 68719476736) (BSN.cos_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1131) (@Nat.cast Real Real.instNatCast ep1132)) 226375608064910080 72057594037927936 Bool.false 27987190595 68719476736 36 1000000000000000 25579520000 12789760000 (BSN.sin_reduce_arg_pos_rat_q1 15680748801389 68719476736 226375608064910080 72057594037927936 36 ep1131 ep1132 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27987190595 68719476736 ep1131 ep1132 59033731365803 140737488355328 25604500001 25579520000 (ep1138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1140 := nat_lit 8004927593152683087957472734891282056239364226832110451954164912909264328837904794521946364792853134752288846815841

noncomputable def ep1141 := nat_lit 6205815975932130475933948815772619174300058935098307850201856211168701179010810671297746935144374213427043908473323520

noncomputable def ep1142 := nat_lit 24014487772762327324097576907437879586018569500739511418088623309893506351122036509575142652455744267916772053000801

noncomputable def ep1143 := nat_lit 279261718916945871417027696709767862843502652079423853259083529502591553055486480208398612081496839604216975881299558400

noncomputable def ep1144 := BSN.cos_dyadic_bound_f 59033731365803 140737488355328 3 2 68719476736 25604500001 ep1140 ep1141 ep1135 ep1142 ep1143 ep1135 62762119510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59033731365803) (BSN.cosEvenQ 140737488355328) 0 2 ep1140 ep1141 ep1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59033731365803) (BSN.cosOddQ 140737488355328) 0 2 ep1142 ep1143 ep1135 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1145 := @Enclosure.Real.IsNear.sin_image qz137 qz495 Bool.false 15680748801389 68719476736 411 68719476736 Bool.false 62762119510 68719476736 1 12789760000 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 25691338836196938039 112589990684262400 371942855391 62450000000000000000 15680748801389 68719476736 411 68719476736 (ep1130 rfl) rfl) (Enclosure.sfrac_false_div 15680748801389 68719476736) (BSN.sin_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1131) (@Nat.cast Real Real.instNatCast ep1132)) 226375608064910080 72057594037927936 Bool.false 62762119510 68719476736 36 1000000000000000 25579520000 12789760000 (BSN.sin_reduce_arg_pos_rat_q1 15680748801389 68719476736 226375608064910080 72057594037927936 36 ep1131 ep1132 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62762119510 68719476736 ep1131 ep1132 59033731365803 140737488355328 25604500001 25579520000 (ep1144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz496 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 1920767 68719476736 1 68719476736 1920767 68719476736 1 68719476736 (ep1125 rfl rfl) rfl)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz134) (@HMul.hMul Real Real Real qz0 qz242 qz417) Bool.true 53756872117586365 4722366482869645213696 22471810145847347 ep1073 Bool.true 60275704002432085 2361183241434822606848 24808994515059611 ep1122 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz134 1920767 68719476736 1 68719476736 27987190595 68719476736 325031179 53644141527040000 53756872117586365 4722366482869645213696 22471810145847347 ep1073 qz496 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 27987190595 68719476736 5325310836736 878905614779023360000 27987190595 68719476736 325031179 53644141527040000 (ep1139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz417 1920767 68719476736 1 68719476736 31381059755 34359738368 325031179 53644141527040000 60275704002432085 2361183241434822606848 24808994515059611 ep1122 qz496 (@Enclosure.Real.IsNear.neg qz135 Bool.false 31381059755 34359738368 325031179 53644141527040000 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 62762119510 68719476736 5325310836736 878905614779023360000 31381059755 34359738368 325031179 53644141527040000 (ep1145 rfl rfl) rfl)) rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 147163458871 240000000 0 1 60275704002432085 2361183241434822606848 24808994515059611 ep1122 ep1067

noncomputable def ep1148 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 ep1120

noncomputable def ep1149 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 53756872117586365 4722366482869645213696 22471810145847347 ep1073 Bool.true 60275704002432085 2361183241434822606848 24808994515059611 ep1122

noncomputable def ep1150 := nat_lit 2098119705603891349729439

noncomputable def ep1151 := nat_lit 2266735911777429702574080000

noncomputable def ep1152 := nat_lit 4317845899084409916072437

noncomputable def ep1153 := nat_lit 8847353605656280307859456000000000

noncomputable def ep1154 := nat_lit 1582209447782005540293578783

noncomputable def ep1155 := nat_lit 3307029308155326561678965237

noncomputable def ep1156 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1150 ep1151 ep1152 ep1153 ep1154 ep1058 ep1155

noncomputable def ep1157 := nat_lit 4062039303631030782430119343853010648197935807856640000

noncomputable def ep1158 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 174043567 4800000 0 1 60275704002432085 2361183241434822606848 24808994515059611 ep1122 ep1150

noncomputable def ep1159 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 147163458871 240000000 0 1 53756872117586365 4722366482869645213696 22471810145847347 ep1073 ep1154

noncomputable abbrev qz497 := (@ep1124 ep1122 (BSN.cpow_neg_s_sub_mk qz16 76170 1000 20 3 1280000000 qz17 rfl EMRow20.d17) ep1146)

noncomputable def ep1160 := ep1062 (@ep1070 ep1071 ep1072 ep1052 ep1053 ep1054 ep1055 (@ep1074 ep1064 ep1065 ep1066 ep1121 (ep1123 qz497) rfl) (@ep1147 ep1068 ep1069 ep1071 ep1148 (ep1149 qz497) rfl) rfl rfl) (@ep1156 ep1061 ep1157 ep1057 ep1058 ep1059 ep1061 (@ep1158 ep1151 ep1152 ep1153 ep1121 (ep1149 qz497) rfl) (@ep1159 ep1058 ep1155 ep1061 ep1148 (ep1123 qz497) rfl) rfl rfl)

noncomputable def ep1161 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1057 ep1058 ep1059 ep1061 ep1057 ep1058 ep1059

noncomputable def ep1162 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1052 ep1053 ep1054 ep1055 Bool.true ep1057 ep1058 ep1059

noncomputable def ep1163 := @ep1022 47166457941964173 126100789566373888 27204962595 126100789566373888 (@ep1023 1 1835008 (ep1024 (@ep1025 524288 1 524288 (ep1026 (@ep1027 232564756 58141189 10000 0 1 (ep1031 rfl) (ep1034 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1035 651 68719476736 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1036 651 68719476736 1179835341 68719476736 651 68719476736 (@ep1041 589917345 589917996 34359738368 (@ep1047 ep1048 ep1049 ep1050 ep1051 ep1037 ep1038 ep1039 ep1040 (@ep1056 ep1055 ep1042 ep1043 ep1044 ep1045 (@ep1060 ep1061 ep1160) (@ep1060 ep1061 ep1160) rfl) (@ep1161 ep1061 ep1046 ep1048 ep1049 ep1050 (@ep1162 ep1061 ep1160) (@ep1162 ep1061 ep1160) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow20.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 433747727622300149 1134907106097364992 337508113266353 3404721318292094976 := ep1020 (ep1021 ep1163) rfl rfl

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex qz538 qz544 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz498 := qz536

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz498) (@HAdd.hAdd Real Real Real qz389 (Complex.re qz425) qz291))

noncomputable abbrev qz499 := (@HPow.hPow Complex Complex Complex qz514 qz528 (@HSub.hSub Complex Complex Complex qz521 qz530 qz516))

noncomputable abbrev qz244 := qz499

noncomputable def ep1164 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 357945085 19327352832 3947743 38654705664 26834844876672909 63050394783186944 14935453587

noncomputable def ep1165 := nat_lit 541215094043396245739798528

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20)) 4427 294912 1 884736 80855 65536 1759 262144 357945085 19327352832

noncomputable def ep1167 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))))) Bool.false 80855 65536 1759 262144

noncomputable def ep1168 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))))) Bool.false 646840 524288 3518 524288

noncomputable def ep1169 := nat_lit 6406872367042588376448745390028113168573

noncomputable def ep1170 := nat_lit 4209011415601578683184419822370816000000

noncomputable def ep1171 := nat_lit 350342395910085485897935218921603346844448111297773681

noncomputable def ep1172 := nat_lit 21167115297403053494382721133337992254018761523200000000

noncomputable def ep1173 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20)))) ep1169 ep1170 ep1171 ep1172 321661 325179

noncomputable def ep1174 := nat_lit 68805476776127351852796227203963138933240349401

noncomputable def ep1175 := nat_lit 45228849847752348651021636382151875231744000000

noncomputable def ep1176 := nat_lit 28428517816306719106499805074216337489917400616863759

noncomputable def ep1177 := nat_lit 1763926274783587791198560094444832687834896793600000000

noncomputable def ep1178 := nat_lit 1474816322645052944182336047588570968049725041

noncomputable def ep1179 := nat_lit 1628238594519084551436778909757467508342784000000

noncomputable def ep1180 := nat_lit 9200182114404856619937558031007296965439303895408573

noncomputable def ep1181 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))) ep1174 ep1175 ep1176 ep1177 ep1178 ep1179 ep1180

noncomputable def ep1182 := nat_lit 112098437047187039576030633883342913951680406620203773198620651017215350334988939991973888000000

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20)) 262307980770939090870299 212670754566189350912000 ep746 ep747 262307980770939090870299 212670754566189350912000 ep746 ep747 ep1174

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20)) 38403337389412563191321 ep863 ep864 ep865 38403337389412563191321 ep863 ep864 ep865 ep1178

noncomputable def ep1185 := @ep1164 63050394783186944 ep1165 252022917402627061 567453553048682496 58087538977835 567453553048682496 (@ep1166 3947743 38654705664 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz480) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow20.d14 EMRow20.d15 rfl) (ep1001 rfl)) (ep1167 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz146 1 20)) (@ep1168 80855 65536 1759 262144 (@ep1173 262144 (@ep1181 ep1172 ep1182 ep1169 ep1170 ep1171 ep1172 (@ep1183 ep1175 ep1176 ep1177 ep981 ep981 rfl) (@ep1184 ep1179 ep1180 ep1172 ep989 ep989 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz498)

noncomputable def ep1186 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz483) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 26834844876672909 63050394783186944 14935453587 63050394783186944 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz151 3)

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz483) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 41287583 1835008 1 1835008 649949523 34359738368 173 17179869184

noncomputable def ep1188 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz483 41287583 524288 1 524288 2 7 0 1 41287583 1835008

noncomputable abbrev qz500 := (Complex.re qz536)

noncomputable abbrev qz501 := (Complex.im qz536)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz267 qz500 qz500) (@HMul.hMul Real Real Real qz267 qz501 qz501))

noncomputable abbrev qz247 := qz498

noncomputable def ep1189 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 41287583 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1190 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 41287583 524288 1 524288 41287583

noncomputable def ep1191 := @Enclosure.Real.IsNear.sqrt_image qz246 387595849 62500 0 1 20643791 20643792 262144

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz500 qz500)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz501 qz501)

noncomputable def ep1192 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 96707556 15625 0 1

noncomputable abbrev qz250 := qz500

noncomputable def ep1193 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1194 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz486 qz151) Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 78672 1000 3 qz152)

noncomputable abbrev qz502 := (ep1194 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz151 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz153))

noncomputable def ep1195 := @ep1193 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz502)

noncomputable def ep1196 := ep1195 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz502)

noncomputable abbrev qz251 := qz501

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 78672 1000 0 1 78672 1000 0 1 96707556 15625

noncomputable def ep1198 := @ep1197 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz502)

noncomputable def ep1199 := ep1198 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 78672 1000 0 1 qz502)

noncomputable def ep1200 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 649949523 34359738368

noncomputable def ep1201 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 1299899046 68719476736

noncomputable def ep1202 := nat_lit 448850243599718093296360128817804260097269464714066418193

noncomputable def ep1203 := nat_lit 1254416917417347551711384152836470334711398400000000000000000

noncomputable def ep1204 := nat_lit 4038513726986481496378321653614368776073039676952815119395803661

noncomputable def ep1205 := nat_lit 10616816653580618478826557019363316832791429120000000000000000000000000000

noncomputable def ep1206 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1202 ep1203 ep1204 ep1205

noncomputable def ep1207 := nat_lit 172762644903553328342634189400775785458071368536522482761

noncomputable def ep1208 := nat_lit 34844914372704098658649559801013064853094400000000000000000000

noncomputable def ep1209 := nat_lit 121416818843274525039473621607601714405774165647514090551429911

noncomputable def ep1210 := nat_lit 21233633307161236957653114038726633665582858240000000000000000000000000000

noncomputable def ep1211 := nat_lit 110657697095797543369006324499844082955194723861687902203401

noncomputable def ep1212 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1207 ep1208 ep1209 ep1210 ep1211

noncomputable def ep1213 := nat_lit 313604229354336887927846038209117583677849600000000000000000000

noncomputable def ep1214 := nat_lit 7955610635129688467717169685621135837740305188258116148240177411

noncomputable def ep1215 := nat_lit 3910037076099888214675966395379215891490798271259622026099089288828237225726822015461983985126604800000000000000000000000

noncomputable def ep1216 := nat_lit 13143920454094102906179431069

noncomputable def ep1217 := nat_lit 5902958103587056517120000000000

noncomputable def ep1218 := nat_lit 5916724548956428268208002131

noncomputable def ep1219 := nat_lit 4607996669612645993676800000000000000

noncomputable def ep1220 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1216 ep1217 ep1218 ep1219 ep1216 ep1217 ep1218

noncomputable def ep1221 := nat_lit 332652517044133522018501000451

noncomputable def ep1222 := nat_lit 17708874310761169551360000000000

noncomputable def ep1223 := nat_lit 45954854329395999688921255881

noncomputable def ep1224 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1216 ep1217 ep1218 ep1219 Bool.true ep1221 ep1222 ep1223

noncomputable def ep1225 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1216 ep1217 ep1218 ep1219 Bool.true ep1221 ep1222 ep1223 ep1219

noncomputable def ep1226 := nat_lit 152884594123759039806905263

noncomputable def ep1227 := nat_lit 141670994486089356410880000000

noncomputable def ep1228 := nat_lit 62881387668892385108667809

noncomputable def ep1229 := nat_lit 110591920070703503848243200000000000

noncomputable def ep1230 := nat_lit 5080296774203107185668783833

noncomputable def ep1231 := nat_lit 4427218577690292387840000000000

noncomputable def ep1232 := nat_lit 2472500047064434166510132567

noncomputable abbrev qz252 := (Complex.re qz499)

noncomputable abbrev qz253 := (Complex.im qz499)

noncomputable def ep1233 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1226 ep1227 ep1228 ep1229 ep1230 ep1231 ep1232

noncomputable def ep1234 := nat_lit 3455997502209484495257600000000000000

noncomputable def ep1235 := nat_lit 1396584211633172071877349617355289242650704651223040000000

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 1160412547 30000000 0 1 131750207733456229 4722366482869645213696 54188820890862347 ep1073 ep1226

noncomputable def ep1237 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 1160412547 30000000 0 1 0 1 0 1 1160412547

noncomputable def ep1238 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3481237641 125000 0 1 1160412547 30000000 0

noncomputable abbrev qz503 := (@HAdd.hAdd Complex Complex Complex qz513 qz529 qz517)

noncomputable abbrev qz254 := qz503

noncomputable def ep1239 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1

noncomputable abbrev qz255 := (Complex.re qz503)

noncomputable abbrev qz256 := (Complex.im qz503)

noncomputable def ep1240 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 386783349 25000 0 1 193415112 15625 0 1

noncomputable def ep1241 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 386783349 62500 0 1 5 2 0 1 386783349 25000

noncomputable abbrev qz504 := (@HAdd.hAdd Complex Complex Complex qz513 qz529 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz504

noncomputable def ep1242 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1

noncomputable abbrev qz258 := (Complex.re qz504)

noncomputable abbrev qz259 := (Complex.im qz504)

noncomputable def ep1243 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 96707556 15625 0 1

noncomputable def ep1244 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1245 := @ep1244 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep1246 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz490 qz151) Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 78672 1000 1 qz152)

noncomputable abbrev qz505 := (ep1246 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz151 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz153))

noncomputable def ep1247 := ep1245 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz505)

noncomputable def ep1248 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 78672 1000 0 1 78672 1000 0 1 96707556 15625

noncomputable def ep1249 := @ep1248 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep1250 := ep1249 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz505)

noncomputable def ep1251 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 (@ep1243 386783349 386783349 62500 0 1 (ep1247 rfl) (ep1250 rfl) rfl rfl)

noncomputable def ep1252 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 4917 125 0 1 14751 125 0 1

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 78672 1000 0 1 4917 125

noncomputable def ep1254 := @ep1253 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep1255 := ep1254 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz505)

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 78672 1000 0 1 3 2 0 1 14751 125

noncomputable def ep1257 := @ep1256 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 78672 1000 0 1 ep946)

noncomputable def ep1258 := ep1257 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 78672 1000 0 1 qz505)

noncomputable abbrev qz260 := (ep1242 (BSN.ascPochhammer_succ_eval_c 1 2 qz425 rfl) (ep1251 (@ep1252 2458500 19668 125 0 1 (ep1255 rfl) (ep1258 rfl) rfl rfl)))

noncomputable def ep1259 := @ep1241 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz260)

noncomputable def ep1260 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz492 qz151) Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 78672 1000 2 qz152)

noncomputable abbrev qz506 := (ep1260 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz151 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz153))

noncomputable def ep1261 := ep1259 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz506)

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 19668 125 0 1 78672 1000 0 1 193415112 15625

noncomputable def ep1263 := @ep1262 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz260)

noncomputable def ep1264 := ep1263 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz506)

noncomputable def ep1265 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 (@ep1240 10878867628125 3481237641 125000 0 1 (ep1261 rfl) (ep1264 rfl) rfl rfl)

noncomputable def ep1266 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 1901813727033 3906250 0 1 9834 25 0 1

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 386783349 62500 0 1 78672 1000 0 1 1901813727033 3906250

noncomputable def ep1268 := @ep1267 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz260)

noncomputable def ep1269 := ep1268 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz506)

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 19668 125 0 1 5 2 0 1 9834 25

noncomputable def ep1271 := @ep1270 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 386783349 62500 0 1 Bool.false 19668 125 0 1 qz260)

noncomputable def ep1272 := ep1271 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 78672 1000 0 1 qz506)

noncomputable abbrev qz261 := (ep1239 (BSN.ascPochhammer_succ_eval_c 2 3 qz425 rfl) (ep1265 (@ep1266 47506929113325 1900277164533 3906250 0 1 (ep1269 rfl) (ep1272 rfl) rfl rfl)))

noncomputable def ep1273 := @ep1238 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz261)

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1900277164533 3906250 0 1 0 1 0

noncomputable def ep1275 := @ep1274 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz261)

noncomputable def ep1276 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 633425721511 937500000 0 1 0 1 0 1 633425721511

noncomputable def ep1277 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1900277164533 3906250 0 1 633425721511 937500000 0

noncomputable def ep1278 := @ep1277 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz261)

noncomputable def ep1279 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3481237641 125000 0 1 0 1 0

noncomputable def ep1280 := @ep1279 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1077) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3481237641 125000 0 1 Bool.true 1900277164533 3906250 0 1 qz261)

noncomputable def ep1281 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 (@ep1237 1160412547 30000000 0 1 (ep1273 rfl) (ep1275 rfl) rfl rfl) (@ep1276 633425721511 937500000 0 1 (ep1278 rfl) (ep1280 rfl) rfl rfl)

noncomputable def ep1282 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 ep1281

noncomputable def ep1283 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 131750207733456229 4722366482869645213696 54188820890862347 ep1073 Bool.false 8020351245106303 4722366482869645213696 3903378033286097 ep1073

noncomputable def ep1284 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz475)) Bool.true 131750207733456229 4722366482869645213696 54188820890862347 ep1073 Bool.false 8020351245106303 4722366482869645213696 3903378033286097

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz136 78672 1000 0 1 3372894687698167 1125899906842624 48830623 624500000000000000 16584523179411887139 70368744177664000 240100173291 39031250000000000000 qz153 (BSN.isNear_log_sfrac 20 1 3372894687698167 1125899906842624 48830623 624500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz420 Bool.false ep1126 ep1127 1000051159040000 ep1128 3372894687698167 1125899906842624 48830623 624500000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 7667154041 34359738368 24973259072661432 36028797018963968 12789760000 1000000000000000 rfl rfl rfl rfl (ep1129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1286 := nat_lit 301069019460377541328502784

noncomputable def ep1287 := nat_lit 4951760157141521099596496896

noncomputable def ep1288 := nat_lit 5361237578416761128907606213830802854543748360201601

noncomputable def ep1289 := nat_lit 9415652603080021145753684134811499624153533166696051769344

noncomputable def ep1290 := nat_lit 141234789046200317186305262022172494362302997500440776540160

noncomputable def ep1291 := BSN.cos_dyadic_bound_f 8556896189599 140737488355328 2 1 68719476736 25604500001 ep1288 ep1289 ep1288 ep1288 ep1290 ep1288 68592498587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 8556896189599) (BSN.cosEvenQ 140737488355328) 0 1 ep1288 ep1289 ep1288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 8556896189599) (BSN.cosOddQ 140737488355328) 0 1 ep1288 ep1290 ep1288 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz507 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8097911708697) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1292 := @Enclosure.Real.IsNear.cos_image qz218 qz507 Bool.false 8097911708697 34359738368 53 8589934592 Bool.true 68592498587 68719476736 1 12789760000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 16584523179411887139 70368744177664000 240100173291 39031250000000000000 8097911708697 34359738368 53 8589934592 (ep1285 rfl) rfl) (Enclosure.sfrac_false_div 8097911708697 34359738368) (BSN.cos_reduce2 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1286) (@Nat.cast Real Real.instNatCast ep1287)) 226375608064910080 72057594037927936 Bool.false 68592498587 68719476736 37 1000000000000000 25579520000 12789760000 (BSN.sin_reduce_arg_pos_rat_q2 8097911708697 34359738368 226375608064910080 72057594037927936 37 ep1286 ep1287 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 68592498587 68719476736 ep1286 ep1287 8556896189599 140737488355328 25604500001 25579520000 (ep1291 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1293 := nat_lit 47078263015400105728768420674057498120767665833480258846720

noncomputable def ep1294 := nat_lit 329547841107800740101378944718402486845373660834361811927040

noncomputable def ep1295 := BSN.sin_dyadic_bound_f 8556896189599 140737488355328 2 1 68719476736 25604500001 ep1288 ep1293 ep1288 ep1288 ep1294 ep1288 4175598209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 8556896189599) (BSN.sinEvenQ 140737488355328) 0 1 ep1288 ep1293 ep1288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 8556896189599) (BSN.sinOddQ 140737488355328) 0 1 ep1288 ep1294 ep1288 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1296 := @Enclosure.Real.IsNear.sin_image qz218 qz507 Bool.false 8097911708697 34359738368 53 8589934592 Bool.true 4175598209 68719476736 1 12789760000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 16584523179411887139 70368744177664000 240100173291 39031250000000000000 8097911708697 34359738368 53 8589934592 (ep1285 rfl) rfl) (Enclosure.sfrac_false_div 8097911708697 34359738368) (BSN.sin_reduce2 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1286) (@Nat.cast Real Real.instNatCast ep1287)) 226375608064910080 72057594037927936 Bool.false 4175598209 68719476736 37 1000000000000000 25579520000 12789760000 (BSN.sin_reduce_arg_pos_rat_q2 8097911708697 34359738368 226375608064910080 72057594037927936 37 ep1286 ep1287 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4175598209 68719476736 ep1286 ep1287 8556896189599 140737488355328 25604500001 25579520000 (ep1295 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1297 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz475) Bool.true 131750207733456229 4722366482869645213696 54188820890862347 ep1073 Bool.false 8020351245106303 4722366482869645213696 3903378033286097 ep1073 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 1920767 68719476736 1 68719476736 68592498587 68719476736 41897413 6705517690880000 131750207733456229 4722366482869645213696 54188820890862347 ep1073 qz496 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 68592498587 68719476736 686447214592 109863201847377920000 68592498587 68719476736 41897413 6705517690880000 (ep1292 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz475 1920767 68719476736 1 68719476736 4175598209 68719476736 41897413 6705517690880000 8020351245106303 4722366482869645213696 3903378033286097 ep1073 qz496 (@Enclosure.Real.IsNear.neg qz217 Bool.true 4175598209 68719476736 41897413 6705517690880000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 4175598209 68719476736 686447214592 109863201847377920000 4175598209 68719476736 41897413 6705517690880000 (ep1296 rfl rfl) rfl)) rfl)

noncomputable def ep1298 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 633425721511 937500000 0 1 8020351245106303 4722366482869645213696 3903378033286097 ep1073 ep1230

noncomputable def ep1299 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1160412547 30000000 0 1 Bool.false 633425721511 937500000 0 1 ep1281

noncomputable def ep1300 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 131750207733456229 4722366482869645213696 54188820890862347 ep1073 Bool.false 8020351245106303 4722366482869645213696 3903378033286097 ep1073

noncomputable def ep1301 := nat_lit 9306916216168426349983741

noncomputable def ep1302 := nat_lit 4529528845509370599459059

noncomputable def ep1303 := nat_lit 83453970392788643828062242019

noncomputable def ep1304 := nat_lit 34324592970624831935457846317

noncomputable def ep1305 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1301 ep1227 ep1302 ep1229 ep1303 ep1231 ep1304

noncomputable def ep1306 := nat_lit 11781803226985796462881019155741542803885997655326720000000

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1160412547 30000000 0 1 8020351245106303 4722366482869645213696 3903378033286097 ep1073 ep1301

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 633425721511 937500000 0 1 131750207733456229 4722366482869645213696 54188820890862347 ep1073 ep1303

noncomputable abbrev qz508 := (@ep1284 ep1073 (BSN.cpow_neg_s_sub_mk qz151 78672 1000 20 3 1280000000 qz152 rfl EMRow20.d17) ep1297)

noncomputable def ep1309 := ep1225 (@ep1233 ep1234 ep1235 ep1216 ep1217 ep1218 ep1219 (@ep1236 ep1227 ep1228 ep1229 ep1282 (ep1283 qz508) rfl) (@ep1298 ep1231 ep1232 ep1234 ep1299 (ep1300 qz508) rfl) rfl rfl) (@ep1305 ep1234 ep1306 ep1221 ep1222 ep1223 ep1219 (@ep1307 ep1227 ep1302 ep1229 ep1282 (ep1300 qz508) rfl) (@ep1308 ep1231 ep1304 ep1234 ep1299 (ep1283 qz508) rfl) rfl rfl)

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1221 ep1222 ep1223 ep1219 ep1221 ep1222 ep1223

noncomputable def ep1311 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1216 ep1217 ep1218 ep1219 Bool.true ep1221 ep1222 ep1223

noncomputable def ep1312 := @ep1187 26834844876672909 63050394783186944 14935453587 63050394783186944 (@ep1188 1 1835008 (ep1189 (@ep1190 524288 1 524288 (ep1191 (@ep1192 387595849 387595849 62500 0 1 (ep1196 rfl) (ep1199 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1200 173 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1201 692 68719476736 649949523 34359738368 173 17179869184 (@ep1206 649949177 649949869 34359738368 (@ep1212 ep1213 ep1214 ep1210 ep1215 ep1202 ep1203 ep1204 ep1205 (@ep1220 ep1219 ep1207 ep1208 ep1209 ep1210 (@ep1224 ep1219 ep1309) (@ep1224 ep1219 ep1309) rfl) (@ep1310 ep1219 ep1211 ep1213 ep1214 ep1210 (@ep1311 ep1219 ep1309) (@ep1311 ep1219 ep1309) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow20.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 252022917402627061 567453553048682496 58087538977835 567453553048682496 := ep1185 (ep1186 ep1312) rfl rfl

noncomputable def EMRow20.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz509 := (EMRow20.d3 qz518 qz531 (@Enclosure.dec_le_dec qz518 qz531 76170 1000 78672 1000 (@Eq.refl Real qz518) (@Eq.refl Real qz531) rfl rfl rfl) 20 20 1 1)

noncomputable abbrev qz262 := qz509

noncomputable def ep1313 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz16 76170 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz509)

noncomputable def ep1314 := @Enclosure.Real.IsNear.pos_val qz263 ep268 ep269

noncomputable def ep1315 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 20 qz16) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz509)

noncomputable def ep1316 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1314 ep270 ep271 (@ep1315 ep268 ep269 ep270 ep271 (@Eq.refl Real (hardyZApproximantEM 1 20 qz16)) EMRow20.d10) rfl rfl rfl)

noncomputable def ep1317 := @Enclosure.Real.IsNear.neg_val qz264 ep730 ep731

noncomputable def ep1318 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 20 qz151) Bool.true

noncomputable def ep1319 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 20 qz16)

noncomputable def ep1320 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 20 qz16) Bool.false

noncomputable def ep1321 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz16) (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 433747727622300149 1134907106097364992 337508113266353 3404721318292094976 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1322 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 20 qz151)

noncomputable def ep1323 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 20 qz151) Bool.true

noncomputable def ep1324 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz151) (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 252022917402627061 567453553048682496 58087538977835 567453553048682496 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz389 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1325 := @List.cons EMRow20.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1313 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl) (ep1316 (@ep1317 ep732 ep733 (@ep1318 ep730 ep731 ep732 ep733 (@Eq.refl Real (hardyZApproximantEM 1 20 qz151)) EMRow20.d13) rfl rfl rfl)) (ep1319 (hardyZErrorBoundEM 1 20 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz16 rfl) (@ep1320 Bool.false ep268 ep269 ep270 ep271 433747727622300149 1134907106097364992 337508113266353 3404721318292094976 (@ep1315 ep268 ep269 ep270 ep271 (@Eq.refl Real (hardyZApproximantEM 1 20 qz16)) EMRow20.d10) (ep1321 EMRow20.d18) rfl rfl rfl rfl rfl)) (ep1322 (hardyZErrorBoundEM 1 20 qz151) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz151 rfl) (@ep1323 Bool.false ep730 ep731 ep732 ep733 252022917402627061 567453553048682496 58087538977835 567453553048682496 (@ep1318 ep730 ep731 ep732 ep733 (@Eq.refl Real (hardyZApproximantEM 1 20 qz151)) EMRow20.d13) (ep1324 EMRow20.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow20.d0)

noncomputable abbrev qz510 := (@Enclosure.dec_le_dec qz518 qz531 76170 1000 78672 1000 (@Eq.refl Real qz518) (@Eq.refl Real qz531) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1325 (@List.IsChain.singleton EMRow20.d1 EMRow20.d20 (EMRow20.d2 qz280 qz432 qz510))))

noncomputable abbrev qz511 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1326 := And (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 qz265)) (@Option.some Real qz16))

noncomputable def ep1327 := ep1326 (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 qz265)) (@Option.some Real qz151))

noncomputable def ep1328 := @And.intro (@Eq Nat (@List.length qz511 qz265) 1) ep1327

noncomputable def ep1329 := @And.intro (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 qz265)) (@Option.some Real qz16))

noncomputable def ep1330 := @ep1329 (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 qz265)) (@Option.some Real qz151))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1325 (@List.IsChain.singleton EMRow20.d1 EMRow20.d20 (EMRow20.d2 qz280 qz432 qz510)))

theorem EMRow20.d21 : Zeta.Certificates.BatchSpec 1 76170 1000 78672 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz151)))) qz266 (ep1328 (@Eq.refl Nat 1) (ep1330 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz151))))

theorem solution : Zeta.Certificates.BatchSpec 1 76170 1000 78672 1000 := EMRow20.d21
#print axioms solution
#check solution
