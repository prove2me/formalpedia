-- Prove2me | solution 1 for RHHeight1000.em_main_0024_0024
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:23:47.823418+00:00
-- url     : https://prove2.me/submissions/8dbff7f5-0d7a-4379-8b1f-5ebec74080e7

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow24.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow24.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow24.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow24.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow24.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000083717 41858500000000000000 4138529546116343 2251799813685248 250000000083717 41858500000000000000 481788 262144

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 167434 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000334868 167434000000000000000 4138529546116343 2251799813685248 250000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 167434 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000334868 167434000000000000000 4138529546116343 2251799813685248 250000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz272 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz272)

theorem EMRow24.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 167434 600168 524288 1 167434 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 167434 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 167434 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 167434 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 167434 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 167434 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 167434 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow24.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz568 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 85999 1000)))

noncomputable abbrev qz524 := qz568

noncomputable abbrev qz273 := qz524

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz569 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz525 := qz569

noncomputable abbrev qz274 := qz525

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz526 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz526

noncomputable abbrev qz6 := qz275

noncomputable abbrev qz527 := (@Neg.neg Complex Complex.instNeg qz568)

noncomputable abbrev qz276 := qz527

noncomputable abbrev qz7 := qz276

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz277) Bool.false 217681867921 274877906944 81127764321099 23011953735630848 Bool.false 19203975065 274877906944 80844956909587 23011953735630848

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz277 Bool.false 39007406751 34359738368 36311845088951 11505976867815424 Bool.false 42388437653 274877906944 72373036205731 23011953735630848 Bool.true

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz278) Bool.false 39007406751 34359738368 36311845088951 11505976867815424 Bool.false 42388437653 274877906944 72373036205731 23011953735630848

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz278 Bool.false 47659995983 34359738368 31766058100223 11505976867815424 Bool.true 8771887155 68719476736 15819493665443 5752988433907712 Bool.true

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz279) Bool.false 47659995983 34359738368 31766058100223 11505976867815424 Bool.true 8771887155 68719476736 15819493665443 5752988433907712

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz279 Bool.false 246107120587 137438953472 13425090776449 5752988433907712 Bool.true 26006234253 137438953472 26741495706497 11505976867815424 Bool.true

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz280) Bool.false 246107120587 137438953472 13425090776449 5752988433907712 Bool.true 26006234253 137438953472 26741495706497 11505976867815424

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz280 Bool.false 371266924559 274877906944 42954150770131 23011953735630848 Bool.true 7506812063 68719476736 21386056713901 11505976867815424 Bool.false

noncomputable abbrev qz281 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz281) Bool.false 371266924559 274877906944 42954150770131 23011953735630848 Bool.true 7506812063 68719476736 21386056713901 11505976867815424

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz281 Bool.false 7362575533 8589934592 15472270713215 11505976867815424 Bool.true 26018649409 137438953472 3849850042863 2876494216953856 Bool.false

noncomputable abbrev qz528 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz282 := qz528

noncomputable abbrev qz8 := qz282

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 7362575533 8589934592 15472270713215 11505976867815424 Bool.true 26018649409 137438953472 3849850042863 2876494216953856

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 10142256155 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 34359738368 8480539474709 11505976867815424 Bool.false

noncomputable abbrev qz529 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz283 := qz529

noncomputable abbrev qz9 := qz283

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 10142256155 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 34359738368 8480539474709 11505976867815424

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz284 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz284

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz285 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz285))

noncomputable abbrev qz570 := (Enclosure.sfrac Bool.false 85999 1000)

noncomputable abbrev qz530 := qz570

noncomputable abbrev qz286 := qz530

noncomputable abbrev qz287 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz268 qz286 (Real.log qz287))

noncomputable abbrev qz13 := qz286

noncomputable abbrev qz288 := (@Eq.refl Real qz530)

noncomputable abbrev qz14 := qz288

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 24217482213 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 34359738368 8480539474709 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz285) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz285) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz285 qz15)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz285 qz15)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 83717 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 26404168095569828430315004014774866098558932846805378081663499479904000409600

noncomputable def ep57 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep58 := nat_lit 43009703457257436491159616111923498959272352703861542128176192484777394176

noncomputable def ep59 := nat_lit 69084138825656848134601228279276773164577430789636404859958784802392266244096

noncomputable def ep60 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz289 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz290 := (BSN.sinOddQ 1073741824)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 1600279368 1073741824 3 2 524288 167598 ep56 ep57 ep58 ep59 ep60 ep58 522593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1600279368) qz289 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1600279368) qz290 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (Real.log qz287)

noncomputable abbrev qz17 := (Enclosure.Real.IsNear.const Bool.false 85999 1000)

noncomputable abbrev qz531 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7813181) qz531)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 83717 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 83717 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz12 qz291 Bool.false 7813181 131072 135 131072 Bool.true 522593 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1953295287 32768000 85999 83717000 7813181 131072 135 131072 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz16 85999 1000 0 1 181704 262144 1 83717 1953295287 32768000 85999 83717000 qz17 qz292 rfl) rfl) (Enclosure.sfrac_false_div 7813181 131072) (BSN.cos_reduce1 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28152412375199579635712) qz293) 226375608064910080 72057594037927936 Bool.false 522593 524288 9 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 7813181 131072 226375608064910080 72057594037927936 9 28152412375199579635712 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522593 524288 28152412375199579635712 18889465931478580854784 1600279368 1073741824 167598 167434 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 14688097699075352433059962059813558276514639293871370730758911352162123513856

noncomputable def ep64 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep65 := nat_lit 43978273690311542426197566947216827831625373176206389108020381671516815753216

noncomputable def ep66 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz294 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz295 := (BSN.cosOddQ 1073741824)

noncomputable def ep67 := BSN.cos_dyadic_bound_f 1600279368 1073741824 3 2 524288 167598 ep63 ep64 ep58 ep65 ep66 ep58 42117 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1600279368) qz294 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1600279368) qz295 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz12 qz291 Bool.false 7813181 131072 135 131072 Bool.false 42117 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1953295287 32768000 85999 83717000 7813181 131072 135 131072 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz16 85999 1000 0 1 181704 262144 1 83717 1953295287 32768000 85999 83717000 qz17 qz292 rfl) rfl) (Enclosure.sfrac_false_div 7813181 131072) (BSN.sin_reduce1 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28152412375199579635712) qz293) 226375608064910080 72057594037927936 Bool.false 42117 524288 9 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 7813181 131072 226375608064910080 72057594037927936 9 28152412375199579635712 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 42117 524288 28152412375199579635712 18889465931478580854784 1600279368 1073741824 167598 167434 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz296 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 24217482213 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 34359738368 8480539474709 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 46341 65536 1 262144 522593 524288 11432867 10972954624 24217482213 34359738368 8520763484001 11505976867815424 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 522593 524288 11432867 10972954624 522593 524288 11432867 10972954624 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 46341 65536 1 262144 42117 524288 11432867 10972954624 1951743897 34359738368 8480539474709 11505976867815424 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.false 42117 524288 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.false 42117 524288 11432867 10972954624 42117 524288 11432867 10972954624 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz297 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz18 := qz297

noncomputable def ep70 := @ep51 24217482213 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 34359738368 8480539474709 11505976867815424 Bool.false 10142256155 10142256155 34359738368 8520763484001 11505976867815424 Bool.true 1951743897 1951743897 34359738368 8480539474709 11505976867815424 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz18)) (ep53 ep69) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz19 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz20 := (@HMul.hMul Real Real Real qz268 qz286 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz20)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20)))) Bool.false 19308045977 34359738368 3475753614607 5752988433907712 Bool.true 18211673821 137438953472 6918860696743 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 3 qz14 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz15)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz15)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 83717 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 3822680935668183270564302291992576

noncomputable def ep75 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep76 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep77 := BSN.cos_dyadic_bound_f 248652032 1073741824 2 1 524288 167598 ep74 ep75 ep74 ep74 ep76 ep74 510292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 248652032) qz294 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 248652032) qz295 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6191799) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 83717 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 83717 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz20 qz299 Bool.false 6191799 65536 539 524288 Bool.false 510292 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 12383598003 131072000 85999 83717000 6191799 65536 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz21 85999 1000 0 1 287994 262144 1 83717 12383598003 131072000 85999 83717000 qz17 qz300 rfl) rfl) (Enclosure.sfrac_false_div 6191799 65536) (BSN.cos_reduce0 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2187166404379492220928) qz301) 226375608064910080 72057594037927936 Bool.false 510292 524288 15 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 6191799 65536 226375608064910080 72057594037927936 15 2187166404379492220928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510292 524288 2187166404379492220928 9444732965739290427392 248652032 1073741824 167598 167434 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep80 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep81 := BSN.sin_dyadic_bound_f 248652032 1073741824 2 1 524288 167598 ep74 ep79 ep74 ep74 ep80 ep74 120329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 248652032) qz289 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 248652032) qz290 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz20 qz299 Bool.false 6191799 65536 539 524288 Bool.false 120329 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 12383598003 131072000 85999 83717000 6191799 65536 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz21 85999 1000 0 1 287994 262144 1 83717 12383598003 131072000 85999 83717000 qz17 qz300 rfl) rfl) (Enclosure.sfrac_false_div 6191799 65536) (BSN.sin_reduce0 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2187166404379492220928) qz301) 226375608064910080 72057594037927936 Bool.false 120329 524288 15 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 6191799 65536 226375608064910080 72057594037927936 15 2187166404379492220928 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 120329 524288 2187166404379492220928 9444732965739290427392 248652032 1073741824 167598 167434 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz19 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz20)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20))) Bool.false 19308045977 34359738368 3475753614607 5752988433907712 Bool.true 18211673821 137438953472 6918860696743 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz19 (Real.cos qz20) 151349 262144 1 262144 127573 131072 45647751 43891818496 19308045977 34359738368 3475753614607 5752988433907712 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz20) Bool.false 510292 524288 45647751 43891818496 127573 131072 45647751 43891818496 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz19 (@Neg.neg Real Real.instNeg (Real.sin qz20)) 151349 262144 1 262144 120329 524288 45647751 43891818496 18211673821 137438953472 6918860696743 11505976867815424 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz20) Bool.false 120329 524288 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz20) Bool.false 120329 524288 45647751 43891818496 120329 524288 45647751 43891818496 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 19308045977 34359738368 3475753614607 5752988433907712 Bool.true 18211673821 137438953472 6918860696743 11505976867815424 Bool.false 1011904676114072600576 7362575533 8589934592 15472270713215 11505976867815424 Bool.true 893993986381957824512 26018649409 137438953472 3849850042863 2876494216953856 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz532 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz532))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz268 qz286 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz281 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 135664507503 274877906944 12009609343701 23011953735630848 Bool.false 11005025283 137438953472 5986656542449 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 4 qz14 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz532) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz532) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz532 qz15)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz532 qz15)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 83717 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 21143305581700548332806911014559436527216759049603639081487493835243210670080

noncomputable def ep91 := nat_lit 27596170557672183523047174567913187689559935086995062307332054289257332736

noncomputable def ep92 := nat_lit 55330644628312824003076023898355236219784605235011538922064898623454373216256

noncomputable def ep93 := BSN.sin_dyadic_bound_f 1513931072 1073741824 3 2 524288 167598 ep90 ep57 ep91 ep92 ep60 ep91 517521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1513931072) qz289 0 2 ep90 ep57 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1513931072) qz290 0 2 ep92 ep60 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz25 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62505449) qz24)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 83717 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 83717 rfl rfl rfl (ep89 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz23 qz303 Bool.false 62505449 524288 539 524288 Bool.false 517521 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1953295287 16384000 85999 83717000 62505449 524288 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz25 85999 1000 0 1 363408 262144 1 83717 1953295287 16384000 85999 83717000 qz17 qz304 rfl) rfl) (Enclosure.sfrac_false_div 62505449 524288) (BSN.cos_reduce3 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106533428315649136918528) qz26) 226375608064910080 72057594037927936 Bool.false 517521 524288 18 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 62505449 524288 226375608064910080 72057594037927936 18 106533428315649136918528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 517521 524288 106533428315649136918528 75557863725914323419136 1513931072 1073741824 167598 167434 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 11758545843414825599791860419007648376315781665374019517407421932597009186816

noncomputable def ep96 := nat_lit 35220445189129132432329486907887118753568225125948068427607601689212512894976

noncomputable def ep97 := BSN.cos_dyadic_bound_f 1513931072 1073741824 3 2 524288 167598 ep95 ep64 ep91 ep96 ep66 ep91 83962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1513931072) qz294 0 2 ep95 ep64 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1513931072) qz295 0 2 ep96 ep66 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz23 qz303 Bool.false 62505449 524288 539 524288 Bool.true 83962 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 1953295287 16384000 85999 83717000 62505449 524288 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz25 85999 1000 0 1 363408 262144 1 83717 1953295287 16384000 85999 83717000 qz17 qz304 rfl) rfl) (Enclosure.sfrac_false_div 62505449 524288) (BSN.sin_reduce3 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106533428315649136918528) qz26) 226375608064910080 72057594037927936 Bool.false 83962 524288 18 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 62505449 524288 226375608064910080 72057594037927936 18 106533428315649136918528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 83962 524288 106533428315649136918528 75557863725914323419136 1513931072 1073741824 167598 167434 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 135664507503 274877906944 12009609343701 23011953735630848 Bool.false 11005025283 137438953472 5986656542449 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 262143 524288 1 524288 517521 524288 45647751 43891818496 135664507503 274877906944 12009609343701 23011953735630848 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 517521 524288 45647751 43891818496 517521 524288 45647751 43891818496 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 262143 524288 1 524288 41981 262144 45647751 43891818496 11005025283 137438953472 5986656542449 11505976867815424 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 41981 262144 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 83962 524288 45647751 43891818496 41981 262144 45647751 43891818496 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 135664507503 274877906944 12009609343701 23011953735630848 Bool.false 11005025283 137438953472 5986656542449 11505976867815424 Bool.false 3189158598134808444928 371266924559 274877906944 42954150770131 23011953735630848 Bool.true 2063456787699410665472 7506812063 68719476736 21386056713901 11505976867815424 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep99) rfl rfl

noncomputable abbrev qz533 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt qz533))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz268 qz286 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 120947316615 274877906944 10746212335665 23011953735630848 Bool.true 10992610127 137438953472 1338859748149 2876494216953856 (BSN.cpow_neg_s_mk qz13 85999 1000 5 qz14 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz533) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz533) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz533 qz15)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz533 qz15)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 11734546589655452485523914939250625

noncomputable def ep104 := nat_lit 2429970938528035899633153341031900

noncomputable def ep105 := nat_lit 824199001261152424427520000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 17 16 ep103 262144 83717 ep104 ep105 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 1389564272027489355923890120811536

noncomputable def ep108 := BSN.cos_dyadic_bound_f 193072162 1073741824 2 1 524288 167598 ep107 ep75 ep107 ep107 ep76 ep107 515835 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 193072162) qz294 0 1 ep107 ep75 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 193072162) qz295 0 1 ep107 ep76 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18141661) qz531)

noncomputable abbrev qz307 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 83717 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 83717 rfl rfl rfl (ep106 rfl)))

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz28 qz306 Bool.false 18141661 131072 539 524288 Bool.false 515835 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 2267707631 16384000 85999 83717000 18141661 131072 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 85999 1000 0 1 421904 262144 1 83717 2267707631 16384000 85999 83717000 qz17 qz307 rfl) rfl) (Enclosure.sfrac_false_div 18141661 131072) (BSN.cos_reduce0 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3396561398436842176512) qz293) 226375608064910080 72057594037927936 Bool.false 515835 524288 22 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 18141661 131072 226375608064910080 72057594037927936 22 3396561398436842176512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515835 524288 3396561398436842176512 18889465931478580854784 193072162 1073741824 167598 167434 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := BSN.sin_dyadic_bound_f 193072162 1073741824 2 1 524288 167598 ep107 ep79 ep107 ep107 ep80 ep107 93766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 193072162) qz289 0 1 ep107 ep79 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 193072162) qz290 0 1 ep107 ep80 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz28 qz306 Bool.false 18141661 131072 539 524288 Bool.false 93766 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 2267707631 16384000 85999 83717000 18141661 131072 539 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 85999 1000 0 1 421904 262144 1 83717 2267707631 16384000 85999 83717000 qz17 qz307 rfl) rfl) (Enclosure.sfrac_false_div 18141661 131072) (BSN.sin_reduce0 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3396561398436842176512) qz293) 226375608064910080 72057594037927936 Bool.false 93766 524288 22 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 18141661 131072 226375608064910080 72057594037927936 22 3396561398436842176512 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93766 524288 3396561398436842176512 18889465931478580854784 193072162 1073741824 167598 167434 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep102 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 120947316615 274877906944 10746212335665 23011953735630848 Bool.true 10992610127 137438953472 1338859748149 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz28) 234469 524288 1 524288 515835 524288 45647751 43891818496 120947316615 274877906944 10746212335665 23011953735630848 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 515835 524288 45647751 43891818496 515835 524288 45647751 43891818496 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 234469 524288 1 524288 46883 262144 45647751 43891818496 10992610127 137438953472 1338859748149 2876494216953856 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 46883 262144 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 93766 524288 45647751 43891818496 46883 262144 45647751 43891818496 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep45 120947316615 274877906944 10746212335665 23011953735630848 Bool.true 10992610127 137438953472 1338859748149 2876494216953856 Bool.false 135298820381938345312256 246107120587 137438953472 13425090776449 5752988433907712 Bool.true 1787134809739999838208 26006234253 137438953472 26741495706497 11505976867815424 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep112) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz534 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz268 qz286 qz534)

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 55467136655 137438953472 4915876547325 11505976867815424 Bool.false 8462459943 137438953472 4897491624389 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 6 qz14 rfl)

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz310) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz310) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 83717 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz534 85999 1000 0 1 4034681531866359 2251799813685248 500000000083717 41858500000000000000 346978577058975007641 2251799813685248000 42999500007199578283 41858500000000000000000 qz17 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 16922680887833197019136 9444732965739290427392 1000000000167434 83717000000000000000 4034681531866359 2251799813685248 500000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 698421478147308754352811048254881

noncomputable def ep119 := BSN.cos_dyadic_bound_f 162565879 1073741824 2 1 524288 167598 ep118 ep75 ep118 ep118 ep76 ep118 518290 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 162565879) qz294 0 1 ep118 ep75 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 162565879) qz295 0 1 ep118 ep76 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80787245) qz24)

noncomputable def ep120 := @Enclosure.Real.IsNear.cos_image qz31 qz311 Bool.false 80787245 524288 135 131072 Bool.true 518290 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 346978577058975007641 2251799813685248000 42999500007199578283 41858500000000000000000 80787245 524288 135 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 80787245 524288) (BSN.cos_reduce2 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11439556793960465694720) qz26) 226375608064910080 72057594037927936 Bool.false 518290 524288 24 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 80787245 524288 226375608064910080 72057594037927936 24 11439556793960465694720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518290 524288 11439556793960465694720 75557863725914323419136 162565879 1073741824 167598 167434 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep121 := BSN.sin_dyadic_bound_f 162565879 1073741824 1 0 524288 167598 0 1 1 0 1 1 79074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 162565879) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 162565879) qz290 0 0 rfl) rfl rfl

noncomputable def ep122 := @Enclosure.Real.IsNear.sin_image qz31 qz311 Bool.false 80787245 524288 135 131072 Bool.true 79074 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 346978577058975007641 2251799813685248000 42999500007199578283 41858500000000000000000 80787245 524288 135 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 80787245 524288) (BSN.sin_reduce2 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11439556793960465694720) qz26) 226375608064910080 72057594037927936 Bool.false 79074 524288 24 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 80787245 524288 226375608064910080 72057594037927936 24 11439556793960465694720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79074 524288 11439556793960465694720 75557863725914323419136 162565879 1073741824 167598 167434 (ep121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz312 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep115 rfl rfl) rfl)

noncomputable def ep123 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 55467136655 137438953472 4915876547325 11505976867815424 Bool.false 8462459943 137438953472 4897491624389 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 214039 524288 1 524288 259145 262144 11432867 10972954624 55467136655 137438953472 4915876547325 11505976867815424 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 518290 524288 11432867 10972954624 259145 262144 11432867 10972954624 (ep120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 214039 524288 1 524288 39537 262144 11432867 10972954624 8462459943 137438953472 4897491624389 11505976867815424 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 39537 262144 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 79074 524288 11432867 10972954624 39537 262144 11432867 10972954624 (ep122 rfl rfl) rfl)) rfl)

noncomputable def ep124 := @ep43 55467136655 137438953472 4915876547325 11505976867815424 Bool.false 8462459943 137438953472 4897491624389 11505976867815424 Bool.false 26201359881532975611904 47659995983 34359738368 31766058100223 11505976867815424 Bool.true 2411197981115358904320 8771887155 68719476736 15819493665443 5752988433907712 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep123) rfl rfl

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt qz313))

noncomputable abbrev qz535 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz268 qz286 qz535)

noncomputable def ep125 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.true 540786827 2147483648 568223373591 1438247108476928 Bool.false 77475986273 274877906944 9095061543959 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 7 qz14 rfl)

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep126 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz313) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz313) (Real.sqrt qz314) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz314) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep127 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 83717 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz535 85999 1000 0 1 4381792198794487 2251799813685248 500000000083717 41858500000000000000 376829747304127087513 2251799813685248000 42999500007199578283 41858500000000000000000 qz17 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 18378568546572512002048 9444732965739290427392 1000000000167434 83717000000000000000 4381792198794487 2251799813685248 500000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep127 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep129 := nat_lit 1489661148678980283947382194905626263971497614287696809287020759616752515201

noncomputable def ep130 := nat_lit 444731721472633131503985578011236256913995696813278763360966961454446721

noncomputable def ep131 := nat_lit 4468093982593995585579138613560856319400664851469463870334340344927348652161

noncomputable def ep132 := BSN.cos_dyadic_bound_f 903674991 1073741824 3 2 524288 167598 ep129 ep64 ep130 ep131 ep66 ep130 349312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 903674991) qz294 0 2 ep129 ep64 ep130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 903674991) qz295 0 2 ep131 ep66 ep130 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10967189) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep133 := @Enclosure.Real.IsNear.cos_image qz33 qz315 Bool.false 10967189 65536 135 131072 Bool.true 349312 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 376829747304127087513 2251799813685248000 42999500007199578283 41858500000000000000000 10967189 65536 135 131072 (ep128 rfl) rfl) (Enclosure.sfrac_false_div 10967189 65536) (BSN.cos_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7948809283411302678528) qz301) 226375608064910080 72057594037927936 Bool.false 349312 524288 26 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 10967189 65536 226375608064910080 72057594037927936 26 7948809283411302678528 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 349312 524288 7948809283411302678528 9444732965739290427392 903674991 1073741824 167598 167434 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep134 := nat_lit 666882089632517519977888598633706561

noncomputable def ep135 := BSN.sin_dyadic_bound_f 903674991 1073741824 2 1 524288 167598 ep134 ep79 ep134 ep134 ep80 ep134 390971 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 903674991) qz289 0 1 ep134 ep79 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 903674991) qz290 0 1 ep134 ep80 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep136 := @Enclosure.Real.IsNear.sin_image qz33 qz315 Bool.false 10967189 65536 135 131072 Bool.true 390971 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 376829747304127087513 2251799813685248000 42999500007199578283 41858500000000000000000 10967189 65536 135 131072 (ep128 rfl) rfl) (Enclosure.sfrac_false_div 10967189 65536) (BSN.sin_reduce2 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7948809283411302678528) qz301) 226375608064910080 72057594037927936 Bool.false 390971 524288 26 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 10967189 65536 226375608064910080 72057594037927936 26 7948809283411302678528 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390971 524288 7948809283411302678528 9444732965739290427392 903674991 1073741824 167598 167434 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep126 rfl rfl) rfl)

noncomputable def ep137 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.true 540786827 2147483648 568223373591 1438247108476928 Bool.false 77475986273 274877906944 9095061543959 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz33) 198163 524288 1 524288 2729 4096 11432867 10972954624 540786827 2147483648 568223373591 1438247108476928 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.true 349312 524288 11432867 10972954624 2729 4096 11432867 10972954624 (ep133 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 198163 524288 1 524288 390971 524288 11432867 10972954624 77475986273 274877906944 9095061543959 23011953735630848 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 390971 524288 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 390971 524288 11432867 10972954624 390971 524288 11432867 10972954624 (ep136 rfl rfl) rfl)) rfl)

noncomputable def ep138 := @ep41 540786827 2147483648 568223373591 1438247108476928 Bool.false 77475986273 274877906944 9095061543959 23011953735630848 Bool.false 83767768148657307648 39007406751 34359738368 36311845088951 11505976867815424 Bool.false 2912911255170719940608 42388437653 274877906944 72373036205731 23011953735630848 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep124 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep125 ep137) rfl rfl

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz317))

noncomputable abbrev qz536 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz268 qz286 qz536)

noncomputable def ep139 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 94377386087 274877906944 8504074143197 23011953735630848 Bool.true 5796115647 68719476736 529495043991 1438247108476928 (BSN.cpow_neg_s_mk qz13 85999 1000 8 qz14 rfl)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep140 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz317) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz317) (Real.sqrt qz318) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep141 := BSN.log_dyadic_bound 0 16 1 0 1 262144 83717 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz536 85999 1000 0 1 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 805378240121178933963 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 19639770079031275290624 9444732965739290427392 1000000000251151 83717000000000000000 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep143 := nat_lit 16730788114686179146524336846015467611728282292847142759794985445979974380865

noncomputable def ep144 := nat_lit 17289093679976431302099735954815672379677164017991422022023018876801756481

noncomputable def ep145 := nat_lit 43790738910600983542598435024208904084959357263332435401903591280337491963201

noncomputable def ep146 := BSN.sin_dyadic_bound_f 1427978039 1073741824 3 2 524288 167598 ep143 ep57 ep144 ep145 ep60 ep144 509149 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1427978039) qz289 0 2 ep143 ep57 ep144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1427978039) qz290 0 2 ep145 ep60 ep144 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93758367) qz24)

noncomputable def ep147 := @Enclosure.Real.IsNear.cos_image qz35 qz319 Bool.false 93758367 524288 539 524288 Bool.true 509149 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 805378240121178933963 4503599627370496000 85999000021598734849 83717000000000000000000 93758367 524288 539 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 93758367 524288) (BSN.cos_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100485021361798595477504) qz26) 226375608064910080 72057594037927936 Bool.false 509149 524288 28 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 93758367 524288 226375608064910080 72057594037927936 28 100485021361798595477504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 509149 524288 100485021361798595477504 75557863725914323419136 1427978039 1073741824 167598 167434 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep148 := nat_lit 9302566327572311273092231463766288972017791124478631054118113256156342103361

noncomputable def ep149 := nat_lit 27873120795356980956672494919389235571294019045399910318310293730715422797121

noncomputable def ep150 := BSN.cos_dyadic_bound_f 1427978039 1073741824 3 2 524288 167598 ep148 ep64 ep144 ep149 ep66 ep144 125076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1427978039) qz294 0 2 ep148 ep64 ep144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1427978039) qz295 0 2 ep149 ep66 ep144 rfl rfl rfl rfl) rfl rfl

noncomputable def ep151 := @Enclosure.Real.IsNear.sin_image qz35 qz319 Bool.false 93758367 524288 539 524288 Bool.false 125076 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 805378240121178933963 4503599627370496000 85999000021598734849 83717000000000000000000 93758367 524288 539 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 93758367 524288) (BSN.sin_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100485021361798595477504) qz26) 226375608064910080 72057594037927936 Bool.false 125076 524288 28 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 93758367 524288 226375608064910080 72057594037927936 28 100485021361798595477504 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 125076 524288 100485021361798595477504 75557863725914323419136 1427978039 1073741824 167598 167434 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep140 rfl rfl) rfl)

noncomputable def ep152 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 94377386087 274877906944 8504074143197 23011953735630848 Bool.true 5796115647 68719476736 529495043991 1438247108476928 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 185363 524288 1 524288 509149 524288 45647751 43891818496 94377386087 274877906944 8504074143197 23011953735630848 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 509149 524288 45647751 43891818496 509149 524288 45647751 43891818496 (ep147 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 185363 524288 1 524288 31269 131072 45647751 43891818496 5796115647 68719476736 529495043991 1438247108476928 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 31269 131072 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 125076 524288 45647751 43891818496 31269 131072 45647751 43891818496 (ep151 rfl rfl) rfl)) rfl)

noncomputable def ep153 := @ep39 94377386087 274877906944 8504074143197 23011953735630848 Bool.true 5796115647 68719476736 529495043991 1438247108476928 Bool.false 7479492029223092092928 217681867921 274877906944 81127764321099 23011953735630848 Bool.false 1319687117717991587840 19203975065 274877906944 80844956909587 23011953735630848 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep138 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep139 ep152) rfl rfl

theorem EMRow24.d6 : Enclosure.Complex.IsNear qz3 Bool.false 217681867921 274877906944 81127764321099 23011953735630848 Bool.false 19203975065 274877906944 80844956909587 23011953735630848 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep153 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz36 := (BSN.headSumC qz273 17)

noncomputable abbrev qz37 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz276)

noncomputable def ep154 := @Enclosure.Complex.IsNear.of_eq qz36 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz37) Bool.false 35680143545 17179869184 34084079850367 5752988433907712 Bool.true 12161664627 68719476736 33978940507237 5752988433907712

noncomputable def ep155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz37 Bool.false 505677488853 274877906944 130311530100387 23011953735630848 Bool.true 17585120465 68719476736 32479690960443 5752988433907712 Bool.false

noncomputable abbrev qz38 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz276)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz38) Bool.false 505677488853 274877906944 130311530100387 23011953735630848 Bool.true 17585120465 68719476736 32479690960443 5752988433907712

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz38 Bool.false 440626849997 274877906944 124080540781979 23011953735630848 Bool.true 10489243387 68719476736 30927612611213 5752988433907712 Bool.false

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz276)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz39) Bool.false 440626849997 274877906944 124080540781979 23011953735630848 Bool.true 10489243387 68719476736 30927612611213 5752988433907712

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz39 Bool.false 387444484931 274877906944 117640781570401 23011953735630848 Bool.false 8723811305 274877906944 117272185832875 23011953735630848 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz276)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz40) Bool.false 387444484931 274877906944 117640781570401 23011953735630848 Bool.false 8723811305 274877906944 117272185832875 23011953735630848

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz40 Bool.false 163874380845 137438953472 55478254460929 11505976867815424 Bool.false 56142338405 274877906944 110594981494359 23011953735630848 Bool.false

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz276)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz41) Bool.false 163874380845 137438953472 55478254460929 11505976867815424 Bool.false 56142338405 274877906944 110594981494359 23011953735630848

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz41 Bool.false 7768718311 8589934592 3249727200947 719123554238464 Bool.false 61779785957 274877906944 103670405521743 23011953735630848 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz276)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz42) Bool.false 7768718311 8589934592 3249727200947 719123554238464 Bool.false 61779785957 274877906944 103670405521743 23011953735630848

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz42 Bool.false 26643128479 34359738368 12094562237933 2876494216953856 Bool.true 13132903669 274877906944 96414736059665 23011953735630848 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz276)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz43) Bool.false 26643128479 34359738368 12094562237933 2876494216953856 Bool.true 13132903669 274877906944 96414736059665 23011953735630848

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz43 Bool.false 149819973871 137438953472 44572304193601 11505976867815424 Bool.true 21761870239 274877906944 88842164399887 23011953735630848 Bool.true

noncomputable abbrev qz321 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz321) Bool.false 149819973871 137438953472 44572304193601 11505976867815424 Bool.true 21761870239 274877906944 88842164399887 23011953735630848

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP qz3 qz321 Bool.false 217681867921 274877906944 81127764321099 23011953735630848 Bool.false 19203975065 274877906944 80844956909587 23011953735630848 Bool.false

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz322))

noncomputable abbrev qz537 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz268 qz286 qz537)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq qz321 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.false 81958079821 274877906944 8016844066103 23011953735630848 Bool.true 5120730663 34359738368 1999301872575 5752988433907712 (BSN.cpow_neg_s_mk qz13 85999 1000 9 qz14 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep171 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt qz323) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep172 := BSN.log_dyadic_bound 1 17 2 1 867 262144 83717 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep173 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz537 85999 1000 0 1 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 850996034795103832779 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 20752195215788806766592 9444732965739290427392 1000000000251151 83717000000000000000 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep172 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep174 := nat_lit 61357579310158682765939340849709056

noncomputable def ep175 := BSN.cos_dyadic_bound_f 497699328 1073741824 2 1 524288 167598 ep174 ep75 ep174 ep174 ep76 ep174 468967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 497699328) qz294 0 1 ep174 ep75 ep174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 497699328) qz295 0 1 ep174 ep76 ep174 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99068977) qz24)

noncomputable def ep176 := @Enclosure.Real.IsNear.cos_image qz45 qz324 Bool.false 99068977 524288 539 524288 Bool.false 468967 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 850996034795103832779 4503599627370496000 85999000021598734849 83717000000000000000000 99068977 524288 539 524288 (ep173 rfl) rfl) (Enclosure.sfrac_false_div 99068977 524288) (BSN.cos_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35022476701370515718144) qz26) 226375608064910080 72057594037927936 Bool.false 468967 524288 30 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 99068977 524288 226375608064910080 72057594037927936 30 35022476701370515718144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 468967 524288 35022476701370515718144 75557863725914323419136 497699328 1073741824 167598 167434 (ep175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep177 := BSN.sin_dyadic_bound_f 497699328 1073741824 2 1 524288 167598 ep174 ep79 ep174 ep174 ep80 ep174 234408 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 497699328) qz289 0 1 ep174 ep79 ep174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 497699328) qz290 0 1 ep174 ep80 ep174 rfl rfl rfl rfl) rfl rfl

noncomputable def ep178 := @Enclosure.Real.IsNear.sin_image qz45 qz324 Bool.false 99068977 524288 539 524288 Bool.false 234408 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 850996034795103832779 4503599627370496000 85999000021598734849 83717000000000000000000 99068977 524288 539 524288 (ep173 rfl) rfl) (Enclosure.sfrac_false_div 99068977 524288) (BSN.sin_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35022476701370515718144) qz26) 226375608064910080 72057594037927936 Bool.false 234408 524288 30 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 99068977 524288 226375608064910080 72057594037927936 30 35022476701370515718144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 234408 524288 35022476701370515718144 75557863725914323419136 497699328 1073741824 167598 167434 (ep177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep171 rfl rfl) rfl)

noncomputable def ep179 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.false 81958079821 274877906944 8016844066103 23011953735630848 Bool.true 5120730663 34359738368 1999301872575 5752988433907712 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz45) 174763 524288 1 524288 468967 524288 45647751 43891818496 81958079821 274877906944 8016844066103 23011953735630848 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.false 468967 524288 45647751 43891818496 468967 524288 45647751 43891818496 (ep176 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 174763 524288 1 524288 29301 65536 45647751 43891818496 5120730663 34359738368 1999301872575 5752988433907712 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.false 29301 65536 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.false 234408 524288 45647751 43891818496 29301 65536 45647751 43891818496 (ep178 rfl rfl) rfl)) rfl)

noncomputable def ep180 := @ep169 81958079821 274877906944 8016844066103 23011953735630848 Bool.true 5120730663 34359738368 1999301872575 5752988433907712 Bool.false 82364401672130498920448 149819973871 137438953472 44572304193601 11505976867815424 Bool.true 747732167810405629952 21761870239 274877906944 88842164399887 23011953735630848 EMRow24.d6 (ep170 ep179) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz538 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz268 qz286 qz538)

noncomputable def ep181 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 43247459955 137438953472 3805944758131 11505976867815424 Bool.false 4314483285 137438953472 3786285829889 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 10 qz14 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep182 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep183 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 83717 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep184 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz538 85999 1000 0 1 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 891801769705685895883 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 21747274560655572598784 9444732965739290427392 1000000000251151 83717000000000000000 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep183 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep185 := nat_lit 129940966577458139291973115100641

noncomputable def ep186 := BSN.cos_dyadic_bound_f 106766873 1073741824 2 1 524288 167598 ep185 ep75 ep185 ep185 ep76 ep185 521698 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 106766873) qz294 0 1 ep185 ep75 ep185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 106766873) qz295 0 1 ep185 ep76 ep185 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz48 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz49 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51909695) qz48)

noncomputable def ep187 := @Enclosure.Real.IsNear.cos_image qz47 qz328 Bool.false 51909695 262144 539 524288 Bool.true 521698 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 891801769705685895883 4503599627370496000 85999000021598734849 83717000000000000000000 51909695 262144 539 524288 (ep184 rfl) rfl) (Enclosure.sfrac_false_div 51909695 262144) (BSN.cos_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3756525413773890027520) qz49) 226375608064910080 72057594037927936 Bool.false 521698 524288 31 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 51909695 262144 226375608064910080 72057594037927936 31 3756525413773890027520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521698 524288 3756525413773890027520 37778931862957161709568 106766873 1073741824 167598 167434 (ep186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep188 := BSN.sin_dyadic_bound_f 106766873 1073741824 1 0 524288 167598 0 1 1 0 1 1 52046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 106766873) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 106766873) qz290 0 0 rfl) rfl rfl

noncomputable def ep189 := @Enclosure.Real.IsNear.sin_image qz47 qz328 Bool.false 51909695 262144 539 524288 Bool.true 52046 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 891801769705685895883 4503599627370496000 85999000021598734849 83717000000000000000000 51909695 262144 539 524288 (ep184 rfl) rfl) (Enclosure.sfrac_false_div 51909695 262144) (BSN.sin_reduce2 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3756525413773890027520) qz49) 226375608064910080 72057594037927936 Bool.false 52046 524288 31 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 51909695 262144 226375608064910080 72057594037927936 31 3756525413773890027520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 52046 524288 3756525413773890027520 37778931862957161709568 106766873 1073741824 167598 167434 (ep188 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep182 rfl rfl) rfl)

noncomputable def ep190 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 43247459955 137438953472 3805944758131 11505976867815424 Bool.false 4314483285 137438953472 3786285829889 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 165795 524288 1 524288 260849 262144 45647751 43891818496 43247459955 137438953472 3805944758131 11505976867815424 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 521698 524288 45647751 43891818496 260849 262144 45647751 43891818496 (ep187 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 165795 524288 1 524288 26023 262144 45647751 43891818496 4314483285 137438953472 3786285829889 11505976867815424 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.true 26023 262144 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.true 52046 524288 45647751 43891818496 26023 262144 45647751 43891818496 (ep189 rfl rfl) rfl)) rfl)

noncomputable def ep191 := @ep167 43247459955 137438953472 3805944758131 11505976867815424 Bool.false 4314483285 137438953472 3786285829889 11505976867815424 Bool.false 14647214781495196516352 26643128479 34359738368 12094562237933 2876494216953856 Bool.true 1804972536315949088768 13132903669 274877906944 96414736059665 23011953735630848 (ep168 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep180 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep181 ep190) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz539 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz268 qz286 qz539)

noncomputable def ep192 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 4431744765 34359738368 904346565855 2876494216953856 Bool.false 37456344813 137438953472 3627834731039 11505976867815424 (BSN.cpow_neg_s_mk qz13 85999 1000 11 qz14 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep193 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz331) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep194 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 83717 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep195 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz539 85999 1000 0 1 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 928715897181006973643 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 22647454054174387339264 9444732965739290427392 1000000000251151 83717000000000000000 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep194 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep196 := nat_lit 50749095943626125691827057433477376

noncomputable def ep197 := BSN.sin_dyadic_bound_f 474632068 1073741824 2 1 524288 167598 ep196 ep79 ep196 ep196 ep80 ep196 224280 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 474632068) qz289 0 1 ep196 ep79 ep196 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 474632068) qz290 0 1 ep196 ep80 ep196 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13514595) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep198 := @Enclosure.Real.IsNear.cos_image qz51 qz332 Bool.false 13514595 65536 539 524288 Bool.false 224280 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 928715897181006973643 4503599627370496000 85999000021598734849 83717000000000000000000 13514595 65536 539 524288 (ep195 rfl) rfl) (Enclosure.sfrac_false_div 13514595 65536) (BSN.cos_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4174907825426331074560) qz301) 226375608064910080 72057594037927936 Bool.false 224280 524288 32 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 13514595 65536 226375608064910080 72057594037927936 32 4174907825426331074560 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 224280 524288 4174907825426331074560 9444732965739290427392 474632068 1073741824 167598 167434 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep199 := BSN.cos_dyadic_bound_f 474632068 1073741824 2 1 524288 167598 ep196 ep75 ep196 ep196 ep76 ep196 473894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 474632068) qz294 0 1 ep196 ep75 ep196 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 474632068) qz295 0 1 ep196 ep76 ep196 rfl rfl rfl rfl) rfl rfl

noncomputable def ep200 := @Enclosure.Real.IsNear.sin_image qz51 qz332 Bool.false 13514595 65536 539 524288 Bool.true 473894 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 928715897181006973643 4503599627370496000 85999000021598734849 83717000000000000000000 13514595 65536 539 524288 (ep195 rfl) rfl) (Enclosure.sfrac_false_div 13514595 65536) (BSN.sin_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4174907825426331074560) qz301) 226375608064910080 72057594037927936 Bool.false 473894 524288 32 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 13514595 65536 226375608064910080 72057594037927936 32 4174907825426331074560 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 473894 524288 4174907825426331074560 9444732965739290427392 474632068 1073741824 167598 167434 (ep199 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep193 rfl rfl) rfl)

noncomputable def ep201 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 4431744765 34359738368 904346565855 2876494216953856 Bool.false 37456344813 137438953472 3627834731039 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 158079 524288 1 524288 28035 65536 45647751 43891818496 4431744765 34359738368 904346565855 2876494216953856 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 224280 524288 45647751 43891818496 28035 65536 45647751 43891818496 (ep198 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 158079 524288 1 524288 236947 262144 45647751 43891818496 37456344813 137438953472 3627834731039 11505976867815424 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 236947 262144 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 473894 524288 45647751 43891818496 236947 262144 45647751 43891818496 (ep200 rfl rfl) rfl)) rfl)

noncomputable def ep202 := @ep165 4431744765 34359738368 904346565855 2876494216953856 Bool.false 37456344813 137438953472 3627834731039 11505976867815424 Bool.false 1067724514482603425792 7768718311 8589934592 3249727200947 719123554238464 Bool.false 8490949127654241992704 61779785957 274877906944 103670405521743 23011953735630848 (ep166 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep191 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep192 ep201) rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz334))

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz268 qz286 qz540)

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 39574887869 137438953472 3482619245777 11505976867815424 Bool.true 44042559 2147483648 865571996577 2876494216953856 (BSN.cpow_neg_s_mk qz13 85999 1000 12 qz14 rfl)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep204 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz335) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz335) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep205 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 83717 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep206 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz540 85999 1000 0 1 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 962416567491676326603 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 23469270914176955449344 9444732965739290427392 1000000000251151 83717000000000000000 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep207 := BSN.cos_dyadic_bound_f 76348655 1073741824 1 0 524288 167598 0 1 1 0 1 1 522962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 76348655) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 76348655) qz295 0 0 rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56020017) qz48)

noncomputable def ep208 := @Enclosure.Real.IsNear.cos_image qz53 qz336 Bool.false 56020017 262144 135 131072 Bool.false 522962 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 962416567491676326603 4503599627370496000 85999000021598734849 83717000000000000000000 56020017 262144 135 131072 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 56020017 262144) (BSN.cos_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2686279490424069423104) qz49) 226375608064910080 72057594037927936 Bool.false 522962 524288 34 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 56020017 262144 226375608064910080 72057594037927936 34 2686279490424069423104 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522962 524288 2686279490424069423104 37778931862957161709568 76348655 1073741824 167598 167434 (ep207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep209 := BSN.sin_dyadic_bound_f 76348655 1073741824 1 0 524288 167598 0 1 1 0 1 1 37248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 76348655) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 76348655) qz290 0 0 rfl) rfl rfl

noncomputable def ep210 := @Enclosure.Real.IsNear.sin_image qz53 qz336 Bool.false 56020017 262144 135 131072 Bool.false 37248 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 962416567491676326603 4503599627370496000 85999000021598734849 83717000000000000000000 56020017 262144 135 131072 (ep206 rfl) rfl) (Enclosure.sfrac_false_div 56020017 262144) (BSN.sin_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2686279490424069423104) qz49) 226375608064910080 72057594037927936 Bool.false 37248 524288 34 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 56020017 262144 226375608064910080 72057594037927936 34 2686279490424069423104 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 37248 524288 2686279490424069423104 37778931862957161709568 76348655 1073741824 167598 167434 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep204 rfl rfl) rfl)

noncomputable def ep211 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 39574887869 137438953472 3482619245777 11505976867815424 Bool.true 44042559 2147483648 865571996577 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 151349 524288 1 524288 261481 262144 11432867 10972954624 39574887869 137438953472 3482619245777 11505976867815424 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 522962 524288 11432867 10972954624 261481 262144 11432867 10972954624 (ep208 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 151349 524288 1 524288 291 4096 11432867 10972954624 44042559 2147483648 865571996577 2876494216953856 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.false 291 4096 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.false 37248 524288 11432867 10972954624 291 4096 11432867 10972954624 (ep210 rfl rfl) rfl)) rfl)

noncomputable def ep212 := @ep163 39574887869 137438953472 3482619245777 11505976867815424 Bool.true 44042559 2147483648 865571996577 2876494216953856 Bool.false 1407670212763047690240 163874380845 137438953472 55478254460929 11505976867815424 Bool.false 120564753685219901440 56142338405 274877906944 110594981494359 23011953735630848 (ep164 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep202 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep203 ep211) rfl rfl

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz338))

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz268 qz286 qz541)

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 59695723241 274877906944 6684272648543 23011953735630848 Bool.true 11854631775 68719476736 1669301084629 5752988433907712 (BSN.cpow_neg_s_mk qz13 85999 1000 13 qz14 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep214 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz339) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep215 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 83717 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz541 85999 1000 0 1 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 198683291266493655183 900719925474099200 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 24225227133228857425920 9444732965739290427392 1000000000251151 83717000000000000000 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep217 := nat_lit 269903756264271518709433969695107856

noncomputable def ep218 := BSN.cos_dyadic_bound_f 720779178 1073741824 2 1 524288 167598 ep217 ep75 ep217 ep217 ep76 ep217 410531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 720779178) qz294 0 1 ep217 ep75 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 720779178) qz295 0 1 ep217 ep76 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 903507) (@Nat.cast Real Real.instNatCast 4096))

noncomputable def ep219 := @Enclosure.Real.IsNear.cos_image qz55 qz340 Bool.false 903507 4096 135 131072 Bool.false 410531 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 198683291266493655183 900719925474099200 85999000021598734849 83717000000000000000000 903507 4096 135 131072 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 903507 4096) (BSN.cos_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 396252544110275067904) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 410531 524288 35 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 903507 4096 226375608064910080 72057594037927936 35 396252544110275067904 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 410531 524288 396252544110275067904 590295810358705651712 720779178 1073741824 167598 167434 (ep218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep220 := BSN.sin_dyadic_bound_f 720779178 1073741824 2 1 524288 167598 ep217 ep79 ep217 ep217 ep80 ep217 326100 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 720779178) qz289 0 1 ep217 ep79 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 720779178) qz290 0 1 ep217 ep80 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable def ep221 := @Enclosure.Real.IsNear.sin_image qz55 qz340 Bool.false 903507 4096 135 131072 Bool.false 326100 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 198683291266493655183 900719925474099200 85999000021598734849 83717000000000000000000 903507 4096 135 131072 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 903507 4096) (BSN.sin_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 396252544110275067904) (@Nat.cast Real Real.instNatCast 590295810358705651712)) 226375608064910080 72057594037927936 Bool.false 326100 524288 35 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 903507 4096 226375608064910080 72057594037927936 35 396252544110275067904 590295810358705651712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 326100 524288 396252544110275067904 590295810358705651712 720779178 1073741824 167598 167434 (ep220 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep214 rfl rfl) rfl)

noncomputable def ep222 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 59695723241 274877906944 6684272648543 23011953735630848 Bool.true 11854631775 68719476736 1669301084629 5752988433907712 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 145411 524288 1 524288 410531 524288 11432867 10972954624 59695723241 274877906944 6684272648543 23011953735630848 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 410531 524288 11432867 10972954624 410531 524288 11432867 10972954624 (ep219 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 145411 524288 1 524288 81525 131072 11432867 10972954624 11854631775 68719476736 1669301084629 5752988433907712 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 81525 131072 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 326100 524288 11432867 10972954624 81525 131072 11432867 10972954624 (ep221 rfl rfl) rfl)) rfl)

noncomputable def ep223 := @ep161 59695723241 274877906944 6684272648543 23011953735630848 Bool.true 11854631775 68719476736 1669301084629 5752988433907712 Bool.false 53249964537414714130432 387444484931 274877906944 117640781570401 23011953735630848 Bool.false 599495748023201300480 8723811305 274877906944 117272185832875 23011953735630848 (ep162 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep212 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep213 ep222) rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz342))

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz268 qz286 qz542)

noncomputable def ep224 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 26591182533 137438953472 3219879605789 11505976867815424 Bool.true 50680784853 274877906944 6438264611977 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 14 qz14 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep225 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz342) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz342) (Real.sqrt qz343) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep226 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 83717 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep227 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz542 85999 1000 0 1 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 1022118907981980486347 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 24925158572916270432256 9444732965739290427392 1000000000251151 83717000000000000000 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep228 := nat_lit 997371358386282794564795144775698878309053260230774742885373815864321515776

noncomputable def ep229 := nat_lit 199398823944187528403757435009189778592534569285734798630342817658839296

noncomputable def ep230 := nat_lit 2991715277510960008637577919457078255369974711553752759058860761957646868736

noncomputable def ep231 := BSN.cos_dyadic_bound_f 817457766 1073741824 3 2 524288 167598 ep228 ep64 ep229 ep230 ep66 ep229 379546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 817457766) qz294 0 2 ep228 ep64 ep229 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 817457766) qz295 0 2 ep230 ep66 ep229 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118990301) qz24)

noncomputable def ep232 := @Enclosure.Real.IsNear.cos_image qz57 qz344 Bool.false 118990301 524288 135 131072 Bool.false 379546 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 1022118907981980486347 4503599627370496000 85999000021598734849 83717000000000000000000 118990301 524288 135 131072 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 118990301 524288) (BSN.cos_reduce0 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57523476454178094579712) qz26) 226375608064910080 72057594037927936 Bool.false 379546 524288 36 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 118990301 524288 226375608064910080 72057594037927936 36 57523476454178094579712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 379546 524288 57523476454178094579712 75557863725914323419136 817457766 1073741824 167598 167434 (ep231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep233 := nat_lit 446540954386255067048748744990091536

noncomputable def ep234 := BSN.sin_dyadic_bound_f 817457766 1073741824 2 1 524288 167598 ep233 ep79 ep233 ep233 ep80 ep233 361693 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 817457766) qz289 0 1 ep233 ep79 ep233 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 817457766) qz290 0 1 ep233 ep80 ep233 rfl rfl rfl rfl) rfl rfl

noncomputable def ep235 := @Enclosure.Real.IsNear.sin_image qz57 qz344 Bool.false 118990301 524288 135 131072 Bool.false 361693 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 1022118907981980486347 4503599627370496000 85999000021598734849 83717000000000000000000 118990301 524288 135 131072 (ep227 rfl) rfl) (Enclosure.sfrac_false_div 118990301 524288) (BSN.sin_reduce0 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57523476454178094579712) qz26) 226375608064910080 72057594037927936 Bool.false 361693 524288 36 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 118990301 524288 226375608064910080 72057594037927936 36 57523476454178094579712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 361693 524288 57523476454178094579712 75557863725914323419136 817457766 1073741824 167598 167434 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep225 rfl rfl) rfl)

noncomputable def ep236 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 26591182533 137438953472 3219879605789 11505976867815424 Bool.true 50680784853 274877906944 6438264611977 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 140121 524288 1 524288 189773 262144 11432867 10972954624 26591182533 137438953472 3219879605789 11505976867815424 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 379546 524288 11432867 10972954624 189773 262144 11432867 10972954624 (ep232 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 140121 524288 1 524288 361693 524288 11432867 10972954624 50680784853 274877906944 6438264611977 23011953735630848 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.false 361693 524288 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.false 361693 524288 11432867 10972954624 361693 524288 11432867 10972954624 (ep235 rfl rfl) rfl)) rfl)

noncomputable def ep237 := @ep159 26591182533 137438953472 3219879605789 11505976867815424 Bool.true 50680784853 274877906944 6438264611977 23011953735630848 Bool.false 60559293135251606339584 440626849997 274877906944 124080540781979 23011953735630848 Bool.true 11533045070579013517312 10489243387 68719476736 30927612611213 5752988433907712 (ep160 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep223 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep224 ep236) rfl rfl

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz346))

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz268 qz286 qz543)

noncomputable def ep238 := @Enclosure.Complex.IsNear.of_eq qz38 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 8131329857 34359738368 778873664801 2876494216953856 Bool.true 3547938539 34359738368 776039174615 2876494216953856 (BSN.cpow_neg_s_mk qz13 85999 1000 15 qz14 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep239 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz346) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz346) (Real.sqrt qz347) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep240 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 83717 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep241 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz543 85999 1000 0 1 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 1048840097076183288523 4503599627370496000 85999000021598734849 83717000000000000000000 qz17 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 25576775395801252757504 9444732965739290427392 1000000000251151 83717000000000000000 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep240 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep242 := nat_lit 38086746744003510036671923220710416

noncomputable def ep243 := BSN.cos_dyadic_bound_f 441767202 1073741824 2 1 524288 167598 ep242 ep75 ep242 ep242 ep76 ep242 480536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 441767202) qz294 0 1 ep242 ep75 ep242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 441767202) qz295 0 1 ep242 ep76 ep242 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122101057) qz24)

noncomputable def ep244 := @Enclosure.Real.IsNear.cos_image qz59 qz348 Bool.false 122101057 524288 135 131072 Bool.false 480536 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 1048840097076183288523 4503599627370496000 85999000021598734849 83717000000000000000000 122101057 524288 135 131072 (ep241 rfl) rfl) (Enclosure.sfrac_false_div 122101057 524288) (BSN.cos_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31086603247732899446784) qz26) 226375608064910080 72057594037927936 Bool.false 480536 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 122101057 524288 226375608064910080 72057594037927936 37 31086603247732899446784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 480536 524288 31086603247732899446784 75557863725914323419136 441767202 1073741824 167598 167434 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep245 := BSN.sin_dyadic_bound_f 441767202 1073741824 2 1 524288 167598 ep242 ep79 ep242 ep242 ep80 ep242 209672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 441767202) qz289 0 1 ep242 ep79 ep242 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 441767202) qz290 0 1 ep242 ep80 ep242 rfl rfl rfl rfl) rfl rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.sin_image qz59 qz348 Bool.false 122101057 524288 135 131072 Bool.false 209672 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 1048840097076183288523 4503599627370496000 85999000021598734849 83717000000000000000000 122101057 524288 135 131072 (ep241 rfl) rfl) (Enclosure.sfrac_false_div 122101057 524288) (BSN.sin_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31086603247732899446784) qz26) 226375608064910080 72057594037927936 Bool.false 209672 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 122101057 524288 226375608064910080 72057594037927936 37 31086603247732899446784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 209672 524288 31086603247732899446784 75557863725914323419136 441767202 1073741824 167598 167434 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep239 rfl rfl) rfl)

noncomputable def ep247 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 8131329857 34359738368 778873664801 2876494216953856 Bool.true 3547938539 34359738368 776039174615 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 135371 524288 1 524288 60067 65536 11432867 10972954624 8131329857 34359738368 778873664801 2876494216953856 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 480536 524288 11432867 10972954624 60067 65536 11432867 10972954624 (ep244 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 135371 524288 1 524288 26209 65536 11432867 10972954624 3547938539 34359738368 776039174615 2876494216953856 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 26209 65536 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 209672 524288 11432867 10972954624 26209 65536 11432867 10972954624 (ep246 rfl rfl) rfl)) rfl)

noncomputable def ep248 := @ep157 8131329857 34359738368 778873664801 2876494216953856 Bool.true 3547938539 34359738368 776039174615 2876494216953856 Bool.false 17374946215576316411904 505677488853 274877906944 130311530100387 23011953735630848 Bool.true 604220138347162501120 17585120465 68719476736 32479690960443 5752988433907712 (ep158 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep237 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep238 ep247) rfl rfl

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz268 qz286 qz544)

noncomputable def ep249 := @Enclosure.Complex.IsNear.of_eq qz37 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 65204807867 274877906944 6024789301081 23011953735630848 Bool.false 2711727919 34359738368 749624773397 2876494216953856 (BSN.cpow_neg_s_mk qz13 85999 1000 16 qz14 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep250 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz351) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep251 := BSN.log_dyadic_bound 0 32 1 0 1 262144 83717 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep252 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 85999 1000 0 1 3121657384082679 1125899906842624 250000000083717 20929250000000000000 268459413373726311321 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 26186360105375033720832 9444732965739290427392 1000000000334868 83717000000000000000 3121657384082679 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep253 := nat_lit 13038623149250105170975638869390631750629878716458227280590207324511957930625

noncomputable def ep254 := nat_lit 10505115608086949728922832098686035660263769913897832615783644216062890625

noncomputable def ep255 := nat_lit 34131766632289563243470321977387115289152112439434760672548798044991026090625

noncomputable def ep256 := BSN.sin_dyadic_bound_f 1341760815 1073741824 3 2 524288 167598 ep253 ep57 ep254 ep255 ep60 ep254 497477 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1341760815) qz289 0 2 ep253 ep57 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1341760815) qz290 0 2 ep255 ep60 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31252789) qz531)

noncomputable def ep257 := @Enclosure.Real.IsNear.cos_image qz61 qz352 Bool.false 31252789 131072 539 524288 Bool.false 497477 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 268459413373726311321 1125899906842624000 21499750007199578283 20929250000000000000000 31252789 131072 539 524288 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 31252789 131072) (BSN.cos_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23604505887171567157248) qz293) 226375608064910080 72057594037927936 Bool.false 497477 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 31252789 131072 226375608064910080 72057594037927936 37 23604505887171567157248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 497477 524288 23604505887171567157248 18889465931478580854784 1341760815 1073741824 167598 167434 (ep256 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep258 := nat_lit 7248348467631430405977098408371989210643383184660747525934907911047115690625

noncomputable def ep259 := nat_lit 21724035171678117318473449560918595560609622014154446912573156444709221290625

noncomputable def ep260 := BSN.cos_dyadic_bound_f 1341760815 1073741824 3 2 524288 167598 ep258 ep64 ep254 ep259 ep66 ep254 165512 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1341760815) qz294 0 2 ep258 ep64 ep254 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1341760815) qz295 0 2 ep259 ep66 ep254 rfl rfl rfl rfl) rfl rfl

noncomputable def ep261 := @Enclosure.Real.IsNear.sin_image qz61 qz352 Bool.false 31252789 131072 539 524288 Bool.true 165512 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 268459413373726311321 1125899906842624000 21499750007199578283 20929250000000000000000 31252789 131072 539 524288 (ep252 rfl) rfl) (Enclosure.sfrac_false_div 31252789 131072) (BSN.sin_reduce3 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23604505887171567157248) qz293) 226375608064910080 72057594037927936 Bool.false 165512 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 31252789 131072 226375608064910080 72057594037927936 37 23604505887171567157248 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 165512 524288 23604505887171567157248 18889465931478580854784 1341760815 1073741824 167598 167434 (ep260 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep250 rfl rfl) rfl)

noncomputable def ep262 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 65204807867 274877906944 6024789301081 23011953735630848 Bool.false 2711727919 34359738368 749624773397 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 131071 524288 1 524288 497477 524288 45647751 43891818496 65204807867 274877906944 6024789301081 23011953735630848 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 497477 524288 45647751 43891818496 497477 524288 45647751 43891818496 (ep257 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 131071 524288 1 524288 20689 65536 45647751 43891818496 2711727919 34359738368 749624773397 2876494216953856 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 20689 65536 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 165512 524288 45647751 43891818496 20689 65536 45647751 43891818496 (ep261 rfl rfl) rfl)) rfl)

noncomputable def ep263 := @ep155 65204807867 274877906944 6024789301081 23011953735630848 Bool.false 2711727919 34359738368 749624773397 2876494216953856 Bool.false 156922930833777156423680 35680143545 17179869184 34084079850367 5752988433907712 Bool.true 417871614703080308736 12161664627 68719476736 33978940507237 5752988433907712 (ep156 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep248 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep249 ep262) rfl rfl

theorem EMRow24.d7 : Enclosure.Complex.IsNear qz36 Bool.false 35680143545 17179869184 34084079850367 5752988433907712 Bool.true 12161664627 68719476736 33978940507237 5752988433907712 := ep154 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep263 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow24.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow24.d9 : @Eq Nat (Nat.pow 22 1) 22 := @Eq.refl Nat 22

noncomputable def ep264 := nat_lit 108339831674218680605354186571161

noncomputable def ep265 := nat_lit 56278842688876639082902034841600

noncomputable def ep266 := nat_lit 294749433090711803422136007722723789917

noncomputable def ep267 := nat_lit 35857481821104156716504252185353545318400

noncomputable abbrev qz571 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz545 := qz571

noncomputable abbrev qz354 := qz545

noncomputable abbrev qz62 := qz354

noncomputable abbrev qz546 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz355 := qz546

noncomputable abbrev qz63 := qz355

noncomputable abbrev qz572 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz573 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz547 := (@HAdd.hAdd Complex Complex Complex qz569 (@HAdd.hAdd Complex Complex Complex qz569 qz572 (@HMul.hMul Complex Complex Complex qz571 Complex.I (@HDiv.hDiv Complex Complex Complex qz573 (↑qz570) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz356 := qz547

noncomputable abbrev qz64 := (Complex.Stirling.logGammaStirling 1 qz356)

noncomputable abbrev qz548 := (@HAdd.hAdd Complex Complex Complex qz569 qz572 (@HMul.hMul Complex Complex Complex qz571 Complex.I (@HDiv.hDiv Complex Complex Complex qz573 (↑qz570) (2 : Complex))))

noncomputable abbrev qz357 := qz548

noncomputable abbrev qz65 := qz357

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz286 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz358 := (@instHSub Real Real.instSub)

noncomputable def ep268 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66))) (zetaApproximant qz5 1 22))

noncomputable def ep269 := @Enclosure.Real.IsNear.of_eq ep268 (@HSub.hSub Real Real Real qz358 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 22))))

noncomputable def ep270 := nat_lit 180565611624328847439955827310813

noncomputable def ep271 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 22))) ep270

noncomputable def ep272 := nat_lit 93798071148127731804836724736000

noncomputable def ep273 := nat_lit 16181984741123837160212653501499310087329

noncomputable def ep274 := nat_lit 1972161500160728619407733870194444992512000

noncomputable def ep275 := nat_lit 89365311802334880901958591

noncomputable def ep276 := nat_lit 10822854363245507515942699008000

noncomputable def ep277 := nat_lit 1124387648665847230954881663480706081

noncomputable def ep278 := nat_lit 75852365390797254592605148853632499712000

noncomputable def ep279 := nat_lit 1954243699914335808262914348300296617078518898240325660180480000

noncomputable def ep280 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 22)) 524287 524288 5405243

noncomputable def ep281 := nat_lit 344402229359737791400427299

noncomputable def ep282 := nat_lit 178905622764831031427072000

noncomputable def ep283 := nat_lit 325910786206642117796069007251

noncomputable def ep284 := nat_lit 44932326063010078373940559872000

noncomputable def ep285 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 524287 524288 5405243

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36235885) qz24)

noncomputable def ep286 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz359 Bool.false 36235885 524288 63

noncomputable def ep287 := nat_lit 6305512054594222223204003

noncomputable def ep288 := nat_lit 13167545548800000000000000000

noncomputable def ep289 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) Bool.false 373516660664756269739 5404319552844595200 ep287 ep288

noncomputable def ep290 := nat_lit 1985765084794222223204003

noncomputable def ep291 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66 3197662034078744362327 27021597764222976000 ep290 ep288 6451730979 131072000

noncomputable def ep292 := nat_lit 244787878733254668936151040000

noncomputable def ep293 := nat_lit 1491377824285862299173047

noncomputable def ep294 := nat_lit 5486477312000000000000000000

noncomputable def ep295 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 152142613680220919649 2251799813685248000 ep293 ep294 Bool.false 3197662034078744362327 27021597764222976000

noncomputable def ep296 := nat_lit 1458609824230997526053047

noncomputable def ep297 := nat_lit 1828478684781054677655203

noncomputable def ep298 := @Enclosure.Complex.IsNear.subLitP qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 135202738721675812649 2251799813685248000 ep296 ep294 Bool.false 3281610536918604874327 27021597764222976000 ep297

noncomputable def ep299 := nat_lit 342594709138708130403450250384637952

noncomputable def ep300 := nat_lit 900061846570863461986391782705856512

noncomputable abbrev qz574 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz549 := qz574

noncomputable abbrev qz360 := (@HSub.hSub Complex Complex Complex qz546 qz547 qz549)

noncomputable abbrev qz361 := (Complex.log qz547)

noncomputable abbrev qz67 := (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 qz360 qz361) qz356)

noncomputable abbrev qz362 := qz549

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz354 qz362 ↑(Real.log qz272))

noncomputable abbrev qz550 := qz573

noncomputable abbrev qz363 := qz550

noncomputable abbrev qz69 := qz363

noncomputable abbrev qz70 := (@instHMul Nat instMulNat)

noncomputable abbrev qz551 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz364 := qz551

noncomputable abbrev qz71 := qz364

noncomputable abbrev qz72 := qz356

noncomputable abbrev qz365 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz73 := qz365

noncomputable abbrev qz366 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz74 := qz366

noncomputable abbrev qz367 := (@instHSub Int Int.instSub)

noncomputable abbrev qz368 := (@instHMul Int Int.instMul)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq qz64 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 135202738721675812649

noncomputable def ep302 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 135202966449969700649 2251799813685248000

noncomputable def ep303 := nat_lit 2322765364556921846566712508416

noncomputable def ep304 := nat_lit 28188819868548817098361310019584000

noncomputable def ep305 := @ep302 89026420054074985783 334868000000000000000000 Bool.false 1093887587333353690653 9007199254740992000 4649950007228879233 33486800000000000000000 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000 Bool.true ep303 135202738721675812649 2251799813685248000 ep296 ep294 Bool.false ep304

noncomputable def ep306 := @Enclosure.Complex.IsNear.addLitP qz67 qz68 Bool.true 137272230153574948649 2251799813685248000 87749000010129673283 334868000000000000000000

noncomputable def ep307 := nat_lit 17721323218530428603465728

noncomputable def ep308 := @ep306 Bool.false 1093887587333353690653 9007199254740992000 4649950007228879233 33486800000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep307 135202966449969700649 2251799813685248000 89026420054074985783 334868000000000000000000 Bool.false 1093887587333353690653 1093887587333353690653 9007199254740992000

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz354 qz360 qz361)

noncomputable def ep309 := @Enclosure.Complex.IsNear.subLitP qz75 qz72 Bool.true 132205680572783140649 2251799813685248000 87749000010129673283 334868000000000000000000 Bool.false 1481192651687588976157

noncomputable def ep310 := nat_lit 4375550349333414762612000

noncomputable def ep311 := @ep309 9007199254740992000 4649950007228879233 33486800000000000000000 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 Bool.true 549088920614299794596000 137272230153574948649 2251799813685248000 87749000010129673283 334868000000000000000000 Bool.false ep310 1093887587333353690653 9007199254740992000 4649950007228879233 33486800000000000000000

noncomputable abbrev qz76 := qz360

noncomputable abbrev qz77 := qz361

noncomputable def ep312 := @Enclosure.Complex.IsNear.mul qz76 qz77 Bool.true 132205680572783140649 2251799813685248000 87749000010129673283 334868000000000000000000 Bool.false 1481192651687588976157 9007199254740992000 4649950007228879233

noncomputable abbrev qz78 := (Complex.re qz360)

noncomputable abbrev qz79 := (Complex.re qz361)

noncomputable abbrev qz80 := (Complex.im qz360)

noncomputable abbrev qz81 := (Complex.im qz361)

noncomputable def ep313 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz78 qz79) (@HMul.hMul Real Real Real qz0 qz80 qz81) 118615307661800901 18014398509481984 350000000586019 66973600000000000000 73516297015254126637 1125899906842624000

noncomputable def ep314 := nat_lit 1190802907527697948816437600801783808

noncomputable def ep315 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz79 7000 4000 0 1 16945043951685843 4503599627370496 50000000083717 16743400000000000000

noncomputable def ep316 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable abbrev qz369 := (Enclosure.sfrac Bool.false 171998 4000)

noncomputable abbrev qz82 := qz369

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz82) Bool.false 7000 4000 0 1 Bool.false 171998 4000 0

noncomputable abbrev qz370 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz83 := qz370

noncomputable abbrev qz371 := (Complex.log (Complex.mk qz83 qz82))

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq qz77 qz371 Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep319 := nat_lit 445616888943529036657176791305688570501508129321349191266965067921496266923593660813148775128470502097965547520

noncomputable def ep320 := nat_lit 13010336100413247216204808284129475365091826987721132490745956272956550341988565801347265584889110073577570304

noncomputable def ep321 := nat_lit 161255520711329383584810236646246970805982625278426077204576503715434627118235876336058915185859960504320

noncomputable def ep322 := BSN.log_dyadic_bound 13280312004 46048312004 6 5 ep319 524288 167434 ep320 ep321 311238 59328624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13280312004) (BSN.artanhQ 46048312004) 0 5 ep320 ep319 ep321 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz84 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz372 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 29664312004 16000000))

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz552 1 2 0 1 16945043951685843 2251799813685248 50000000083717 8371700000000000000 16945043951685843 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 29664312004 16000000 16945043951685843 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664312004) qz373)) Bool.false 142145331253463476076544 18889465931478580854784 1000000001674340 167434000000000000000 16945043951685843 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 29664312004 16000000 10 59328624008 32768000000 311238 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := BSN.arctan_dyadic_bound_f 9000 171998 1 0 524288 167434 0 1 1 0 1 1 27408 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz86 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz372 BSN.pi_near_15 rfl)

noncomputable abbrev qz374 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 171998)))

noncomputable def ep325 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz374 884279719003555 562949953421312 1 2000000000000000 27408 524288 1 167434 448187912993564524544 854850603091363 562949953421312 1000000000083717 167434000000000000000 qz86 (ep324 rfl) rfl rfl

noncomputable abbrev qz375 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 171998) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep326 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (ep318 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 85999 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz371 Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz371) (@HMul.hMul Real Real Real qz0 qz84 qz552) Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 9000 171998 4000 29664312004 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz371) qz375 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 9000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz375 (@HSub.hSub Real Real Real qz358 qz85 qz374) Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 171998 9000 rfl rfl) ep325))))

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz81 171998 4000 0 1 854850603091363 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep328 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable def ep329 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (ep318 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 85999 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz371 Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz371) (@HMul.hMul Real Real Real qz0 qz84 qz552) Bool.false 16945043951685843 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 9000 171998 4000 29664312004 16000000 rfl rfl rfl) (ep323 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz371) qz375 Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 9000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz375 (@HSub.hSub Real Real Real qz358 qz85 qz374) Bool.false 854850603091363 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 171998 9000 rfl rfl) ep325))))

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 171998 4000)

noncomputable abbrev qz87 := (@ep317 1 (BSN.w_sub_half_mk qz286 Bool.false 85999 1000 2 qz288 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz369 Bool.false 7000 4000 0 1 Bool.false 171998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz376))

noncomputable def ep330 := @ep313 85999000007199578283 334868000000000000000000 ep314 132205680572783140649 2251799813685248000 87749000010129673283 334868000000000000000000 (@ep315 118615307661800901 18014398509481984 350000000586019 66973600000000000000 (ep316 qz87) ep326 rfl) (@ep327 73516297015254126637 1125899906842624000 85999000007199578283 334868000000000000000000 (ep328 qz87) ep329 rfl) rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz78 qz81) (@HMul.hMul Real Real Real qz0 qz80 qz79) 5983954221639541 2251799813685248 7000000000586019 669736000000000000000 1457256834801030812157 9007199254740992000

noncomputable def ep332 := nat_lit 3335349337102071293114811029374631936

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz81 7000 4000 0 1 854850603091363 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz79 171998 4000 0 1 16945043951685843 4503599627370496 50000000083717 16743400000000000000

noncomputable def ep335 := @ep331 4299950007199578283 33486800000000000000000 ep332 1481192651687588976157 9007199254740992000 4649950007228879233 33486800000000000000000 (@ep333 5983954221639541 2251799813685248 7000000000586019 669736000000000000000 (ep316 qz87) ep329 rfl) (@ep334 1457256834801030812157 9007199254740992000 4299950007199578283 33486800000000000000000 (ep328 qz87) ep326 rfl) rfl

noncomputable def ep336 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk qz83 qz82) Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 85999 1000 2 qz14 rfl)

noncomputable abbrev qz377 := (ep336 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 171998 4000) Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 171998 4000)))

noncomputable abbrev qz88 := qz377

noncomputable def ep337 := ep311 (@ep312 33486800000000000000000 (ep330 rfl) (ep335 rfl)) qz88 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz89 := qz362

noncomputable def ep338 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz90 := (@Enclosure.Complex.IsNear.of_eq qz362 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz284) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz284 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz372 qz297))

noncomputable def ep340 := ep339 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow24.d4)

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep342 := ep341 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz18)

noncomputable def ep343 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep345 := ep344 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz18)

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep347 := ep346 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow24.d4)

noncomputable def ep348 := @ep308 4649950007228879233 33486800000000000000000 (ep337 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz91 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz378 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz92 := (@HMul.hMul Complex Complex Complex qz354 (@HMul.hMul Complex Complex Complex qz354 (2 : Complex) qz378) (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 (2 : Complex) qz378) (1 : Complex)))

noncomputable abbrev qz379 := (@HPow.hPow Complex Int Complex qz551 qz547 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz93 := qz379

noncomputable def ep349 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93)) Bool.false 1737429 17179869184 3 17179869184

noncomputable def ep350 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93) Bool.false 0 1 0 1 Bool.false

noncomputable def ep351 := @ep350 0 1 0 1 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000 Bool.false 1737429 1737429 17179869184 3 17179869184 Bool.true 49805718857 49805718857 25769803776000 85999

noncomputable def ep352 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep353 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93 Bool.false 1737429 17179869184 3 17179869184 Bool.true 49805718857 25769803776000 85999 25769803776000

noncomputable abbrev qz94 := (Complex.re qz379)

noncomputable abbrev qz95 := (Complex.im qz379)

noncomputable def ep354 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) 1737429 17179869184 3 17179869184 0 1 0

noncomputable def ep355 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 1 12 0 1 5212287 4294967296 9 4294967296 1737429

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz380 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz18)

noncomputable def ep357 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz380)

noncomputable def ep358 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999 2147483648000

noncomputable abbrev qz553 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz381 := (@HPow.hPow Complex Nat Complex qz553 qz547 1)

noncomputable abbrev qz96 := (@Inv.inv Complex Complex.instInv qz381)

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz93 qz96 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_parts qz96 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999

noncomputable abbrev qz97 := (Complex.re qz381)

noncomputable abbrev qz98 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz100 := qz381

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 9000 4000 0 1 579143 1073741824 1 1073741824

noncomputable def ep362 := @Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz100 qz72 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0

noncomputable def ep364 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) Bool.false 579143 1073741824 1 1073741824 579143 1073741824 1

noncomputable abbrev qz101 := (Complex.im qz381)

noncomputable abbrev qz382 := (@instHAdd Real Real.instAdd)

noncomputable def ep365 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101)) Bool.false 7416078001 4000000 0 1

noncomputable def ep366 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101) 81 16 0 1 7395828001 4000000

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz97 9000 4000 0 1 9000 4000 0 1

noncomputable def ep368 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 171998 4000 0 1 171998 4000 0 1

noncomputable def ep369 := @Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 171998 4000 0 1

noncomputable abbrev qz102 := (ep362 (@ep363 1 (BSN.pow_one_c qz356) qz377))

noncomputable abbrev qz103 := (ep369 (@ep363 1 (BSN.pow_one_c qz356) qz377))

noncomputable def ep370 := @ep366 0 1 118657248016 7416078001 4000000 0 1 (@ep367 81 16 0 1 qz102 qz102 rfl) (@ep368 7395828001 4000000 0 1 qz103 qz103 rfl)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) 7416078001 4000000 0 1 289571 289572 536870912 (ep365 (Enclosure.Complex.normSq_eq_mul_add_mul qz100) (ep370 rfl rfl)) rfl

noncomputable def ep372 := @Enclosure.Real.IsNear.of_eq (Complex.re qz96) (@HMul.hMul Real Real Real qz0 qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.false 5212287 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz100) (@ep361 5212287 4294967296 9 4294967296 qz102 (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep373 := @Enclosure.Real.IsNear.of_eq (Complex.im qz96) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.true 49805718857 2147483648000 85999 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz100)

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 171998 4000 0 1 579143 1073741824 1

noncomputable def ep375 := @ep374 1073741824 49805718857 2147483648000 85999 2147483648000 (@Enclosure.Real.IsNear.neg qz101 Bool.false 171998 4000 0 1 qz103) (@ep364 1073741824 (ep371 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 0 1 0 1 49805718857 2147483648000 85999 2147483648000 0

noncomputable def ep377 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep356 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz380)

noncomputable def ep378 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 5212287 4294967296 9 4294967296 Bool.true 49805718857 2147483648000 85999 2147483648000

noncomputable abbrev qz104 := (@ep359 2147483648000 (BSN.zpow_one_sub_two_mul qz356 1 1 rfl rfl) (@ep360 2147483648000 ep372 (ep373 ep375)))

noncomputable def ep379 := @ep354 1 1737429 1737429 17179869184 3 17179869184 (@ep355 17179869184 3 17179869184 ep357 (ep358 qz104) rfl) (@ep376 1 0 1 ep377 (ep378 qz104) rfl) rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) 49805718857 25769803776000 85999 25769803776000 0 1 0

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 1 12 0 1 49805718857 2147483648000 85999 2147483648000 49805718857

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 0 1 0 1 5212287 4294967296 9 4294967296 0

noncomputable def ep383 := @ep380 1 49805718857 49805718857 25769803776000 85999 25769803776000 (@ep381 25769803776000 85999 25769803776000 ep357 (ep378 qz104) rfl) (@ep382 1 0 1 ep377 (ep358 qz104) rfl) rfl

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.mk qz284 qz284 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz297 qz297)

noncomputable def ep384 := @ep351 25769803776000 (@ep352 0 1 0 1 (BSN.stirling_sum_base qz72) qz105) (ep353 (ep379 rfl) (ep383 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep385 := @ep305 3281610536918604874327 27021597764222976000 ep297 ep288 (ep348 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep349 Bool.true 49805718857 25769803776000 85999 25769803776000 (BSN.stirling_sum_succ qz72 0 1 rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 16939874958545107 2251799813685248 50000000083717 8371700000000000000 Bool.false 874463571248547 281474976710656

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz357 qz378))

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz106) Bool.false 16939874958545107 2251799813685248 50000000083717 8371700000000000000 Bool.false 874463571248547 281474976710656 1000000000083717 83717000000000000000

noncomputable def ep388 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz106 Bool.false 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000 Bool.false

noncomputable def ep389 := nat_lit 152580829102013080521032433926144

noncomputable def ep390 := nat_lit 984558453406007362196317667328

noncomputable abbrev qz107 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz357 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz107) Bool.false 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz107 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz383 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz107 qz383 Bool.false 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep394 := nat_lit 437935405166394800019957250910035964188596667621415704592893314689875907902852173933481095774490704593965547520

noncomputable def ep395 := nat_lit 12670670537683241802231207996609486562442984826354745069971463268408909830276434410158395425828098412777570304

noncomputable def ep396 := nat_lit 151800699253155918747652231221233791912582282768251464217912183211248259831789728332048454476995960504320

noncomputable def ep397 := BSN.log_dyadic_bound 13200312004 45968312004 6 5 ep394 524288 167434 ep395 ep396 309822 59168624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13200312004) (BSN.artanhQ 45968312004) 0 5 ep395 ep394 ep396 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep398 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 29584312004 16000000)) 1 2 0 1 16938962277994707 2251799813685248 50000000083717 8371700000000000000 16938962277994707 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 29584312004 16000000 16938962277994707 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29584312004) qz373)) Bool.false 142094314476884623097856 18889465931478580854784 1000000001674340 167434000000000000000 16938962277994707 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 29584312004 16000000 10 59168624008 32768000000 309822 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep397 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep399 := BSN.arctan_dyadic_bound_f 1000 171998 1 0 524288 167434 0 1 1 0 1 1 3048 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast 171998)

noncomputable def ep400 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz385)) 884279719003555 562949953421312 1 2000000000000000 3048 524288 1 167434 461901373858907684864 881006953924003 562949953421312 1000000000083717 167434000000000000000 qz86 (ep399 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz274 qz357 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz386 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82)

noncomputable def ep401 := @ep392 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000 Bool.false 16938962277994707 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 881006953924003 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz105) (ep393 (@congrArg Complex Complex qz108 qz386 Complex.log (BSN.w_shift_mk qz13 Bool.false 85999 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz383 Bool.false 16938962277994707 4503599627370496 50000000083717 16743400000000000000 Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz383) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 29584312004 16000000))) Bool.false 16938962277994707 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 1000 171998 4000 29584312004 16000000 rfl rfl rfl) (ep398 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz383) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz384)) Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 1000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz384)) (@HSub.hSub Real Real Real qz358 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz385))) Bool.false 881006953924003 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 171998 1000 rfl rfl) ep400)))) rfl rfl

noncomputable abbrev qz387 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82))

noncomputable def ep402 := @Enclosure.Complex.IsNear.of_eq qz106 qz387 Bool.false 16940787639095507 4503599627370496 50000000083717 16743400000000000000 Bool.false 867920188573091 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep403 := nat_lit 440227239996759517878856072247136054195559733416360599330990016305758465426527783335300169004659043845165547520

noncomputable def ep404 := nat_lit 12771757931540831080620976717445651124220733508713670621844958774951975159012672474351668648517281911017570304

noncomputable def ep405 := nat_lit 154583337415052852780881187735588335469271960184861394269603940538809570871794740705162863089655160504320

noncomputable def ep406 := BSN.log_dyadic_bound 13224312004 45992312004 6 5 ep403 524288 167434 ep404 ep405 310247 59216624008 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13224312004) (BSN.artanhQ 45992312004) 0 5 ep404 ep403 ep405 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep407 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 29608312004 16000000)) 1 2 0 1 16940787639095507 2251799813685248 50000000083717 8371700000000000000 16940787639095507 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 29608312004 16000000 16940787639095507 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29608312004) qz373)) Bool.false 142109626715617682784256 18889465931478580854784 1000000001674340 167434000000000000000 16940787639095507 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 29608312004 16000000 10 59216624008 32768000000 310247 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep406 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep408 := BSN.arctan_dyadic_bound_f 5000 171998 1 0 524288 167434 0 1 1 0 1 1 15236 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 171998) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 171998) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep409 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz385)) 884279719003555 562949953421312 1 2000000000000000 15236 524288 1 167434 455040139826608734208 867920188573091 562949953421312 1000000000083717 167434000000000000000 qz86 (ep408 rfl) rfl rfl

noncomputable abbrev qz109 := (@HAdd.hAdd Complex Complex Complex qz274 qz357 qz378)

noncomputable abbrev qz389 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82)

noncomputable def ep410 := @ep388 16940787639095507 4503599627370496 50000000083717 16743400000000000000 Bool.false 867920188573091 562949953421312 1000000000083717 167434000000000000000 Bool.false ep389 16939874958545107 2251799813685248 50000000083717 8371700000000000000 Bool.false ep390 874463571248547 281474976710656 1000000000083717 83717000000000000000 (ep391 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep402 (@congrArg Complex Complex qz109 qz389 Complex.log (BSN.w_shift_mk qz13 Bool.false 85999 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz387 Bool.false 16940787639095507 4503599627370496 50000000083717 16743400000000000000 Bool.false 867920188573091 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz387) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 29608312004 16000000))) Bool.false 16940787639095507 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 5000 171998 4000 29608312004 16000000 rfl rfl rfl) (ep407 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz387) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz388)) Bool.false 867920188573091 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 5000 171998 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz385 qz388)) (@HSub.hSub Real Real Real qz358 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz385))) Bool.false 867920188573091 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 171998 5000 rfl rfl) ep409)))) rfl rfl

noncomputable def ep411 := @ep298 ep288 Bool.false 16939874958545107 2251799813685248 50000000083717 8371700000000000000 Bool.false 874463571248547 281474976710656 1000000000083717 83717000000000000000 Bool.true ep299 152142613680220919649 2251799813685248000 ep293 ep294 Bool.false ep300 3197662034078744362327 27021597764222976000 ep290 ep288 (@ep301 2251799813685248000 ep296 ep294 Bool.false 3281610536918604874327 27021597764222976000 ep297 ep288 (BSN.logGammaStirling_unfold 1 qz72) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep386 1000000000083717 83717000000000000000 (BSN.log_sum_c_eq qz13 2) (ep387 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep410 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz110 := (@HDiv.hDiv Real Real Real qz271 qz286 (2 : Real))

noncomputable def ep412 := @Enclosure.Real.IsNear.mulLit_ff qz110 (Real.log Real.pi) 85999 2000 0 1 75021 65536 1 131072 6451730979 131072000 85999 262144000 (@Enclosure.Real.IsNear.of_eq qz110 (Enclosure.sfrac Bool.false 85999 2000) Bool.false 85999 2000 0 1 (BSN.t_half_eq qz13 Bool.false 85999 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 85999 2000)) EMRow24.d5 rfl

noncomputable def ep413 := @ep291 85999 262144000 ep292 373516660664756269739 5404319552844595200 ep287 ep288 (@ep295 ep290 ep288 (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep412 rfl rfl

noncomputable def ep414 := nat_lit 32546104012325647597857302204971608834503224602072622116671158223340518867200

noncomputable def ep415 := nat_lit 65296679634319364338697652138165925048890389865255766765259971543882629376

noncomputable def ep416 := nat_lit 85134077789063988547363614338130516402191194278979786683185469678630310871296

noncomputable def ep417 := BSN.sin_dyadic_bound_f 1686014818 1073741824 3 2 524288 167598 ep414 ep57 ep415 ep416 ep60 ep415 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686014818) qz289 0 2 ep414 ep57 ep415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686014818) qz290 0 2 ep416 ep60 ep415 rfl rfl rfl rfl) rfl rfl

noncomputable def ep418 := @ep286 131072 Bool.false 524287 524288 1 83717 (@ep289 36235885 524288 63 131072 ep413 rfl) (Enclosure.sfrac_false_div 36235885 524288) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118642745421254885376000) qz26) 226375608064910080 72057594037927936 Bool.false 524287 524288 10 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 36235885 524288 226375608064910080 72057594037927936 10 118642745421254885376000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 118642745421254885376000 75557863725914323419136 1686014818 1073741824 167598 167434 (ep417 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep419 := nat_lit 3885448339231951343563417

noncomputable def ep420 := nat_lit 268358434147246547140608000

noncomputable def ep421 := nat_lit 14778969801196910606349101329

noncomputable def ep422 := nat_lit 2042378457409549016997298176000

noncomputable abbrev qz390 := (@HPow.hPow Complex Complex Complex qz526 (@Nat.cast Complex Complex.instNatCast 22) qz527)

noncomputable abbrev qz111 := qz390

noncomputable abbrev qz391 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz363 qz391 (@HSub.hSub Complex Complex Complex qz355 qz273 (1 : Complex))) qz362)

noncomputable abbrev qz113 := (@instHSub Nat instSubNat)

noncomputable abbrev qz392 := qz553

noncomputable abbrev qz114 := qz392

noncomputable abbrev qz115 := qz391

noncomputable def ep423 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 22) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 22, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep281 ep282 ep283

noncomputable def ep424 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 22, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 66962291869 34359738368 5124792047863 719123554238464

noncomputable def ep425 := nat_lit 4259637627614068603348701

noncomputable def ep426 := nat_lit 5703186354693056435050383251

noncomputable def ep427 := nat_lit 28193839250894634508336583

noncomputable def ep428 := nat_lit 260210645461658401370585329

noncomputable def ep429 := nat_lit 11833570494156518665600842317044908032

noncomputable def ep430 := nat_lit 1068023907027119665847560711488667648

noncomputable def ep431 := @ep424 Bool.false 32858618575 274877906944 163586240727543 23011953735630848 Bool.true ep425 ep282 ep426 ep284 Bool.true ep427 ep420 ep428 ep422 Bool.false ep429 ep281 ep282 ep283 ep284 Bool.false ep430 ep419 ep420

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 22, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 22) Bool.false 66962291869 34359738368 5124792047863 719123554238464 Bool.false 32858618575 274877906944 163586240727543

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 21) qz276)

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz116) Bool.false 66962291869 34359738368 5124792047863 719123554238464 Bool.false 32858618575 274877906944 163586240727543 23011953735630848

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz116 Bool.false 282158415515 137438953472 79370133569961 11505976867815424 Bool.true 2482159141 34359738368 39578882360681 5752988433907712 Bool.true

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 20) qz276)

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz117) Bool.false 282158415515 137438953472 79370133569961 11505976867815424 Bool.true 2482159141 34359738368 39578882360681 5752988433907712

noncomputable def ep436 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz117 Bool.false 502863299145 274877906944 153344823705739 23011953735630848 Bool.true 18681054373 274877906944 152963129773827 23011953735630848 Bool.false

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 19) qz276)

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz118) Bool.false 502863299145 274877906944 153344823705739 23011953735630848 Bool.true 18681054373 274877906944 152963129773827 23011953735630848

noncomputable def ep438 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz118 Bool.false 522725692089 274877906944 147830418044187 23011953735630848 Bool.false 20584948153 137438953472 73710445569935 11505976867815424 Bool.true

noncomputable abbrev qz119 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz276)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz119) Bool.false 522725692089 274877906944 147830418044187 23011953735630848 Bool.false 20584948153 137438953472 73710445569935 11505976867815424

noncomputable def ep440 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz119 Bool.false 582815024439 274877906944 142148743505625 23011953735630848 Bool.false 16944624031 274877906944 141763513032765 23011953735630848 Bool.true

noncomputable abbrev qz120 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz276)

noncomputable def ep441 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz36 qz120) Bool.false 582815024439 274877906944 142148743505625 23011953735630848 Bool.false 16944624031 274877906944 141763513032765 23011953735630848

noncomputable def ep442 := @Enclosure.Complex.IsNear.addLitP qz36 qz120 Bool.false 35680143545 17179869184 34084079850367 5752988433907712 Bool.true 12161664627 68719476736 33978940507237 5752988433907712 Bool.false

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz121 := (@Inv.inv Real Real.instInv (Real.sqrt qz393))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz268 qz286 qz554)

noncomputable def ep443 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)))) Bool.false 11932727719 274877906944 5812424104157 23011953735630848 Bool.false 65591282539 274877906944 5847751003817 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 17 qz14 rfl)

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep444 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz393) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz393) (Real.sqrt qz394) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz394) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep445 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 83717 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep446 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 85999 1000 0 1 3189913004350711 1125899906842624 250000000083717 20929250000000000000 274329328461156795289 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 26758929747600409100288 9444732965739290427392 1000000000334868 83717000000000000000 3189913004350711 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep445 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep447 := nat_lit 1394078500112019137272648836944656

noncomputable def ep448 := BSN.sin_dyadic_bound_f 193228778 1073741824 2 1 524288 167598 ep447 ep79 ep447 ep447 ep80 ep447 93841 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 193228778) qz289 0 1 ep447 ep79 ep447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 193228778) qz290 0 1 ep447 ep80 ep447 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31936137) qz531)

noncomputable def ep449 := @Enclosure.Real.IsNear.cos_image qz122 qz395 Bool.false 31936137 131072 539 524288 Bool.false 93841 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 274329328461156795289 1125899906842624000 21499750007199578283 20929250000000000000000 31936137 131072 539 524288 (ep446 rfl) rfl) (Enclosure.sfrac_false_div 31936137 131072) (BSN.cos_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3399316627295949553664) qz293) 226375608064910080 72057594037927936 Bool.false 93841 524288 38 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 31936137 131072 226375608064910080 72057594037927936 38 3399316627295949553664 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93841 524288 3399316627295949553664 18889465931478580854784 193228778 1073741824 167598 167434 (ep448 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep450 := BSN.cos_dyadic_bound_f 193228778 1073741824 2 1 524288 167598 ep447 ep75 ep447 ep447 ep76 ep447 515821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 193228778) qz294 0 1 ep447 ep75 ep447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 193228778) qz295 0 1 ep447 ep76 ep447 rfl rfl rfl rfl) rfl rfl

noncomputable def ep451 := @Enclosure.Real.IsNear.sin_image qz122 qz395 Bool.false 31936137 131072 539 524288 Bool.true 515821 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 274329328461156795289 1125899906842624000 21499750007199578283 20929250000000000000000 31936137 131072 539 524288 (ep446 rfl) rfl) (Enclosure.sfrac_false_div 31936137 131072) (BSN.sin_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3399316627295949553664) qz293) 226375608064910080 72057594037927936 Bool.false 515821 524288 38 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 31936137 131072 226375608064910080 72057594037927936 38 3399316627295949553664 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515821 524288 3399316627295949553664 18889465931478580854784 193228778 1073741824 167598 167434 (ep450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep444 rfl rfl) rfl)

noncomputable def ep452 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122))) Bool.false 11932727719 274877906944 5812424104157 23011953735630848 Bool.false 65591282539 274877906944 5847751003817 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz122) 127159 524288 1 524288 93841 524288 45647751 43891818496 11932727719 274877906944 5812424104157 23011953735630848 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz122) Bool.false 93841 524288 45647751 43891818496 93841 524288 45647751 43891818496 (ep449 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)) 127159 524288 1 524288 515821 524288 45647751 43891818496 65591282539 274877906944 5847751003817 23011953735630848 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz122) Bool.true 515821 524288 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz122) Bool.true 515821 524288 45647751 43891818496 515821 524288 45647751 43891818496 (ep451 rfl rfl) rfl)) rfl)

noncomputable def ep453 := @ep442 11932727719 274877906944 5812424104157 23011953735630848 Bool.false 65591282539 274877906944 5847751003817 23011953735630848 Bool.false 10012685878331782987776 582815024439 274877906944 142148743505625 23011953735630848 Bool.false 1164425696898571042816 16944624031 274877906944 141763513032765 23011953735630848 EMRow24.d7 (ep443 ep452) rfl rfl

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz397))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz268 qz286 qz555)

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.true 30044666175 137438953472 2840837269281 11505976867815424 Bool.false 24225272275 274877906944 5657378107105 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 18 qz14 rfl)

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep455 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz397) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz397) (Real.sqrt qz398) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz398) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep456 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 83717 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 85999 1000 0 1 3254268794313975 1125899906842624 250000000083717 20929250000000000000 11194554481688301441 45035996273704960 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz398) Bool.false 27298785242132565196800 9444732965739290427392 1000000000334868 83717000000000000000 3254268794313975 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 28668422947826433757399533974206881

noncomputable def ep459 := BSN.cos_dyadic_bound_f 411482103 1073741824 2 1 524288 167598 ep458 ep75 ep458 ep458 ep76 ep458 486258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 411482103) qz294 0 1 ep458 ep75 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 411482103) qz295 0 1 ep458 ep76 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65160883) qz48)

noncomputable def ep460 := @Enclosure.Real.IsNear.cos_image qz124 qz399 Bool.false 65160883 262144 539 524288 Bool.true 486258 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 11194554481688301441 45035996273704960 21499750007199578283 20929250000000000000000 65160883 262144 539 524288 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 65160883 262144) (BSN.cos_reduce2 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14477739444129094434816) qz49) 226375608064910080 72057594037927936 Bool.false 486258 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 65160883 262144 226375608064910080 72057594037927936 39 14477739444129094434816 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 486258 524288 14477739444129094434816 37778931862957161709568 411482103 1073741824 167598 167434 (ep459 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep461 := BSN.sin_dyadic_bound_f 411482103 1073741824 2 1 524288 167598 ep458 ep79 ep458 ep458 ep80 ep458 196037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 411482103) qz289 0 1 ep458 ep79 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 411482103) qz290 0 1 ep458 ep80 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.sin_image qz124 qz399 Bool.false 65160883 262144 539 524288 Bool.true 196037 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 11194554481688301441 45035996273704960 21499750007199578283 20929250000000000000000 65160883 262144 539 524288 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 65160883 262144) (BSN.sin_reduce2 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14477739444129094434816) qz49) 226375608064910080 72057594037927936 Bool.false 196037 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 65160883 262144 226375608064910080 72057594037927936 39 14477739444129094434816 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196037 524288 14477739444129094434816 37778931862957161709568 411482103 1073741824 167598 167434 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz400 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep455 rfl rfl) rfl)

noncomputable def ep463 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.true 30044666175 137438953472 2840837269281 11505976867815424 Bool.false 24225272275 274877906944 5657378107105 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz123 (Real.cos qz124) 123575 524288 1 524288 243129 262144 45647751 43891818496 30044666175 137438953472 2840837269281 11505976867815424 qz400 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.true 486258 524288 45647751 43891818496 243129 262144 45647751 43891818496 (ep460 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 123575 524288 1 524288 196037 524288 45647751 43891818496 24225272275 274877906944 5657378107105 23011953735630848 qz400 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.true 196037 524288 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.true 196037 524288 45647751 43891818496 196037 524288 45647751 43891818496 (ep462 rfl rfl) rfl)) rfl)

noncomputable def ep464 := @ep440 30044666175 137438953472 2840837269281 11505976867815424 Bool.false 24225272275 274877906944 5657378107105 23011953735630848 Bool.false 71842872073639069483008 522725692089 274877906944 147830418044187 23011953735630848 Bool.false 11316694925694797348864 20584948153 137438953472 73710445569935 11505976867815424 (ep441 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep453 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep454 ep463) rfl rfl

noncomputable abbrev qz401 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz401))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz268 qz286 qz556)

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.true 1241399559 17179869184 344650353847 1438247108476928 Bool.true 59850950679 274877906944 5542238633957 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 19 qz14 rfl)

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep466 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz401) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz401) (Real.sqrt qz402) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz402) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep467 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 83717 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 85999 1000 0 1 3315141365800183 1125899906842624 250000000083717 20929250000000000000 285098842317449937817 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 27809421382282341515264 9444732965739290427392 1000000000334868 83717000000000000000 3315141365800183 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep467 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep469 := nat_lit 14012832636484586359282906176160000

noncomputable def ep470 := BSN.sin_dyadic_bound_f 344057860 1073741824 2 1 524288 167598 ep469 ep79 ep469 ep469 ep80 ep469 165136 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 344057860) qz289 0 1 ep469 ep79 ep469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 344057860) qz290 0 1 ep469 ep80 ep469 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz403 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132759493) qz24)

noncomputable def ep471 := @Enclosure.Real.IsNear.cos_image qz126 qz403 Bool.false 132759493 524288 135 131072 Bool.true 165136 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 285098842317449937817 1125899906842624000 21499750007199578283 20929250000000000000000 132759493 524288 135 131072 (ep468 rfl) rfl) (Enclosure.sfrac_false_div 132759493 524288) (BSN.cos_reduce1 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24210919567443368083456) qz26) 226375608064910080 72057594037927936 Bool.false 165136 524288 40 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 132759493 524288 226375608064910080 72057594037927936 40 24210919567443368083456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 165136 524288 24210919567443368083456 75557863725914323419136 344057860 1073741824 167598 167434 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep472 := BSN.cos_dyadic_bound_f 344057860 1073741824 2 1 524288 167598 ep469 ep75 ep469 ep469 ep76 ep469 497601 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 344057860) qz294 0 1 ep469 ep75 ep469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 344057860) qz295 0 1 ep469 ep76 ep469 rfl rfl rfl rfl) rfl rfl

noncomputable def ep473 := @Enclosure.Real.IsNear.sin_image qz126 qz403 Bool.false 132759493 524288 135 131072 Bool.false 497601 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 285098842317449937817 1125899906842624000 21499750007199578283 20929250000000000000000 132759493 524288 135 131072 (ep468 rfl) rfl) (Enclosure.sfrac_false_div 132759493 524288) (BSN.sin_reduce1 qz403 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24210919567443368083456) qz26) 226375608064910080 72057594037927936 Bool.false 497601 524288 40 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 132759493 524288 226375608064910080 72057594037927936 40 24210919567443368083456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 497601 524288 24210919567443368083456 75557863725914323419136 344057860 1073741824 167598 167434 (ep472 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz404 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep466 rfl rfl) rfl)

noncomputable def ep474 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.true 1241399559 17179869184 344650353847 1438247108476928 Bool.true 59850950679 274877906944 5542238633957 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz125 (Real.cos qz126) 120279 524288 1 524288 10321 32768 11432867 10972954624 1241399559 17179869184 344650353847 1438247108476928 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.true 165136 524288 11432867 10972954624 10321 32768 11432867 10972954624 (ep471 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 120279 524288 1 524288 497601 524288 11432867 10972954624 59850950679 274877906944 5542238633957 23011953735630848 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 497601 524288 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 497601 524288 11432867 10972954624 497601 524288 11432867 10972954624 (ep473 rfl rfl) rfl)) rfl)

noncomputable def ep475 := @ep438 1241399559 17179869184 344650353847 1438247108476928 Bool.true 59850950679 274877906944 5542238633957 23011953735630848 Bool.false 8639125696745759047680 502863299145 274877906944 153344823705739 23011953735630848 Bool.true 2567504562778649133056 18681054373 274877906944 152963129773827 23011953735630848 (ep439 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep465 ep474) rfl rfl

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz405))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz268 qz286 qz557)

noncomputable def ep476 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 61453531885 274877906944 5395443434183 23011953735630848 Bool.true 1176218755 274877906944 5352399668897 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 20 qz14 rfl)

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep477 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz405) 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz405) (Real.sqrt qz406) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz406) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep478 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 83717 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 85999 1000 0 1 3372891496062199 1125899906842624 250000000083717 20929250000000000000 290065295769853051801 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz406) Bool.false 28293864586999331028992 9444732965739290427392 1000000000334868 83717000000000000000 3372891496062199 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep478 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep480 := BSN.cos_dyadic_bound_f 20549649 1073741824 1 0 524288 167598 0 1 1 0 1 1 524191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20549649) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20549649) qz295 0 0 rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135072179) qz24)

noncomputable def ep481 := @Enclosure.Real.IsNear.cos_image qz128 qz407 Bool.false 135072179 524288 539 524288 Bool.false 524191 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 290065295769853051801 1125899906842624000 21499750007199578283 20929250000000000000000 135072179 524288 539 524288 (ep479 rfl) rfl) (Enclosure.sfrac_false_div 135072179 524288) (BSN.cos_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1446053014435453206528) qz26) 226375608064910080 72057594037927936 Bool.false 524191 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 135072179 524288 226375608064910080 72057594037927936 41 1446053014435453206528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524191 524288 1446053014435453206528 75557863725914323419136 20549649 1073741824 167598 167434 (ep480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep482 := BSN.sin_dyadic_bound_f 20549649 1073741824 1 0 524288 167598 0 1 1 0 1 1 10033 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 20549649) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 20549649) qz290 0 0 rfl) rfl rfl

noncomputable def ep483 := @Enclosure.Real.IsNear.sin_image qz128 qz407 Bool.false 135072179 524288 539 524288 Bool.false 10033 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 290065295769853051801 1125899906842624000 21499750007199578283 20929250000000000000000 135072179 524288 539 524288 (ep479 rfl) rfl) (Enclosure.sfrac_false_div 135072179 524288) (BSN.sin_reduce0 qz407 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1446053014435453206528) qz26) 226375608064910080 72057594037927936 Bool.false 10033 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 135072179 524288 226375608064910080 72057594037927936 41 1446053014435453206528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10033 524288 1446053014435453206528 75557863725914323419136 20549649 1073741824 167598 167434 (ep482 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz408 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep477 rfl rfl) rfl)

noncomputable def ep484 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 61453531885 274877906944 5395443434183 23011953735630848 Bool.true 1176218755 274877906944 5352399668897 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 117235 524288 1 524288 524191 524288 45647751 43891818496 61453531885 274877906944 5395443434183 23011953735630848 qz408 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 524191 524288 45647751 43891818496 524191 524288 45647751 43891818496 (ep481 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 117235 524288 1 524288 10033 524288 45647751 43891818496 1176218755 274877906944 5352399668897 23011953735630848 qz408 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.false 10033 524288 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.false 10033 524288 45647751 43891818496 10033 524288 45647751 43891818496 (ep483 rfl rfl) rfl)) rfl)

noncomputable def ep485 := @ep436 61453531885 274877906944 5395443434183 23011953735630848 Bool.true 1176218755 274877906944 5352399668897 23011953735630848 Bool.false 155118229366797311672320 282158415515 137438953472 79370133569961 11505976867815424 Bool.true 5458325675039975800832 2482159141 34359738368 39578882360681 5752988433907712 (ep437 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep475 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep476 ep484) rfl rfl

noncomputable abbrev qz409 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz409))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz268 qz286 qz558)

noncomputable def ep486 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.true 14309248039 137438953472 2626539195847 11505976867815424 Bool.false 52715891703 274877906944 5270711284819 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 21 qz14 rfl)

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep487 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz409) 2402589 524288 1 524288 57204 57205 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz409) (Real.sqrt qz410) Bool.false 2402589 524288 1 524288 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz410) Bool.false 2402589 524288 1 524288 2402589 524288 1 524288 (BSN.sqrt_enclosure 21 1 1201294 1201295 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep488 := BSN.log_dyadic_bound 5 37 3 2 28112415 262144 83717 173000 1875 71285 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 85999 1000 0 1 3427824127778039 1125899906842624 250000000083717 20929250000000000000 294789447164783575961 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 28754672900871880179712 9444732965739290427392 1000000000334868 83717000000000000000 3427824127778039 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep488 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep490 := nat_lit 3944146787366480054915797023328805156054862300117218502600661914125187690625

noncomputable def ep491 := nat_lit 3114601157589334470664374380638361571774769383555908517321269819062890625

noncomputable def ep492 := nat_lit 11826211159784261495806062321225138745021037361584543690767343202737437290625

noncomputable def ep493 := BSN.cos_dyadic_bound_f 1152591215 1073741824 3 2 524288 167598 ep490 ep64 ep491 ep492 ep66 ep491 250142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1152591215) qz294 0 2 ep490 ep64 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1152591215) qz295 0 2 ep492 ep66 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137272033) qz24)

noncomputable def ep494 := @Enclosure.Real.IsNear.cos_image qz130 qz411 Bool.false 137272033 524288 135 131072 Bool.true 250142 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 294789447164783575961 1125899906842624000 21499750007199578283 20929250000000000000000 137272033 524288 135 131072 (ep489 rfl) rfl) (Enclosure.sfrac_false_div 137272033 524288) (BSN.cos_reduce2 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81106396361588144603136) qz26) 226375608064910080 72057594037927936 Bool.false 250142 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 137272033 524288 226375608064910080 72057594037927936 41 81106396361588144603136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 250142 524288 81106396361588144603136 75557863725914323419136 1152591215 1073741824 167598 167434 (ep493 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep495 := nat_lit 7096972536333592631271903142487338591641332324704148577867334429570087530625

noncomputable def ep496 := nat_lit 18582266336142359873712004005136281821277758842842250994910212878690794090625

noncomputable def ep497 := BSN.sin_dyadic_bound_f 1152591215 1073741824 3 2 524288 167598 ep495 ep57 ep491 ep496 ep60 ep491 460767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1152591215) qz289 0 2 ep495 ep57 ep491 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1152591215) qz290 0 2 ep496 ep60 ep491 rfl rfl rfl rfl) rfl rfl

noncomputable def ep498 := @Enclosure.Real.IsNear.sin_image qz130 qz411 Bool.false 137272033 524288 135 131072 Bool.true 460767 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 294789447164783575961 1125899906842624000 21499750007199578283 20929250000000000000000 137272033 524288 135 131072 (ep489 rfl) rfl) (Enclosure.sfrac_false_div 137272033 524288) (BSN.sin_reduce2 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81106396361588144603136) qz26) 226375608064910080 72057594037927936 Bool.false 460767 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 137272033 524288 226375608064910080 72057594037927936 41 81106396361588144603136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 460767 524288 81106396361588144603136 75557863725914323419136 1152591215 1073741824 167598 167434 (ep497 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz412 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 114409 524288 1 524288 114409 524288 1 524288 (ep487 rfl rfl) rfl)

noncomputable def ep499 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.true 14309248039 137438953472 2626539195847 11505976867815424 Bool.false 52715891703 274877906944 5270711284819 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz129 (Real.cos qz130) 114409 524288 1 524288 125071 262144 11432867 10972954624 14309248039 137438953472 2626539195847 11505976867815424 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.true 250142 524288 11432867 10972954624 125071 262144 11432867 10972954624 (ep494 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 114409 524288 1 524288 460767 524288 11432867 10972954624 52715891703 274877906944 5270711284819 23011953735630848 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 460767 524288 11432867 10972954624 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 460767 524288 11432867 10972954624 460767 524288 11432867 10972954624 (ep498 rfl rfl) rfl)) rfl)

noncomputable def ep500 := @ep434 14309248039 137438953472 2626539195847 11505976867815424 Bool.false 52715891703 274877906944 5270711284819 23011953735630848 Bool.false 36812909266247899676672 66962291869 34359738368 5124792047863 719123554238464 Bool.false 1129013537370904985600 32858618575 274877906944 163586240727543 23011953735630848 (ep435 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep485 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep486 ep499) rfl rfl

noncomputable def ep501 := @Enclosure.Complex.IsNear.mul qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true ep425 ep282 ep426 ep284 Bool.true

noncomputable def ep502 := nat_lit 5000714751335222097137215

noncomputable abbrev qz131 := (Complex.re qz390)

noncomputable abbrev qz132 := (Complex.im qz390)

noncomputable def ep503 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 20264706170136475279255 536716868294493094281216 ep502

noncomputable def ep504 := nat_lit 44932326063010078373940559872

noncomputable def ep505 := nat_lit 7485793287294269469208897

noncomputable def ep506 := nat_lit 536716868294493094281216000

noncomputable def ep507 := nat_lit 702471603357834337913168251

noncomputable def ep508 := nat_lit 6858658102687221236997642805812010904190606901248

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 10370073167 137438953472 2559019480631 11505976867815424 1954152670265

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz413))

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz530 (Real.log (Enclosure.sfrac Bool.false 22 1)))

noncomputable abbrev qz134 := (Real.cos qz414)

noncomputable abbrev qz135 := (Real.sin qz414)

noncomputable abbrev qz415 := (@Neg.neg Real Real.instNeg qz135)

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz415)) Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (BSN.cpow_neg_s_mk qz13 85999 1000 22 qz14 rfl)

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep511 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz413) 2459129 524288 1 524288 55889 55890 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz413) (Real.sqrt qz416) Bool.false 2459129 524288 1 524288 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz416) Bool.false 2459129 524288 1 524288 2459129 524288 1 524288 (BSN.sqrt_enclosure 22 1 1229564 1229565 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep512 := BSN.log_dyadic_bound 6 38 4 3 316148320320 262144 83717 2667271104 699840 83480 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz417 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz136 := qz417

noncomputable abbrev qz418 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15))

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz136 85999 1000 0 1 3480201253952759 1125899906842624 250000000083717 20929250000000000000 299293827638683321241 1125899906842624000 21499750007199578283 20929250000000000000000 qz17 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 29194044080518145769472 9444732965739290427392 1000000000334868 83717000000000000000 3480201253952759 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep514 := nat_lit 22760577191157563829723806799193201

noncomputable def ep515 := BSN.sin_dyadic_bound_f 388414843 1073741824 2 1 524288 167598 ep514 ep79 ep514 ep514 ep80 ep514 185546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 388414843) qz289 0 1 ep514 ep79 ep514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 388414843) qz290 0 1 ep514 ep80 ep514 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz137 := qz414

noncomputable abbrev qz419 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139369549) qz24)

noncomputable def ep516 := @Enclosure.Real.IsNear.cos_image qz137 qz419 Bool.false 139369549 524288 539 524288 Bool.true 185546 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 299293827638683321241 1125899906842624000 21499750007199578283 20929250000000000000000 139369549 524288 539 524288 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 139369549 524288) (BSN.cos_reduce1 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27332264790298321747968) qz26) 226375608064910080 72057594037927936 Bool.false 185546 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 139369549 524288 226375608064910080 72057594037927936 42 27332264790298321747968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 185546 524288 27332264790298321747968 75557863725914323419136 388414843 1073741824 167598 167434 (ep515 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep517 := BSN.cos_dyadic_bound_f 388414843 1073741824 2 1 524288 167598 ep514 ep75 ep514 ep514 ep76 ep514 490357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 388414843) qz294 0 1 ep514 ep75 ep514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 388414843) qz295 0 1 ep514 ep76 ep514 rfl rfl rfl rfl) rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.sin_image qz137 qz419 Bool.false 139369549 524288 539 524288 Bool.false 490357 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 299293827638683321241 1125899906842624000 21499750007199578283 20929250000000000000000 139369549 524288 539 524288 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 139369549 524288) (BSN.sin_reduce1 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27332264790298321747968) qz26) 226375608064910080 72057594037927936 Bool.false 490357 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 139369549 524288 226375608064910080 72057594037927936 42 27332264790298321747968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 490357 524288 27332264790298321747968 75557863725914323419136 388414843 1073741824 167598 167434 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz420 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 111779 524288 1 524288 111779 524288 1 524288 (ep511 rfl rfl) rfl)

noncomputable def ep519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz415) Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz133 qz134 111779 524288 1 524288 92773 262144 45647751 43891818496 10370073167 137438953472 2559019480631 11505976867815424 qz420 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 185546 524288 45647751 43891818496 92773 262144 45647751 43891818496 (ep516 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz133 qz415 111779 524288 1 524288 490357 524288 45647751 43891818496 54811615103 274877906944 5143556823749 23011953735630848 qz420 (@Enclosure.Real.IsNear.neg qz135 Bool.false 490357 524288 45647751 43891818496 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 490357 524288 45647751 43891818496 490357 524288 45647751 43891818496 (ep518 rfl rfl) rfl)) rfl)

noncomputable def ep520 := @ep509 3905129184528 0 1 20264706170136475279255 536716868294493094281216 ep502 ep504 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (ep510 ep519))

noncomputable def ep521 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 1954152670265 3905129184528 0 1 Bool.false

noncomputable def ep522 := @Enclosure.Complex.IsNear.addLitP qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 7374078001 14792156002 0 1 Bool.true 1891978000

noncomputable def ep523 := @ep522 7396078001 0 1 Bool.false 1 528 0 1 Bool.false 85999 264000 0 1 Bool.false 3908305340530 1954152670265 3905129184528 0 1 Bool.false 136573120007999 136573120007999 1952564592264000 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz363 qz391 (@HSub.hSub Complex Complex Complex qz355 qz273 (1 : Complex)))

noncomputable def ep524 := @Enclosure.Complex.IsNear.addLitP qz138 qz89 Bool.true 44000000 29584312004 0 1 Bool.true 7567912000 29584312004 0 1

noncomputable def ep525 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 44000000 29584312004) (Enclosure.sfrac Bool.true 7567912000 29584312004)) Bool.true 44000000 29584312004 0 1 Bool.true 7567912000 29584312004 0 1

noncomputable def ep526 := @ep524 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 29496312004 7374078001 14792156002 0 1 Bool.true 7567912000 1891978000 7396078001 0 1 (ep525 (BSN.N_div_s_sub_one_mk qz13 85999 1000 22 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 44000000 29584312004) (Enclosure.sfrac Bool.true 7567912000 29584312004) Bool.true 44000000 29584312004 0 1 Bool.true 7567912000 29584312004 0 1 (Enclosure.Real.IsNear.const Bool.true 44000000 29584312004) (Enclosure.Real.IsNear.const Bool.true 7567912000 29584312004))) qz90 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz140 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz391 1))

noncomputable def ep527 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 528 0 1

noncomputable def ep528 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep529 := @ep528 0 1 0 1 Bool.false 1 528 0 1 Bool.false 85999 264000 0 1 Bool.false 1 1 528 0 1 Bool.false 85999 85999 264000 0

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep531 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 528 0 1 Bool.false 85999 264000 0 1

noncomputable def ep532 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) 1 528 0 1 0 1 0

noncomputable def ep533 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 1 24 0 1 1 22 0 1 1

noncomputable def ep534 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep536 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow24.d8 rfl) qz380

noncomputable def ep537 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep538 := ep537 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz84 qz13) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 85999 1000 qz14) (@Enclosure.Complex.IsNear.mk qz84 qz13 Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 qz372 qz17))

noncomputable def ep539 := @ep535 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 85999 1000 0 1 0 1 0

noncomputable def ep541 := @ep540 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep542 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 85999 12000 0 1 0 1 0 1 85999

noncomputable def ep543 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 85999 1000 0 1 85999 12000 0

noncomputable def ep544 := @ep543 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep545 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep546 := @ep545 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep547 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 (@ep534 1 24 0 1 (ep539 rfl) (ep541 rfl) rfl rfl) (@ep542 85999 12000 0 1 (ep544 rfl) (ep546 rfl) rfl rfl)

noncomputable def ep548 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 ep547

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz391 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 22) qz284) Bool.false 1 22 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 22 1 22 EMRow24.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 22) qz284 Bool.false 1 22 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 22) qz297))

noncomputable def ep549 := @ep533 528 0 1 ep548 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 22 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep550 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 85999 12000 0 1 0 1 0 1 0

noncomputable def ep551 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 85999 12000 0 1 ep547

noncomputable def ep552 := @ep550 1 0 1 ep551 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 22 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep553 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140)) 0 1 0 1 85999 264000 0

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz140) 1 24 0 1 0 1 0 1 0

noncomputable def ep555 := @ep554 1 0 1 ep548 (@Enclosure.Complex.IsNear.im_isNear qz140 Bool.false 1 22 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz140) 85999 12000 0 1 1 22 0 1 85999

noncomputable def ep557 := @ep556 264000 0 1 ep551 (@Enclosure.Complex.IsNear.re_isNear qz140 Bool.false 1 22 0 1 Bool.false 0 1 0 1 qz141)

noncomputable def ep558 := @ep529 1 (@ep530 0 1 0 1 (BSN.bern_sum_base qz5 22) qz105) (ep531 (@ep532 1 1 1 528 0 1 (ep549 rfl) (ep552 rfl) rfl rfl) (@ep553 1 85999 85999 264000 0 1 (ep555 rfl) (ep557 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep559 := ep523 (ep526 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep527 Bool.false 85999 264000 0 1 (BSN.bern_sum_succ qz5 22 0 1 1 rfl rfl) (ep558 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep560 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 54811615103 274877906944 5143556823749 23011953735630848 136573120007999

noncomputable def ep561 := @ep560 1952564592264000 0 1 ep505 ep506 ep507 ep284 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (ep510 ep519))

noncomputable def ep562 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 1954152670265 3905129184528 0 1 Bool.false

noncomputable def ep563 := nat_lit 1416273247128421255262833

noncomputable def ep564 := nat_lit 349493274631024835545567369

noncomputable def ep565 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) ep563 ep420 ep564

noncomputable def ep566 := nat_lit 22466163031505039186970279936000

noncomputable def ep567 := nat_lit 10051295301788870318123485

noncomputable def ep568 := nat_lit 89864652126020156747881119744

noncomputable def ep569 := nat_lit 30264218215877050783964585201441677317908365049856

noncomputable def ep570 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 10370073167 137438953472 2559019480631 11505976867815424 136573120007999

noncomputable def ep571 := @ep570 1952564592264000 0 1 ep563 ep420 ep564 ep566 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (ep510 ep519))

noncomputable def ep572 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 54811615103 274877906944 5143556823749 23011953735630848 1954152670265

noncomputable def ep573 := @ep572 3905129184528 0 1 107110264015064853012295 1073433736588986188562432 ep567 ep568 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 10370073167 137438953472 2559019480631 11505976867815424 Bool.true 54811615103 274877906944 5143556823749 23011953735630848 (ep510 ep519))

noncomputable abbrev qz421 := (ep559 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep574 := @ep501 ep427 ep420 ep428 ep422 (@ep503 ep504 ep505 ep506 ep507 ep284 ep508 ep425 ep282 ep426 ep284 (ep520 (@ep521 136573120007999 1952564592264000 0 1 qz421) rfl) (ep561 (@ep562 136573120007999 1952564592264000 0 1 qz421) rfl) rfl rfl) (@ep565 ep566 107110264015064853012295 1073433736588986188562432 ep567 ep568 ep569 ep427 ep420 ep428 ep422 (ep571 (@ep562 136573120007999 1952564592264000 0 1 qz421) rfl) (ep573 (@ep521 136573120007999 1952564592264000 0 1 qz421) rfl) rfl rfl)

noncomputable def ep575 := @ep431 ep421 ep422 (@ep432 23011953735630848 (BSN.head_sum_c_eq qz5 22) (ep433 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep500 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep574 rfl rfl rfl

noncomputable def ep576 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 22) Bool.false ep281 ep282 ep283 ep284 Bool.false ep419 ep420 ep421 ep422 (@ep423 ep284 Bool.false ep419 ep420 ep421 ep422 (BSN.zetaApproximant_eq_folded' qz5 1 22 rfl) (ep575 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 22)) 299 524288 5405243

noncomputable def ep578 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.true 299 524288 5405243

noncomputable def ep579 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz359 Bool.false 36235885 524288 63

noncomputable def ep580 := nat_lit 18110189642240612827404589070378967541412409396647125961157425666986458317056

noncomputable def ep581 := nat_lit 54199975567453199753536371906860570774139447410210866349941757057871609692416

noncomputable def ep582 := BSN.cos_dyadic_bound_f 1686014818 1073741824 3 2 524288 167598 ep580 ep64 ep415 ep581 ep66 ep415 299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686014818) qz294 0 2 ep580 ep64 ep415 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686014818) qz295 0 2 ep581 ep66 ep415 rfl rfl rfl rfl) rfl rfl

noncomputable def ep583 := @ep579 131072 Bool.true 299 524288 1 83717 (@ep289 36235885 524288 63 131072 ep413 rfl) (Enclosure.sfrac_false_div 36235885 524288) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118642745421254885376000) qz26) 226375608064910080 72057594037927936 Bool.false 299 524288 10 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 36235885 524288 226375608064910080 72057594037927936 10 118642745421254885376000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 299 524288 118642745421254885376000 75557863725914323419136 1686014818 1073741824 167598 167434 (ep582 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 22) Bool.false ep281 ep282 ep283 ep284 Bool.false ep419 ep420 ep421 ep422 (@ep423 ep284 Bool.false ep419 ep420 ep421 ep422 (BSN.zetaApproximant_eq_folded' qz5 1 22 rfl) (ep575 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow24.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 22 qz13) Bool.false ep264 ep265 ep266 ep267 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 22 qz13) ep268 Bool.false ep264 ep265 ep266 ep267 (@Eq.refl Real ep268) (@ep269 Bool.false ep264 ep265 ep266 ep267 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) (zetaApproximant qz5 1 22)) (@ep271 ep272 ep273 ep274 ep275 ep276 ep277 ep278 ep279 ep264 ep265 ep266 ep267 (@ep280 10972954624 ep281 ep282 ep283 ep284 ep270 ep272 ep273 ep274 (@ep285 10972954624 524287 524288 5405243 10972954624 (ep418 rfl rfl) rfl) ep576 rfl) (@ep577 10972954624 ep419 ep420 ep421 ep422 ep275 ep276 ep277 ep278 (@ep578 10972954624 299 524288 5405243 10972954624 (ep583 rfl rfl) rfl) ep584 rfl) rfl rfl))

noncomputable abbrev qz575 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 88388 1000)))

noncomputable abbrev qz559 := qz575

noncomputable abbrev qz422 := qz559

noncomputable abbrev qz142 := (BSN.headSumC qz422 9)

noncomputable abbrev qz143 := qz422

noncomputable abbrev qz560 := (@Neg.neg Complex Complex.instNeg qz575)

noncomputable abbrev qz423 := qz560

noncomputable abbrev qz144 := qz423

noncomputable abbrev qz424 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz144)

noncomputable def ep585 := @Enclosure.Complex.IsNear.of_eq qz142 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 8) qz424) Bool.true 135207735647 274877906944 83164278629857 23011953735630848 Bool.true 33045197875 274877906944 83228453235679 23011953735630848

noncomputable def ep586 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 8) qz424 Bool.true 8362378127 17179869184 18613475589475 5752988433907712 Bool.false 64128018341 274877906944 74474826501163 23011953735630848 Bool.true

noncomputable abbrev qz425 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz144)

noncomputable def ep587 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 7) qz425) Bool.true 8362378127 17179869184 18613475589475 5752988433907712 Bool.false 64128018341 274877906944 74474826501163 23011953735630848

noncomputable def ep588 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 7) qz425 Bool.true 15219903649 68719476736 4070531905187 1438247108476928 Bool.false 34533542621 68719476736 32574487551821 11505976867815424 Bool.true

noncomputable abbrev qz426 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz144)

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 6) qz426) Bool.true 15219903649 68719476736 4070531905187 1438247108476928 Bool.false 34533542621 68719476736 32574487551821 11505976867815424

noncomputable def ep590 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 6) qz426 Bool.true 91942880627 274877906944 55077134294259 23011953735630848 Bool.false 61491754671 68719476736 27533786027401 11505976867815424 Bool.false

noncomputable abbrev qz427 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz144)

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 5) qz427) Bool.true 91942880627 274877906944 55077134294259 23011953735630848 Bool.false 61491754671 68719476736 27533786027401 11505976867815424

noncomputable def ep592 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 5) qz427 Bool.true 3479599257 68719476736 22016090763821 11505976867815424 Bool.false 75486889543 137438953472 22008280302589 11505976867815424 Bool.true

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz144)

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 4) qz428) Bool.true 3479599257 68719476736 22016090763821 11505976867815424 Bool.false 75486889543 137438953472 22008280302589 11505976867815424

noncomputable def ep594 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 4) qz428 Bool.false 30878435181 68719476736 15835436566121 11505976867815424 Bool.false 18709914619 34359738368 3962341078065 2876494216953856 Bool.true

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144)) Bool.false 30878435181 68719476736 15835436566121 11505976867815424 Bool.false 18709914619 34359738368 3962341078065 2876494216953856

noncomputable def ep596 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) Bool.false 34474154297 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 17179869184 2184539926471 2876494216953856 Bool.true

noncomputable def ep597 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144)) Bool.false 34474154297 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 17179869184 2184539926471 2876494216953856

noncomputable def ep598 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep599 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz143)

noncomputable abbrev qz576 := (Enclosure.sfrac Bool.false 88388 1000)

noncomputable abbrev qz561 := qz576

noncomputable abbrev qz429 := qz561

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz268 qz429 (Real.log qz287))

noncomputable abbrev qz146 := qz429

noncomputable abbrev qz430 := (@Eq.refl Real qz561)

noncomputable abbrev qz147 := qz430

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.false 114415929 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 17179869184 2184539926471 2876494216953856 (BSN.cpow_neg_s_mk qz146 88388 1000 2 qz147 rfl)

noncomputable def ep601 := BSN.sin_dyadic_bound_f 5056678 1073741824 1 0 524288 167598 0 1 1 0 1 1 2469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 5056678) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 5056678) qz290 0 0 rfl) rfl rfl

noncomputable abbrev qz148 := (Enclosure.Real.IsNear.const Bool.false 88388 1000)

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16060453) qz48)

noncomputable abbrev qz432 := (@Nat.cast Real Real.instNatCast 177916056299934580736)

noncomputable def ep602 := @Enclosure.Real.IsNear.cos_image qz145 qz431 Bool.false 16060453 262144 277 262144 Bool.false 2469 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 501889161 8192000 22097 20929250 16060453 262144 277 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz16 88388 1000 0 1 181704 262144 1 83717 501889161 8192000 22097 20929250 qz148 qz292 rfl) rfl) (Enclosure.sfrac_false_div 16060453 262144) (BSN.cos_reduce3 qz431 (@HDiv.hDiv Real Real Real qz1 qz432 qz49) 226375608064910080 72057594037927936 Bool.false 2469 524288 9 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 16060453 262144 226375608064910080 72057594037927936 9 177916056299934580736 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2469 524288 177916056299934580736 37778931862957161709568 5056678 1073741824 167598 167434 (ep601 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep603 := BSN.cos_dyadic_bound_f 5056678 1073741824 1 0 524288 167598 0 1 1 0 1 1 524282 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 5056678) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 5056678) qz295 0 0 rfl) rfl rfl

noncomputable def ep604 := @Enclosure.Real.IsNear.sin_image qz145 qz431 Bool.false 16060453 262144 277 262144 Bool.true 524282 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 501889161 8192000 22097 20929250 16060453 262144 277 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz16 88388 1000 0 1 181704 262144 1 83717 501889161 8192000 22097 20929250 qz148 qz292 rfl) rfl) (Enclosure.sfrac_false_div 16060453 262144) (BSN.sin_reduce3 qz431 (@HDiv.hDiv Real Real Real qz1 qz432 qz49) 226375608064910080 72057594037927936 Bool.false 524282 524288 9 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 16060453 262144 226375608064910080 72057594037927936 9 177916056299934580736 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524282 524288 177916056299934580736 37778931862957161709568 5056678 1073741824 167598 167434 (ep603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep605 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.false 114415929 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 17179869184 2184539926471 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz145) 46341 65536 1 262144 2469 524288 23451753 21945909248 114415929 34359738368 8694475086963 11505976867815424 qz296 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.false 2469 524288 23451753 21945909248 2469 524288 23451753 21945909248 (ep602 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 46341 65536 1 262144 262141 262144 23451753 21945909248 12147876081 17179869184 2184539926471 2876494216953856 qz296 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.true 262141 262144 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.true 524282 524288 23451753 21945909248 262141 262144 23451753 21945909248 (ep604 rfl rfl) rfl)) rfl)

noncomputable def ep606 := @ep598 114415929 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 17179869184 2184539926471 2876494216953856 Bool.false 34474154297 34474154297 34359738368 8694475086963 11505976867815424 Bool.false 12147876081 12147876081 17179869184 2184539926471 2876494216953856 (ep599 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz18)) (ep600 ep605) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz268 qz429 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz144) (Complex.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 38069873413 68719476736 3570480739579 5752988433907712 Bool.true 5585837543 34359738368 888900575797 1438247108476928 (BSN.cpow_neg_s_mk qz146 88388 1000 3 qz147 rfl)

noncomputable def ep608 := nat_lit 14597153965355395647192303672205856230821016833667869026517940103640884829825

noncomputable def ep609 := nat_lit 13164069802710565108988460388455317071099663414261495991242790185550864001

noncomputable def ep610 := nat_lit 38209328081964504827708147348481648186416120823602281218799259563520949345921

noncomputable def ep611 := BSN.sin_dyadic_bound_f 1380141999 1073741824 3 2 524288 167598 ep608 ep57 ep609 ep610 ep60 ep609 503074 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1380141999) qz289 0 2 ep608 ep57 ep609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1380141999) qz290 0 2 ep610 ep60 ep609 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50910427) qz24)

noncomputable def ep612 := @Enclosure.Real.IsNear.cos_image qz149 qz433 Bool.false 50910427 524288 277 262144 Bool.true 503074 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 3181901709 32768000 22097 20929250 50910427 524288 277 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz21 88388 1000 0 1 287994 262144 1 83717 3181901709 32768000 22097 20929250 qz148 qz300 rfl) rfl) (Enclosure.sfrac_false_div 50910427 524288) (BSN.cos_reduce1 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97118859257860696571904) qz26) 226375608064910080 72057594037927936 Bool.false 503074 524288 15 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 50910427 524288 226375608064910080 72057594037927936 15 97118859257860696571904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503074 524288 97118859257860696571904 75557863725914323419136 1380141999 1073741824 167598 167434 (ep611 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep613 := nat_lit 8115380678443091166266385800287011380265498091332932346283852408771847511681

noncomputable def ep614 := nat_lit 24319813895723852368581180480084123506654294947170274046869071645944440807041

noncomputable def ep615 := BSN.cos_dyadic_bound_f 1380141999 1073741824 3 2 524288 167598 ep613 ep64 ep609 ep614 ep66 ep609 147628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1380141999) qz294 0 2 ep613 ep64 ep609 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1380141999) qz295 0 2 ep614 ep66 ep609 rfl rfl rfl rfl) rfl rfl

noncomputable def ep616 := @Enclosure.Real.IsNear.sin_image qz149 qz433 Bool.false 50910427 524288 277 262144 Bool.false 147628 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 3181901709 32768000 22097 20929250 50910427 524288 277 262144 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz21 88388 1000 0 1 287994 262144 1 83717 3181901709 32768000 22097 20929250 qz148 qz300 rfl) rfl) (Enclosure.sfrac_false_div 50910427 524288) (BSN.sin_reduce1 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97118859257860696571904) qz26) 226375608064910080 72057594037927936 Bool.false 147628 524288 15 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 50910427 524288 226375608064910080 72057594037927936 15 97118859257860696571904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 147628 524288 97118859257860696571904 75557863725914323419136 1380141999 1073741824 167598 167434 (ep615 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep617 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz19 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz19 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 38069873413 68719476736 3570480739579 5752988433907712 Bool.true 5585837543 34359738368 888900575797 1438247108476928 (@Enclosure.Real.IsNear.mulLit_ft qz19 (Real.cos qz149) 151349 262144 1 262144 251537 262144 23451753 21945909248 38069873413 68719476736 3570480739579 5752988433907712 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 503074 524288 23451753 21945909248 251537 262144 23451753 21945909248 (ep612 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz19 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 151349 262144 1 262144 36907 131072 23451753 21945909248 5585837543 34359738368 888900575797 1438247108476928 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 36907 131072 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 147628 524288 23451753 21945909248 36907 131072 23451753 21945909248 (ep616 rfl rfl) rfl)) rfl)

noncomputable def ep618 := @ep596 38069873413 68719476736 3570480739579 5752988433907712 Bool.true 5585837543 34359738368 888900575797 1438247108476928 Bool.false 1060974954032406724608 30878435181 68719476736 15835436566121 11505976867815424 Bool.false 321433885598229200896 18709914619 34359738368 3962341078065 2876494216953856 (ep597 (BSN.head_sum_c_succ qz143 2 3 rfl rfl) (ep606 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep607 ep617) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz268 qz429 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep619 := @Enclosure.Complex.IsNear.of_eq qz428 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 17179017219 34359738368 1545163549425 2876494216953856 Bool.false 647231067 137438953472 6158915990329 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 4 qz147 rfl)

noncomputable def ep620 := BSN.cos_dyadic_bound_f 10113356 1073741824 1 0 524288 167598 0 1 1 0 1 1 524264 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 10113356) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 10113356) qz295 0 0 rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16060453) qz531)

noncomputable def ep621 := @Enclosure.Real.IsNear.cos_image qz150 qz434 Bool.false 16060453 131072 555 524288 Bool.true 524264 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 501889161 4096000 22097 20929250 16060453 131072 555 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz25 88388 1000 0 1 363408 262144 1 83717 501889161 4096000 22097 20929250 qz148 qz304 rfl) rfl) (Enclosure.sfrac_false_div 16060453 131072) (BSN.cos_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 qz432 qz293) 226375608064910080 72057594037927936 Bool.false 524264 524288 19 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 16060453 131072 226375608064910080 72057594037927936 19 177916056299934580736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524264 524288 177916056299934580736 18889465931478580854784 10113356 1073741824 167598 167434 (ep620 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep622 := BSN.sin_dyadic_bound_f 10113356 1073741824 1 0 524288 167598 0 1 1 0 1 1 4938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 10113356) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 10113356) qz290 0 0 rfl) rfl rfl

noncomputable def ep623 := @Enclosure.Real.IsNear.sin_image qz150 qz434 Bool.false 16060453 131072 555 524288 Bool.true 4938 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 501889161 4096000 22097 20929250 16060453 131072 555 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz25 88388 1000 0 1 363408 262144 1 83717 501889161 4096000 22097 20929250 qz148 qz304 rfl) rfl) (Enclosure.sfrac_false_div 16060453 131072) (BSN.sin_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 qz432 qz293) 226375608064910080 72057594037927936 Bool.false 4938 524288 19 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 16060453 131072 226375608064910080 72057594037927936 19 177916056299934580736 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4938 524288 177916056299934580736 18889465931478580854784 10113356 1073741824 167598 167434 (ep622 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep624 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 17179017219 34359738368 1545163549425 2876494216953856 Bool.false 647231067 137438953472 6158915990329 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz150) 262143 524288 1 524288 65533 65536 46987223 43891818496 17179017219 34359738368 1545163549425 2876494216953856 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 524264 524288 46987223 43891818496 65533 65536 46987223 43891818496 (ep621 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 262143 524288 1 524288 2469 262144 46987223 43891818496 647231067 137438953472 6158915990329 11505976867815424 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 2469 262144 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 4938 524288 46987223 43891818496 2469 262144 46987223 43891818496 (ep623 rfl rfl) rfl)) rfl)

noncomputable def ep625 := @ep594 17179017219 34359738368 1545163549425 2876494216953856 Bool.false 647231067 137438953472 6158915990329 11505976867815424 Bool.true 119558120096007192576 3479599257 68719476736 22016090763821 11505976867815424 Bool.false 2593709774911595085824 75486889543 137438953472 22008280302589 11505976867815424 (ep595 (BSN.head_sum_c_succ qz143 3 4 rfl rfl) (ep618 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep619 ep624) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz268 qz429 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 78024483599 274877906944 11044952766617 23011953735630848 Bool.false 47496619799 137438953472 1381376431203 2876494216953856 (BSN.cpow_neg_s_mk qz146 88388 1000 5 qz147 rfl)

noncomputable def ep627 := nat_lit 1806453490010845928071807440616231524553931350661261129086441146291129942016

noncomputable def ep628 := nat_lit 653915406985652012085272300946601254267797296512684548212767566055079936

noncomputable def ep629 := nat_lit 5418052639218566480191251777246801371153258457390758018162897903741279666176

noncomputable def ep630 := BSN.cos_dyadic_bound_f 948287872 1073741824 3 2 524288 167598 ep627 ep64 ep628 ep629 ep66 ep628 332771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 948287872) qz294 0 2 ep627 ep64 ep628 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 948287872) qz295 0 2 ep629 ep66 ep628 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74582501) qz24)

noncomputable def ep631 := @Enclosure.Real.IsNear.cos_image qz151 qz435 Bool.false 74582501 524288 555 524288 Bool.true 332771 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 582675793 4096000 22097 20929250 74582501 524288 555 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz29 88388 1000 0 1 421904 262144 1 83717 582675793 4096000 22097 20929250 qz148 qz307 rfl) rfl) (Enclosure.sfrac_false_div 74582501 524288) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66729826680506807222272) qz26) 226375608064910080 72057594037927936 Bool.false 332771 524288 22 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 74582501 524288 226375608064910080 72057594037927936 22 66729826680506807222272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 332771 524288 66729826680506807222272 75557863725914323419136 948287872 1073741824 167598 167434 (ep630 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep632 := nat_lit 808650361395858161824631038941331456

noncomputable def ep633 := BSN.sin_dyadic_bound_f 948287872 1073741824 2 1 524288 167598 ep632 ep79 ep632 ep632 ep80 ep632 405142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 948287872) qz289 0 1 ep632 ep79 ep632 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 948287872) qz290 0 1 ep632 ep80 ep632 rfl rfl rfl rfl) rfl rfl

noncomputable def ep634 := @Enclosure.Real.IsNear.sin_image qz151 qz435 Bool.false 74582501 524288 555 524288 Bool.true 405142 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 582675793 4096000 22097 20929250 74582501 524288 555 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz29 88388 1000 0 1 421904 262144 1 83717 582675793 4096000 22097 20929250 qz148 qz307 rfl) rfl) (Enclosure.sfrac_false_div 74582501 524288) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66729826680506807222272) qz26) 226375608064910080 72057594037927936 Bool.false 405142 524288 22 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 74582501 524288 226375608064910080 72057594037927936 22 66729826680506807222272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 405142 524288 66729826680506807222272 75557863725914323419136 948287872 1073741824 167598 167434 (ep633 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep635 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 78024483599 274877906944 11044952766617 23011953735630848 Bool.false 47496619799 137438953472 1381376431203 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz151) 234469 524288 1 524288 332771 524288 46987223 43891818496 78024483599 274877906944 11044952766617 23011953735630848 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 332771 524288 46987223 43891818496 332771 524288 46987223 43891818496 (ep631 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 234469 524288 1 524288 202571 262144 46987223 43891818496 47496619799 137438953472 1381376431203 2876494216953856 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 202571 262144 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 405142 524288 46987223 43891818496 202571 262144 46987223 43891818496 (ep634 rfl rfl) rfl)) rfl)

noncomputable def ep636 := @ep592 78024483599 274877906944 11044952766617 23011953735630848 Bool.false 47496619799 137438953472 1381376431203 2876494216953856 Bool.true 6318266646287951593472 91942880627 274877906944 55077134294259 23011953735630848 Bool.false 16902724818278415335424 61491754671 68719476736 27533786027401 11505976867815424 (ep593 (BSN.head_sum_c_succ qz143 4 5 rfl rfl) (ep625 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep626 ep635) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz268 qz429 qz534)

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq qz426 (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 31063266031 274877906944 10051376188733 23011953735630848 Bool.true 13479106025 34359738368 1260175381105 2876494216953856 (BSN.cpow_neg_s_mk qz146 88388 1000 6 qz147 rfl)

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz534 88388 1000 0 1 4034681531866359 2251799813685248 500000000083717 41858500000000000000 89154357809650934823 562949953421312000 11048500001849894549 10464625000000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 16922680887833197019136 9444732965739290427392 1000000000167434 83717000000000000000 4034681531866359 2251799813685248 500000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep639 := nat_lit 8241657976454095551109249049656991613026372895337354429936322028421048984161

noncomputable def ep640 := nat_lit 13576245137732837964114539336096596166751886903349168255242964522948125281

noncomputable def ep641 := nat_lit 24697821439086820977399518070298781646745614912205364953298480156217250701921

noncomputable def ep642 := BSN.cos_dyadic_bound_f 1385471061 1073741824 3 2 524288 167598 ep639 ep64 ep640 ep641 ep66 ep640 145129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1385471061) qz294 0 2 ep639 ep64 ep640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1385471061) qz295 0 2 ep641 ep66 ep640 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41515733) qz48)

noncomputable def ep643 := @Enclosure.Real.IsNear.cos_image qz152 qz436 Bool.false 41515733 262144 277 262144 Bool.false 145129 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 89154357809650934823 562949953421312000 11048500001849894549 10464625000000000000000 41515733 262144 277 262144 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 41515733 262144) (BSN.cos_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48746929345237327282176) qz49) 226375608064910080 72057594037927936 Bool.false 145129 524288 25 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 41515733 262144 226375608064910080 72057594037927936 25 48746929345237327282176 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 145129 524288 48746929345237327282176 37778931862957161709568 1385471061 1073741824 167598 167434 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := nat_lit 14824123361507185721625356657913707626514069702084558639281185279539529671265

noncomputable def ep645 := nat_lit 38803104407057728485648320087991744532790679498092231116180329980042566460001

noncomputable def ep646 := BSN.sin_dyadic_bound_f 1385471061 1073741824 3 2 524288 167598 ep644 ep57 ep640 ep645 ep60 ep640 503800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1385471061) qz289 0 2 ep644 ep57 ep640 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1385471061) qz290 0 2 ep645 ep60 ep640 rfl rfl rfl rfl) rfl rfl

noncomputable def ep647 := @Enclosure.Real.IsNear.sin_image qz152 qz436 Bool.false 41515733 262144 277 262144 Bool.false 503800 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 89154357809650934823 562949953421312000 11048500001849894549 10464625000000000000000 41515733 262144 277 262144 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 41515733 262144) (BSN.sin_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48746929345237327282176) qz49) 226375608064910080 72057594037927936 Bool.false 503800 524288 25 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 41515733 262144 226375608064910080 72057594037927936 25 48746929345237327282176 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503800 524288 48746929345237327282176 37778931862957161709568 1385471061 1073741824 167598 167434 (ep646 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep648 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 31063266031 274877906944 10051376188733 23011953735630848 Bool.true 13479106025 34359738368 1260175381105 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz152) 214039 524288 1 524288 145129 524288 23451753 21945909248 31063266031 274877906944 10051376188733 23011953735630848 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 145129 524288 23451753 21945909248 145129 524288 23451753 21945909248 (ep643 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 214039 524288 1 524288 62975 65536 23451753 21945909248 13479106025 34359738368 1260175381105 2876494216953856 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 62975 65536 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 503800 524288 23451753 21945909248 62975 65536 23451753 21945909248 (ep647 rfl rfl) rfl)) rfl)

noncomputable def ep649 := @ep590 31063266031 274877906944 10051376188733 23011953735630848 Bool.true 13479106025 34359738368 1260175381105 2876494216953856 Bool.true 16734461035705872154624 15219903649 68719476736 4070531905187 1438247108476928 Bool.false 1186563489377736982528 34533542621 68719476736 32574487551821 11505976867815424 (ep591 (BSN.head_sum_c_succ qz143 5 6 rfl rfl) (ep636 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep637 ep648) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz429 qz535)

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq qz425 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 18229608859 68719476736 2331347968727 5752988433907712 Bool.true 74006152143 274877906944 9325851397521 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 7 qz147 rfl)

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz535 88388 1000 0 1 4381792198794487 2251799813685248 500000000083717 41858500000000000000 96824462216761779239 562949953421312000 11048500001849894549 10464625000000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000083717 41858500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 18378568546572512002048 9444732965739290427392 1000000000167434 83717000000000000000 4381792198794487 2251799813685248 500000000083717 41858500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep127 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep652 := nat_lit 486975602552349824466680843544598641

noncomputable def ep653 := BSN.sin_dyadic_bound_f 835366011 1073741824 2 1 524288 167598 ep652 ep79 ep652 ep652 ep80 ep652 367972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 835366011) qz289 0 1 ep652 ep79 ep652 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 835366011) qz290 0 1 ep652 ep80 ep652 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90174807) qz24)

noncomputable def ep654 := @Enclosure.Real.IsNear.cos_image qz153 qz437 Bool.false 90174807 524288 277 262144 Bool.true 367972 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 96824462216761779239 562949953421312000 11048500001849894549 10464625000000000000000 90174807 524288 277 262144 (ep651 rfl) rfl) (Enclosure.sfrac_false_div 90174807 524288) (BSN.cos_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58783657185226830905344) qz26) 226375608064910080 72057594037927936 Bool.false 367972 524288 27 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 90174807 524288 226375608064910080 72057594037927936 27 58783657185226830905344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 367972 524288 58783657185226830905344 75557863725914323419136 835366011 1073741824 167598 167434 (ep653 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep655 := nat_lit 1087703840254524913570341375200683707188393949375167365488958005615998689761

noncomputable def ep656 := nat_lit 237145237481224180873602794042370613908565964745476523053656405779046881

noncomputable def ep657 := nat_lit 3262637230288612292349276920013966380337364716196011143420766704036437975521

noncomputable def ep658 := BSN.cos_dyadic_bound_f 835366011 1073741824 3 2 524288 167598 ep655 ep64 ep656 ep657 ep66 ep656 373461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 835366011) qz294 0 2 ep655 ep64 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 835366011) qz295 0 2 ep657 ep66 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable def ep659 := @Enclosure.Real.IsNear.sin_image qz153 qz437 Bool.false 90174807 524288 277 262144 Bool.false 373461 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 96824462216761779239 562949953421312000 11048500001849894549 10464625000000000000000 90174807 524288 277 262144 (ep651 rfl) rfl) (Enclosure.sfrac_false_div 90174807 524288) (BSN.sin_reduce1 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58783657185226830905344) qz26) 226375608064910080 72057594037927936 Bool.false 373461 524288 27 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 90174807 524288 226375608064910080 72057594037927936 27 58783657185226830905344 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 373461 524288 58783657185226830905344 75557863725914323419136 835366011 1073741824 167598 167434 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 18229608859 68719476736 2331347968727 5752988433907712 Bool.true 74006152143 274877906944 9325851397521 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz153) 198163 524288 1 524288 91993 131072 23451753 21945909248 18229608859 68719476736 2331347968727 5752988433907712 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 367972 524288 23451753 21945909248 91993 131072 23451753 21945909248 (ep654 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz32 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 198163 524288 1 524288 373461 524288 23451753 21945909248 74006152143 274877906944 9325851397521 23011953735630848 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 373461 524288 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 373461 524288 23451753 21945909248 373461 524288 23451753 21945909248 (ep659 rfl rfl) rfl)) rfl)

noncomputable def ep661 := @ep588 18229608859 68719476736 2331347968727 5752988433907712 Bool.true 74006152143 274877906944 9325851397521 23011953735630848 Bool.true 2298632996624047013888 8362378127 17179869184 18613475589475 5752988433907712 Bool.false 4406843864510130814976 64128018341 274877906944 74474826501163 23011953735630848 (ep589 (BSN.head_sum_c_succ qz143 6 7 rfl rfl) (ep649 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep650 ep660) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz429 qz536)

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq qz424 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.true 1409685615 274877906944 8710376271957 23011953735630848 Bool.true 12146652027 34359738368 2188406683629 5752988433907712 (BSN.cpow_neg_s_mk qz146 88388 1000 8 qz147 rfl)

noncomputable def ep663 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz536 88388 1000 0 1 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 206937789648224873589 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 19639770079031275290624 9444732965739290427392 1000000000251151 83717000000000000000 9364972152248037 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep664 := BSN.sin_dyadic_bound_f 15577587 1073741824 1 0 524288 167598 0 1 1 0 1 1 7605 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 15577587) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 15577587) qz290 0 0 rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96362917) qz24)

noncomputable def ep665 := @Enclosure.Real.IsNear.cos_image qz154 qz438 Bool.false 96362917 524288 555 524288 Bool.true 7605 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 206937789648224873589 1125899906842624000 22097000005549683647 20929250000000000000000 96362917 524288 555 524288 (ep663 rfl) rfl) (Enclosure.sfrac_false_div 96362917 524288) (BSN.cos_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1096175260226702802944) qz26) 226375608064910080 72057594037927936 Bool.false 7605 524288 29 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 96362917 524288 226375608064910080 72057594037927936 29 1096175260226702802944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7605 524288 1096175260226702802944 75557863725914323419136 15577587 1073741824 167598 167434 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := BSN.cos_dyadic_bound_f 15577587 1073741824 1 0 524288 167598 0 1 1 0 1 1 524232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 15577587) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 15577587) qz295 0 0 rfl) rfl rfl

noncomputable def ep667 := @Enclosure.Real.IsNear.sin_image qz154 qz438 Bool.false 96362917 524288 555 524288 Bool.false 524232 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 206937789648224873589 1125899906842624000 22097000005549683647 20929250000000000000000 96362917 524288 555 524288 (ep663 rfl) rfl) (Enclosure.sfrac_false_div 96362917 524288) (BSN.sin_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1096175260226702802944) qz26) 226375608064910080 72057594037927936 Bool.false 524232 524288 29 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 96362917 524288 226375608064910080 72057594037927936 29 1096175260226702802944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524232 524288 1096175260226702802944 75557863725914323419136 15577587 1073741824 167598 167434 (ep666 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep668 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.true 1409685615 274877906944 8710376271957 23011953735630848 Bool.true 12146652027 34359738368 2188406683629 5752988433907712 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz154) 185363 524288 1 524288 7605 524288 46987223 43891818496 1409685615 274877906944 8710376271957 23011953735630848 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.true 7605 524288 46987223 43891818496 7605 524288 46987223 43891818496 (ep665 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 185363 524288 1 524288 65529 65536 46987223 43891818496 12146652027 34359738368 2188406683629 5752988433907712 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 65529 65536 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 524232 524288 46987223 43891818496 65529 65536 46987223 43891818496 (ep667 rfl rfl) rfl)) rfl)

noncomputable def ep669 := @ep586 1409685615 274877906944 8710376271957 23011953735630848 Bool.true 12146652027 34359738368 2188406683629 5752988433907712 Bool.true 2322851211080313602048 135207735647 274877906944 83164278629857 23011953735630848 Bool.true 1135424353303789568000 33045197875 274877906944 83228453235679 23011953735630848 (ep587 (BSN.head_sum_c_succ qz143 7 8 rfl rfl) (ep661 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep662 ep668) rfl rfl

theorem EMRow24.d11 : Enclosure.Complex.IsNear qz142 Bool.true 135207735647 274877906944 83164278629857 23011953735630848 Bool.true 33045197875 274877906944 83228453235679 23011953735630848 := ep585 (BSN.head_sum_c_succ qz143 8 9 rfl rfl) (ep669 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz155 := (BSN.headSumC qz422 17)

noncomputable abbrev qz156 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz423)

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 16) qz156) Bool.false 187291989515 274877906944 139870197897717 23011953735630848 Bool.true 65149037491 274877906944 139851868730303 23011953735630848

noncomputable def ep671 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 16) qz156 Bool.false 14823251637 34359738368 33419644507193 5752988433907712 Bool.true 3988740405 17179869184 66851641708887 11505976867815424 Bool.false

noncomputable abbrev qz157 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz423)

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 15) qz157) Bool.false 14823251637 34359738368 33419644507193 5752988433907712 Bool.true 3988740405 17179869184 66851641708887 11505976867815424

noncomputable def ep673 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 15) qz157 Bool.false 59919876713 274877906944 127281542989375 23011953735630848 Bool.true 23876331623 274877906944 127317826941779 23011953735630848 Bool.false

noncomputable abbrev qz158 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz423)

noncomputable def ep674 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 14) qz158) Bool.false 59919876713 274877906944 127281542989375 23011953735630848 Bool.true 23876331623 274877906944 127317826941779 23011953735630848

noncomputable def ep675 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 14) qz158 Bool.false 7839983675 274877906944 120666483561043 23011953735630848 Bool.false 27936771031 274877906944 120702926910615 23011953735630848 Bool.false

noncomputable abbrev qz159 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz423)

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 13) qz159) Bool.false 7839983675 274877906944 120666483561043 23011953735630848 Bool.false 27936771031 274877906944 120702926910615 23011953735630848

noncomputable def ep677 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 13) qz159 Bool.true 58480519315 274877906944 113795795003637 23011953735630848 Bool.false 8191979839 34359738368 28462193512833 5752988433907712 Bool.false

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz423)

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 12) qz160) Bool.true 58480519315 274877906944 113795795003637 23011953735630848 Bool.false 8191979839 34359738368 28462193512833 5752988433907712

noncomputable def ep679 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 12) qz160 Bool.true 134835484419 274877906944 106642043910955 23011953735630848 Bool.false 43939698553 274877906944 106725312187835 23011953735630848 Bool.false

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz423)

noncomputable def ep680 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 11) qz161) Bool.true 134835484419 274877906944 106642043910955 23011953735630848 Bool.false 43939698553 274877906944 106725312187835 23011953735630848

noncomputable def ep681 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 11) qz161 Bool.true 125524315161 274877906944 99222606583741 23011953735630848 Bool.true 38414401919 274877906944 99267192081299 23011953735630848 Bool.true

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz423)

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 10) qz162) Bool.true 125524315161 274877906944 99222606583741 23011953735630848 Bool.true 38414401919 274877906944 99267192081299 23011953735630848

noncomputable def ep683 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 10) qz162 Bool.true 14523084639 68719476736 45699131832355 11505976867815424 Bool.false 16437547471 274877906944 91449201357077 23011953735630848 Bool.true

noncomputable abbrev qz439 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz144)

noncomputable def ep684 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 10) (@HAdd.hAdd Complex Complex Complex qz4 qz142 qz439) Bool.true 14523084639 68719476736 45699131832355 11505976867815424 Bool.false 16437547471 274877906944 91449201357077 23011953735630848

noncomputable def ep685 := @Enclosure.Complex.IsNear.addLitP qz142 qz439 Bool.true 135207735647 274877906944 83164278629857 23011953735630848 Bool.true 33045197875 274877906944 83228453235679 23011953735630848 Bool.false

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz268 qz429 qz537)

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq qz439 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 77115397091 274877906944 8233985034853 23011953735630848 Bool.false 24741372673 137438953472 4110374060699 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 9 qz147 rfl)

noncomputable def ep687 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz537 88388 1000 0 1 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 218659046975748664437 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 20752195215788806766592 9444732965739290427392 1000000000251151 83717000000000000000 9895417793173221 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep172 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep688 := nat_lit 5351088962322271007421113454446237927814571068681607632536906915104585482240

noncomputable def ep689 := nat_lit 1771064111334614531222004192124719580863348394262951559220676721712889856

noncomputable def ep690 := nat_lit 14011889368949501357814271040571945026859621663432546639834113205819712536576

noncomputable def ep691 := BSN.sin_dyadic_bound_f 1074061836 1073741824 3 2 524288 167598 ep688 ep57 ep689 ep690 ep60 ep689 441257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1074061836) qz289 0 2 ep688 ep57 ep689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1074061836) qz290 0 2 ep690 ep60 ep689 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101821053) qz24)

noncomputable def ep692 := @Enclosure.Real.IsNear.cos_image qz163 qz440 Bool.false 101821053 524288 277 262144 Bool.false 441257 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 218659046975748664437 1125899906842624000 22097000005549683647 20929250000000000000000 101821053 524288 277 262144 (ep687 rfl) rfl) (Enclosure.sfrac_false_div 101821053 524288) (BSN.cos_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75580382637012912439296) qz26) 226375608064910080 72057594037927936 Bool.false 441257 524288 30 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 101821053 524288 226375608064910080 72057594037927936 30 75580382637012912439296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441257 524288 75580382637012912439296 75557863725914323419136 1074061836 1073741824 167598 167434 (ep691 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep693 := nat_lit 2973614340895188166136717254333298724155145415220565552102379698045530996736

noncomputable def ep694 := nat_lit 8917300894462895269347707754615646733303709548873170753188697740693167210496

noncomputable def ep695 := BSN.cos_dyadic_bound_f 1074061836 1073741824 3 2 524288 167598 ep693 ep64 ep689 ep694 ep66 ep689 283142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1074061836) qz294 0 2 ep693 ep64 ep689 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1074061836) qz295 0 2 ep694 ep66 ep689 rfl rfl rfl rfl) rfl rfl

noncomputable def ep696 := @Enclosure.Real.IsNear.sin_image qz163 qz440 Bool.false 101821053 524288 277 262144 Bool.true 283142 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 218659046975748664437 1125899906842624000 22097000005549683647 20929250000000000000000 101821053 524288 277 262144 (ep687 rfl) rfl) (Enclosure.sfrac_false_div 101821053 524288) (BSN.sin_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75580382637012912439296) qz26) 226375608064910080 72057594037927936 Bool.false 283142 524288 30 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 101821053 524288 226375608064910080 72057594037927936 30 75580382637012912439296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 283142 524288 75580382637012912439296 75557863725914323419136 1074061836 1073741824 167598 167434 (ep695 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep697 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 77115397091 274877906944 8233985034853 23011953735630848 Bool.false 24741372673 137438953472 4110374060699 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz163) 174763 524288 1 524288 441257 524288 23451753 21945909248 77115397091 274877906944 8233985034853 23011953735630848 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 441257 524288 23451753 21945909248 441257 524288 23451753 21945909248 (ep692 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 174763 524288 1 524288 141571 262144 23451753 21945909248 24741372673 137438953472 4110374060699 11505976867815424 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 141571 262144 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 283142 524288 23451753 21945909248 141571 262144 23451753 21945909248 (ep696 rfl rfl) rfl)) rfl)

noncomputable def ep698 := @ep685 77115397091 274877906944 8233985034853 23011953735630848 Bool.false 24741372673 137438953472 4110374060699 11505976867815424 Bool.true 15968300431755511332864 14523084639 68719476736 45699131832355 11505976867815424 Bool.false 2259159322060560269312 16437547471 274877906944 91449201357077 23011953735630848 EMRow24.d11 (ep686 ep697) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz268 qz429 qz538)

noncomputable def ep699 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 67431976605 274877906944 7824342919031 23011953735630848 Bool.true 27425974695 137438953472 3908995362111 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 10 qz147 rfl)

noncomputable def ep700 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz538 88388 1000 0 1 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 229143870337870687349 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 21747274560655572598784 9444732965739290427392 1000000000251151 83717000000000000000 10369908600166117 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep183 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep701 := nat_lit 826193267155770060557989128435175696

noncomputable def ep702 := BSN.sin_dyadic_bound_f 953389606 1073741824 2 1 524288 167598 ep701 ep79 ep701 ep701 ep80 ep701 406719 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 953389606) qz289 0 1 ep701 ep79 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 953389606) qz290 0 1 ep701 ep80 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106703429) qz24)

noncomputable def ep703 := @Enclosure.Real.IsNear.cos_image qz164 qz441 Bool.false 106703429 524288 555 524288 Bool.true 406719 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 229143870337870687349 1125899906842624000 22097000005549683647 20929250000000000000000 106703429 524288 555 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 106703429 524288) (BSN.cos_reduce1 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67088829327244345212928) qz26) 226375608064910080 72057594037927936 Bool.false 406719 524288 32 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 106703429 524288 226375608064910080 72057594037927936 32 67088829327244345212928 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 406719 524288 67088829327244345212928 75557863725914323419136 953389606 1073741824 167598 167434 (ep702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep704 := nat_lit 1845657285977219269225108562257549262754645661773221900453555869149838909696

noncomputable def ep705 := nat_lit 682595314693525639490650073710920412337219580004770518465044062389084416

noncomputable def ep706 := nat_lit 5535606667302270756396344386625225947439262546159656160323737519324738560256

noncomputable def ep707 := BSN.cos_dyadic_bound_f 953389606 1073741824 3 2 524288 167598 ep704 ep64 ep705 ep706 ep66 ep705 330842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 953389606) qz294 0 2 ep704 ep64 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 953389606) qz295 0 2 ep706 ep66 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable def ep708 := @Enclosure.Real.IsNear.sin_image qz164 qz441 Bool.false 106703429 524288 555 524288 Bool.false 330842 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 229143870337870687349 1125899906842624000 22097000005549683647 20929250000000000000000 106703429 524288 555 524288 (ep700 rfl) rfl) (Enclosure.sfrac_false_div 106703429 524288) (BSN.sin_reduce1 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67088829327244345212928) qz26) 226375608064910080 72057594037927936 Bool.false 330842 524288 32 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 106703429 524288 226375608064910080 72057594037927936 32 67088829327244345212928 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 330842 524288 67088829327244345212928 75557863725914323419136 953389606 1073741824 167598 167434 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep709 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 67431976605 274877906944 7824342919031 23011953735630848 Bool.true 27425974695 137438953472 3908995362111 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz164) 165795 524288 1 524288 406719 524288 46987223 43891818496 67431976605 274877906944 7824342919031 23011953735630848 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 406719 524288 46987223 43891818496 406719 524288 46987223 43891818496 (ep703 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 165795 524288 1 524288 165421 262144 46987223 43891818496 27425974695 137438953472 3908995362111 11505976867815424 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 165421 262144 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 330842 524288 46987223 43891818496 165421 262144 46987223 43891818496 (ep708 rfl rfl) rfl)) rfl)

noncomputable def ep710 := @ep683 67431976605 274877906944 7824342919031 23011953735630848 Bool.true 27425974695 137438953472 3908995362111 11505976867815424 Bool.true 8625965255508671594496 125524315161 274877906944 99222606583741 23011953735630848 Bool.true 5279635198000148512768 38414401919 274877906944 99267192081299 23011953735630848 (ep684 (BSN.head_sum_c_succ qz143 9 10 rfl rfl) (ep698 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep699 ep709) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz429 qz539)

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 4655584629 137438953472 3709718663607 11505976867815424 Bool.false 10294262559 34359738368 932265013317 2876494216953856 (BSN.cpow_neg_s_mk qz146 88388 1000 11 qz147 rfl)

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz539 88388 1000 0 1 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 238628765218301504629 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 22647454054174387339264 9444732965739290427392 1000000000251151 83717000000000000000 10799147631728357 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep194 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep713 := nat_lit 13457300338896643893646274155099464604454666971790574084894441119011482212481

noncomputable def ep714 := nat_lit 36121336803724780549000879389100982583872458340741555702036811040934172801

noncomputable def ep715 := nat_lit 40299658343082482119840820706520191848196255998690239143279249734952578291841

noncomputable def ep716 := BSN.cos_dyadic_bound_f 1565742993 1073741824 3 2 524288 167598 ep713 ep64 ep714 ep715 ep66 ep714 58902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1565742993) qz294 0 2 ep713 ep64 ep714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1565742993) qz295 0 2 ep715 ep66 ep714 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55560089) qz48)

noncomputable def ep717 := @Enclosure.Real.IsNear.cos_image qz165 qz442 Bool.false 55560089 262144 277 262144 Bool.true 58902 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 238628765218301504629 1125899906842624000 22097000005549683647 20929250000000000000000 55560089 262144 277 262144 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 55560089 262144) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55089684070207405948928) qz49) 226375608064910080 72057594037927936 Bool.false 58902 524288 33 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 55560089 262144 226375608064910080 72057594037927936 33 55089684070207405948928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 58902 524288 55089684070207405948928 37778931862957161709568 1565742993 1073741824 167598 167434 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := nat_lit 24194243540570979184124092775667755501951302582550440108248364565387920644225

noncomputable def ep719 := nat_lit 63307393775241772028007574893452243771403332307461380621894799977187803502721

noncomputable def ep720 := BSN.sin_dyadic_bound_f 1565742993 1073741824 3 2 524288 167598 ep718 ep57 ep714 ep719 ep60 ep714 520968 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1565742993) qz289 0 2 ep718 ep57 ep714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1565742993) qz290 0 2 ep719 ep60 ep714 rfl rfl rfl rfl) rfl rfl

noncomputable def ep721 := @Enclosure.Real.IsNear.sin_image qz165 qz442 Bool.false 55560089 262144 277 262144 Bool.true 520968 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 238628765218301504629 1125899906842624000 22097000005549683647 20929250000000000000000 55560089 262144 277 262144 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 55560089 262144) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55089684070207405948928) qz49) 226375608064910080 72057594037927936 Bool.false 520968 524288 33 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 55560089 262144 226375608064910080 72057594037927936 33 55089684070207405948928 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 520968 524288 55089684070207405948928 37778931862957161709568 1565742993 1073741824 167598 167434 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 4655584629 137438953472 3709718663607 11505976867815424 Bool.false 10294262559 34359738368 932265013317 2876494216953856 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz165) 158079 524288 1 524288 29451 262144 23451753 21945909248 4655584629 137438953472 3709718663607 11505976867815424 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 58902 524288 23451753 21945909248 29451 262144 23451753 21945909248 (ep717 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 158079 524288 1 524288 65121 65536 23451753 21945909248 10294262559 34359738368 932265013317 2876494216953856 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 65121 65536 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 520968 524288 23451753 21945909248 65121 65536 23451753 21945909248 (ep721 rfl rfl) rfl)) rfl)

noncomputable def ep723 := @ep681 4655584629 137438953472 3709718663607 11505976867815424 Bool.false 10294262559 34359738368 932265013317 2876494216953856 Bool.true 18531647869437521952768 134835484419 274877906944 106642043910955 23011953735630848 Bool.false 1509756546249868181504 43939698553 274877906944 106725312187835 23011953735630848 (ep682 (BSN.head_sum_c_succ qz143 10 11 rfl rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep711 ep722) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz429 qz540)

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 4772185319 17179869184 3576875546341 11505976867815424 Bool.false 21596140159 274877906944 7123461863497 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 12 qz147 rfl)

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz540 88388 1000 0 1 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 247287978835376827509 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz335) Bool.false 23469270914176955449344 9444732965739290427392 1000000000251151 83717000000000000000 11191020447815397 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep205 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep726 := nat_lit 15047787993231647483705304611451069509494641302227991022504155579004805869025

noncomputable def ep727 := nat_lit 13988623046904085046036546205531159231871008937836672352607928751469522401

noncomputable def ep728 := nat_lit 39388225068768851081534595764705750648015317015173955208463804155605445668321

noncomputable def ep729 := BSN.sin_dyadic_bound_f 1390662907 1073741824 3 2 524288 167598 ep726 ep57 ep727 ep728 ep60 ep727 504496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1390662907) qz289 0 2 ep726 ep57 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1390662907) qz290 0 2 ep728 ep60 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57576219) qz48)

noncomputable def ep730 := @Enclosure.Real.IsNear.cos_image qz166 qz443 Bool.false 57576219 262144 555 524288 Bool.false 504496 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 247287978835376827509 1125899906842624000 22097000005549683647 20929250000000000000000 57576219 262144 555 524288 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 57576219 262144) (BSN.cos_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48929601202743765106688) qz49) 226375608064910080 72057594037927936 Bool.false 504496 524288 34 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 57576219 262144 226375608064910080 72057594037927936 34 48929601202743765106688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504496 524288 48929601202743765106688 37778931862957161709568 1390662907 1073741824 167598 167434 (ep729 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep731 := nat_lit 8366099384260650417634518804675274687155632282987922422436801067781100826081

noncomputable def ep732 := nat_lit 25070320906688143082811483321614761743003154831088093922605187345840363433441

noncomputable def ep733 := BSN.cos_dyadic_bound_f 1390662907 1073741824 3 2 524288 167598 ep731 ep64 ep727 ep732 ep66 ep727 142691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1390662907) qz294 0 2 ep731 ep64 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1390662907) qz295 0 2 ep732 ep66 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable def ep734 := @Enclosure.Real.IsNear.sin_image qz166 qz443 Bool.false 57576219 262144 555 524288 Bool.true 142691 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 247287978835376827509 1125899906842624000 22097000005549683647 20929250000000000000000 57576219 262144 555 524288 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 57576219 262144) (BSN.sin_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48929601202743765106688) qz49) 226375608064910080 72057594037927936 Bool.false 142691 524288 34 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 57576219 262144 226375608064910080 72057594037927936 34 48929601202743765106688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 142691 524288 48929601202743765106688 37778931862957161709568 1390662907 1073741824 167598 167434 (ep733 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep735 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 4772185319 17179869184 3576875546341 11505976867815424 Bool.false 21596140159 274877906944 7123461863497 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz166) 151349 524288 1 524288 31531 32768 46987223 43891818496 4772185319 17179869184 3576875546341 11505976867815424 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 504496 524288 46987223 43891818496 31531 32768 46987223 43891818496 (ep730 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 151349 524288 1 524288 142691 524288 46987223 43891818496 21596140159 274877906944 7123461863497 23011953735630848 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 142691 524288 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 142691 524288 46987223 43891818496 142691 524288 46987223 43891818496 (ep734 rfl rfl) rfl)) rfl)

noncomputable def ep736 := @ep679 4772185319 17179869184 3576875546341 11505976867815424 Bool.false 21596140159 274877906944 7123461863497 23011953735630848 Bool.true 1004687671644085288960 58480519315 274877906944 113795795003637 23011953735630848 Bool.false 18014354174974128816128 8191979839 34359738368 28462193512833 5752988433907712 (ep680 (BSN.head_sum_c_succ qz143 11 12 rfl rfl) (ep723 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep724 ep735) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz429 qz541)

noncomputable def ep737 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 33160251495 137438953472 3435344278703 11505976867815424 Bool.true 37599067681 274877906944 6854152859283 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 13 qz147 rfl)

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz541 88388 1000 0 1 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 51050648113532835249 225179981368524800 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 24225227133228857425920 9444732965739290427392 1000000000251151 83717000000000000000 11551488463034085 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep739 := nat_lit 94047766119795408959594941374163216

noncomputable def ep740 := BSN.cos_dyadic_bound_f 553779814 1073741824 2 1 524288 167598 ep739 ep75 ep739 ep739 ep76 ep739 456090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553779814) qz294 0 1 ep739 ep75 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553779814) qz295 0 1 ep739 ep76 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7428847) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz445 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep741 := @Enclosure.Real.IsNear.cos_image qz167 qz444 Bool.false 7428847 32768 555 524288 Bool.false 456090 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 51050648113532835249 225179981368524800 22097000005549683647 20929250000000000000000 7428847 32768 555 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 7428847 32768) (BSN.cos_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435549381537482932224) qz445) 226375608064910080 72057594037927936 Bool.false 456090 524288 36 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 7428847 32768 226375608064910080 72057594037927936 36 2435549381537482932224 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456090 524288 2435549381537482932224 4722366482869645213696 553779814 1073741824 167598 167434 (ep740 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep742 := BSN.sin_dyadic_bound_f 553779814 1073741824 2 1 524288 167598 ep739 ep79 ep739 ep739 ep80 ep739 258571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553779814) qz289 0 1 ep739 ep79 ep739 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553779814) qz290 0 1 ep739 ep80 ep739 rfl rfl rfl rfl) rfl rfl

noncomputable def ep743 := @Enclosure.Real.IsNear.sin_image qz167 qz444 Bool.false 7428847 32768 555 524288 Bool.false 258571 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 51050648113532835249 225179981368524800 22097000005549683647 20929250000000000000000 7428847 32768 555 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 7428847 32768) (BSN.sin_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2435549381537482932224) qz445) 226375608064910080 72057594037927936 Bool.false 258571 524288 36 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 7428847 32768 226375608064910080 72057594037927936 36 2435549381537482932224 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 258571 524288 2435549381537482932224 4722366482869645213696 553779814 1073741824 167598 167434 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep744 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 33160251495 137438953472 3435344278703 11505976867815424 Bool.true 37599067681 274877906944 6854152859283 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz167) 145411 524288 1 524288 228045 262144 46987223 43891818496 33160251495 137438953472 3435344278703 11505976867815424 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 456090 524288 46987223 43891818496 228045 262144 46987223 43891818496 (ep741 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 145411 524288 1 524288 258571 524288 46987223 43891818496 37599067681 274877906944 6854152859283 23011953735630848 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 258571 524288 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 258571 524288 46987223 43891818496 258571 524288 46987223 43891818496 (ep743 rfl rfl) rfl)) rfl)

noncomputable def ep745 := @ep677 33160251495 137438953472 3435344278703 11505976867815424 Bool.true 37599067681 274877906944 6854152859283 23011953735630848 Bool.false 1077519151529564569600 7839983675 274877906944 120666483561043 23011953735630848 Bool.false 959900143471881617408 27936771031 274877906944 120702926910615 23011953735630848 (ep678 (BSN.head_sum_c_succ qz143 12 13 rfl rfl) (ep736 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep737 ep744) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz429 qz542)

noncomputable def ep746 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 26039946519 137438953472 1653764857083 5752988433907712 Bool.true 25906551327 137438953472 1653725007791 5752988433907712 (BSN.cpow_neg_s_mk qz146 88388 1000 14 qz147 rfl)

noncomputable def ep747 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz542 88388 1000 0 1 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 262628187649598516341 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 24925158572916270432256 9444732965739290427392 1000000000251151 83717000000000000000 11885241781671653 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep226 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep748 := nat_lit 1115003637828047851546471038990059545302552843294584287809599142298173604096

noncomputable def ep749 := nat_lit 249195904387015738746607815393010191773655502722037177242191347336642816

noncomputable def ep750 := nat_lit 3344512521675369523161919901339392615524111218878308789074313044199847526656

noncomputable def ep751 := BSN.cos_dyadic_bound_f 840557858 1073741824 3 2 524288 167598 ep748 ep64 ep749 ep750 ep66 ep749 371678 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 840557858) qz294 0 2 ep748 ep64 ep749 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 840557858) qz295 0 2 ep750 ep66 ep749 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122295779) qz24)

noncomputable def ep752 := @Enclosure.Real.IsNear.cos_image qz168 qz446 Bool.false 122295779 524288 555 524288 Bool.false 371678 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 262628187649598516341 1125899906842624000 22097000005549683647 20929250000000000000000 122295779 524288 555 524288 (ep747 rfl) rfl) (Enclosure.sfrac_false_div 122295779 524288) (BSN.cos_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59149000900239706554368) qz26) 226375608064910080 72057594037927936 Bool.false 371678 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 122295779 524288 226375608064910080 72057594037927936 37 59149000900239706554368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371678 524288 59149000900239706554368 75557863725914323419136 840557858 1073741824 167598 167434 (ep751 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep753 := nat_lit 499195256775358131754188368043770896

noncomputable def ep754 := BSN.sin_dyadic_bound_f 840557858 1073741824 2 1 524288 167598 ep753 ep79 ep753 ep753 ep80 ep753 369774 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 840557858) qz289 0 1 ep753 ep79 ep753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 840557858) qz290 0 1 ep753 ep80 ep753 rfl rfl rfl rfl) rfl rfl

noncomputable def ep755 := @Enclosure.Real.IsNear.sin_image qz168 qz446 Bool.false 122295779 524288 555 524288 Bool.false 369774 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 262628187649598516341 1125899906842624000 22097000005549683647 20929250000000000000000 122295779 524288 555 524288 (ep747 rfl) rfl) (Enclosure.sfrac_false_div 122295779 524288) (BSN.sin_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59149000900239706554368) qz26) 226375608064910080 72057594037927936 Bool.false 369774 524288 37 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 122295779 524288 226375608064910080 72057594037927936 37 59149000900239706554368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369774 524288 59149000900239706554368 75557863725914323419136 840557858 1073741824 167598 167434 (ep754 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep756 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 26039946519 137438953472 1653764857083 5752988433907712 Bool.true 25906551327 137438953472 1653725007791 5752988433907712 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz168) 140121 524288 1 524288 185839 262144 46987223 43891818496 26039946519 137438953472 1653764857083 5752988433907712 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 371678 524288 46987223 43891818496 185839 262144 46987223 43891818496 (ep752 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 140121 524288 1 524288 184887 262144 46987223 43891818496 25906551327 137438953472 1653725007791 5752988433907712 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 184887 262144 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 369774 524288 46987223 43891818496 184887 262144 46987223 43891818496 (ep755 rfl rfl) rfl)) rfl)

noncomputable def ep757 := @ep675 26039946519 137438953472 1653764857083 5752988433907712 Bool.true 25906551327 137438953472 1653725007791 5752988433907712 Bool.false 8235325147605983297536 59919876713 274877906944 127281542989375 23011953735630848 Bool.true 3281538031015539245056 23876331623 274877906944 127317826941779 23011953735630848 (ep676 (BSN.head_sum_c_succ qz143 13 14 rfl rfl) (ep745 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep746 ep756) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz429 qz543)

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq qz157 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 58666136383 274877906944 6397035039397 23011953735630848 Bool.true 39943514857 274877906944 6385456475995 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 15 qz147 rfl)

noncomputable def ep759 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz543 88388 1000 0 1 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 269494059525022641269 1125899906842624000 22097000005549683647 20929250000000000000000 qz148 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 25576775395801252757504 9444732965739290427392 1000000000251151 83717000000000000000 12195956895733477 4503599627370496 1000000000251151 83717000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep240 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep760 := nat_lit 169715390882963839534495182675993616

noncomputable def ep761 := BSN.cos_dyadic_bound_f 641845214 1073741824 2 1 524288 167598 ep760 ep75 ep760 ep760 ep76 ep760 433373 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 641845214) qz294 0 1 ep760 ep75 ep760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 641845214) qz295 0 1 ep760 ep76 ep760 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62746475) qz48)

noncomputable def ep762 := @Enclosure.Real.IsNear.cos_image qz169 qz447 Bool.false 62746475 262144 555 524288 Bool.false 433373 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 269494059525022641269 1125899906842624000 22097000005549683647 20929250000000000000000 62746475 262144 555 524288 (ep759 rfl) rfl) (Enclosure.sfrac_false_div 62746475 262144) (BSN.cos_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22582920835684798300160) qz49) 226375608064910080 72057594037927936 Bool.false 433373 524288 38 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 62746475 262144 226375608064910080 72057594037927936 38 22582920835684798300160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 433373 524288 22582920835684798300160 37778931862957161709568 641845214 1073741824 167598 167434 (ep761 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep763 := BSN.sin_dyadic_bound_f 641845214 1073741824 2 1 524288 167598 ep760 ep79 ep760 ep760 ep80 ep760 295067 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 641845214) qz289 0 1 ep760 ep79 ep760 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 641845214) qz290 0 1 ep760 ep80 ep760 rfl rfl rfl rfl) rfl rfl

noncomputable def ep764 := @Enclosure.Real.IsNear.sin_image qz169 qz447 Bool.false 62746475 262144 555 524288 Bool.false 295067 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 269494059525022641269 1125899906842624000 22097000005549683647 20929250000000000000000 62746475 262144 555 524288 (ep759 rfl) rfl) (Enclosure.sfrac_false_div 62746475 262144) (BSN.sin_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22582920835684798300160) qz49) 226375608064910080 72057594037927936 Bool.false 295067 524288 38 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 62746475 262144 226375608064910080 72057594037927936 38 22582920835684798300160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 295067 524288 22582920835684798300160 37778931862957161709568 641845214 1073741824 167598 167434 (ep763 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep765 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 58666136383 274877906944 6397035039397 23011953735630848 Bool.true 39943514857 274877906944 6385456475995 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz169) 135371 524288 1 524288 433373 524288 46987223 43891818496 58666136383 274877906944 6397035039397 23011953735630848 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 433373 524288 46987223 43891818496 433373 524288 46987223 43891818496 (ep762 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 135371 524288 1 524288 295067 524288 46987223 43891818496 39943514857 274877906944 6385456475995 23011953735630848 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 295067 524288 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 295067 524288 46987223 43891818496 295067 524288 46987223 43891818496 (ep764 rfl rfl) rfl)) rfl)

noncomputable def ep766 := @ep673 58666136383 274877906944 6397035039397 23011953735630848 Bool.true 39943514857 274877906944 6385456475995 23011953735630848 Bool.false 32596675072662253338624 14823251637 34359738368 33419644507193 5752988433907712 Bool.true 17542665821909805957120 3988740405 17179869184 66851641708887 11505976867815424 (ep674 (BSN.head_sum_c_succ qz143 14 15 rfl rfl) (ep757 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep758 ep765) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz429 qz544)

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq qz156 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 68705976419 274877906944 6191619868945 23011953735630848 Bool.true 1329191011 274877906944 6148585312529 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 16 qz147 rfl)

noncomputable def ep768 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz544 88388 1000 0 1 3121657384082679 1125899906842624 250000000083717 20929250000000000000 68979263216074957863 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 26186360105375033720832 9444732965739290427392 1000000000334868 83717000000000000000 3121657384082679 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep251 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep769 := BSN.cos_dyadic_bound_f 20771481 1073741824 1 0 524288 167598 0 1 1 0 1 1 524189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20771481) qz294 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20771481) qz295 0 0 rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64241945) qz48)

noncomputable def ep770 := @Enclosure.Real.IsNear.cos_image qz170 qz448 Bool.false 64241945 262144 277 262144 Bool.false 524189 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 68979263216074957863 281474976710656000 5524250001849894549 5232312500000000000000 64241945 262144 277 262144 (ep768 rfl) rfl) (Enclosure.sfrac_false_div 64241945 262144) (BSN.cos_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 730831545213827153920) qz49) 226375608064910080 72057594037927936 Bool.false 524189 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 64241945 262144 226375608064910080 72057594037927936 39 730831545213827153920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524189 524288 730831545213827153920 37778931862957161709568 20771481 1073741824 167598 167434 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep771 := BSN.sin_dyadic_bound_f 20771481 1073741824 1 0 524288 167598 0 1 1 0 1 1 10141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 20771481) qz289 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 20771481) qz290 0 0 rfl) rfl rfl

noncomputable def ep772 := @Enclosure.Real.IsNear.sin_image qz170 qz448 Bool.false 64241945 262144 277 262144 Bool.false 10141 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 68979263216074957863 281474976710656000 5524250001849894549 5232312500000000000000 64241945 262144 277 262144 (ep768 rfl) rfl) (Enclosure.sfrac_false_div 64241945 262144) (BSN.sin_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 730831545213827153920) qz49) 226375608064910080 72057594037927936 Bool.false 10141 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 64241945 262144 226375608064910080 72057594037927936 39 730831545213827153920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10141 524288 730831545213827153920 37778931862957161709568 20771481 1073741824 167598 167434 (ep771 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep773 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 68705976419 274877906944 6191619868945 23011953735630848 Bool.true 1329191011 274877906944 6148585312529 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz170) 131071 524288 1 524288 524189 524288 23451753 21945909248 68705976419 274877906944 6191619868945 23011953735630848 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 524189 524288 23451753 21945909248 524189 524288 23451753 21945909248 (ep770 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 131071 524288 1 524288 10141 524288 23451753 21945909248 1329191011 274877906944 6148585312529 23011953735630848 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 10141 524288 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 10141 524288 23451753 21945909248 10141 524288 23451753 21945909248 (ep772 rfl rfl) rfl)) rfl)

noncomputable def ep774 := @ep671 68705976419 274877906944 6191619868945 23011953735630848 Bool.true 1329191011 274877906944 6148585312529 23011953735630848 Bool.false 6435303758157599211520 187291989515 274877906944 139870197897717 23011953735630848 Bool.true 1119251941558891577344 65149037491 274877906944 139851868730303 23011953735630848 (ep672 (BSN.head_sum_c_succ qz143 15 16 rfl rfl) (ep766 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep767 ep773) rfl rfl

theorem EMRow24.d12 : Enclosure.Complex.IsNear qz155 Bool.false 187291989515 274877906944 139870197897717 23011953735630848 Bool.true 65149037491 274877906944 139851868730303 23011953735630848 := ep670 (BSN.head_sum_c_succ qz143 16 17 rfl rfl) (ep774 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow24.d13 : @Eq Nat (Nat.pow 23 1) 23 := @Eq.refl Nat 23

noncomputable def ep775 := nat_lit 252442394366137549805911454671

noncomputable def ep776 := nat_lit 404630043978481643842174976000

noncomputable def ep777 := nat_lit 68084501182746389376702705674412047809

noncomputable def ep778 := nat_lit 8507592797750537220875783818646126592000

noncomputable abbrev qz562 := (@HAdd.hAdd Complex Complex Complex qz569 (@HAdd.hAdd Complex Complex Complex qz569 qz572 (@HMul.hMul Complex Complex Complex qz571 Complex.I (@HDiv.hDiv Complex Complex Complex qz573 (↑qz576) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz449 := qz562

noncomputable abbrev qz171 := (Complex.Stirling.logGammaStirling 1 qz449)

noncomputable abbrev qz563 := (@HAdd.hAdd Complex Complex Complex qz569 qz572 (@HMul.hMul Complex Complex Complex qz571 Complex.I (@HDiv.hDiv Complex Complex Complex qz573 (↑qz576) (2 : Complex))))

noncomputable abbrev qz450 := qz563

noncomputable abbrev qz172 := qz450

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz429 (2 : Real)) (Real.log Real.pi))

noncomputable def ep779 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173))) (zetaApproximant qz143 1 23))

noncomputable def ep780 := @Enclosure.Real.IsNear.of_eq ep779 (@HSub.hSub Real Real Real qz358 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.im (zetaApproximant qz143 1 23))))

noncomputable def ep781 := nat_lit 757335390727670351520063616613

noncomputable def ep782 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.im (zetaApproximant qz143 1 23))) ep781

noncomputable def ep783 := nat_lit 1213890131935444931526524928000

noncomputable def ep784 := nat_lit 22650244053651210062205093561969846671

noncomputable def ep785 := nat_lit 2835864265916845740291927939548708864000

noncomputable def ep786 := nat_lit 6069450659677224657632624640

noncomputable def ep787 := nat_lit 1454011106443034674863315092418563

noncomputable def ep788 := nat_lit 92473834758158013270388954550501376000

noncomputable def ep789 := nat_lit 4596559971048154959152106342261882525862157480190353080320

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.re (zetaApproximant qz143 1 23)) 524287 524288 11061637

noncomputable def ep791 := nat_lit 1444505377260298942220699

noncomputable def ep792 := nat_lit 2315311683531656134656000

noncomputable def ep793 := nat_lit 1486441299531868233325552507

noncomputable def ep794 := nat_lit 193830948210219656624996352000

noncomputable def ep795 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) Bool.true 524287 524288 11061637

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9470771) qz531)

noncomputable def ep796 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173) qz451 Bool.false 9470771 131072 129

noncomputable def ep797 := nat_lit 1618120718593864845783709

noncomputable def ep798 := nat_lit 3291886387200000000000000000

noncomputable def ep799 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173) Bool.false 488119823163395870753 6755399441055744000 ep797 ep798

noncomputable def ep800 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173 829876700725837500449 6755399441055744000 508183989193864845783709 ep798 1657739037 32768000

noncomputable def ep801 := nat_lit 15994710365418155892834304000

noncomputable def ep802 := nat_lit 1530519200289139097747639

noncomputable def ep803 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 156383031797185514399 2251799813685248000 ep802 ep294 Bool.false 829876700725837500449 6755399441055744000

noncomputable def ep804 := nat_lit 1497751200234274324627639

noncomputable def ep805 := @Enclosure.Complex.IsNear.subLitP qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 139319809672866583399 2251799813685248000 ep804 ep294 Bool.false 850870191577335300449 6755399441055744000 468862389190572959396509

noncomputable def ep806 := nat_lit 352143281864436555022934786757885952

noncomputable def ep807 := nat_lit 233589525009521149649803038943084544

noncomputable abbrev qz452 := (@HSub.hSub Complex Complex Complex qz546 qz562 qz549)

noncomputable abbrev qz453 := (Complex.log qz562)

noncomputable abbrev qz174 := (@HSub.hSub Complex Complex Complex qz355 (@HMul.hMul Complex Complex Complex qz354 qz452 qz453) qz449)

noncomputable abbrev qz175 := qz449

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz171 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz174 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 139319809672866583399

noncomputable def ep809 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz174 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 139320025288534807399 2251799813685248000

noncomputable def ep810 := nat_lit 2393496104919625737079846076416

noncomputable def ep811 := nat_lit 1827229822982954885127394557952000

noncomputable def ep812 := @ep809 2856731876696093303 10464625000000000000000 Bool.false 283627632267485763019 2251799813685248000 2384700003714439573 16743400000000000000000 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000 Bool.true ep810 139319809672866583399 2251799813685248000 ep804 ep294 Bool.false ep811

noncomputable def ep813 := @Enclosure.Complex.IsNear.addLitP qz174 qz68 Bool.true 141389288992140055399 2251799813685248000 22534500002582418299 83717000000000000000000

noncomputable def ep814 := nat_lit 18260954354618834275401728

noncomputable def ep815 := @ep813 Bool.false 283627632267485763019 2251799813685248000 2384700003714439573 16743400000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep814 139320025288534807399 2251799813685248000 2856731876696093303 10464625000000000000000 Bool.false 283627632267485763019 283627632267485763019 2251799813685248000

noncomputable abbrev qz176 := (@HMul.hMul Complex Complex Complex qz354 qz452 qz453)

noncomputable def ep816 := @Enclosure.Complex.IsNear.subLitP qz176 qz175 Bool.true 136322739411348247399 2251799813685248000 22534500002582418299 83717000000000000000000 Bool.false 383143673233491613131

noncomputable def ep817 := @ep816 2251799813685248000 2384700003714439573 16743400000000000000000 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 Bool.true 565557155968560221596000 141389288992140055399 2251799813685248000 22534500002582418299 83717000000000000000000 Bool.false 1134510529069943052076000 283627632267485763019 2251799813685248000 2384700003714439573 16743400000000000000000

noncomputable abbrev qz177 := qz452

noncomputable abbrev qz178 := qz453

noncomputable def ep818 := @Enclosure.Complex.IsNear.mul qz177 qz178 Bool.true 136322739411348247399 2251799813685248000 22534500002582418299 83717000000000000000000 Bool.false 383143673233491613131 2251799813685248000 2384700003714439573

noncomputable abbrev qz179 := (Complex.re qz452)

noncomputable abbrev qz180 := (Complex.re qz453)

noncomputable abbrev qz181 := (Complex.im qz452)

noncomputable abbrev qz182 := (Complex.im qz453)

noncomputable def ep819 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz179 qz180) (@HMul.hMul Real Real Real qz0 qz181 qz182) 119476813676869061 18014398509481984 350000000586019 66973600000000000000 18907167640119610003 281474976710656000

noncomputable def ep820 := nat_lit 306971519207536598107093500220669952

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ff qz179 qz180 7000 4000 0 1 17068116239552723 4503599627370496 50000000083717 16743400000000000000

noncomputable def ep822 := @Enclosure.Complex.IsNear.re_isNear qz177 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable abbrev qz454 := (Enclosure.sfrac Bool.false 176776 4000)

noncomputable abbrev qz183 := qz454

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq qz177 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz183) Bool.false 7000 4000 0 1 Bool.false 176776 4000 0

noncomputable abbrev qz455 := (Complex.log (Complex.mk qz83 qz183))

noncomputable def ep824 := @Enclosure.Complex.IsNear.of_eq qz178 qz455 Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep825 := nat_lit 635845205240609391031789047472803105248161392803457011794453470450906455375572602728609089761775607076114923520

noncomputable def ep826 := nat_lit 22115255609893088642736053231877506976201412914136884778055564371615889631045546043139032674287937586414485504

noncomputable def ep827 := nat_lit 525897041232995796544638717960618294729378022107211442356684574867799602066082088706993177617211137720320

noncomputable def ep828 := BSN.log_dyadic_bound 14946754176 47714754176 6 5 ep825 524288 167434 ep826 ep827 339893 62661508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14946754176) (BSN.artanhQ 47714754176) 0 5 ep826 ep825 ep827 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 31330754176 16000000))

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz564 1 2 0 1 17068116239552723 2251799813685248 50000000083717 8371700000000000000 17068116239552723 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 31330754176 16000000 17068116239552723 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31330754176) qz373)) Bool.false 143177736432041888579584 18889465931478580854784 1000000001674340 167434000000000000000 17068116239552723 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 31330754176 16000000 10 62661508352 32768000000 339893 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep828 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep830 := BSN.arctan_dyadic_bound_f 9000 176776 1 0 524288 167434 0 1 1 0 1 1 26669 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz456 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 176776)))

noncomputable def ep831 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz456 884279719003555 562949953421312 1 2000000000000000 26669 524288 1 167434 448603933009142874112 855644098299299 562949953421312 1000000000083717 167434000000000000000 qz86 (ep830 rfl) rfl rfl

noncomputable abbrev qz457 := (Complex.mk qz83 qz183)

noncomputable abbrev qz458 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176776) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep832 := @Enclosure.Complex.IsNear.re_isNear qz178 Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (ep824 (@congrArg Complex Complex qz175 qz457 Complex.log (BSN.w_shift_mk qz146 Bool.false 88388 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz455 Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz455) (@HMul.hMul Real Real Real qz0 qz84 qz564) Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 9000 176776 4000 31330754176 16000000 rfl rfl rfl) (ep829 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz455) qz458 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 9000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz458 (@HSub.hSub Real Real Real qz358 qz85 qz456) Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 176776 9000 rfl rfl) ep831))))

noncomputable def ep833 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz182 176776 4000 0 1 855644098299299 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep834 := @Enclosure.Complex.IsNear.im_isNear qz177 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable def ep835 := @Enclosure.Complex.IsNear.im_isNear qz178 Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (ep824 (@congrArg Complex Complex qz175 qz457 Complex.log (BSN.w_shift_mk qz146 Bool.false 88388 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz455 Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz455) (@HMul.hMul Real Real Real qz0 qz84 qz564) Bool.false 17068116239552723 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 9000 176776 4000 31330754176 16000000 rfl rfl rfl) (ep829 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz455) qz458 Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 9000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz458 (@HSub.hSub Real Real Real qz358 qz85 qz456) Bool.false 855644098299299 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 176776 9000 rfl rfl) ep831))))

noncomputable abbrev qz459 := (Enclosure.Real.IsNear.const Bool.false 176776 4000)

noncomputable abbrev qz184 := (@ep823 1 (BSN.w_sub_half_mk qz429 Bool.false 88388 1000 2 qz430 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz454 Bool.false 7000 4000 0 1 Bool.false 176776 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz459))

noncomputable def ep836 := @ep819 22097000001849894549 83717000000000000000000 ep820 136322739411348247399 2251799813685248000 22534500002582418299 83717000000000000000000 (@ep821 119476813676869061 18014398509481984 350000000586019 66973600000000000000 (ep822 qz184) ep832 rfl) (@ep833 18907167640119610003 281474976710656000 22097000001849894549 83717000000000000000000 (ep834 qz184) ep835 rfl) rfl

noncomputable def ep837 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz179 qz182) (@HMul.hMul Real Real Real qz0 qz181 qz180) 5989508688095093 2251799813685248 7000000000586019 669736000000000000000 377154164545396520131 2251799813685248000

noncomputable def ep838 := nat_lit 862762852001857955581357805417791488

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff qz179 qz182 7000 4000 0 1 855644098299299 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz180 176776 4000 0 1 17068116239552723 4503599627370496 50000000083717 16743400000000000000

noncomputable def ep841 := @ep837 1104850001849894549 8371700000000000000000 ep838 383143673233491613131 2251799813685248000 2384700003714439573 16743400000000000000000 (@ep839 5989508688095093 2251799813685248 7000000000586019 669736000000000000000 (ep822 qz184) ep835 rfl) (@ep840 377154164545396520131 2251799813685248000 1104850001849894549 8371700000000000000000 (ep834 qz184) ep832 rfl) rfl

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq qz175 qz457 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 88388 1000 2 qz147 rfl)

noncomputable abbrev qz460 := (ep842 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 176776 4000) Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 176776 4000)))

noncomputable abbrev qz185 := qz460

noncomputable def ep843 := ep817 (@ep818 16743400000000000000000 (ep836 rfl) (ep841 rfl)) qz185 rfl rfl rfl rfl rfl rfl

noncomputable def ep844 := @ep815 2384700003714439573 16743400000000000000000 (ep843 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep338 131072 1 262144 (ep340 rfl) (ep342 rfl) rfl rfl) (@ep343 1 0 1 (ep345 rfl) (ep347 rfl) rfl rfl))

noncomputable abbrev qz461 := (@HPow.hPow Complex Int Complex qz551 qz562 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz186 := qz461

noncomputable def ep845 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz186)) Bool.false 1645017 17179869184 3 17179869184

noncomputable def ep846 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz186) Bool.false 0 1 0 1 Bool.false

noncomputable def ep847 := @ep846 0 1 0 1 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000 Bool.false 1645017 1645017 17179869184 3 17179869184 Bool.true 12116646883 12116646883 6442450944000 22097

noncomputable def ep848 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz175 (@HSub.hSub Int Int Int qz367 qz73 (@HMul.hMul Int Int Int qz368 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep849 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz186 Bool.false 1645017 17179869184 3 17179869184 Bool.true 12116646883 6442450944000 22097 6442450944000

noncomputable abbrev qz187 := (Complex.re qz461)

noncomputable abbrev qz188 := (Complex.im qz461)

noncomputable def ep850 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz187) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188) 1645017 17179869184 3 17179869184 0 1 0

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz187 1 12 0 1 4935051 4294967296 9 4294967296 1645017

noncomputable def ep852 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097 536870912000

noncomputable abbrev qz462 := (@HPow.hPow Complex Nat Complex qz553 qz562 1)

noncomputable abbrev qz189 := (@Inv.inv Complex Complex.instInv qz462)

noncomputable def ep853 := @Enclosure.Complex.IsNear.of_eq qz186 qz189 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_parts qz189 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097

noncomputable abbrev qz190 := (Complex.re qz462)

noncomputable abbrev qz191 := qz462

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ff qz190 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191)) 9000 4000 0 1 548339 1073741824 1 1073741824

noncomputable def ep856 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable def ep857 := @Enclosure.Complex.IsNear.of_eq qz191 qz175 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0

noncomputable def ep858 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191)) Bool.false 548339 1073741824 1 1073741824 548339 1073741824 1

noncomputable abbrev qz192 := (Complex.im qz462)

noncomputable def ep859 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 qz190 qz190) (@HMul.hMul Real Real Real qz0 qz192 qz192)) Bool.false 244771517 125000 0 1

noncomputable def ep860 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz190 qz190) (@HMul.hMul Real Real Real qz0 qz192 qz192) 81 16 0 1 488277409 250000

noncomputable def ep861 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz190 9000 4000 0 1 9000 4000 0 1

noncomputable def ep862 := @Enclosure.Real.IsNear.mulLit_ff qz192 qz192 176776 4000 0 1 176776 4000 0 1

noncomputable def ep863 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 9000 4000 0 1 Bool.false 176776 4000 0 1

noncomputable abbrev qz193 := (ep856 (@ep857 1 (BSN.pow_one_c qz449) qz460))

noncomputable abbrev qz194 := (ep863 (@ep857 1 (BSN.pow_one_c qz449) qz460))

noncomputable def ep864 := @ep860 0 1 7832688544 244771517 125000 0 1 (@ep861 81 16 0 1 qz193 qz193 rfl) (@ep862 488277409 250000 0 1 qz194 qz194 rfl)

noncomputable def ep865 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191) 244771517 125000 0 1 274169 274170 536870912 (ep859 (Enclosure.Complex.normSq_eq_mul_add_mul qz191) (ep864 rfl rfl)) rfl

noncomputable def ep866 := @Enclosure.Real.IsNear.of_eq (Complex.re qz189) (@HMul.hMul Real Real Real qz0 qz190 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191))) Bool.false 4935051 4294967296 9 4294967296 (Enclosure.Complex.inv_re_eq_mul qz191) (@ep855 4935051 4294967296 9 4294967296 qz193 (@ep858 1073741824 (ep865 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep867 := @Enclosure.Real.IsNear.of_eq (Complex.im qz189) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz192) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191))) Bool.true 12116646883 536870912000 22097 536870912000 (Enclosure.Complex.inv_im_eq_mul qz191)

noncomputable def ep868 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz192) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz191)) 176776 4000 0 1 548339 1073741824 1

noncomputable def ep869 := @ep868 1073741824 12116646883 536870912000 22097 536870912000 (@Enclosure.Real.IsNear.neg qz192 Bool.false 176776 4000 0 1 qz194) (@ep858 1073741824 (ep865 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep870 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188 0 1 0 1 12116646883 536870912000 22097 536870912000 0

noncomputable def ep871 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 4935051 4294967296 9 4294967296 Bool.true 12116646883 536870912000 22097 536870912000

noncomputable abbrev qz195 := (@ep853 536870912000 (BSN.zpow_one_sub_two_mul qz449 1 1 rfl rfl) (@ep854 536870912000 ep866 (ep867 ep869)))

noncomputable def ep872 := @ep850 1 1645017 1645017 17179869184 3 17179869184 (@ep851 17179869184 3 17179869184 ep357 (ep852 qz195) rfl) (@ep870 1 0 1 ep377 (ep871 qz195) rfl) rfl

noncomputable def ep873 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz187) 12116646883 6442450944000 22097 6442450944000 0 1 0

noncomputable def ep874 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188 1 12 0 1 12116646883 536870912000 22097 536870912000 12116646883

noncomputable def ep875 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz187 0 1 0 1 4935051 4294967296 9 4294967296 0

noncomputable def ep876 := @ep873 1 12116646883 12116646883 6442450944000 22097 6442450944000 (@ep874 6442450944000 22097 6442450944000 ep357 (ep871 qz195) rfl) (@ep875 1 0 1 ep377 (ep852 qz195) rfl) rfl

noncomputable def ep877 := @ep847 6442450944000 (@ep848 0 1 0 1 (BSN.stirling_sum_base qz175) qz105) (ep849 (ep872 rfl) (ep876 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep878 := @ep812 850870191577335300449 6755399441055744000 468862389190572959396509 ep798 (ep844 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep845 Bool.true 12116646883 6442450944000 22097 6442450944000 (BSN.stirling_sum_succ qz175 0 1 rfl) (ep877 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 17063222124318931 2251799813685248 50000000083717 8371700000000000000 Bool.false 874728785479075 281474976710656

noncomputable abbrev qz196 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz450 qz378))

noncomputable def ep880 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 1) qz196) Bool.false 17063222124318931 2251799813685248 50000000083717 8371700000000000000 Bool.false 874728785479075 281474976710656 1000000000083717 83717000000000000000

noncomputable def ep881 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz196 Bool.false 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000 Bool.false

noncomputable def ep882 := nat_lit 153691841601645481649620807319552

noncomputable def ep883 := nat_lit 984857058083452175602470092800

noncomputable abbrev qz197 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz450 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 0) qz197) Bool.false 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep885 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz197 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz463 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz183))

noncomputable def ep886 := @Enclosure.Complex.IsNear.of_eq qz197 qz463 Bool.false 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep887 := nat_lit 625264507433737490040657385264243568138969179850704061998891533219893257442710145431721518388871585060114923520

noncomputable def ep888 := nat_lit 21577235711168552308956860924081194505997158173926035732955734712123165763921609486751860953946764543214485504

noncomputable def ep889 := nat_lit 498417648795060858570602414083608490111150741205530636785287824546941289758163696373335731069755137720320

noncomputable def ep890 := BSN.log_dyadic_bound 14866754176 47634754176 6 5 ep887 524288 167434 ep888 ep889 338552 62501508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14866754176) (BSN.artanhQ 47634754176) 0 5 ep888 ep887 ep889 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep891 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 31250754176 16000000)) 1 2 0 1 17062356688408787 2251799813685248 50000000083717 8371700000000000000 17062356688408787 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 31250754176 16000000 17062356688408787 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31250754176) qz373)) Bool.false 143129421815239457898496 18889465931478580854784 1000000001674340 167434000000000000000 17062356688408787 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 31250754176 16000000 10 62501508352 32768000000 338552 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep890 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep892 := BSN.arctan_dyadic_bound_f 1000 176776 1 0 524288 167434 0 1 1 0 1 1 2965 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz464 := (@Nat.cast Real Real.instNatCast 176776)

noncomputable def ep893 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz464)) 884279719003555 562949953421312 1 2000000000000000 2965 524288 1 167434 461948098705041653760 881096074495395 562949953421312 1000000000083717 167434000000000000000 qz86 (ep892 rfl) rfl rfl

noncomputable abbrev qz198 := (@HAdd.hAdd Complex Complex Complex qz274 qz450 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz465 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz183)

noncomputable def ep894 := @ep885 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000 Bool.false 17062356688408787 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 881096074495395 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz105) (ep886 (@congrArg Complex Complex qz198 qz465 Complex.log (BSN.w_shift_mk qz146 Bool.false 88388 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz463 Bool.false 17062356688408787 4503599627370496 50000000083717 16743400000000000000 Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz463) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 31250754176 16000000))) Bool.false 17062356688408787 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 1000 176776 4000 31250754176 16000000 rfl rfl rfl) (ep891 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz463) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz464 qz384)) Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 1000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz464 qz384)) (@HSub.hSub Real Real Real qz358 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz384 qz464))) Bool.false 881096074495395 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 176776 1000 rfl rfl) ep893)))) rfl rfl

noncomputable abbrev qz466 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz183))

noncomputable def ep895 := @Enclosure.Complex.IsNear.of_eq qz196 qz466 Bool.false 17064087560229075 4503599627370496 50000000083717 16743400000000000000 Bool.false 868361496462755 562949953421312 1000000000083717 167434000000000000000

noncomputable def ep896 := nat_lit 628421953581308850485736092016143264236326173514042338478367504708031072299979416285804685462413191664914923520

noncomputable def ep897 := nat_lit 21737434578772462517084389606263932533425438614863911166506865068280002144453159292445884872399196456174485504

noncomputable def ep898 := nat_lit 506522509527336647338435361925863633575655418247527324852622971023090966745247311531438571433991937720320

noncomputable def ep899 := BSN.log_dyadic_bound 14890754176 47658754176 6 5 ep896 524288 167434 ep897 ep898 338955 62549508352 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14890754176) (BSN.artanhQ 47658754176) 0 5 ep897 ep896 ep898 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 31274754176 16000000)) 1 2 0 1 17064087560229075 2251799813685248 50000000083717 8371700000000000000 17064087560229075 4503599627370496 50000000083717 16743400000000000000 qz372 (BSN.isNear_log_sfrac 31274754176 16000000 17064087560229075 2251799813685248 50000000083717 8371700000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31274754176) qz373)) Bool.false 143143941420438100377600 18889465931478580854784 1000000001674340 167434000000000000000 17064087560229075 2251799813685248 50000000083717 8371700000000000000 (BSN.log_rat_reduce_isNear 31274754176 16000000 10 62549508352 32768000000 338955 524288 24973259072661432 36028797018963968 167434 1000000000000000 rfl rfl rfl rfl (ep899 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep901 := BSN.arctan_dyadic_bound_f 5000 176776 1 0 524288 167434 0 1 1 0 1 1 14825 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 176776) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 176776) 0 0 rfl) rfl rfl rfl

noncomputable def ep902 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz464)) 884279719003555 562949953421312 1 2000000000000000 14825 524288 1 167434 455271512257464893440 868361496462755 562949953421312 1000000000083717 167434000000000000000 qz86 (ep901 rfl) rfl rfl

noncomputable abbrev qz199 := (@HAdd.hAdd Complex Complex Complex qz274 qz450 qz378)

noncomputable abbrev qz467 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz183)

noncomputable def ep903 := @ep881 17064087560229075 4503599627370496 50000000083717 16743400000000000000 Bool.false 868361496462755 562949953421312 1000000000083717 167434000000000000000 Bool.false ep882 17063222124318931 2251799813685248 50000000083717 8371700000000000000 Bool.false ep883 874728785479075 281474976710656 1000000000083717 83717000000000000000 (ep884 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep894 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep895 (@congrArg Complex Complex qz199 qz467 Complex.log (BSN.w_shift_mk qz146 Bool.false 88388 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz466 Bool.false 17064087560229075 4503599627370496 50000000083717 16743400000000000000 Bool.false 868361496462755 562949953421312 1000000000083717 167434000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz466) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 31274754176 16000000))) Bool.false 17064087560229075 4503599627370496 50000000083717 16743400000000000000 (Enclosure.clog_re_eq 5000 176776 4000 31274754176 16000000 rfl rfl rfl) (ep900 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz466) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz464 qz388)) Bool.false 868361496462755 562949953421312 1000000000083717 167434000000000000000 (Enclosure.clog_im_eq 5000 176776 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz464 qz388)) (@HSub.hSub Real Real Real qz358 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz464))) Bool.false 868361496462755 562949953421312 1000000000083717 167434000000000000000 (BSN.arctan_recip 176776 5000 rfl rfl) ep902)))) rfl rfl

noncomputable def ep904 := @ep805 ep798 Bool.false 17063222124318931 2251799813685248 50000000083717 8371700000000000000 Bool.false 874728785479075 281474976710656 1000000000083717 83717000000000000000 Bool.true ep806 156383031797185514399 2251799813685248000 ep802 ep294 Bool.false ep807 829876700725837500449 6755399441055744000 508183989193864845783709 ep798 (@ep808 2251799813685248000 ep804 ep294 Bool.false 850870191577335300449 6755399441055744000 468862389190572959396509 ep798 (BSN.logGammaStirling_unfold 1 qz175) (ep878 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep879 1000000000083717 83717000000000000000 (BSN.log_sum_c_eq qz146 2) (ep880 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep903 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz200 := (@HDiv.hDiv Real Real Real qz271 qz429 (2 : Real))

noncomputable def ep905 := @Enclosure.Real.IsNear.mulLit_ff qz200 (Real.log Real.pi) 88388 2000 0 1 75021 65536 1 131072 1657739037 32768000 22097 65536000 (@Enclosure.Real.IsNear.of_eq qz200 (Enclosure.sfrac Bool.false 88388 2000) Bool.false 88388 2000 0 1 (BSN.t_half_eq qz146 Bool.false 88388 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 88388 2000)) EMRow24.d5 rfl

noncomputable def ep906 := @ep800 22097 65536000 ep801 488119823163395870753 6755399441055744000 ep797 ep798 (@ep803 508183989193864845783709 ep798 (ep904 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep905 rfl rfl

noncomputable def ep907 := nat_lit 32561899959495086425130797810549157745980795822231971188894044223523489054720

noncomputable def ep908 := nat_lit 65359950249731834054229282200537387833715038066547963599010892417404502016

noncomputable def ep909 := nat_lit 85175345688749470048778575427875495468695117091833132601276479140552387854336

noncomputable def ep910 := BSN.sin_dyadic_bound_f 1686218944 1073741824 3 2 524288 167598 ep907 ep57 ep908 ep909 ep60 ep908 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686218944) qz289 0 2 ep907 ep57 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686218944) qz290 0 2 ep909 ep60 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable def ep911 := @ep796 262144 Bool.true 524287 524288 1 83717 (@ep799 9470771 131072 129 262144 ep906 rfl) (Enclosure.sfrac_false_div 9470771 131072) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664277375586362458112) qz293) 226375608064910080 72057594037927936 Bool.false 524287 524288 11 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 9470771 131072 226375608064910080 72057594037927936 11 29664277375586362458112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 29664277375586362458112 18889465931478580854784 1686218944 1073741824 167598 167434 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := nat_lit 1486170696467885580136271683

noncomputable abbrev qz468 := (@HPow.hPow Complex Complex Complex qz526 (@Nat.cast Complex Complex.instNatCast 23) qz560)

noncomputable abbrev qz201 := qz468

noncomputable abbrev qz469 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz363 qz469 (@HSub.hSub Complex Complex Complex qz355 qz422 (1 : Complex))) qz362)

noncomputable abbrev qz203 := qz469

noncomputable def ep913 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz143 1 23) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz62 qz201 (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep791 ep792 ep793

noncomputable def ep914 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (@HMul.hMul Complex Complex Complex qz62 qz201 (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 147027886727 274877906944 173580823737453 23011953735630848

noncomputable def ep915 := nat_lit 24360502626460735484118007

noncomputable def ep916 := nat_lit 24336224977435802320438183

noncomputable def ep917 := nat_lit 397062614670664066305362932432633856

noncomputable def ep918 := nat_lit 11280479756647451396667309159350272

noncomputable def ep919 := @ep914 Bool.false 10477849767 274877906944 173551579547579 23011953735630848 Bool.false 206081424864067437085199 ep792 ep915 ep794 Bool.true 129293649444560259741763 ep792 ep916 ep794 Bool.false ep917 ep791 ep792 ep793 ep794 Bool.true ep918 41038146288510511646263 ep792

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 23, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz144) (BSN.headSumC qz143 23) Bool.false 147027886727 274877906944 173580823737453 23011953735630848 Bool.false 10477849767 274877906944 173551579547579

noncomputable abbrev qz204 := (@HPow.hPow Complex Complex Complex qz275 qz391 qz423)

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 22) qz204) Bool.false 147027886727 274877906944 173580823737453 23011953735630848 Bool.false 10477849767 274877906944 173551579547579 23011953735630848

noncomputable def ep922 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 22) qz204 Bool.false 51323088785 68719476736 84142477357707 11505976867815424 Bool.false 16780173345 274877906944 168294627628745 23011953735630848 Bool.true

noncomputable abbrev qz205 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 21) qz423)

noncomputable def ep923 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 21) qz205) Bool.false 51323088785 68719476736 84142477357707 11505976867815424 Bool.false 16780173345 274877906944 168294627628745 23011953735630848

noncomputable def ep924 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 21) qz205 Bool.false 88457058981 137438953472 10181122453865 1438247108476928 Bool.true 9016364541 68719476736 40722432135317 5752988433907712 Bool.false

noncomputable abbrev qz206 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 20) qz423)

noncomputable def ep925 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 20) qz206) Bool.false 88457058981 137438953472 10181122453865 1438247108476928 Bool.true 9016364541 68719476736 40722432135317 5752988433907712

noncomputable def ep926 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 20) qz206 Bool.false 138358926277 274877906944 157371647738917 23011953735630848 Bool.false 5901616813 137438953472 78678383144357 11505976867815424 Bool.false

noncomputable abbrev qz207 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 19) qz423)

noncomputable def ep927 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 19) qz207) Bool.false 138358926277 274877906944 157371647738917 23011953735630848 Bool.false 5901616813 137438953472 78678383144357 11505976867815424

noncomputable def ep928 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 19) qz207 Bool.false 193721425513 274877906944 151691560441609 23011953735630848 Bool.false 10499217749 68719476736 37923549277131 5752988433907712 Bool.true

noncomputable abbrev qz470 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz144)

noncomputable def ep929 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz143 18) qz470) Bool.false 193721425513 274877906944 151691560441609 23011953735630848 Bool.false 10499217749 68719476736 37923549277131 5752988433907712

noncomputable def ep930 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz143 18) qz470 Bool.false 57111654597 68719476736 4558173202393 719123554238464 Bool.true 12700019079 274877906944 145850649136819 23011953735630848 Bool.true

noncomputable abbrev qz471 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz144)

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz143 18) (@HAdd.hAdd Complex Complex Complex qz4 qz155 qz471) Bool.false 57111654597 68719476736 4558173202393 719123554238464 Bool.true 12700019079 274877906944 145850649136819 23011953735630848

noncomputable def ep932 := @Enclosure.Complex.IsNear.addLitP qz155 qz471 Bool.false 187291989515 274877906944 139870197897717 23011953735630848 Bool.true 65149037491 274877906944 139851868730303 23011953735630848 Bool.false

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz268 qz429 qz554)

noncomputable def ep933 := @Enclosure.Complex.IsNear.of_eq qz471 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 41154628873 274877906944 5991344578859 23011953735630848 Bool.false 13112254603 68719476736 1499695101629 5752988433907712 (BSN.cpow_neg_s_mk qz146 88388 1000 17 qz147 rfl)

noncomputable def ep934 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz554 88388 1000 0 1 3189913004350711 1125899906842624 250000000083717 20929250000000000000 70487507657137660967 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz394) Bool.false 26758929747600409100288 9444732965739290427392 1000000000334868 83717000000000000000 3189913004350711 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep445 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep935 := nat_lit 260442603689736077924723021358055696

noncomputable def ep936 := BSN.sin_dyadic_bound_f 714377894 1073741824 2 1 524288 167598 ep935 ep79 ep935 ep935 ep80 ep935 323647 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 714377894) qz289 0 1 ep935 ep79 ep935 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 714377894) qz290 0 1 ep935 ep80 ep935 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65646607) qz48)

noncomputable def ep937 := @Enclosure.Real.IsNear.cos_image qz208 qz472 Bool.false 65646607 262144 277 262144 Bool.false 323647 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 70487507657137660967 281474976710656000 5524250001849894549 5232312500000000000000 65646607 262144 277 262144 (ep934 rfl) rfl) (Enclosure.sfrac_false_div 65646607 262144) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25134937656518323994624) qz49) 226375608064910080 72057594037927936 Bool.false 323647 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 65646607 262144 226375608064910080 72057594037927936 39 25134937656518323994624 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 323647 524288 25134937656518323994624 37778931862957161709568 714377894 1073741824 167598 167434 (ep936 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep938 := BSN.cos_dyadic_bound_f 714377894 1073741824 2 1 524288 167598 ep935 ep75 ep935 ep935 ep76 ep935 412468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 714377894) qz294 0 1 ep935 ep75 ep935 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 714377894) qz295 0 1 ep935 ep76 ep935 rfl rfl rfl rfl) rfl rfl

noncomputable def ep939 := @Enclosure.Real.IsNear.sin_image qz208 qz472 Bool.false 65646607 262144 277 262144 Bool.true 412468 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 70487507657137660967 281474976710656000 5524250001849894549 5232312500000000000000 65646607 262144 277 262144 (ep934 rfl) rfl) (Enclosure.sfrac_false_div 65646607 262144) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25134937656518323994624) qz49) 226375608064910080 72057594037927936 Bool.false 412468 524288 39 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 65646607 262144 226375608064910080 72057594037927936 39 25134937656518323994624 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 412468 524288 25134937656518323994624 37778931862957161709568 714377894 1073741824 167598 167434 (ep938 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep940 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 41154628873 274877906944 5991344578859 23011953735630848 Bool.false 13112254603 68719476736 1499695101629 5752988433907712 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz208) 127159 524288 1 524288 323647 524288 23451753 21945909248 41154628873 274877906944 5991344578859 23011953735630848 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 323647 524288 23451753 21945909248 323647 524288 23451753 21945909248 (ep937 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz121 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 127159 524288 1 524288 103117 131072 23451753 21945909248 13112254603 68719476736 1499695101629 5752988433907712 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.true 103117 131072 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.true 412468 524288 23451753 21945909248 103117 131072 23451753 21945909248 (ep939 rfl rfl) rfl)) rfl)

noncomputable def ep941 := @ep932 41154628873 274877906944 5991344578859 23011953735630848 Bool.false 13112254603 68719476736 1499695101629 5752988433907712 Bool.false 62794928310928143286272 57111654597 68719476736 4558173202393 719123554238464 Bool.true 872738665646096646144 12700019079 274877906944 145850649136819 23011953735630848 EMRow24.d12 (ep933 ep940) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz268 qz429 qz555)

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_eq qz470 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.true 34725192875 274877906944 5830017965033 23011953735630848 Bool.false 54696890075 274877906944 5843547971705 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 18 qz147 rfl)

noncomputable def ep943 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz555 88388 1000 0 1 3254268794313975 1125899906842624 250000000083717 20929250000000000000 2876383101918236223 11258999068426240 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz398) Bool.false 27298785242132565196800 9444732965739290427392 1000000000334868 83717000000000000000 3254268794313975 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep944 := nat_lit 3031563688036610826136341820419318221250057683149922385166402057986149605921

noncomputable def ep945 := nat_lit 1840722475019044501588197797310523052779598305201061916438306898842116641

noncomputable def ep946 := nat_lit 9091009619159794389405849065663333617644613852839365031666329560160764584481

noncomputable def ep947 := BSN.cos_dyadic_bound_f 1079253683 1073741824 3 2 524288 167598 ep944 ep64 ep945 ep946 ep66 ep945 281005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1079253683) qz294 0 2 ep944 ep64 ep945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1079253683) qz295 0 2 ep946 ep66 ep945 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133942025) qz24)

noncomputable def ep948 := @Enclosure.Real.IsNear.cos_image qz209 qz473 Bool.false 133942025 524288 555 524288 Bool.true 281005 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 2876383101918236223 11258999068426240 5524250001849894549 5232312500000000000000 133942025 524288 555 524288 (ep943 rfl) rfl) (Enclosure.sfrac_false_div 133942025 524288) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75945726352025788088320) qz26) 226375608064910080 72057594037927936 Bool.false 281005 524288 40 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 133942025 524288 226375608064910080 72057594037927936 40 75945726352025788088320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 281005 524288 75945726352025788088320 75557863725914323419136 1079253683 1073741824 167598 167434 (ep947 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep949 := nat_lit 5455342060485884251444144718516924379807880151025699443766373058855995597345

noncomputable def ep950 := nat_lit 14284820417265380300779712418729632528839947712573173014380553133453291708961

noncomputable def ep951 := BSN.sin_dyadic_bound_f 1079253683 1073741824 3 2 524288 167598 ep949 ep57 ep945 ep950 ep60 ep945 442621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1079253683) qz289 0 2 ep949 ep57 ep945 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1079253683) qz290 0 2 ep950 ep60 ep945 rfl rfl rfl rfl) rfl rfl

noncomputable def ep952 := @Enclosure.Real.IsNear.sin_image qz209 qz473 Bool.false 133942025 524288 555 524288 Bool.true 442621 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 2876383101918236223 11258999068426240 5524250001849894549 5232312500000000000000 133942025 524288 555 524288 (ep943 rfl) rfl) (Enclosure.sfrac_false_div 133942025 524288) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75945726352025788088320) qz26) 226375608064910080 72057594037927936 Bool.false 442621 524288 40 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q2 133942025 524288 226375608064910080 72057594037927936 40 75945726352025788088320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 442621 524288 75945726352025788088320 75557863725914323419136 1079253683 1073741824 167598 167434 (ep951 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep953 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.true 34725192875 274877906944 5830017965033 23011953735630848 Bool.false 54696890075 274877906944 5843547971705 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ft qz123 (Real.cos qz209) 123575 524288 1 524288 281005 524288 46987223 43891818496 34725192875 274877906944 5830017965033 23011953735630848 qz400 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.true 281005 524288 46987223 43891818496 281005 524288 46987223 43891818496 (ep948 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 123575 524288 1 524288 442621 524288 46987223 43891818496 54696890075 274877906944 5843547971705 23011953735630848 qz400 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.true 442621 524288 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.true 442621 524288 46987223 43891818496 442621 524288 46987223 43891818496 (ep952 rfl rfl) rfl)) rfl)

noncomputable def ep954 := @ep930 34725192875 274877906944 5830017965033 23011953735630848 Bool.false 54696890075 274877906944 5843547971705 23011953735630848 Bool.false 13312434993805360365568 193721425513 274877906944 151691560441609 23011953735630848 Bool.false 11544011997577660596224 10499217749 68719476736 37923549277131 5752988433907712 (ep931 (BSN.head_sum_c_succ qz143 17 18 rfl rfl) (ep941 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep942 ep953) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz268 qz429 qz556)

noncomputable def ep955 := @Enclosure.Complex.IsNear.of_eq qz207 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.true 13840624809 68719476736 1420021824327 5752988433907712 Bool.true 15096818685 137438953472 2831284590095 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 19 qz147 rfl)

noncomputable def ep956 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz556 88388 1000 0 1 3315141365800183 1125899906842624 250000000083717 20929250000000000000 73254678760086643751 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz402) Bool.false 27809421382282341515264 9444732965739290427392 1000000000334868 83717000000000000000 3315141365800183 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep467 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep957 := nat_lit 7046074460870067820137503429782288668640981604608620982435840000000000000000

noncomputable def ep958 := nat_lit 3070106073733959121869040404600525429145600000000000000000000000000000000

noncomputable def ep959 := nat_lit 18449033892445084547496149584012831376698239897784483525427200000000000000000

noncomputable def ep960 := BSN.sin_dyadic_bound_f 1150520000 1073741824 3 2 524288 167598 ep957 ep57 ep958 ep959 ep60 ep958 460284 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1150520000) qz289 0 2 ep957 ep57 ep958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1150520000) qz290 0 2 ep959 ep60 ep958 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8527967) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep961 := @Enclosure.Real.IsNear.cos_image qz210 qz474 Bool.false 8527967 32768 277 262144 Bool.true 460284 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 73254678760086643751 281474976710656000 5524250001849894549 5232312500000000000000 8527967 32768 277 262144 (ep956 rfl) rfl) (Enclosure.sfrac_false_div 8527967 32768) (BSN.cos_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5060040472981745434624) qz445) 226375608064910080 72057594037927936 Bool.false 460284 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 8527967 32768 226375608064910080 72057594037927936 41 5060040472981745434624 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 460284 524288 5060040472981745434624 4722366482869645213696 1150520000 1073741824 167598 167434 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := nat_lit 3915850303182808326352777034503316160546832269227011656908800000000000000000

noncomputable def ep963 := nat_lit 11741410697400957060814593022700747430782205607681034970726400000000000000000

noncomputable def ep964 := BSN.cos_dyadic_bound_f 1150520000 1073741824 3 2 524288 167598 ep962 ep64 ep958 ep963 ep66 ep958 251030 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1150520000) qz294 0 2 ep962 ep64 ep958 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1150520000) qz295 0 2 ep963 ep66 ep958 rfl rfl rfl rfl) rfl rfl

noncomputable def ep965 := @Enclosure.Real.IsNear.sin_image qz210 qz474 Bool.false 8527967 32768 277 262144 Bool.false 251030 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 73254678760086643751 281474976710656000 5524250001849894549 5232312500000000000000 8527967 32768 277 262144 (ep956 rfl) rfl) (Enclosure.sfrac_false_div 8527967 32768) (BSN.sin_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5060040472981745434624) qz445) 226375608064910080 72057594037927936 Bool.false 251030 524288 41 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 8527967 32768 226375608064910080 72057594037927936 41 5060040472981745434624 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 251030 524288 5060040472981745434624 4722366482869645213696 1150520000 1073741824 167598 167434 (ep964 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep966 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.true 13840624809 68719476736 1420021824327 5752988433907712 Bool.true 15096818685 137438953472 2831284590095 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz125 (Real.cos qz210) 120279 524288 1 524288 115071 131072 23451753 21945909248 13840624809 68719476736 1420021824327 5752988433907712 qz404 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.true 460284 524288 23451753 21945909248 115071 131072 23451753 21945909248 (ep961 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 120279 524288 1 524288 125515 262144 23451753 21945909248 15096818685 137438953472 2831284590095 11505976867815424 qz404 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 125515 262144 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 251030 524288 23451753 21945909248 125515 262144 23451753 21945909248 (ep965 rfl rfl) rfl)) rfl)

noncomputable def ep967 := @ep928 13840624809 68719476736 1420021824327 5752988433907712 Bool.true 15096818685 137438953472 2831284590095 11505976867815424 Bool.false 9507953015510240591872 138358926277 274877906944 157371647738917 23011953735630848 Bool.false 405556019285739962368 5901616813 137438953472 78678383144357 11505976867815424 (ep929 (BSN.head_sum_c_succ qz143 18 19 rfl rfl) (ep954 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep955 ep966) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz429 qz557)

noncomputable def ep968 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 38555191685 274877906944 5526311522923 23011953735630848 Bool.true 23934345895 137438953472 2766481126277 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 20 qz147 rfl)

noncomputable def ep969 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz557 88388 1000 0 1 3372891496062199 1125899906842624 250000000083717 20929250000000000000 74530783388486411303 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz406) Bool.false 28293864586999331028992 9444732965739290427392 1000000000334868 83717000000000000000 3372891496062199 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep478 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep970 := nat_lit 1886221703072157623816998993816022594696856708287538174409165116590755675681

noncomputable def ep971 := nat_lit 712918028864824825352160571602640526255235526284200273062934764891668001

noncomputable def ep972 := nat_lit 5657239273158743221800292660304862503038059653810046122681369480242483691041

noncomputable def ep973 := BSN.cos_dyadic_bound_f 958583501 1073741824 3 2 524288 167598 ep970 ep64 ep971 ep972 ep66 ep971 328871 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 958583501) qz294 0 2 ep970 ep64 ep971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 958583501) qz295 0 2 ep972 ep66 ep971 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69412201) qz48)

noncomputable def ep974 := @Enclosure.Real.IsNear.cos_image qz211 qz475 Bool.false 69412201 262144 277 262144 Bool.false 328871 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 74530783388486411303 281474976710656000 5524250001849894549 5232312500000000000000 69412201 262144 277 262144 (ep969 rfl) rfl) (Enclosure.sfrac_false_div 69412201 262144) (BSN.cos_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33727158578722648358912) qz49) 226375608064910080 72057594037927936 Bool.false 328871 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 69412201 262144 226375608064910080 72057594037927936 42 33727158578722648358912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 328871 524288 33727158578722648358912 37778931862957161709568 958583501 1073741824 167598 167434 (ep973 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep975 := nat_lit 844344733426356385034962256667834001

noncomputable def ep976 := BSN.sin_dyadic_bound_f 958583501 1073741824 2 1 524288 167598 ep975 ep79 ep975 ep975 ep80 ep975 408314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 958583501) qz289 0 1 ep975 ep79 ep975 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 958583501) qz290 0 1 ep975 ep80 ep975 rfl rfl rfl rfl) rfl rfl

noncomputable def ep977 := @Enclosure.Real.IsNear.sin_image qz211 qz475 Bool.false 69412201 262144 277 262144 Bool.false 408314 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 74530783388486411303 281474976710656000 5524250001849894549 5232312500000000000000 69412201 262144 277 262144 (ep969 rfl) rfl) (Enclosure.sfrac_false_div 69412201 262144) (BSN.sin_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33727158578722648358912) qz49) 226375608064910080 72057594037927936 Bool.false 408314 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 69412201 262144 226375608064910080 72057594037927936 42 33727158578722648358912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 408314 524288 33727158578722648358912 37778931862957161709568 958583501 1073741824 167598 167434 (ep976 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep978 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 38555191685 274877906944 5526311522923 23011953735630848 Bool.true 23934345895 137438953472 2766481126277 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz211) 117235 524288 1 524288 328871 524288 23451753 21945909248 38555191685 274877906944 5526311522923 23011953735630848 qz408 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 328871 524288 23451753 21945909248 328871 524288 23451753 21945909248 (ep974 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 117235 524288 1 524288 204157 262144 23451753 21945909248 23934345895 137438953472 2766481126277 11505976867815424 qz408 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 204157 262144 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 408314 524288 23451753 21945909248 204157 262144 23451753 21945909248 (ep977 rfl rfl) rfl)) rfl)

noncomputable def ep979 := @ep926 38555191685 274877906944 5526311522923 23011953735630848 Bool.true 23934345895 137438953472 2766481126277 11505976867815424 Bool.false 48629782454238474928128 88457058981 137438953472 10181122453865 1438247108476928 Bool.true 2478399413274179272704 9016364541 68719476736 40722432135317 5752988433907712 (ep927 (BSN.head_sum_c_succ qz143 19 20 rfl rfl) (ep967 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep968 ep978) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz429 qz558)

noncomputable def ep980 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 14189118589 137438953472 2693497726787 11505976867815424 Bool.false 52845631509 274877906944 5404899087477 23011953735630848 (BSN.cpow_neg_s_mk qz146 88388 1000 21 qz147 rfl)

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz558 88388 1000 0 1 3427824127778039 1125899906842624 250000000083717 20929250000000000000 75744629751511327783 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 21 1 3427824127778039 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 28754672900871880179712 9444732965739290427392 1000000000334868 83717000000000000000 3427824127778039 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 71285 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep488 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep982 := nat_lit 78400248193744134849805388774865121

noncomputable def ep983 := BSN.sin_dyadic_bound_f 529150681 1073741824 2 1 524288 167598 ep982 ep79 ep982 ep982 ep80 ep982 248042 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 529150681) qz289 0 1 ep982 ep79 ep982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 529150681) qz290 0 1 ep982 ep80 ep982 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141085367) qz24)

noncomputable def ep984 := @Enclosure.Real.IsNear.cos_image qz212 qz476 Bool.false 141085367 524288 277 262144 Bool.false 248042 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 75744629751511327783 281474976710656000 5524250001849894549 5232312500000000000000 141085367 524288 277 262144 (ep981 rfl) rfl) (Enclosure.sfrac_false_div 141085367 524288) (BSN.cos_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37235668961966040285184) qz26) 226375608064910080 72057594037927936 Bool.false 248042 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 141085367 524288 226375608064910080 72057594037927936 42 37235668961966040285184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 248042 524288 37235668961966040285184 75557863725914323419136 529150681 1073741824 167598 167434 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := BSN.cos_dyadic_bound_f 529150681 1073741824 2 1 524288 167598 ep982 ep75 ep982 ep982 ep76 ep982 461901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 529150681) qz294 0 1 ep982 ep75 ep982 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 529150681) qz295 0 1 ep982 ep76 ep982 rfl rfl rfl rfl) rfl rfl

noncomputable def ep986 := @Enclosure.Real.IsNear.sin_image qz212 qz476 Bool.false 141085367 524288 277 262144 Bool.true 461901 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 75744629751511327783 281474976710656000 5524250001849894549 5232312500000000000000 141085367 524288 277 262144 (ep981 rfl) rfl) (Enclosure.sfrac_false_div 141085367 524288) (BSN.sin_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37235668961966040285184) qz26) 226375608064910080 72057594037927936 Bool.false 461901 524288 42 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q3 141085367 524288 226375608064910080 72057594037927936 42 37235668961966040285184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 461901 524288 37235668961966040285184 75557863725914323419136 529150681 1073741824 167598 167434 (ep985 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep987 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 14189118589 137438953472 2693497726787 11505976867815424 Bool.false 52845631509 274877906944 5404899087477 23011953735630848 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz212) 114409 524288 1 524288 124021 262144 23451753 21945909248 14189118589 137438953472 2693497726787 11505976867815424 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 248042 524288 23451753 21945909248 124021 262144 23451753 21945909248 (ep984 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 114409 524288 1 524288 461901 524288 23451753 21945909248 52845631509 274877906944 5404899087477 23011953735630848 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 461901 524288 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 461901 524288 23451753 21945909248 461901 524288 23451753 21945909248 (ep986 rfl rfl) rfl)) rfl)

noncomputable def ep988 := @ep924 14189118589 137438953472 2693497726787 11505976867815424 Bool.false 52845631509 274877906944 5404899087477 23011953735630848 Bool.false 14107583223121880023040 51323088785 68719476736 84142477357707 11505976867815424 Bool.false 1153124731807774801920 16780173345 274877906944 168294627628745 23011953735630848 (ep925 (BSN.head_sum_c_succ qz143 20 21 rfl rfl) (ep979 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep980 ep987) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz429 qz417)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq qz204 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 58264468413 274877906944 5295869022039 23011953735630848 Bool.true 3151161789 137438953472 2628475959417 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 22 qz147 rfl)

noncomputable def ep990 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz136 88388 1000 0 1 3480201253952759 1125899906842624 250000000083717 20929250000000000000 76902007108594115623 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 22 1 3480201253952759 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 29194044080518145769472 9444732965739290427392 1000000000334868 83717000000000000000 3480201253952759 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 83480 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep991 := nat_lit 24517233793602514712205713316709267663904552699232649586709200811455402681665

noncomputable def ep992 := nat_lit 37090729069764372334845404805795787827449360989030398770470960378365814081

noncomputable def ep993 := nat_lit 64151751136179348595806166126457745939457958104008033033848096760818224276801

noncomputable def ep994 := BSN.sin_dyadic_bound_f 1570934839 1073741824 3 2 524288 167598 ep991 ep57 ep992 ep993 ep60 ep992 521247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1570934839) qz289 0 2 ep991 ep57 ep992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1570934839) qz290 0 2 ep993 ep60 ep992 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71620575) qz48)

noncomputable def ep995 := @Enclosure.Real.IsNear.cos_image qz213 qz477 Bool.false 71620575 262144 555 524288 Bool.true 521247 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 76902007108594115623 281474976710656000 5524250001849894549 5232312500000000000000 71620575 262144 555 524288 (ep990 rfl) rfl) (Enclosure.sfrac_false_div 71620575 262144) (BSN.cos_reduce1 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55272355927713843773440) qz49) 226375608064910080 72057594037927936 Bool.false 521247 524288 43 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 71620575 262144 226375608064910080 72057594037927936 43 55272355927713843773440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521247 524288 55272355927713843773440 37778931862957161709568 1570934839 1073741824 167598 167434 (ep994 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep996 := nat_lit 13637170209365736783374216466974391274536951215568818836514209766532275184961

noncomputable def ep997 := nat_lit 40837329169957681605452958591311582247955954924728395712001687378840093926721

noncomputable def ep998 := BSN.cos_dyadic_bound_f 1570934839 1073741824 3 2 524288 167598 ep996 ep64 ep992 ep997 ep66 ep992 56382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1570934839) qz294 0 2 ep996 ep64 ep992 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1570934839) qz295 0 2 ep997 ep66 ep992 rfl rfl rfl rfl) rfl rfl

noncomputable def ep999 := @Enclosure.Real.IsNear.sin_image qz213 qz477 Bool.false 71620575 262144 555 524288 Bool.false 56382 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 76902007108594115623 281474976710656000 5524250001849894549 5232312500000000000000 71620575 262144 555 524288 (ep990 rfl) rfl) (Enclosure.sfrac_false_div 71620575 262144) (BSN.sin_reduce1 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55272355927713843773440) qz49) 226375608064910080 72057594037927936 Bool.false 56382 524288 43 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 71620575 262144 226375608064910080 72057594037927936 43 55272355927713843773440 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56382 524288 55272355927713843773440 37778931862957161709568 1570934839 1073741824 167598 167434 (ep998 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1000 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 58264468413 274877906944 5295869022039 23011953735630848 Bool.true 3151161789 137438953472 2628475959417 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ft qz133 (Real.cos qz213) 111779 524288 1 524288 521247 524288 46987223 43891818496 58264468413 274877906944 5295869022039 23011953735630848 qz420 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 521247 524288 46987223 43891818496 521247 524288 46987223 43891818496 (ep995 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 111779 524288 1 524288 28191 262144 46987223 43891818496 3151161789 137438953472 2628475959417 11505976867815424 qz420 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 28191 262144 46987223 43891818496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 56382 524288 46987223 43891818496 28191 262144 46987223 43891818496 (ep999 rfl rfl) rfl)) rfl)

noncomputable def ep1001 := @ep922 58264468413 274877906944 5295869022039 23011953735630848 Bool.true 3151161789 137438953472 2628475959417 11505976867815424 Bool.false 10103679441479319683072 147027886727 274877906944 173580823737453 23011953735630848 Bool.false 1440064706613319041024 10477849767 274877906944 173551579547579 23011953735630848 (ep923 (BSN.head_sum_c_succ qz143 21 22 rfl rfl) (ep988 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep989 ep1000) rfl rfl

noncomputable def ep1002 := @Enclosure.Complex.IsNear.mul qz201 (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 206081424864067437085199 ep792 ep915 ep794 Bool.true

noncomputable abbrev qz214 := (Complex.re qz468)

noncomputable abbrev qz215 := (Complex.im qz468)

noncomputable def ep1003 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 751447213227699334571 9261246734126624538624 21753496563483197860291

noncomputable def ep1004 := nat_lit 193830948210219656624996352

noncomputable def ep1005 := nat_lit 64610316070073218874998784000

noncomputable def ep1006 := nat_lit 636190307662168637001146259875667156918075392

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 11144073419 68719476736 322607574499 1438247108476928 67430210209

noncomputable abbrev qz478 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz561 (Real.log (Enclosure.sfrac Bool.false 23 1)))

noncomputable abbrev qz216 := (Real.cos qz478)

noncomputable abbrev qz217 := (Real.sin qz478)

noncomputable abbrev qz479 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable abbrev qz480 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.of_eq qz201 (Complex.mk (@HMul.hMul Real Real Real qz0 qz479 qz216) (@HMul.hMul Real Real Real qz0 qz479 qz480)) Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (BSN.cpow_neg_s_mk qz146 88388 1000 23 qz147 rfl)

noncomputable abbrev qz481 := (Real.sqrt (@Nat.cast Real Real.instNatCast 23))

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep1009 := @Enclosure.Real.IsNear.inv_image qz481 2514397 524288 1 524288 54660 54661 262144 (@Enclosure.Real.IsNear.of_eq qz481 (Real.sqrt qz482) Bool.false 2514397 524288 1 524288 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz482) Bool.false 2514397 524288 1 524288 2514397 524288 1 524288 (BSN.sqrt_enclosure 23 1 1257198 1257199 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1010 := BSN.log_dyadic_bound 7 39 4 3 369468094905 262144 83717 4046006391 1764735 95133 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz483 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz483 88388 1000 0 1 3530250507853047 1125899906842624 250000000083717 20929250000000000000 78007945472028779559 281474976710656000 5524250001849894549 5232312500000000000000 qz148 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000083717 20929250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz482) Bool.false 29613887652180132888576 9444732965739290427392 1000000000334868 83717000000000000000 3530250507853047 1125899906842624 250000000083717 20929250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 95133 262144 24973259072661432 36028797018963968 83717 1000000000000000 rfl rfl rfl rfl (ep1010 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1012 := nat_lit 283774433298858363792059615035146496

noncomputable def ep1013 := BSN.cos_dyadic_bound_f 729866308 1073741824 2 1 524288 167598 ep1012 ep75 ep1012 ep1012 ep76 ep1012 407756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 729866308) qz294 0 1 ep1012 ep75 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 729866308) qz295 0 1 ep1012 ep76 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz478

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145301121) qz24)

noncomputable def ep1014 := @Enclosure.Real.IsNear.cos_image qz218 qz484 Bool.false 145301121 524288 277 262144 Bool.false 407756 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 78007945472028779559 281474976710656000 5524250001849894549 5232312500000000000000 145301121 524288 277 262144 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 145301121 524288) (BSN.cos_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51359775547829855977472) qz26) 226375608064910080 72057594037927936 Bool.false 407756 524288 44 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 145301121 524288 226375608064910080 72057594037927936 44 51359775547829855977472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 407756 524288 51359775547829855977472 75557863725914323419136 729866308 1073741824 167598 167434 (ep1013 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1015 := BSN.sin_dyadic_bound_f 729866308 1073741824 2 1 524288 167598 ep1012 ep79 ep1012 ep1012 ep80 ep1012 329562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 729866308) qz289 0 1 ep1012 ep79 ep1012 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 729866308) qz290 0 1 ep1012 ep80 ep1012 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1016 := @Enclosure.Real.IsNear.sin_image qz218 qz484 Bool.false 145301121 524288 277 262144 Bool.false 329562 524288 1 83717 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 78007945472028779559 281474976710656000 5524250001849894549 5232312500000000000000 145301121 524288 277 262144 (ep1011 rfl) rfl) (Enclosure.sfrac_false_div 145301121 524288) (BSN.sin_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51359775547829855977472) qz26) 226375608064910080 72057594037927936 Bool.false 329562 524288 44 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q0 145301121 524288 226375608064910080 72057594037927936 44 51359775547829855977472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 329562 524288 51359775547829855977472 75557863725914323419136 729866308 1073741824 167598 167434 (ep1015 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz479 qz216) (@HMul.hMul Real Real Real qz0 qz479 qz480) Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (@Enclosure.Real.IsNear.mulLit_ff qz479 qz216 109321 524288 1 524288 101939 131072 23451753 21945909248 11144073419 68719476736 322607574499 1438247108476928 (@Enclosure.Real.IsNear.recentre' qz479 Bool.false 109321 524288 1 524288 109321 524288 1 524288 (ep1009 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 407756 524288 23451753 21945909248 101939 131072 23451753 21945909248 (ep1014 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz479 qz480 109321 524288 1 524288 164781 262144 23451753 21945909248 18014023701 137438953472 2577587512443 11505976867815424 (@Enclosure.Real.IsNear.recentre' qz479 Bool.false 109321 524288 1 524288 109321 524288 1 524288 (ep1009 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 164781 262144 23451753 21945909248 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 329562 524288 23451753 21945909248 164781 262144 23451753 21945909248 (ep1016 rfl rfl) rfl)) rfl)

noncomputable def ep1018 := @ep1007 134768877384 0 1 751447213227699334571 9261246734126624538624 21753496563483197860291 ep1004 (@Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (ep1008 ep1017))

noncomputable def ep1019 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 67430210209 134768877384 0 1 Bool.false

noncomputable def ep1020 := @Enclosure.Complex.IsNear.addLitP qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 243427767 488293034 0 1 Bool.true 63528875

noncomputable def ep1021 := @ep1020 244146517 0 1 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1 Bool.false 134860420418 67430210209 134768877384 0 1 Bool.false 1011413211149 1011413211149 16846109673000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz363 qz469 (@HSub.hSub Complex Complex Complex qz355 qz422 (1 : Complex)))

noncomputable def ep1022 := @Enclosure.Complex.IsNear.addLitP qz219 qz89 Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1

noncomputable def ep1023 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 46000000 31250754176) (Enclosure.sfrac Bool.true 8131696000 31250754176)) Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1

noncomputable def ep1024 := @ep1022 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 31158754176 243427767 488293034 0 1 Bool.true 8131696000 63528875 244146517 0 1 (ep1023 (BSN.N_div_s_sub_one_mk qz146 88388 1000 23 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 46000000 31250754176) (Enclosure.sfrac Bool.true 8131696000 31250754176) Bool.true 46000000 31250754176 0 1 Bool.true 8131696000 31250754176 0 1 (Enclosure.Real.IsNear.const Bool.true 46000000 31250754176) (Enclosure.Real.IsNear.const Bool.true 8131696000 31250754176))) qz90 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz469 1))

noncomputable def ep1025 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 552 0 1

noncomputable def ep1026 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1027 := @ep1026 0 1 0 1 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1 Bool.false 1 1 552 0 1 Bool.false 22097 22097 69000 0

noncomputable def ep1028 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1029 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 552 0 1 Bool.false 22097 69000 0 1

noncomputable def ep1030 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 552 0 1 0 1 0

noncomputable def ep1031 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 23 0 1 1

noncomputable def ep1032 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1033 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz143 Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 (BSN.ascPochhammer_one_eval qz143)

noncomputable def ep1035 := ep1034 (@Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk qz84 qz146) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 88388 1000 qz147) (@Enclosure.Complex.IsNear.mk qz84 qz146 Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 qz372 qz148))

noncomputable def ep1036 := @ep1033 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 88388 1000 0 1 0 1 0

noncomputable def ep1038 := @ep1037 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1039 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) 22097 3000 0 1 0 1 0 1 22097

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 88388 1000 0 1 22097 3000 0

noncomputable def ep1041 := @ep1040 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1042 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1043 := @ep1042 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep536) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1044 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 (@ep1032 1 24 0 1 (ep1036 rfl) (ep1038 rfl) rfl rfl) (@ep1039 22097 3000 0 1 (ep1041 rfl) (ep1043 rfl) rfl rfl)

noncomputable def ep1045 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 ep1044

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz392 qz469 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 23) qz284) Bool.false 1 23 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 23 1 23 EMRow24.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 23) qz284 Bool.false 1 23 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 23) qz297))

noncomputable def ep1046 := @ep1031 552 0 1 ep1045 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 22097 3000 0 1 0 1 0 1 0

noncomputable def ep1048 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 22097 3000 0 1 ep1044

noncomputable def ep1049 := @ep1047 1 0 1 ep1048 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1050 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 22097 69000 0

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1052 := @ep1051 1 0 1 ep1045 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1053 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 22097 3000 0 1 1 23 0 1 22097

noncomputable def ep1054 := @ep1053 69000 0 1 ep1048 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 23 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1055 := @ep1027 1 (@ep1028 0 1 0 1 (BSN.bern_sum_base qz143 23) qz105) (ep1029 (@ep1030 1 1 1 552 0 1 (ep1046 rfl) (ep1049 rfl) rfl rfl) (@ep1050 1 22097 22097 69000 0 1 (ep1052 rfl) (ep1054 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1056 := ep1021 (ep1024 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1025 Bool.false 22097 69000 0 1 (BSN.bern_sum_succ qz143 23 0 1 1 rfl rfl) (ep1055 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1057 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 18014023701 137438953472 2577587512443 11505976867815424 1011413211149

noncomputable def ep1058 := @ep1057 16846109673000 0 1 6073207185714201147483 771770561177218711552000 869002020992512541275669 ep1005 (@Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (ep1008 ep1017))

noncomputable def ep1059 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 67430210209 134768877384 0 1 Bool.false

noncomputable def ep1060 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 11271263081991005348431 1157655841765828067328000 326289562865023834889351

noncomputable def ep1061 := nat_lit 24228868526277457078124544000

noncomputable def ep1062 := nat_lit 516882528560585750999990272

noncomputable def ep1063 := nat_lit 399140129553915456102508301302802780419784704

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 11144073419 68719476736 322607574499 1438247108476928 1011413211149

noncomputable def ep1065 := @ep1064 16846109673000 0 1 11271263081991005348431 1157655841765828067328000 326289562865023834889351 ep1061 (@Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (ep1008 ep1017))

noncomputable def ep1066 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz202 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz203 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 18014023701 137438953472 2577587512443 11505976867815424 67430210209

noncomputable def ep1067 := @ep1066 134768877384 0 1 404896468289446054503 6174164489417749692416 57935755932041631043529 ep1062 (@Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 11144073419 68719476736 322607574499 1438247108476928 Bool.true 18014023701 137438953472 2577587512443 11505976867815424 (ep1008 ep1017))

noncomputable abbrev qz485 := (ep1056 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1068 := @ep1002 129293649444560259741763 ep792 ep916 ep794 (@ep1003 ep1004 6073207185714201147483 771770561177218711552000 869002020992512541275669 ep1005 ep1006 206081424864067437085199 ep792 ep915 ep794 (ep1018 (@ep1019 1011413211149 16846109673000 0 1 qz485) rfl) (ep1058 (@ep1059 1011413211149 16846109673000 0 1 qz485) rfl) rfl rfl) (@ep1060 ep1061 404896468289446054503 6174164489417749692416 57935755932041631043529 ep1062 ep1063 129293649444560259741763 ep792 ep916 ep794 (ep1065 (@ep1059 1011413211149 16846109673000 0 1 qz485) rfl) (ep1067 (@ep1019 1011413211149 16846109673000 0 1 qz485) rfl) rfl rfl)

noncomputable def ep1069 := @ep919 ep912 ep794 (@ep920 23011953735630848 (BSN.head_sum_c_eq qz143 23) (ep921 (BSN.head_sum_c_succ qz143 22 23 rfl rfl) (ep1001 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1068 rfl rfl rfl

noncomputable def ep1070 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz143 1 23) Bool.false ep791 ep792 ep793 ep794 Bool.true 41038146288510511646263 ep792 ep912 ep794 (@ep913 ep794 Bool.true 41038146288510511646263 ep792 ep912 ep794 (BSN.zetaApproximant_eq_folded' qz143 1 23 rfl) (ep1069 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) (Complex.im (zetaApproximant qz143 1 23)) 25 65536 11061637

noncomputable def ep1072 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173)) Bool.false 200 524288 11061637

noncomputable def ep1073 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173) qz451 Bool.false 9470771 131072 129

noncomputable def ep1074 := nat_lit 18118993288719373273541211797949770920137648807047338644318473854143007031296

noncomputable def ep1075 := nat_lit 54226259965658656152515176829448237984745516345008920005757399777594212089856

noncomputable def ep1076 := BSN.cos_dyadic_bound_f 1686218944 1073741824 3 2 524288 167598 ep1074 ep64 ep908 ep1075 ep66 ep908 200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686218944) qz294 0 2 ep1074 ep64 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686218944) qz295 0 2 ep1075 ep66 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1077 := @ep1073 262144 Bool.false 200 524288 1 83717 (@ep799 9470771 131072 129 262144 ep906 rfl) (Enclosure.sfrac_false_div 9470771 131072) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29664277375586362458112) qz293) 226375608064910080 72057594037927936 Bool.false 200 524288 11 1000000000000000 167434 83717 (BSN.sin_reduce_arg_pos_rat_q1 9470771 131072 226375608064910080 72057594037927936 11 29664277375586362458112 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 200 524288 29664277375586362458112 18889465931478580854784 1686218944 1073741824 167598 167434 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz143 1 23) Bool.false ep791 ep792 ep793 ep794 Bool.true 41038146288510511646263 ep792 ep912 ep794 (@ep913 ep794 Bool.true 41038146288510511646263 ep792 ep912 ep794 (BSN.zetaApproximant_eq_folded' qz143 1 23 rfl) (ep1069 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow24.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 1 23 qz146) Bool.true ep775 ep776 ep777 ep778 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 23 qz146) ep779 Bool.true ep775 ep776 ep777 ep778 (@Eq.refl Real ep779) (@ep780 Bool.true ep775 ep776 ep777 ep778 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz358 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz171 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz172 (@Nat.cast Complex Complex.instNatCast j))))) qz173) (zetaApproximant qz143 1 23)) (@ep782 ep783 ep784 ep785 41038146288510511646263 ep786 ep787 ep788 ep789 ep775 ep776 ep777 ep778 (@ep790 21945909248 ep791 ep792 ep793 ep794 ep781 ep783 ep784 ep785 (@ep795 21945909248 524287 524288 11061637 21945909248 (ep911 rfl rfl) rfl) ep1070 rfl) (@ep1071 21945909248 41038146288510511646263 ep792 ep912 ep794 41038146288510511646263 ep786 ep787 ep788 (@ep1072 21945909248 25 65536 11061637 21945909248 (ep1077 rfl rfl) rfl) ep1078 rfl) rfl rfl))

theorem EMRow24.d15 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow24.d16 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow24.d17 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow24.d18 : @Eq Nat (Nat.pow 22 (Nat.succ (Nat.mul 2 3))) 2494357888 := @Eq.refl Nat 2494357888

noncomputable abbrev qz565 := (@HAdd.hAdd Complex Complex Complex qz569 qz568 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz486 := qz565

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz486) (@HAdd.hAdd Real Real Real qz382 (Complex.re qz273) qz298))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz487 := (@HPow.hPow Complex Complex Complex qz526 (@Nat.cast Complex Complex.instNatCast 22) (@HSub.hSub Complex Complex Complex qz546 qz527 qz528))

noncomputable abbrev qz225 := qz487

noncomputable def ep1079 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 744696659 25769803776 2893993 25769803776 15680495211554873 36028797018963968 6336293607

noncomputable def ep1080 := nat_lit 430913809480088311677583360

noncomputable def ep1081 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22)) 4427 294912 1 884736 504651 262144 1923 262144 744696659 25769803776

noncomputable abbrev qz226 := qz272

noncomputable abbrev qz566 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz488 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz566 qz226 2))

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz488 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep1083 := nat_lit 781950621441006189802102638025

noncomputable def ep1084 := nat_lit 19807040628566084398385987584

noncomputable def ep1085 := nat_lit 26986075409044041160201671

noncomputable def ep1086 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz489 := (@HPow.hPow Real Nat Real qz566 qz226 1)

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff qz489 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1083 ep1084 ep1085 ep1086

noncomputable def ep1088 := ep1087 (@Enclosure.Real.IsNear.of_eq qz489 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz490 := (@HPow.hPow Real Nat Real qz566 qz226 2)

noncomputable def ep1089 := @Enclosure.Real.IsNear.inv_image qz490 ep1083 ep1084 ep1085 ep1086 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz490 (@HMul.hMul Real Real Real qz0 qz489 qz226) Bool.false ep1083 ep1084 ep1085 ep1086 (BSN.pow_succ_r qz226 1 2 rfl) ep1088) rfl rfl rfl

noncomputable def ep1090 := ep1082 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz488 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep1089 rfl rfl rfl) rfl)

noncomputable def ep1091 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 22)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 22)) (Complex.im (zetaApproximant qz5 1 22))))) Bool.false 504651 262144 1923 262144

noncomputable def ep1092 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 22)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 22)) (Complex.im (zetaApproximant qz5 1 22))))) Bool.false 1009302 524288 3846 524288

noncomputable def ep1093 := nat_lit 28868717906502897665405024993351208514782433

noncomputable def ep1094 := nat_lit 7789668975175759412795087099360654131200000

noncomputable def ep1095 := nat_lit 57015559601724169954076140839282156418899652294529783312465971

noncomputable def ep1096 := nat_lit 2018913925432654769537164258272576373628322349384816656384000000

noncomputable def ep1097 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 22)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 22)) (Complex.im (zetaApproximant qz5 1 22)))) ep1093 ep1094 ep1095 ep1096 502728 506574

noncomputable def ep1098 := nat_lit 118612895587957435557099665217756287157055039784435401

noncomputable def ep1099 := nat_lit 32007221856872027389690234231366797324854493184000000

noncomputable def ep1100 := nat_lit 56486805123431219270574188952754295346562211502284026967379799

noncomputable def ep1101 := nat_lit 15096708796840328846208395273409600308955500715889

noncomputable def ep1102 := nat_lit 72016249177962061626803027020575293980922609664000000

noncomputable def ep1103 := nat_lit 1335238581547855261368565370019851192771315131933728144157

noncomputable def ep1104 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 22)) (Complex.re (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 22)) (Complex.im (zetaApproximant qz5 1 22))) ep1098 ep1099 ep1100 ep1096 ep1101 ep1102 ep1103

noncomputable def ep1105 := nat_lit 5098267488466299923073647116849940337445258458042466304000000

noncomputable def ep1106 := nat_lit 8542539048089708574819930829242408131574245511499060917874607467127457935656237463318212628017315840000000

noncomputable def ep1107 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 22)) (Complex.re (zetaApproximant qz5 1 22)) ep281 ep282 ep283 ep284 ep281 ep282 ep283 ep284 ep1098

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 22)) (Complex.im (zetaApproximant qz5 1 22)) ep419 ep420 ep421 ep422 ep419 ep420 ep421 ep422 ep1101

noncomputable def ep1109 := @ep1079 36028797018963968 ep1080 50164969810294955 108086391056891904 12157295296693 108086391056891904 (@ep1081 2893993 25769803776 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz488) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow24.d15 EMRow24.d16 rfl) (ep1090 rfl)) (ep1091 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 22)) (@ep1092 504651 262144 1923 262144 (@ep1097 262144 (@ep1104 ep1105 ep1106 ep1093 ep1094 ep1095 ep1096 (@ep1107 ep1099 ep1100 ep1096 ep576 ep576 rfl) (@ep1108 ep1102 ep1103 ep1105 ep584 ep584 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz486)

noncomputable abbrev qz491 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1110 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz491) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 15680495211554873 36028797018963968 6336293607 36028797018963968 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz13 3)

noncomputable def ep1111 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz491) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 45125569 1835008 1 1835008 2432400719 137438953472 929 137438953472

noncomputable def ep1112 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz491 45125569 524288 1 524288 2 7 0 1 45125569 1835008

noncomputable abbrev qz492 := (Complex.re qz565)

noncomputable abbrev qz493 := (Complex.im qz565)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz268 qz492 qz492) (@HMul.hMul Real Real Real qz268 qz493 qz493))

noncomputable abbrev qz229 := qz486

noncomputable def ep1113 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 45125569 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1114 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 45125569 524288 1 524288 45125569

noncomputable def ep1115 := @Enclosure.Real.IsNear.sqrt_image qz228 7408078001 1000000 0 1 22562784 22562785 262144

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz492 qz492)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz493 qz493)

noncomputable def ep1116 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 7395828001 1000000 0 1

noncomputable abbrev qz232 := qz492

noncomputable def ep1117 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz494 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz494 qz13) Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 85999 1000 3 qz14)

noncomputable abbrev qz495 := (ep1118 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz17))

noncomputable def ep1119 := @ep1117 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz495)

noncomputable def ep1120 := ep1119 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz495)

noncomputable abbrev qz233 := qz493

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 85999 1000 0 1 85999 1000 0 1 7395828001 1000000

noncomputable def ep1122 := @ep1121 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz495)

noncomputable def ep1123 := ep1122 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 85999 1000 0 1 qz495)

noncomputable def ep1124 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 2432400719 137438953472

noncomputable def ep1125 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 2432400719 137438953472

noncomputable def ep1126 := nat_lit 144842138053329945895240119804074371963118654768594337047967461

noncomputable def ep1127 := nat_lit 462428252436731001462884654101636424188009906176000000000000000000

noncomputable def ep1128 := nat_lit 830946434818382922117483091687575283118712217617025893527036210184028882127

noncomputable def ep1129 := nat_lit 3473626820564939601490913158134758381149049633173211192854755409920000000000000000000

noncomputable def ep1130 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1126 ep1127 ep1128 ep1129

noncomputable def ep1131 := nat_lit 3034284891756058435174683683504901952982823252664560695836243801

noncomputable def ep1132 := nat_lit 11560706310918275036572116352540910604700247654400000000000000000000

noncomputable def ep1133 := nat_lit 698719723678874528692494581721785746667043356477494240592092380653834343523

noncomputable def ep1134 := nat_lit 146692139894297553051579827899239336523785779137574432590735681

noncomputable def ep1135 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1131 ep1132 ep1133 ep1129 ep1134

noncomputable def ep1136 := nat_lit 2890176577729568759143029088135227651175061913600000000000000000000

noncomputable def ep1137 := nat_lit 33056677784877098356247127491447384112917215284882913233735957382548634651

noncomputable def ep1138 := nat_lit 868406705141234900372728289533689595287262408293302798213688852480000000000000000000

noncomputable def ep1139 := nat_lit 10465483871750172135257288335551539921771807690656670191221951819412013775382624957476309297530116742829834240000000000000000000000

noncomputable def ep1140 := nat_lit 55084343435826285930560451410651

noncomputable def ep1141 := nat_lit 3400103867666144553861120000000000

noncomputable def ep1142 := nat_lit 25872020895992651179317102325026521

noncomputable def ep1143 := nat_lit 4167509340460402376355873439088640000000000

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1140 ep1141 ep1142 ep1143 ep1140 ep1141 ep1142

noncomputable def ep1145 := nat_lit 12111653062001798978527404612959

noncomputable def ep1146 := nat_lit 1700051933833072276930560000000000

noncomputable def ep1147 := nat_lit 5566872981882409153069731986083949

noncomputable def ep1148 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.false ep1140 ep1141 ep1142 ep1143 Bool.true ep1145 ep1146 ep1147

noncomputable def ep1149 := nat_lit 2083754670230201188177936719544320000000000

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.false ep1140 ep1141 ep1142 ep1143 Bool.true ep1145 ep1146 ep1147 ep1149

noncomputable def ep1151 := nat_lit 371444072879530262995594873

noncomputable def ep1152 := nat_lit 1133367955888714851287040000000

noncomputable def ep1153 := nat_lit 171158077436492874187887639403

noncomputable def ep1154 := nat_lit 1389169780153467458785291146362880000000

noncomputable def ep1155 := nat_lit 56198675654464876719547236029651

noncomputable def ep1156 := nat_lit 25358546663683172556753439406817521

noncomputable abbrev qz234 := (Complex.re qz487)

noncomputable abbrev qz235 := (Complex.im qz487)

noncomputable def ep1157 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1151 ep1152 ep1153 ep1154 ep1155 ep1141 ep1156

noncomputable def ep1158 := nat_lit 62430829721334385505179166521647394124122515250914263040000000

noncomputable def ep1159 := nat_lit 2894103708653057205802689888256

noncomputable def ep1160 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 22186234003 480000000 0 1 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 ep1151

noncomputable def ep1161 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 22186234003 480000000 0 1 0 1 0 1 22186234003

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 66558702009 2000000 0 1 22186234003 480000000 0

noncomputable def ep1163 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow24.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz18)

noncomputable abbrev qz496 := (@HAdd.hAdd Complex Complex Complex qz525 qz524 qz529)

noncomputable abbrev qz236 := qz496

noncomputable def ep1164 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1

noncomputable abbrev qz237 := (Complex.re qz496)

noncomputable abbrev qz238 := (Complex.im qz496)

noncomputable def ep1165 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 7395078001 400000 0 1 7395828001 500000 0 1

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 7395078001 1000000 0 1 5 2 0 1 7395078001 400000

noncomputable abbrev qz497 := (@HAdd.hAdd Complex Complex Complex qz525 qz524 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz497

noncomputable def ep1167 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1

noncomputable abbrev qz240 := (Complex.re qz497)

noncomputable abbrev qz241 := (Complex.im qz497)

noncomputable def ep1168 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 7395828001 1000000 0 1

noncomputable def ep1169 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1170 := @ep1169 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable abbrev qz498 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1171 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz498 qz13) Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 85999 1000 1 qz14)

noncomputable abbrev qz499 := (ep1171 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz17))

noncomputable def ep1172 := ep1170 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz499)

noncomputable def ep1173 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 85999 1000 0 1 85999 1000 0 1 7395828001 1000000

noncomputable def ep1174 := @ep1173 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep1175 := ep1174 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz499)

noncomputable def ep1176 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 (@ep1168 29580312004 7395078001 1000000 0 1 (ep1172 rfl) (ep1175 rfl) rfl rfl)

noncomputable def ep1177 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 85999 2000 0 1 257997 2000 0 1

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 85999 1000 0 1 85999 2000

noncomputable def ep1179 := @ep1178 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep1180 := ep1179 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz499)

noncomputable def ep1181 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 85999 1000 0 1 3 2 0 1 257997 2000

noncomputable def ep1182 := @ep1181 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 85999 1000 0 1 ep538)

noncomputable def ep1183 := ep1182 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 85999 1000 0 1 qz499)

noncomputable abbrev qz242 := (ep1167 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1176 (@ep1177 687992000 85999 500 0 1 (ep1180 rfl) (ep1183 rfl) rfl rfl)))

noncomputable def ep1184 := @ep1166 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz242)

noncomputable abbrev qz500 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1185 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz500 qz13) Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 85999 1000 2 qz14)

noncomputable abbrev qz501 := (ep1185 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz17))

noncomputable def ep1186 := ep1184 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz501)

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 85999 500 0 1 85999 1000 0 1 7395828001 500000

noncomputable def ep1188 := @ep1187 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz242)

noncomputable def ep1189 := ep1188 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz501)

noncomputable def ep1190 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 (@ep1165 6655870200900000 66558702009 2000000 0 1 (ep1186 rfl) (ep1189 rfl) rfl rfl)

noncomputable def ep1191 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 635969313007999 1000000000 0 1 85999 200 0 1

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 7395078001 1000000 0 1 85999 1000 0 1 635969313007999 1000000000

noncomputable def ep1193 := @ep1192 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz242)

noncomputable def ep1194 := ep1193 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz501)

noncomputable def ep1195 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 85999 500 0 1 5 2 0 1 85999 200

noncomputable def ep1196 := @ep1195 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 7395078001 1000000 0 1 Bool.false 85999 500 0 1 qz242)

noncomputable def ep1197 := ep1196 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 85999 1000 0 1 qz501)

noncomputable abbrev qz243 := (ep1164 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1190 (@ep1191 127107863601599800 635539318007999 1000000000 0 1 (ep1194 rfl) (ep1197 rfl) rfl rfl)))

noncomputable def ep1198 := @ep1162 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz243)

noncomputable def ep1199 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 635539318007999 1000000000 0 1 0 1 0

noncomputable def ep1200 := @ep1199 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz243)

noncomputable def ep1201 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 635539318007999 720000000000 0 1 0 1 0 1 635539318007999

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 635539318007999 1000000000 0 1 635539318007999 720000000000 0

noncomputable def ep1203 := @ep1202 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz243)

noncomputable def ep1204 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 66558702009 2000000 0 1 0 1 0

noncomputable def ep1205 := @ep1204 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 66558702009 2000000 0 1 Bool.true 635539318007999 1000000000 0 1 qz243)

noncomputable def ep1206 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 (@ep1161 22186234003 480000000 0 1 (ep1198 rfl) (ep1200 rfl) rfl rfl) (@ep1201 635539318007999 720000000000 0 1 (ep1203 rfl) (ep1205 rfl) rfl rfl)

noncomputable def ep1207 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 ep1206

noncomputable def ep1208 := nat_lit 5788207417306114411605379776512

noncomputable def ep1209 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.true 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 Bool.true 88426748844762349 4722366482869645213696 39900830594031014479 ep1208

noncomputable abbrev qz502 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2494357888)))

noncomputable def ep1210 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz502 qz134) (@HMul.hMul Real Real Real qz0 qz502 qz415)) Bool.true 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 Bool.true 88426748844762349 4722366482869645213696 39900830594031014479

noncomputable abbrev qz503 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2494357888))

noncomputable abbrev qz504 := (@Nat.cast Real Real.instNatCast 2494357888)

noncomputable def ep1211 := @Enclosure.Real.IsNear.inv_image qz503 6864188833816481 137438953472 1 137438953472 1375943 1375944 68719476736 (@Enclosure.Real.IsNear.of_eq qz503 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz504 qz15)) Bool.false 6864188833816481 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 2494357888) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz504 qz15)) Bool.false 6864188833816481 137438953472 1 137438953472 6864188833816481 137438953472 1 137438953472 (BSN.sqrt_enclosure 2494357888 1 3432094416908240 3432094416908241 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1212 := nat_lit 306425149250000000000000000

noncomputable def ep1213 := nat_lit 7653050432283008116944011264

noncomputable def ep1214 := nat_lit 2475880078570760549798248448

noncomputable def ep1215 := nat_lit 19611209552000000000000000

noncomputable def ep1216 := nat_lit 1225098492264471210946560

noncomputable def ep1217 := BSN.log_dyadic_bound 6 38 7 6 ep1216 68719476736 19611209552 10335929591183785132032 22627652382720 21883973767 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 6) (BSN.artanhQ 38) 0 6 10335929591183785132032 ep1216 22627652382720 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz136 85999 1000 0 1 3480204410281207 1125899906842624 15626225700597 306425149250000000000000 299294099079773520793 1125899906842624000 1343839784025641403 ep1212 qz17 (BSN.isNear_log_sfrac 22 1 3480204410281207 1125899906842624 15626225700597 306425149250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false ep1213 ep1214 1000078444838208 ep1215 3480204410281207 1125899906842624 15626225700597 306425149250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 21883973767 68719476736 24973259072661432 36028797018963968 19611209552 1000000000000000 rfl rfl rfl rfl (ep1217 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1219 := nat_lit 7169766786237824151601545216

noncomputable def ep1220 := nat_lit 2045711259899683157999534133913025467182166960687257455055631482888440756700656524804680327502776210254051982468563200

noncomputable def ep1221 := nat_lit 14298200008547628616551818071540114577587335786466501286865076710532687516440907786670008938572638187735909165122537390080

noncomputable def ep1222 := nat_lit 11614535108934155666170595039948020527307810184538975640578625018041801799284819422482900547614042675449210716416

noncomputable def ep1223 := nat_lit 5357796400013755710889606074523097260110535922488232652518473899314934676060711103828431123525432032691518750600315136

noncomputable def ep1224 := nat_lit 262133666823373191303449997978235433922434489418552523592526406359765937801416642755616830540498366775158334693913185484800

noncomputable def ep1225 := BSN.sin_dyadic_bound_f 101888514141106 281474976710656 3 2 137438953472 39260722248 ep1220 ep1221 ep1222 ep1223 ep1224 ep1222 48670883944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 101888514141106) (BSN.sinEvenQ 281474976710656) 0 2 ep1220 ep1221 ep1222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 101888514141106) (BSN.sinOddQ 281474976710656) 0 2 ep1223 ep1224 ep1222 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz505 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36534924204073) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1226 := @Enclosure.Real.IsNear.cos_image qz137 qz505 Bool.false 36534924204073 137438953472 151 34359738368 Bool.true 48670883944 137438953472 1 19611209552 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 299294099079773520793 1125899906842624000 1343839784025641403 ep1212 36534924204073 137438953472 151 34359738368 (ep1218 rfl) rfl) (Enclosure.sfrac_false_div 36534924204073 137438953472) (BSN.cos_reduce1 qz505 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1219) (@Nat.cast Real Real.instNatCast ep1084)) 226375608064910080 72057594037927936 Bool.false 48670883944 137438953472 42 1000000000000000 39222419104 19611209552 (BSN.sin_reduce_arg_pos_rat_q1 36534924204073 137438953472 226375608064910080 72057594037927936 42 ep1219 ep1084 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 48670883944 137438953472 ep1219 ep1084 101888514141106 281474976710656 39260722248 39222419104 (ep1225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1227 := nat_lit 1136511417515427947402259483549476347554771559408558381242302192104697327856719973700121285457341278604551301020631296

noncomputable def ep1228 := nat_lit 1588688889838625401839090896837790508620815087385166809651675190059187501826767531852223215396959798637323240569170821120

noncomputable def ep1229 := nat_lit 3409511023476065973895446109458349146623260062605306065775625419064055899966561351461518890570928607728303004640461056

noncomputable def ep1230 := nat_lit 71491000042738143082759090357700572887936678932332506434325383552663437582204538933350044692863190938679545825612686950400

noncomputable def ep1231 := BSN.cos_dyadic_bound_f 101888514141106 281474976710656 3 2 137438953472 39260722248 ep1227 ep1228 ep1222 ep1229 ep1230 ep1222 128532528908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 101888514141106) (BSN.cosEvenQ 281474976710656) 0 2 ep1227 ep1228 ep1222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 101888514141106) (BSN.cosOddQ 281474976710656) 0 2 ep1229 ep1230 ep1222 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1232 := @Enclosure.Real.IsNear.sin_image qz137 qz505 Bool.false 36534924204073 137438953472 151 34359738368 Bool.false 128532528908 137438953472 1 19611209552 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 299294099079773520793 1125899906842624000 1343839784025641403 ep1212 36534924204073 137438953472 151 34359738368 (ep1218 rfl) rfl) (Enclosure.sfrac_false_div 36534924204073 137438953472) (BSN.sin_reduce1 qz505 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1219) (@Nat.cast Real Real.instNatCast ep1084)) 226375608064910080 72057594037927936 Bool.false 128532528908 137438953472 42 1000000000000000 39222419104 19611209552 (BSN.sin_reduce_arg_pos_rat_q1 36534924204073 137438953472 226375608064910080 72057594037927936 42 ep1219 ep1084 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128532528908 137438953472 ep1219 ep1084 101888514141106 281474976710656 39260722248 39222419104 (ep1231 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1233 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz502 qz134) (@HMul.hMul Real Real Real qz0 qz502 qz415) Bool.true 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 Bool.true 88426748844762349 4722366482869645213696 39900830594031014479 ep1208 (@Enclosure.Real.IsNear.mulLit_ft qz502 qz134 2751887 137438953472 1 137438953472 6083860493 17179869184 187228273795 42114751830421405696 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 (@Enclosure.Real.IsNear.recentre' qz502 Bool.false 2751887 137438953472 1 137438953472 2751887 137438953472 1 137438953472 (ep1211 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 48670883944 137438953472 2995652380720 673836029286742491136 6083860493 17179869184 187228273795 42114751830421405696 (ep1226 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz502 qz415 2751887 137438953472 1 137438953472 32133132227 34359738368 187228273795 42114751830421405696 88426748844762349 4722366482869645213696 39900830594031014479 ep1208 (@Enclosure.Real.IsNear.recentre' qz502 Bool.false 2751887 137438953472 1 137438953472 2751887 137438953472 1 137438953472 (ep1211 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz135 Bool.false 32133132227 34359738368 187228273795 42114751830421405696 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 128532528908 137438953472 2995652380720 673836029286742491136 32133132227 34359738368 187228273795 42114751830421405696 (ep1232 rfl rfl) rfl)) rfl)

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 635539318007999 720000000000 0 1 88426748844762349 4722366482869645213696 39900830594031014479 ep1208 ep1155

noncomputable def ep1235 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 22186234003 480000000 0 1 Bool.false 635539318007999 720000000000 0 1 ep1206

noncomputable def ep1236 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.true 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 Bool.true 88426748844762349 4722366482869645213696 39900830594031014479 ep1208

noncomputable def ep1237 := nat_lit 1961856541994407395837953047

noncomputable def ep1238 := nat_lit 2266735911777429702574080000000

noncomputable def ep1239 := nat_lit 885249164473233582270575129437

noncomputable def ep1240 := nat_lit 2778339560306934917570582292725760000000

noncomputable def ep1241 := nat_lit 10640260655505993431648939827709

noncomputable def ep1242 := nat_lit 4902936108527483966366800639006199

noncomputable def ep1243 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1237 ep1238 ep1239 ep1240 ep1241 ep1146 ep1242

noncomputable def ep1244 := nat_lit 27453918946628546128903689826995678595328153148425502720000000

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 22186234003 480000000 0 1 88426748844762349 4722366482869645213696 39900830594031014479 ep1208 ep1237

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 635539318007999 720000000000 0 1 16742096600500291 2361183241434822606848 7714607058293401801 ep1159 ep1241

noncomputable abbrev qz506 := (@ep1210 ep1208 (BSN.cpow_neg_s_sub_mk qz13 85999 1000 22 3 2494357888 qz14 rfl EMRow24.d18) ep1233)

noncomputable def ep1247 := ep1150 (@ep1157 ep1143 ep1158 ep1140 ep1141 ep1142 ep1143 (@ep1160 ep1152 ep1153 ep1154 ep1207 (ep1209 qz506) rfl) (@ep1234 ep1141 ep1156 ep1143 ep1235 (ep1236 qz506) rfl) rfl rfl) (@ep1243 ep1149 ep1244 ep1145 ep1146 ep1147 ep1149 (@ep1245 ep1238 ep1239 ep1240 ep1207 (ep1236 qz506) rfl) (@ep1246 ep1146 ep1242 ep1149 ep1235 (ep1209 qz506) rfl) rfl rfl)

noncomputable def ep1248 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1145 ep1146 ep1147 ep1149 ep1145 ep1146 ep1147

noncomputable def ep1249 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.false ep1140 ep1141 ep1142 ep1143 Bool.true ep1145 ep1146 ep1147

noncomputable def ep1250 := @ep1111 15680495211554873 36028797018963968 6336293607 36028797018963968 (@ep1112 1 1835008 (ep1113 (@ep1114 524288 1 524288 (ep1115 (@ep1116 29632312004 7408078001 1000000 0 1 (ep1120 rfl) (ep1123 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1124 929 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1125 929 137438953472 2432400719 137438953472 929 137438953472 (@ep1130 1216199895 1216200824 68719476736 (@ep1135 ep1136 ep1137 ep1138 ep1139 ep1126 ep1127 ep1128 ep1129 (@ep1144 ep1143 ep1131 ep1132 ep1133 ep1129 (@ep1148 ep1149 ep1247) (@ep1148 ep1149 ep1247) rfl) (@ep1248 ep1149 ep1134 ep1136 ep1137 ep1138 (@ep1249 ep1149 ep1247) (@ep1249 ep1149 ep1247) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow24.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 50164969810294955 108086391056891904 12157295296693 108086391056891904 := ep1109 (ep1110 ep1250) rfl rfl

theorem EMRow24.d20 : @Eq Nat (Nat.pow 23 (Nat.succ (Nat.mul 2 3))) 3404825447 := @Eq.refl Nat 3404825447

noncomputable abbrev qz567 := (@HAdd.hAdd Complex Complex Complex qz569 qz575 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz507 := qz567

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz507) (@HAdd.hAdd Real Real Real qz382 (Complex.re qz422) qz298))

noncomputable abbrev qz508 := (@HPow.hPow Complex Complex Complex qz526 (@Nat.cast Complex Complex.instNatCast 23) (@HSub.hSub Complex Complex Complex qz546 qz560 qz528))

noncomputable abbrev qz245 := qz508

noncomputable def ep1251 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 40237003 4294967296 13974773 115964116992 104822925067503745 252201579132747776 49518481631

noncomputable def ep1252 := nat_lit 460358870732156286793678848

noncomputable def ep1253 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23)) 4427 294912 1 884736 81801 131072 523 65536 40237003 4294967296

noncomputable def ep1254 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 23)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 23)) (Complex.im (zetaApproximant qz143 1 23))))) Bool.false 81801 131072 523 65536

noncomputable def ep1255 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 23)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 23)) (Complex.im (zetaApproximant qz143 1 23))))) Bool.false 327204 524288 4184 524288

noncomputable def ep1256 := nat_lit 855338810499891653781145683821262645581

noncomputable def ep1257 := nat_lit 2195676701747988405297616520006860800000

noncomputable def ep1258 := nat_lit 187069815463186183855779157306304962261270548261099781543

noncomputable def ep1259 := nat_lit 18785218242036427353953675420467382314005132006653952000000

noncomputable def ep1260 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 23)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 23)) (Complex.im (zetaApproximant qz143 1 23)))) ep1256 ep1257 ep1258 ep1259 161510 165694

noncomputable def ep1261 := nat_lit 2086595784933918572398179591718260796449624048601

noncomputable def ep1262 := nat_lit 5360668191898191809097974217613358804238336000000

noncomputable def ep1263 := nat_lit 40191019972922417129592021027114462405275526019057757179

noncomputable def ep1264 := nat_lit 4174492942674761634211927871214973847556696001478656000000

noncomputable def ep1265 := nat_lit 1684129450797189082186398027184458158441865169

noncomputable def ep1266 := nat_lit 496818046802824541809205014743190515002454494027189939

noncomputable def ep1267 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz143 1 23)) (Complex.re (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz143 1 23)) (Complex.im (zetaApproximant qz143 1 23))) ep1261 ep1262 ep1263 ep1264 ep1265 ep1262 ep1266

noncomputable def ep1268 := nat_lit 1502817459362914188316294033637390585120410560532316160000

noncomputable def ep1269 := nat_lit 11194575712822025033348311594791037444521433594460154395967632284061854505915402328704286720000000

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz143 1 23)) (Complex.re (zetaApproximant qz143 1 23)) ep791 ep792 ep793 ep794 ep791 ep792 ep793 ep794 ep1261

noncomputable def ep1271 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz143 1 23)) (Complex.im (zetaApproximant qz143 1 23)) 41038146288510511646263 ep792 ep912 ep794 41038146288510511646263 ep792 ep912 ep794 ep1265

noncomputable def ep1272 := @ep1251 252201579132747776 ep1252 107185652184336513 252201579132747776 821939247105925 6809442636584189952 (@ep1253 13974773 115964116992 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz488) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow24.d15 EMRow24.d16 rfl) (ep1090 rfl)) (ep1254 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz143 1 23)) (@ep1255 81801 131072 523 65536 (@ep1260 262144 (@ep1267 ep1268 ep1269 ep1256 ep1257 ep1258 ep1259 (@ep1270 ep1262 ep1263 ep1264 ep1070 ep1070 rfl) (@ep1271 ep1262 ep1266 ep1268 ep1078 ep1078 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz507)

noncomputable def ep1273 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz491) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 104822925067503745 252201579132747776 49518481631 252201579132747776 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz146 3)

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz491) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 46377085 1835008 1 1835008 2260230997 137438953472 1019 137438953472

noncomputable def ep1275 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz491 46377085 524288 1 524288 2 7 0 1 46377085 1835008

noncomputable abbrev qz509 := (Complex.re qz567)

noncomputable abbrev qz510 := (Complex.im qz567)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz268 qz509 qz509) (@HMul.hMul Real Real Real qz268 qz510 qz510))

noncomputable abbrev qz248 := qz507

noncomputable def ep1276 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 46377085 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1277 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 46377085 524288 1 524288 46377085

noncomputable def ep1278 := @Enclosure.Real.IsNear.sqrt_image qz247 244521517 31250 0 1 23188542 23188543 262144

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz509 qz509)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz510 qz510)

noncomputable def ep1279 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 488277409 62500 0 1

noncomputable abbrev qz251 := qz509

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1281 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz494 qz146) Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 88388 1000 3 qz147)

noncomputable abbrev qz511 := (ep1281 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz146 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz148))

noncomputable def ep1282 := @ep1280 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz511)

noncomputable def ep1283 := ep1282 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz511)

noncomputable abbrev qz252 := qz510

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 88388 1000 0 1 88388 1000 0 1 488277409 62500

noncomputable def ep1285 := @ep1284 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz511)

noncomputable def ep1286 := ep1285 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 88388 1000 0 1 qz511)

noncomputable def ep1287 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 2260230997 137438953472

noncomputable def ep1288 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 2260230997 137438953472

noncomputable def ep1289 := nat_lit 530087914034065243823085924695483777051081542171362821497

noncomputable def ep1290 := nat_lit 1960026433464605549549037738806984897986560000000000000000000

noncomputable def ep1291 := nat_lit 2358973155956863109280475262584951166673990835535515211642785422980311721

noncomputable def ep1292 := nat_lit 9681762836145245790525852331754617865194205960428035757163151360000000000000000000

noncomputable def ep1293 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1289 ep1290 ep1291 ep1292

noncomputable def ep1294 := nat_lit 262406537021999708779401906024299050781133834166884255889

noncomputable def ep1295 := nat_lit 2177807148294006166165597487563316553318400000000000000000000

noncomputable def ep1296 := nat_lit 10045899422774050582144333545364446755544190701653322695457016298466824023

noncomputable def ep1297 := nat_lit 96817628361452457905258523317546178651942059604280357571631513600000000000000000000

noncomputable def ep1298 := nat_lit 2939220307142655059216242092736146313480610914211669911969

noncomputable def ep1299 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1294 ep1295 ep1296 ep1297 ep1298

noncomputable def ep1300 := nat_lit 19600264334646055495490377388069848979865600000000000000000000

noncomputable def ep1301 := nat_lit 13543832136794580510660419080485064911195717653701829420970837931336293187

noncomputable def ep1302 := nat_lit 11544292484076459188321537167020155014487228977482596962092597870938153509780933809844062622056448000000000000000000000

noncomputable def ep1303 := nat_lit 16198967159112327454666373417

noncomputable def ep1304 := nat_lit 1475739525896764129280000000000

noncomputable def ep1305 := nat_lit 1470631625703489842577271505609911

noncomputable def ep1306 := nat_lit 311155312282230620934416828989440000000000

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1303 ep1304 ep1305 ep1306 ep1303 ep1304 ep1305

noncomputable def ep1308 := nat_lit 54214576519075154159438841937

noncomputable def ep1309 := nat_lit 4427218577690292387840000000000

noncomputable def ep1310 := nat_lit 1777252525186458464108976112607459

noncomputable def ep1311 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1303 ep1304 ep1305 ep1306 Bool.false ep1308 ep1309 ep1310

noncomputable def ep1312 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.false ep1303 ep1304 ep1305 ep1306 Bool.false ep1308 ep1309 ep1310 ep1306

noncomputable def ep1313 := nat_lit 1920474274364313960193447

noncomputable def ep1314 := nat_lit 2951479051793528258560000000

noncomputable def ep1315 := nat_lit 14492279118160120668209388101

noncomputable def ep1316 := nat_lit 51859218713705103489069471498240000000

noncomputable def ep1317 := nat_lit 15238730021930170474569649917

noncomputable def ep1318 := nat_lit 1383677950994529118568015177003911

noncomputable abbrev qz253 := (Complex.re qz508)

noncomputable abbrev qz254 := (Complex.im qz508)

noncomputable def ep1319 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1313 ep1314 ep1315 ep1316 ep1317 ep1304 ep1318

noncomputable def ep1320 := nat_lit 47810912230811356438540988974948671910382686699520000000

noncomputable def ep1321 := nat_lit 3457281247580340232604631433216

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 732377051 15000000 0 1 7866744070183791 590295810358705651712 19788002775854483551 ep1321 ep1313

noncomputable def ep1323 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 732377051 15000000 0 1 0 1 0 1 732377051

noncomputable def ep1324 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2197131153 62500 0 1 732377051 15000000 0

noncomputable abbrev qz512 := (@HAdd.hAdd Complex Complex Complex qz525 qz559 qz529)

noncomputable abbrev qz255 := qz512

noncomputable def ep1325 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1

noncomputable abbrev qz256 := (Complex.re qz512)

noncomputable abbrev qz257 := (Complex.im qz512)

noncomputable def ep1326 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 244115267 12500 0 1 488277409 31250 0 1

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 244115267 31250 0 1 5 2 0 1 244115267 12500

noncomputable abbrev qz513 := (@HAdd.hAdd Complex Complex Complex qz525 qz559 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz513

noncomputable def ep1328 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1

noncomputable abbrev qz259 := (Complex.re qz513)

noncomputable abbrev qz260 := (Complex.im qz513)

noncomputable def ep1329 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 488277409 62500 0 1

noncomputable def ep1330 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1331 := @ep1330 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1332 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz498 qz146) Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 88388 1000 1 qz147)

noncomputable abbrev qz514 := (ep1332 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz146 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz148))

noncomputable def ep1333 := ep1331 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz514)

noncomputable def ep1334 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 88388 1000 0 1 88388 1000 0 1 488277409 62500

noncomputable def ep1335 := @ep1334 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1336 := ep1335 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz514)

noncomputable def ep1337 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 (@ep1329 1952922136 244115267 31250 0 1 (ep1333 rfl) (ep1336 rfl) rfl rfl)

noncomputable def ep1338 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 22097 500 0 1 66291 500 0 1

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 88388 1000 0 1 22097 500

noncomputable def ep1340 := @ep1339 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1341 := ep1340 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz514)

noncomputable def ep1342 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 88388 1000 0 1 3 2 0 1 66291 500

noncomputable def ep1343 := @ep1342 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 88388 1000 0 1 ep1035)

noncomputable def ep1344 := ep1343 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 88388 1000 0 1 qz514)

noncomputable abbrev qz261 := (ep1328 (BSN.ascPochhammer_succ_eval_c 1 2 qz422 rfl) (ep1337 (@ep1338 44194000 22097 125 0 1 (ep1341 rfl) (ep1344 rfl) rfl rfl)))

noncomputable def ep1345 := @ep1327 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz261)

noncomputable def ep1346 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz500 qz146) Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 88388 1000 2 qz147)

noncomputable abbrev qz515 := (ep1346 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz146 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz148))

noncomputable def ep1347 := ep1345 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz515)

noncomputable def ep1348 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 22097 125 0 1 88388 1000 0 1 488277409 31250

noncomputable def ep1349 := @ep1348 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz261)

noncomputable def ep1350 := ep1349 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz515)

noncomputable def ep1351 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 (@ep1326 13732069706250 2197131153 62500 0 1 (ep1347 rfl) (ep1350 rfl) rfl rfl)

noncomputable def ep1352 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 5394215054899 7812500 0 1 22097 50 0 1

noncomputable def ep1353 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 244115267 31250 0 1 88388 1000 0 1 5394215054899 7812500

noncomputable def ep1354 := @ep1353 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz261)

noncomputable def ep1355 := ep1354 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz515)

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 22097 125 0 1 5 2 0 1 22097 50

noncomputable def ep1357 := @ep1356 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 244115267 31250 0 1 Bool.false 22097 125 0 1 qz261)

noncomputable def ep1358 := ep1357 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 88388 1000 0 1 qz515)

noncomputable abbrev qz262 := (ep1325 (BSN.ascPochhammer_succ_eval_c 2 3 qz422 rfl) (ep1351 (@ep1352 269538119932450 5390762398649 7812500 0 1 (ep1355 rfl) (ep1358 rfl) rfl rfl)))

noncomputable def ep1359 := @ep1324 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz262)

noncomputable def ep1360 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5390762398649 7812500 0 1 0 1 0

noncomputable def ep1361 := @ep1360 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz262)

noncomputable def ep1362 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) 5390762398649 5625000000 0 1 0 1 0 1 5390762398649

noncomputable def ep1363 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5390762398649 7812500 0 1 5390762398649 5625000000 0

noncomputable def ep1364 := @ep1363 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz262)

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2197131153 62500 0 1 0 1 0

noncomputable def ep1366 := @ep1365 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1163) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2197131153 62500 0 1 Bool.true 5390762398649 7812500 0 1 qz262)

noncomputable def ep1367 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 (@ep1323 732377051 15000000 0 1 (ep1359 rfl) (ep1361 rfl) rfl rfl) (@ep1362 5390762398649 5625000000 0 1 (ep1364 rfl) (ep1366 rfl) rfl rfl)

noncomputable def ep1368 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 ep1367

noncomputable def ep1369 := nat_lit 55316499961285443721674102931456

noncomputable def ep1370 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 7866744070183791 590295810358705651712 19788002775854483551 ep1321 Bool.true 25441405139974797 2361183241434822606848 256675744295704453439 ep1369

noncomputable abbrev qz516 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3404825447)))

noncomputable def ep1371 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz516 qz216) (@HMul.hMul Real Real Real qz0 qz516 qz480)) Bool.false 7866744070183791 590295810358705651712 19788002775854483551 ep1321 Bool.true 25441405139974797 2361183241434822606848 256675744295704453439

noncomputable abbrev qz517 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3404825447))

noncomputable abbrev qz518 := (@Nat.cast Real Real.instNatCast 3404825447)

noncomputable def ep1372 := @Enclosure.Real.IsNear.inv_image qz517 8019684176059419 137438953472 1 137438953472 1177693 1177694 68719476736 (@Enclosure.Real.IsNear.of_eq qz517 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz518 qz15)) Bool.false 8019684176059419 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 3404825447) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz518 qz15)) Bool.false 8019684176059419 137438953472 1 137438953472 8019684176059419 137438953472 1 137438953472 (BSN.sqrt_enclosure 3404825447 1 4009842088029709 4009842088029710 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1373 := nat_lit 1464215562312500000000000000

noncomputable def ep1374 := nat_lit 5856862249250000000000000

noncomputable def ep1375 := nat_lit 7763107665658486196323483648

noncomputable def ep1376 := nat_lit 23427448997000000000000000

noncomputable def ep1377 := nat_lit 38173642625234895562091333025

noncomputable def ep1378 := nat_lit 418040252652648286100516895

noncomputable def ep1379 := BSN.log_dyadic_bound 7 39 8 7 ep1377 68719476736 23427448997 ep1378 91651674949449615 24938675630 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 7) (BSN.artanhQ 39) 0 7 ep1378 ep1377 91651674949449615 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1380 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz483 88388 1000 0 1 3530252645604599 1125899906842624 250023427448997 ep1374 78007992709924824103 281474976710656000 5524767676340486709 ep1373 qz148 (BSN.isNear_log_sfrac 23 1 3530252645604599 1125899906842624 250023427448997 ep1374 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz482) Bool.false ep1375 ep1214 1000093709795988 ep1376 3530252645604599 1125899906842624 250023427448997 ep1374 (BSN.log_rat_reduce_isNear 23 1 4 46 32 24938675630 68719476736 24973259072661432 36028797018963968 23427448997 1000000000000000 rfl rfl rfl rfl (ep1379 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1381 := nat_lit 1683373743569156758210347008

noncomputable def ep1382 := nat_lit 1055023758371737820006808555397075724208797490587020991115177267179222550564023953442579669671675663131950432489681830228619710359269424620601006835718245567942774102699555428499456

noncomputable def ep1383 := nat_lit 118471658034259428782235204372444635462331972429639033257780066369387519461588934825569028614577116538889267969336012369372246813616988720376390556367654990461123310430062324062617600

noncomputable def ep1384 := nat_lit 2413730760889046641095353007285186369521824238713174869028120827033046381334023847663891406853336794006682977028106004662034948464899490313812175555470138873450685924376576

noncomputable def ep1385 := nat_lit 6399934754545590260319163696199364024298328901003064891145304357060812367010548703417093173235298317050893425501686588011615082141189287740129780553861882354638282878896705256816640

noncomputable def ep1386 := nat_lit 10780920881117608019183403597892461827072209491097152026457986039614264271004593069126781603926517605038923385209577125612874460039145973554251540629456604131962221249135671489698201600

noncomputable def ep1387 := BSN.cos_dyadic_bound_f 191377437609976 281474976710656 4 3 137438953472 46900654731 ep1382 ep1383 ep1384 ep1385 ep1386 ep1384 106876623776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 191377437609976) (BSN.cosEvenQ 281474976710656) 0 3 ep1382 ep1383 ep1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 191377437609976) (BSN.cosOddQ 281474976710656) 0 3 ep1385 ep1386 ep1384 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz519 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4761230023799) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1388 := @Enclosure.Real.IsNear.cos_image qz218 qz519 Bool.false 4761230023799 17179869184 65 17179869184 Bool.false 106876623776 137438953472 1 23427448997 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 78007992709924824103 281474976710656000 5524767676340486709 ep1373 4761230023799 17179869184 65 17179869184 (ep1380 rfl) rfl) (Enclosure.sfrac_false_div 4761230023799 17179869184) (BSN.cos_reduce0 qz519 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1381) (@Nat.cast Real Real.instNatCast ep1214)) 226375608064910080 72057594037927936 Bool.false 106876623776 137438953472 44 1000000000000000 46854897994 23427448997 (BSN.sin_reduce_arg_pos_rat_q0 4761230023799 17179869184 226375608064910080 72057594037927936 44 ep1381 ep1214 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 106876623776 137438953472 ep1381 ep1214 191377437609976 281474976710656 46900654731 46854897994 (ep1387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1389 := nat_lit 25464466723487993371802906475870798486202561068014493320511382901428700529570088038776702681606561726005511313455841280

noncomputable def ep1390 := nat_lit 1799392406663595049494920059672388709745750881913104637617049014751729186837649661972967357583064117491516022194176

noncomputable def ep1391 := nat_lit 66689737640476813010356048994803097882143309676705337479545099043432236682571541049724360314200146226205162414062698496

noncomputable def ep1392 := BSN.sin_dyadic_bound_f 191377437609976 281474976710656 3 2 137438953472 46900654731 ep1389 ep1221 ep1390 ep1391 ep1224 ep1390 86410955448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 191377437609976) (BSN.sinEvenQ 281474976710656) 0 2 ep1389 ep1221 ep1390 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 191377437609976) (BSN.sinOddQ 281474976710656) 0 2 ep1391 ep1224 ep1390 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1393 := @Enclosure.Real.IsNear.sin_image qz218 qz519 Bool.false 4761230023799 17179869184 65 17179869184 Bool.false 86410955448 137438953472 1 23427448997 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 78007992709924824103 281474976710656000 5524767676340486709 ep1373 4761230023799 17179869184 65 17179869184 (ep1380 rfl) rfl) (Enclosure.sfrac_false_div 4761230023799 17179869184) (BSN.sin_reduce0 qz519 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1381) (@Nat.cast Real Real.instNatCast ep1214)) 226375608064910080 72057594037927936 Bool.false 86410955448 137438953472 44 1000000000000000 46854897994 23427448997 (BSN.sin_reduce_arg_pos_rat_q0 4761230023799 17179869184 226375608064910080 72057594037927936 44 ep1381 ep1214 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 86410955448 137438953472 ep1381 ep1214 191377437609976 281474976710656 46900654731 46854897994 (ep1392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1394 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz516 qz216) (@HMul.hMul Real Real Real qz0 qz516 qz480) Bool.false 7866744070183791 590295810358705651712 19788002775854483551 ep1321 Bool.true 25441405139974797 2361183241434822606848 256675744295704453439 ep1369 (@Enclosure.Real.IsNear.mulLit_ff qz516 qz216 2355387 137438953472 1 137438953472 3339894493 4294967296 1539964053989 402480509083292008448 7866744070183791 590295810358705651712 19788002775854483551 ep1321 (@Enclosure.Real.IsNear.recentre' qz516 Bool.false 2355387 137438953472 1 137438953472 2355387 137438953472 1 137438953472 (ep1372 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 106876623776 137438953472 1539964053989 402480509083292008448 3339894493 4294967296 1539964053989 402480509083292008448 (ep1388 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz516 qz480 2355387 137438953472 1 137438953472 10801369431 17179869184 1539964053989 402480509083292008448 25441405139974797 2361183241434822606848 256675744295704453439 ep1369 (@Enclosure.Real.IsNear.recentre' qz516 Bool.false 2355387 137438953472 1 137438953472 2355387 137438953472 1 137438953472 (ep1372 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 10801369431 17179869184 1539964053989 402480509083292008448 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 86410955448 137438953472 1539964053989 402480509083292008448 10801369431 17179869184 1539964053989 402480509083292008448 (ep1393 rfl rfl) rfl)) rfl)

noncomputable def ep1395 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 5390762398649 5625000000 0 1 25441405139974797 2361183241434822606848 256675744295704453439 ep1369 ep1317

noncomputable def ep1396 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 732377051 15000000 0 1 Bool.false 5390762398649 5625000000 0 1 ep1367

noncomputable def ep1397 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 7866744070183791 590295810358705651712 19788002775854483551 ep1321 Bool.true 25441405139974797 2361183241434822606848 256675744295704453439 ep1369

noncomputable def ep1398 := nat_lit 6210900423236994680394549

noncomputable def ep1399 := nat_lit 11805916207174113034240000000

noncomputable def ep1400 := nat_lit 187983424670518099577221628389

noncomputable def ep1401 := nat_lit 829747499419281655825111543971840000000

noncomputable def ep1402 := nat_lit 14135916044447256791146699453

noncomputable def ep1403 := nat_lit 1106804644422573096960000000000

noncomputable def ep1404 := nat_lit 106672421308438386047969875122599

noncomputable def ep1405 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1398 ep1399 ep1400 ep1401 ep1402 ep1403 ep1404

noncomputable def ep1406 := nat_lit 19447207017639413808401051811840000000000

noncomputable def ep1407 := nat_lit 160013186897907617889928829594658806616090707230720000000

noncomputable def ep1408 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 732377051 15000000 0 1 25441405139974797 2361183241434822606848 256675744295704453439 ep1369 ep1398

noncomputable def ep1409 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 5390762398649 5625000000 0 1 7866744070183791 590295810358705651712 19788002775854483551 ep1321 ep1402

noncomputable abbrev qz520 := (@ep1371 ep1369 (BSN.cpow_neg_s_sub_mk qz146 88388 1000 23 3 3404825447 qz147 rfl EMRow24.d20) ep1394)

noncomputable def ep1410 := ep1312 (@ep1319 ep1306 ep1320 ep1303 ep1304 ep1305 ep1306 (@ep1322 ep1314 ep1315 ep1316 ep1368 (ep1370 qz520) rfl) (@ep1395 ep1304 ep1318 ep1306 ep1396 (ep1397 qz520) rfl) rfl rfl) (@ep1405 ep1406 ep1407 ep1308 ep1309 ep1310 ep1306 (@ep1408 ep1399 ep1400 ep1401 ep1368 (ep1397 qz520) rfl) (@ep1409 ep1403 ep1404 ep1406 ep1396 (ep1370 qz520) rfl) rfl rfl)

noncomputable def ep1411 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1308 ep1309 ep1310 ep1306 ep1308 ep1309 ep1310

noncomputable def ep1412 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1303 ep1304 ep1305 ep1306 Bool.false ep1308 ep1309 ep1310

noncomputable def ep1413 := @ep1274 104822925067503745 252201579132747776 49518481631 252201579132747776 (@ep1275 1 1835008 (ep1276 (@ep1277 524288 1 524288 (ep1278 (@ep1279 1956172136 244521517 31250 0 1 (ep1283 rfl) (ep1286 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1287 1019 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1288 1019 137438953472 2260230997 137438953472 1019 137438953472 (@ep1293 1130114989 1130116008 68719476736 (@ep1299 ep1300 ep1301 ep1297 ep1302 ep1289 ep1290 ep1291 ep1292 (@ep1307 ep1306 ep1294 ep1295 ep1296 ep1297 (@ep1311 ep1306 ep1410) (@ep1311 ep1306 ep1410) rfl) (@ep1411 ep1306 ep1298 ep1300 ep1301 ep1297 (@ep1412 ep1306 ep1410) (@ep1412 ep1306 ep1410) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow24.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 107185652184336513 252201579132747776 821939247105925 6809442636584189952 := ep1272 (ep1273 ep1413) rfl rfl

noncomputable def EMRow24.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz521 := (EMRow24.d3 qz530 qz561 (@Enclosure.dec_le_dec qz530 qz561 85999 1000 88388 1000 (@Eq.refl Real qz530) (@Eq.refl Real qz561) rfl rfl rfl) 22 23 1 1)

noncomputable abbrev qz263 := qz521

noncomputable def ep1414 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz13 85999 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 22 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz521)

noncomputable def ep1415 := @Enclosure.Real.IsNear.pos_val qz264 ep264 ep265

noncomputable def ep1416 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 22 qz13) Bool.false

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz521)

noncomputable def ep1417 := BSN.mul_neg_of_pos_neg_r qz264 qz265 (@ep1415 ep266 ep267 (@ep1416 ep264 ep265 ep266 ep267 (@Eq.refl Real (hardyZApproximantEM 1 22 qz13)) EMRow24.d10) rfl rfl rfl)

noncomputable def ep1418 := @Enclosure.Real.IsNear.neg_val qz265 ep775 ep776

noncomputable def ep1419 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 23 qz146) Bool.true

noncomputable def ep1420 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 22 qz13)

noncomputable def ep1421 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 22 qz13) Bool.false

noncomputable def ep1422 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 22 qz13) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 50164969810294955 108086391056891904 12157295296693 108086391056891904 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 22))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1423 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 23 qz146)

noncomputable def ep1424 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 23 qz146) Bool.true

noncomputable def ep1425 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 23 qz146) (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 107185652184336513 252201579132747776 821939247105925 6809442636584189952 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz382 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz143 1 23))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz143 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1426 := @List.cons EMRow24.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1414 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 23 rfl) (ep1417 (@ep1418 ep777 ep778 (@ep1419 ep775 ep776 ep777 ep778 (@Eq.refl Real (hardyZApproximantEM 1 23 qz146)) EMRow24.d14) rfl rfl rfl)) (ep1420 (hardyZErrorBoundEM 1 22 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 22 qz13 rfl) (@ep1421 Bool.false ep264 ep265 ep266 ep267 50164969810294955 108086391056891904 12157295296693 108086391056891904 (@ep1416 ep264 ep265 ep266 ep267 (@Eq.refl Real (hardyZApproximantEM 1 22 qz13)) EMRow24.d10) (ep1422 EMRow24.d19) rfl rfl rfl rfl rfl)) (ep1423 (hardyZErrorBoundEM 1 23 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 23 qz146 rfl) (@ep1424 Bool.false ep775 ep776 ep777 ep778 107185652184336513 252201579132747776 821939247105925 6809442636584189952 (@ep1419 ep775 ep776 ep777 ep778 (@Eq.refl Real (hardyZApproximantEM 1 23 qz146)) EMRow24.d14) (ep1425 EMRow24.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow24.d0)

noncomputable abbrev qz522 := (@Enclosure.dec_le_dec qz530 qz561 85999 1000 88388 1000 (@Eq.refl Real qz530) (@Eq.refl Real qz561) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1426 (@List.IsChain.singleton EMRow24.d1 EMRow24.d22 (EMRow24.d2 qz286 qz429 qz522))))

noncomputable abbrev qz523 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1427 := And (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 qz266)) (@Option.some Real qz13))

noncomputable def ep1428 := ep1427 (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 qz266)) (@Option.some Real qz146))

noncomputable def ep1429 := @And.intro (@Eq Nat (@List.length qz523 qz266) 1) ep1428

noncomputable def ep1430 := @And.intro (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 qz266)) (@Option.some Real qz13))

noncomputable def ep1431 := @ep1430 (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 qz266)) (@Option.some Real qz146))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1426 (@List.IsChain.singleton EMRow24.d1 EMRow24.d22 (EMRow24.d2 qz286 qz429 qz522)))

theorem EMRow24.d23 : Zeta.Certificates.BatchSpec 1 85999 1000 88388 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz523 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz523 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz267 (ep1429 (@Eq.refl Nat 1) (ep1431 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 85999 1000 88388 1000 := EMRow24.d23
#print axioms solution
#check solution
