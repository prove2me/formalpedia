-- Prove2me | solution 1 for RHHeight1000.em_main_0033_0033
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:34:54.183866+00:00
-- url     : https://prove2.me/submissions/79e3a14c-f53d-4747-8ff5-c75e74bd75ad

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow33.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow33.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow33.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow33.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow33.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000067873 33936500000000000000 4138529546116343 2251799813685248 125000000067873 33936500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 271492 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000542984 271492000000000000000 4138529546116343 2251799813685248 125000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 271492 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000542984 271492000000000000000 4138529546116343 2251799813685248 125000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi))

theorem EMRow33.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 271492 1200336 1048576 1 271492 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 271492 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 271492 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 271492 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 271492 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 271492 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 271492 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow33.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz600 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 106726 1000)))

noncomputable abbrev qz537 := qz600

noncomputable abbrev qz272 := qz537

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz601 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz538 := qz601

noncomputable abbrev qz273 := qz538

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz539 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz539

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz540 := (@Neg.neg Complex Complex.instNeg qz600)

noncomputable abbrev qz275 := qz540

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz276 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7)) Bool.true 92419032371 1099511627776 200206605985311 74627152712040448 Bool.false 384530863073 1099511627776 200217661818281 74627152712040448

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) Bool.false 2376101201 34359738368 89598618401853 37313576356020224 Bool.false 734870843889 1099511627776 179174992853289 74627152712040448 Bool.true

noncomputable abbrev qz277 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7)) Bool.false 2376101201 34359738368 89598618401853 37313576356020224 Bool.false 734870843889 1099511627776 179174992853289 74627152712040448

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) Bool.true 158293646709 549755813888 39175736382359 18656788178010112 Bool.false 871075063989 1099511627776 156724614731289 74627152712040448 Bool.false

noncomputable abbrev qz278 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7)) Bool.true 158293646709 549755813888 39175736382359 18656788178010112 Bool.false 871075063989 1099511627776 156724614731289 74627152712040448

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) Bool.false 95095852803 1099511627776 10185672610333 5740550208618496 Bool.false 1049971846563 1099511627776 10190178615267 5740550208618496 Bool.true

noncomputable abbrev qz279 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7)) Bool.false 95095852803 1099511627776 10185672610333 5740550208618496 Bool.false 1049971846563 1099511627776 10190178615267 5740550208618496

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) Bool.false 352893030679 1099511627776 105872283501131 74627152712040448 Bool.false 183586239287 137438953472 1654805784355 1166049261125632 Bool.true

noncomputable abbrev qz280 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz7)) Bool.false 352893030679 1099511627776 105872283501131 74627152712040448 Bool.false 183586239287 137438953472 1654805784355 1166049261125632

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz7) Bool.false 878305150581 1099511627776 5859366339533 5740550208618496 Bool.false 81681982705 68719476736 733212733953 717568776077312 Bool.true

noncomputable abbrev qz541 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz541

noncomputable abbrev qz8 := qz281

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 878305150581 1099511627776 5859366339533 5740550208618496 Bool.false 81681982705 68719476736 733212733953 717568776077312

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 607557421323 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 1099511627776 41977110834215 74627152712040448 Bool.true

noncomputable def ep50 := nat_lit 1436964636223130073825280

noncomputable abbrev qz542 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz542

noncomputable abbrev qz9 := qz282

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 607557421323 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 1099511627776 41977110834215 74627152712040448

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz283

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz543 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz543))

noncomputable abbrev qz602 := (Enclosure.sfrac Bool.false 106726 1000)

noncomputable abbrev qz544 := qz602

noncomputable abbrev qz284 := qz544

noncomputable abbrev qz285 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz268 qz284 (Real.log qz285))

noncomputable abbrev qz13 := qz284

noncomputable abbrev qz286 := (@Eq.refl Real qz544)

noncomputable abbrev qz14 := qz286

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.false 57801607435 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 1099511627776 41977110834215 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz543) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz543) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 135746 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz287 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz288 := (BSN.sinOddQ 2147483648)

noncomputable def ep57 := BSN.sin_dyadic_bound_f 320502843 2147483648 1 0 1048576 271758 0 1 1 0 1 1 155914 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 320502843) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 320502843) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz17 := (Real.log qz285)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 106726 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19392541) qz16)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 135746 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 135746 rfl rfl rfl (ep56 rfl)))

noncomputable def ep58 := @Enclosure.Real.IsNear.cos_image qz12 qz289 Bool.false 19392541 262144 825 1048576 Bool.false 155914 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1212033819 16384000 53363 67873000 19392541 262144 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 106726 1000 0 1 363408 524288 1 135746 1212033819 16384000 53363 67873000 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 19392541 262144) (BSN.cos_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5638345657060071309312) qz19) 226375608064910080 72057594037927936 Bool.false 155914 1048576 11 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 19392541 262144 226375608064910080 72057594037927936 11 5638345657060071309312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 155914 1048576 5638345657060071309312 37778931862957161709568 320502843 2147483648 271758 271492 (ep57 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep59 := nat_lit 10551824152209941314759788388857201

noncomputable def ep60 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep61 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz291 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz292 := (BSN.cosOddQ 2147483648)

noncomputable def ep62 := BSN.cos_dyadic_bound_f 320502843 2147483648 2 1 1048576 271758 ep59 ep60 ep59 ep59 ep61 ep59 1036919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320502843) qz291 0 1 ep59 ep60 ep59 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320502843) qz292 0 1 ep59 ep61 ep59 rfl rfl rfl rfl) rfl rfl

noncomputable def ep63 := @Enclosure.Real.IsNear.sin_image qz12 qz289 Bool.false 19392541 262144 825 1048576 Bool.true 1036919 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 1212033819 16384000 53363 67873000 19392541 262144 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 106726 1000 0 1 363408 524288 1 135746 1212033819 16384000 53363 67873000 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 19392541 262144) (BSN.sin_reduce3 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5638345657060071309312) qz19) 226375608064910080 72057594037927936 Bool.false 1036919 1048576 11 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 19392541 262144 226375608064910080 72057594037927936 11 5638345657060071309312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036919 1048576 5638345657060071309312 37778931862957161709568 320502843 2147483648 271758 271492 (ep62 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep64 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.false 57801607435 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 1099511627776 41977110834215 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz12) 741455 1048576 1 1048576 77957 524288 56519513 71169998848 57801607435 549755813888 20958657190925 37313576356020224 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.false 155914 1048576 113039026 142339997696 77957 524288 56519513 71169998848 (ep58 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 1036919 1048576 56519513 71169998848 768828777145 1099511627776 41977110834215 74627152712040448 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 1036919 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 1036919 1048576 113039026 142339997696 1036919 1048576 56519513 71169998848 (ep63 rfl rfl) rfl)) rfl)

noncomputable abbrev qz294 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz20 := qz294

noncomputable def ep65 := @ep52 57801607435 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 1099511627776 41977110834215 74627152712040448 Bool.false 607557421323 607557421323 549755813888 20958657190925 37313576356020224 Bool.false 768828777145 768828777145 1099511627776 41977110834215 74627152712040448 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep54 ep64) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz268 qz284 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep66 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.true 336809692065 1099511627776 34254448032079 74627152712040448 Bool.false 538082946135 1099511627776 34277013496897 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 3 qz14 rfl)

noncomputable def ep67 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep68 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 135746 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep69 := nat_lit 796000690880680567213874814482592738303871055861483198746819888950870851748096

noncomputable def ep70 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep71 := nat_lit 495710727647335133296505704122213988391734565662625715803694935527199375616

noncomputable def ep72 := nat_lit 2387010651186747031375031432039533786934829698453124344808852276981558156493056

noncomputable def ep73 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep74 := BSN.cos_dyadic_bound_f 2172218658 2147483648 3 2 1048576 271758 ep69 ep70 ep71 ep72 ep73 ep71 556347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2172218658) qz291 0 2 ep69 ep70 ep71 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2172218658) qz292 0 2 ep72 ep73 ep71 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30736501) qz16)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 135746 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 135746 rfl rfl rfl (ep68 rfl)))

noncomputable def ep75 := @Enclosure.Real.IsNear.cos_image qz22 qz296 Bool.false 30736501 262144 825 1048576 Bool.true 556347 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 30736501007 262144000 53363 67873000 30736501 262144 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 106726 1000 0 1 575989 524288 1 135746 30736501007 262144000 53363 67873000 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 30736501 262144) (BSN.cos_reduce2 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38214074766715772731392) qz19) 226375608064910080 72057594037927936 Bool.false 556347 1048576 18 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 30736501 262144 226375608064910080 72057594037927936 18 38214074766715772731392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 556347 1048576 38214074766715772731392 37778931862957161709568 2172218658 2147483648 271758 271492 (ep74 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep76 := nat_lit 1432404675003107152878337461505369157756254512898139657171632844163145773646080

noncomputable def ep77 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep78 := nat_lit 3750733474306232572084594247088340400047079963531673898576308609579290131988736

noncomputable def ep79 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep80 := BSN.sin_dyadic_bound_f 2172218658 2147483648 3 2 1048576 271758 ep76 ep77 ep71 ep78 ep79 ep71 888813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2172218658) qz287 0 2 ep76 ep77 ep71 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2172218658) qz288 0 2 ep78 ep79 ep71 rfl rfl rfl rfl) rfl rfl

noncomputable def ep81 := @Enclosure.Real.IsNear.sin_image qz22 qz296 Bool.false 30736501 262144 825 1048576 Bool.true 888813 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 30736501007 262144000 53363 67873000 30736501 262144 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 106726 1000 0 1 575989 524288 1 135746 30736501007 262144000 53363 67873000 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 30736501 262144) (BSN.sin_reduce2 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38214074766715772731392) qz19) 226375608064910080 72057594037927936 Bool.false 888813 1048576 18 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 30736501 262144 226375608064910080 72057594037927936 18 38214074766715772731392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 888813 1048576 38214074766715772731392 37778931862957161709568 2172218658 2147483648 271758 271492 (ep80 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep67 rfl rfl) rfl)

noncomputable def ep82 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.true 336809692065 1099511627776 34254448032079 74627152712040448 Bool.false 538082946135 1099511627776 34277013496897 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz21 (Real.cos qz22) 605395 1048576 1 1048576 556347 1048576 56519513 71169998848 336809692065 1099511627776 34254448032079 74627152712040448 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.true 556347 1048576 113039026 142339997696 556347 1048576 56519513 71169998848 (ep75 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 888813 1048576 56519513 71169998848 538082946135 1099511627776 34277013496897 74627152712040448 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.true 888813 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.true 888813 1048576 113039026 142339997696 888813 1048576 56519513 71169998848 (ep81 rfl rfl) rfl)) rfl)

noncomputable def ep83 := @ep49 336809692065 1099511627776 34254448032079 74627152712040448 Bool.false 538082946135 1099511627776 34277013496897 74627152712040448 Bool.false 482853362899680051068928 878305150581 1099511627776 5859366339533 5740550208618496 Bool.false ep50 81681982705 68719476736 733212733953 717568776077312 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep65 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep66 ep82) rfl rfl

noncomputable abbrev qz545 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz545))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz268 qz284 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep84 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz280 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.true 262706059951 549755813888 14850260543601 37313576356020224 Bool.false 20222273877 137438953472 3706680733451 9328394089005056 (BSN.cpow_neg_s_mk qz13 106726 1000 4 qz14 rfl)

noncomputable def ep85 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz545) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz545) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep86 := nat_lit 318077276165597140789031982421875

noncomputable def ep87 := nat_lit 49379992292270016474244603430625

noncomputable def ep88 := nat_lit 20095619060363156210525625

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 14 13 ep86 524288 135746 ep87 ep88 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep87 ep86 ep88 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 169291392603310122849858389851129761

noncomputable def ep91 := BSN.cos_dyadic_bound_f 641443959 2147483648 2 1 1048576 271758 ep90 ep60 ep90 ep90 ep61 ep90 1002146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 641443959) qz291 0 1 ep90 ep60 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 641443959) qz292 0 1 ep90 ep61 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77570271) qz26)

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 135746 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 135746 rfl rfl rfl (ep89 rfl)))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz25 qz299 Bool.false 77570271 524288 825 1048576 Bool.true 1002146 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 38785135571 262144000 53363 67873000 77570271 524288 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 106726 1000 0 1 726817 524288 1 135746 38785135571 262144000 53363 67873000 qz18 qz300 rfl) rfl) (Enclosure.sfrac_false_div 77570271 524288) (BSN.cos_reduce2 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22568802953364401815552) qz301) 226375608064910080 72057594037927936 Bool.false 1002146 1048576 23 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 77570271 524288 226375608064910080 72057594037927936 23 22568802953364401815552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002146 1048576 22568802953364401815552 75557863725914323419136 641443959 2147483648 271758 271492 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep94 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep95 := BSN.sin_dyadic_bound_f 641443959 2147483648 2 1 1048576 271758 ep90 ep93 ep90 ep90 ep94 ep90 308568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 641443959) qz287 0 1 ep90 ep93 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 641443959) qz288 0 1 ep90 ep94 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable def ep96 := @Enclosure.Real.IsNear.sin_image qz25 qz299 Bool.false 77570271 524288 825 1048576 Bool.true 308568 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 38785135571 262144000 53363 67873000 77570271 524288 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 106726 1000 0 1 726817 524288 1 135746 38785135571 262144000 53363 67873000 qz18 qz300 rfl) rfl) (Enclosure.sfrac_false_div 77570271 524288) (BSN.sin_reduce2 qz299 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22568802953364401815552) qz301) 226375608064910080 72057594037927936 Bool.false 308568 1048576 23 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 77570271 524288 226375608064910080 72057594037927936 23 22568802953364401815552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 308568 1048576 22568802953364401815552 75557863725914323419136 641443959 2147483648 271758 271492 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep85 rfl rfl) rfl)

noncomputable def ep97 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.true 262706059951 549755813888 14850260543601 37313576356020224 Bool.false 20222273877 137438953472 3706680733451 9328394089005056 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz25) 524287 1048576 1 1048576 501073 524288 56519513 71169998848 262706059951 549755813888 14850260543601 37313576356020224 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.true 1002146 1048576 113039026 142339997696 501073 524288 56519513 71169998848 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 38571 131072 56519513 71169998848 20222273877 137438953472 3706680733451 9328394089005056 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 38571 131072 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 308568 1048576 113039026 142339997696 38571 131072 56519513 71169998848 (ep96 rfl rfl) rfl)) rfl)

noncomputable def ep98 := @ep47 262706059951 549755813888 14850260543601 37313576356020224 Bool.false 20222273877 137438953472 3706680733451 9328394089005056 Bool.false 194004995296336598269952 352893030679 1099511627776 105872283501131 74627152712040448 Bool.false 12615950299732725727232 183586239287 137438953472 1654805784355 1166049261125632 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep83 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep84 ep97) rfl rfl

noncomputable abbrev qz546 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz546))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz284 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep99 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 64449294469 274877906944 13270730216599 37313576356020224 Bool.true 418718067733 1099511627776 26564751799751 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 5 qz14 rfl)

noncomputable def ep100 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz546) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz546) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz546 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz546 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep101 := nat_lit 11734546589655452485523914939250625

noncomputable def ep102 := nat_lit 2429970938528035899633153341031900

noncomputable def ep103 := nat_lit 824199001261152424427520000

noncomputable def ep104 := BSN.log_dyadic_bound 2 3 17 16 ep101 524288 135746 ep102 ep103 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep102 ep101 ep103 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep105 := nat_lit 1972731859619046091346532692899001761

noncomputable def ep106 := BSN.sin_dyadic_bound_f 1185132791 2147483648 2 1 1048576 271758 ep105 ep93 ep105 ep105 ep94 ep105 549748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1185132791) qz287 0 1 ep105 ep93 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1185132791) qz288 0 1 ep105 ep94 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz31 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180112505) qz30)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 135746 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 135746 rfl rfl rfl (ep104 rfl)))

noncomputable def ep107 := @Enclosure.Real.IsNear.cos_image qz29 qz303 Bool.false 180112505 1048576 825 1048576 Bool.true 549748 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1407128947 8192000 53363 67873000 180112505 1048576 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz31 106726 1000 0 1 843808 524288 1 135746 1407128947 8192000 53363 67873000 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 180112505 1048576) (BSN.cos_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83396306240975551856640) qz32) 226375608064910080 72057594037927936 Bool.false 549748 1048576 27 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 180112505 1048576 226375608064910080 72057594037927936 27 83396306240975551856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 549748 1048576 83396306240975551856640 151115727451828646838272 1185132791 2147483648 271758 271492 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep108 := BSN.cos_dyadic_bound_f 1185132791 2147483648 2 1 1048576 271758 ep105 ep60 ep105 ep105 ep61 ep105 892909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1185132791) qz291 0 1 ep105 ep60 ep105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1185132791) qz292 0 1 ep105 ep61 ep105 rfl rfl rfl rfl) rfl rfl

noncomputable def ep109 := @Enclosure.Real.IsNear.sin_image qz29 qz303 Bool.false 180112505 1048576 825 1048576 Bool.false 892909 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1407128947 8192000 53363 67873000 180112505 1048576 825 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz31 106726 1000 0 1 843808 524288 1 135746 1407128947 8192000 53363 67873000 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 180112505 1048576) (BSN.sin_reduce1 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83396306240975551856640) qz32) 226375608064910080 72057594037927936 Bool.false 892909 1048576 27 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 180112505 1048576 226375608064910080 72057594037927936 27 83396306240975551856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892909 1048576 83396306240975551856640 151115727451828646838272 1185132791 2147483648 271758 271492 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep100 rfl rfl) rfl)

noncomputable def ep110 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 64449294469 274877906944 13270730216599 37313576356020224 Bool.true 418718067733 1099511627776 26564751799751 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 468937 1048576 1 1048576 137437 262144 56519513 71169998848 64449294469 274877906944 13270730216599 37313576356020224 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 549748 1048576 113039026 142339997696 137437 262144 56519513 71169998848 (ep107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 892909 1048576 56519513 71169998848 418718067733 1099511627776 26564751799751 74627152712040448 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 892909 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 892909 1048576 113039026 142339997696 892909 1048576 56519513 71169998848 (ep109 rfl rfl) rfl)) rfl)

noncomputable def ep111 := @ep45 64449294469 274877906944 13270730216599 37313576356020224 Bool.true 418718067733 1099511627776 26564751799751 74627152712040448 Bool.false 26139748977543355564032 95095852803 1099511627776 10185672610333 5740550208618496 Bool.false 144307031766682080116736 1049971846563 1099511627776 10190178615267 5740550208618496 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep98 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep99 ep110) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz306))

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz268 qz284 qz547)

noncomputable def ep112 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.true 411683146221 1099511627776 24289201595107 74627152712040448 Bool.true 89448391287 549755813888 12126146366409 37313576356020224 (BSN.cpow_neg_s_mk qz13 106726 1000 6 qz14 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep113 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz306) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz306) (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep114 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 135746 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep115 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz547 106726 1000 0 1 4034681531866359 2251799813685248 250000000067873 33936500000000000000 215302710584984515317 1125899906842624000 13340750003621906899 16968250000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000271492 135746000000000000000 4034681531866359 2251799813685248 250000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep116 := nat_lit 2485468741480888372975574793302561432243098416345912193951556829616694766240000

noncomputable def ep117 := nat_lit 1491738310280217047863467391111003163951877450435302761497689330192100000000

noncomputable def ep118 := nat_lit 6507145794233301577810916940016338317418859479319541446354509723413889559200000

noncomputable def ep119 := BSN.sin_dyadic_bound_f 2492938590 2147483648 3 2 1048576 271758 ep116 ep77 ep117 ep118 ep79 ep117 961699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2492938590) qz287 0 2 ep116 ep77 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2492938590) qz288 0 2 ep118 ep79 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100258137) qz26)

noncomputable def ep120 := @Enclosure.Real.IsNear.cos_image qz34 qz308 Bool.false 100258137 524288 413 524288 Bool.true 961699 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 215302710584984515317 1125899906842624000 13340750003621906899 16968250000000000000000 100258137 524288 413 524288 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 100258137 524288) (BSN.cos_reduce1 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87712478952519708442624) qz301) 226375608064910080 72057594037927936 Bool.false 961699 1048576 30 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 100258137 524288 226375608064910080 72057594037927936 30 87712478952519708442624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 961699 1048576 87712478952519708442624 75557863725914323419136 2492938590 2147483648 271758 271492 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep121 := nat_lit 1381478962293951414785480870675250130430144399059033575644863878378249136800000

noncomputable def ep122 := nat_lit 4141453410261293810260715677243528384962529442276230121411596256474363210400000

noncomputable def ep123 := BSN.cos_dyadic_bound_f 2492938590 2147483648 3 2 1048576 271758 ep121 ep70 ep117 ep122 ep73 ep117 417906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2492938590) qz291 0 2 ep121 ep70 ep117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2492938590) qz292 0 2 ep122 ep73 ep117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.sin_image qz34 qz308 Bool.false 100258137 524288 413 524288 Bool.false 417906 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 215302710584984515317 1125899906842624000 13340750003621906899 16968250000000000000000 100258137 524288 413 524288 (ep115 rfl) rfl) (Enclosure.sfrac_false_div 100258137 524288) (BSN.sin_reduce1 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87712478952519708442624) qz301) 226375608064910080 72057594037927936 Bool.false 417906 1048576 30 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 100258137 524288 226375608064910080 72057594037927936 30 87712478952519708442624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 417906 1048576 87712478952519708442624 75557863725914323419136 2492938590 2147483648 271758 271492 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep113 rfl rfl) rfl)

noncomputable def ep125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.true 411683146221 1099511627776 24289201595107 74627152712040448 Bool.true 89448391287 549755813888 12126146366409 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz34) 428079 1048576 1 1048576 961699 1048576 28293693 35584999424 411683146221 1099511627776 24289201595107 74627152712040448 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.true 961699 1048576 56587386 71169998848 961699 1048576 28293693 35584999424 (ep120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 428079 1048576 1 1048576 208953 524288 28293693 35584999424 89448391287 549755813888 12126146366409 37313576356020224 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 208953 524288 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 417906 1048576 56587386 71169998848 208953 524288 28293693 35584999424 (ep124 rfl rfl) rfl)) rfl)

noncomputable def ep126 := @ep43 411683146221 1099511627776 24289201595107 74627152712040448 Bool.true 89448391287 549755813888 12126146366409 37313576356020224 Bool.true 348091410319223310778368 158293646709 549755813888 39175736382359 18656788178010112 Bool.false 478878580760814374879232 871075063989 1099511627776 156724614731289 74627152712040448 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep111 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep112 ep125) rfl rfl

noncomputable abbrev qz310 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt qz310))

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz268 qz284 qz548)

noncomputable def ep127 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.false 196311265925 549755813888 11247145637135 37313576356020224 Bool.true 34051055025 274877906944 1403148632625 4664197044502528 (BSN.cpow_neg_s_mk qz13 106726 1000 7 qz14 rfl)

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz310) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz310) (Real.sqrt qz311) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz311) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep129 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 135746 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz548 106726 1000 0 1 4381796493761783 2251799813685248 250000000067873 33936500000000000000 233825806296610026229 1125899906842624000 13340750003621906899 16968250000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 36757173121942042968064 18889465931478580854784 1000000000271492 135746000000000000000 4381796493761783 2251799813685248 250000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep131 := nat_lit 264414023822388810687894386436614416

noncomputable def ep132 := BSN.cos_dyadic_bound_f 717085798 2147483648 2 1 1048576 271758 ep131 ep60 ep131 ep131 ep61 ep131 990658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 717085798) qz291 0 1 ep131 ep60 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 717085798) qz292 0 1 ep131 ep61 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217767251) qz30)

noncomputable def ep133 := @Enclosure.Real.IsNear.cos_image qz36 qz312 Bool.false 217767251 1048576 413 524288 Bool.false 990658 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 233825806296610026229 1125899906842624000 13340750003621906899 16968250000000000000000 217767251 1048576 413 524288 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 217767251 1048576) (BSN.cos_reduce0 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50460427127320647565312) qz32) 226375608064910080 72057594037927936 Bool.false 990658 1048576 33 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 217767251 1048576 226375608064910080 72057594037927936 33 50460427127320647565312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 990658 1048576 50460427127320647565312 151115727451828646838272 717085798 2147483648 271758 271492 (ep132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep134 := BSN.sin_dyadic_bound_f 717085798 2147483648 2 1 1048576 271758 ep131 ep93 ep131 ep131 ep94 ep131 343668 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 717085798) qz287 0 1 ep131 ep93 ep131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 717085798) qz288 0 1 ep131 ep94 ep131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.sin_image qz36 qz312 Bool.false 217767251 1048576 413 524288 Bool.false 343668 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 233825806296610026229 1125899906842624000 13340750003621906899 16968250000000000000000 217767251 1048576 413 524288 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 217767251 1048576) (BSN.sin_reduce0 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50460427127320647565312) qz32) 226375608064910080 72057594037927936 Bool.false 343668 1048576 33 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 217767251 1048576 226375608064910080 72057594037927936 33 50460427127320647565312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343668 1048576 50460427127320647565312 151115727451828646838272 717085798 2147483648 271758 271492 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep128 rfl rfl) rfl)

noncomputable def ep136 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.false 196311265925 549755813888 11247145637135 37313576356020224 Bool.true 34051055025 274877906944 1403148632625 4664197044502528 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz36) 396325 1048576 1 1048576 495329 524288 28293693 35584999424 196311265925 549755813888 11247145637135 37313576356020224 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 990658 1048576 56587386 71169998848 495329 524288 28293693 35584999424 (ep133 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 396325 1048576 1 1048576 85917 262144 28293693 35584999424 34051055025 274877906944 1403148632625 4664197044502528 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.false 85917 262144 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.false 343668 1048576 56587386 71169998848 85917 262144 28293693 35584999424 (ep135 rfl rfl) rfl)) rfl)

noncomputable def ep137 := @ep41 196311265925 549755813888 11247145637135 37313576356020224 Bool.true 34051055025 274877906944 1403148632625 4664197044502528 Bool.false 20900407194176148471808 2376101201 34359738368 89598618401853 37313576356020224 Bool.false 201999759442379293065216 734870843889 1099511627776 179174992853289 74627152712040448 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep127 ep136) rfl rfl

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz314))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz268 qz284 qz549)

noncomputable def ep138 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 168454270803 1099511627776 21009369181605 74627152712040448 Bool.true 21896248801 68719476736 164395851289 583024630562816 (BSN.cpow_neg_s_mk qz13 106726 1000 8 qz14 rfl)

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep139 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz314) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz314) (Real.sqrt qz315) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz315) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep140 := BSN.log_dyadic_bound 0 16 1 0 1 524288 135746 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 106726 1000 0 1 9364972152248037 4503599627370496 500000000203619 67873000000000000000 499743008960411998431 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 39279540158062550581248 18889465931478580854784 1000000000407238 135746000000000000000 9364972152248037 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep142 := nat_lit 858198477022593477274825606479937681

noncomputable def ep143 := BSN.sin_dyadic_bound_f 962491571 2147483648 2 1 1048576 271758 ep142 ep93 ep142 ep142 ep94 ep142 454389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 962491571) qz287 0 1 ep142 ep93 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 962491571) qz288 0 1 ep142 ep94 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58177743) qz16)

noncomputable def ep144 := @Enclosure.Real.IsNear.cos_image qz38 qz316 Bool.false 58177743 262144 413 524288 Bool.true 454389 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 499743008960411998431 2251799813685248000 26681500010865720697 33936500000000000000000 58177743 262144 413 524288 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 58177743 262144) (BSN.cos_reduce1 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16932330793749316632576) qz19) 226375608064910080 72057594037927936 Bool.false 454389 1048576 35 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 58177743 262144 226375608064910080 72057594037927936 35 16932330793749316632576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 454389 1048576 16932330793749316632576 37778931862957161709568 962491571 2147483648 271758 271492 (ep143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep145 := BSN.cos_dyadic_bound_f 962491571 2147483648 2 1 1048576 271758 ep142 ep60 ep142 ep142 ep61 ep142 945008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 962491571) qz291 0 1 ep142 ep60 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 962491571) qz292 0 1 ep142 ep61 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.sin_image qz38 qz316 Bool.false 58177743 262144 413 524288 Bool.false 945008 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 499743008960411998431 2251799813685248000 26681500010865720697 33936500000000000000000 58177743 262144 413 524288 (ep141 rfl) rfl) (Enclosure.sfrac_false_div 58177743 262144) (BSN.sin_reduce1 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16932330793749316632576) qz19) 226375608064910080 72057594037927936 Bool.false 945008 1048576 35 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 58177743 262144 226375608064910080 72057594037927936 35 16932330793749316632576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945008 1048576 16932330793749316632576 37778931862957161709568 962491571 2147483648 271758 271492 (ep145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz317 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep139 rfl rfl) rfl)

noncomputable def ep147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 168454270803 1099511627776 21009369181605 74627152712040448 Bool.true 21896248801 68719476736 164395851289 583024630562816 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 370727 1048576 1 1048576 454389 1048576 28293693 35584999424 168454270803 1099511627776 21009369181605 74627152712040448 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 454389 1048576 56587386 71169998848 454389 1048576 28293693 35584999424 (ep144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 370727 1048576 1 1048576 59063 65536 28293693 35584999424 21896248801 68719476736 164395851289 583024630562816 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 59063 65536 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 945008 1048576 56587386 71169998848 59063 65536 28293693 35584999424 (ep146 rfl rfl) rfl)) rfl)

noncomputable def ep148 := @ep39 168454270803 1099511627776 21009369181605 74627152712040448 Bool.true 21896248801 68719476736 164395851289 583024630562816 Bool.true 3175493772491282710528 92419032371 1099511627776 200206605985311 74627152712040448 Bool.false 26424759699219024969728 384530863073 1099511627776 200217661818281 74627152712040448 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep137 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep138 ep147) rfl rfl

theorem EMRow33.d6 : Enclosure.Complex.IsNear qz3 Bool.true 92419032371 1099511627776 200206605985311 74627152712040448 Bool.false 384530863073 1099511627776 200217661818281 74627152712040448 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz39 := (BSN.headSumC qz272 17)

noncomputable abbrev qz550 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 qz550 qz275)

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq qz39 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz40) Bool.false 13270483097 34359738368 168240121137169 37313576356020224 Bool.false 87085072289 1099511627776 336533466719859 74627152712040448

noncomputable def ep150 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz40 Bool.false 3084645685 17179869184 160802577742081 37313576356020224 Bool.false 241745772287 1099511627776 321677171384209 74627152712040448 Bool.false

noncomputable abbrev qz551 := (@Nat.cast Complex Complex.instNatCast 15)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 qz551 qz275)

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz41) Bool.false 3084645685 17179869184 160802577742081 37313576356020224 Bool.false 241745772287 1099511627776 321677171384209 74627152712040448

noncomputable def ep152 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz41 Bool.true 86467339487 1099511627776 306213405393219 74627152712040448 Bool.false 7489281421 34359738368 153178032841801 37313576356020224 Bool.false

noncomputable abbrev qz552 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 qz552 qz275)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz42) Bool.true 86467339487 1099511627776 306213405393219 74627152712040448 Bool.false 7489281421 34359738368 153178032841801 37313576356020224

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz42 Bool.true 223028071929 1099511627776 290341076886385 74627152712040448 Bool.true 20539932495 1099511627776 290453793305993 74627152712040448 Bool.false

noncomputable abbrev qz553 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 qz553 qz275)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz43) Bool.true 223028071929 1099511627776 290341076886385 74627152712040448 Bool.true 20539932495 1099511627776 290453793305993 74627152712040448

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz43 Bool.false 54410090319 1099511627776 273839096824625 74627152712040448 Bool.true 147120061599 1099511627776 273987020869777 74627152712040448 Bool.true

noncomputable abbrev qz554 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 qz554 qz275)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz44) Bool.false 54410090319 1099511627776 273839096824625 74627152712040448 Bool.true 147120061599 1099511627776 273987020869777 74627152712040448

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz44 Bool.true 6837622065 274877906944 64178105076535 18656788178010112 Bool.false 79784604567 549755813888 128404954573353 37313576356020224 Bool.false

noncomputable abbrev qz318 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz318 qz7)) Bool.true 6837622065 274877906944 64178105076535 18656788178010112 Bool.false 79784604567 549755813888 128404954573353 37313576356020224

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) (@HPow.hPow Complex Complex Complex qz6 qz318 qz7) Bool.false 1629425865 137438953472 119417327009033 37313576356020224 Bool.true 21184530891 137438953472 119435086522467 37313576356020224 Bool.true

noncomputable abbrev qz319 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz319 qz7)) Bool.false 1629425865 137438953472 119417327009033 37313576356020224 Bool.true 21184530891 137438953472 119435086522467 37313576356020224

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) (@HPow.hPow Complex Complex Complex qz6 qz319 qz7) Bool.true 252590261721 1099511627776 16924343979853 5740550208618496 Bool.false 54879854573 1099511627776 16927726018349 5740550208618496 Bool.false

noncomputable abbrev qz320 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep163 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 (@HPow.hPow Complex Complex Complex qz6 qz320 qz7)) Bool.true 252590261721 1099511627776 16924343979853 5740550208618496 Bool.false 54879854573 1099511627776 16927726018349 5740550208618496

noncomputable def ep164 := @Enclosure.Complex.IsNear.addLitP qz3 (@HPow.hPow Complex Complex Complex qz6 qz320 qz7) Bool.true 92419032371 1099511627776 200206605985311 74627152712040448 Bool.false 384530863073 1099511627776 200217661818281 74627152712040448 Bool.true

noncomputable abbrev qz321 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz321))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz268 qz284 qz555)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz320 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 80085614675 549755813888 9904932876389 37313576356020224 Bool.true 82412752125 274877906944 620086763133 2332098522251264 (BSN.cpow_neg_s_mk qz13 106726 1000 9 qz14 rfl)

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep166 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz321) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz321) (Real.sqrt qz322) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz322) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep167 := BSN.log_dyadic_bound 1 17 2 1 867 524288 135746 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep168 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 106726 1000 0 1 9895417793173221 4503599627370496 500000000203619 67873000000000000000 528049179697102592223 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 41504390431577613533184 18889465931478580854784 1000000000407238 135746000000000000000 9895417793173221 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep167 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep169 := nat_lit 889991028838130341708660967709824016

noncomputable def ep170 := BSN.sin_dyadic_bound_f 971284386 2147483648 2 1 1048576 271758 ep169 ep93 ep169 ep169 ep94 ep169 458254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 971284386) qz287 0 1 ep169 ep93 ep169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 971284386) qz288 0 1 ep169 ep94 ep169 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61473015) qz16)

noncomputable def ep171 := @Enclosure.Real.IsNear.cos_image qz46 qz323 Bool.false 61473015 262144 413 524288 Bool.true 458254 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 528049179697102592223 2251799813685248000 26681500010865720697 33936500000000000000000 61473015 262144 413 524288 (ep168 rfl) rfl) (Enclosure.sfrac_false_div 61473015 262144) (BSN.cos_reduce1 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17087015630308743577600) qz19) 226375608064910080 72057594037927936 Bool.false 458254 1048576 37 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 61473015 262144 226375608064910080 72057594037927936 37 17087015630308743577600 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 458254 1048576 17087015630308743577600 37778931862957161709568 971284386 2147483648 271758 271492 (ep170 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep172 := BSN.cos_dyadic_bound_f 971284386 2147483648 2 1 1048576 271758 ep169 ep60 ep169 ep169 ep61 ep169 943140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 971284386) qz291 0 1 ep169 ep60 ep169 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 971284386) qz292 0 1 ep169 ep61 ep169 rfl rfl rfl rfl) rfl rfl

noncomputable def ep173 := @Enclosure.Real.IsNear.sin_image qz46 qz323 Bool.false 61473015 262144 413 524288 Bool.false 943140 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 528049179697102592223 2251799813685248000 26681500010865720697 33936500000000000000000 61473015 262144 413 524288 (ep168 rfl) rfl) (Enclosure.sfrac_false_div 61473015 262144) (BSN.sin_reduce1 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17087015630308743577600) qz19) 226375608064910080 72057594037927936 Bool.false 943140 1048576 37 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 61473015 262144 226375608064910080 72057594037927936 37 17087015630308743577600 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943140 1048576 17087015630308743577600 37778931862957161709568 971284386 2147483648 271758 271492 (ep172 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep166 rfl rfl) rfl)

noncomputable def ep174 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 80085614675 549755813888 9904932876389 37313576356020224 Bool.true 82412752125 274877906944 620086763133 2332098522251264 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 349525 1048576 1 1048576 229127 524288 28293693 35584999424 80085614675 549755813888 9904932876389 37313576356020224 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 458254 1048576 56587386 71169998848 229127 524288 28293693 35584999424 (ep171 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 349525 1048576 1 1048576 235785 262144 28293693 35584999424 82412752125 274877906944 620086763133 2332098522251264 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 235785 262144 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 943140 1048576 56587386 71169998848 235785 262144 28293693 35584999424 (ep173 rfl rfl) rfl)) rfl)

noncomputable def ep175 := @ep164 80085614675 549755813888 9904932876389 37313576356020224 Bool.true 82412752125 274877906944 620086763133 2332098522251264 Bool.true 138862964912611286581248 252590261721 1099511627776 16924343979853 5740550208618496 Bool.false 15085259558417346854912 54879854573 1099511627776 16927726018349 5740550208618496 EMRow33.d6 (ep165 ep174) rfl rfl

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv (Real.sqrt qz325))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz268 qz284 qz556)

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz319 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)))) Bool.false 265625668641 1099511627776 18818182279977 74627152712040448 Bool.true 224356101701 1099511627776 18809734806397 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 10 qz14 rfl)

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep177 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz325) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz325) (Real.sqrt qz326) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz326) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep178 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 135746 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 106726 1000 0 1 10369917190100709 4503599627370496 500000000203619 67873000000000000000 553369891015344134367 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 43494585150108164161536 18889465931478580854784 1000000000407238 135746000000000000000 10369917190100709 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep180 := nat_lit 183907425781742105538496844842392940470439765184326692764060964523396871454241

noncomputable def ep181 := nat_lit 26485973572080483592591124642955194674967141751859018250877257255238204961

noncomputable def ep182 := nat_lit 551669305398082155648305352277892911021969361269476360255681139055680137952801

noncomputable def ep183 := BSN.cos_dyadic_bound_f 1506180403 2147483648 3 2 1048576 271758 ep180 ep70 ep181 ep182 ep73 ep181 801069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1506180403) qz291 0 2 ep180 ep70 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1506180403) qz292 0 2 ep182 ep73 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 257682935) qz30)

noncomputable def ep184 := @Enclosure.Real.IsNear.cos_image qz48 qz327 Bool.false 257682935 1048576 413 524288 Bool.false 801069 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 553369891015344134367 2251799813685248000 26681500010865720697 33936500000000000000000 257682935 1048576 413 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 257682935 1048576) (BSN.cos_reduce0 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105988023509244014755840) qz32) 226375608064910080 72057594037927936 Bool.false 801069 1048576 39 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 257682935 1048576 226375608064910080 72057594037927936 39 105988023509244014755840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 801069 1048576 105988023509244014755840 151115727451828646838272 1506180403 2147483648 271758 271492 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep185 := nat_lit 5146452523057070191647803882420123281

noncomputable def ep186 := BSN.sin_dyadic_bound_f 1506180403 2147483648 2 1 1048576 271758 ep185 ep93 ep185 ep185 ep94 ep185 676609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1506180403) qz287 0 1 ep185 ep93 ep185 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1506180403) qz288 0 1 ep185 ep94 ep185 rfl rfl rfl rfl) rfl rfl

noncomputable def ep187 := @Enclosure.Real.IsNear.sin_image qz48 qz327 Bool.false 257682935 1048576 413 524288 Bool.false 676609 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 553369891015344134367 2251799813685248000 26681500010865720697 33936500000000000000000 257682935 1048576 413 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 257682935 1048576) (BSN.sin_reduce0 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105988023509244014755840) qz32) 226375608064910080 72057594037927936 Bool.false 676609 1048576 39 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 257682935 1048576 226375608064910080 72057594037927936 39 105988023509244014755840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 676609 1048576 105988023509244014755840 151115727451828646838272 1506180403 2147483648 271758 271492 (ep186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep177 rfl rfl) rfl)

noncomputable def ep188 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48))) Bool.false 265625668641 1099511627776 18818182279977 74627152712040448 Bool.true 224356101701 1099511627776 18809734806397 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz47 (Real.cos qz48) 331589 1048576 1 1048576 801069 1048576 28293693 35584999424 265625668641 1099511627776 18818182279977 74627152712040448 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz48) Bool.false 801069 1048576 56587386 71169998848 801069 1048576 28293693 35584999424 (ep184 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)) 331589 1048576 1 1048576 676609 1048576 28293693 35584999424 224356101701 1099511627776 18809734806397 74627152712040448 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz48) Bool.false 676609 1048576 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz48) Bool.false 676609 1048576 56587386 71169998848 676609 1048576 28293693 35584999424 (ep187 rfl rfl) rfl)) rfl)

noncomputable def ep189 := @ep162 265625668641 1099511627776 18818182279977 74627152712040448 Bool.true 224356101701 1099511627776 18809734806397 74627152712040448 Bool.false 14332581481331734609920 1629425865 137438953472 119417327009033 37313576356020224 Bool.true 186341104349074925027328 21184530891 137438953472 119435086522467 37313576356020224 (ep163 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep175 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep176 ep188) rfl rfl

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz329))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz268 qz284 qz557)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz318 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 10096473795 274877906944 388647093219 1622329406783488 Bool.false 164522728131 549755813888 194997131541 811164703391744 (BSN.cpow_neg_s_mk qz13 106726 1000 11 qz14 rfl)

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep191 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz329) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz329) (Real.sqrt qz330) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep192 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 135746 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 106726 1000 0 1 10799156221662949 4503599627370496 500000000203619 67873000000000000000 576275373456599947487 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 45294944137145793642496 18889465931478580854784 1000000000407238 135746000000000000000 10799156221662949 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep194 := nat_lit 3355546238302087006318591873788684533210104177526973347202484852796755611361536

noncomputable def ep195 := nat_lit 8773943676240816566901232444165836300131740225924782127600166364153628467456

noncomputable def ep196 := nat_lit 10049090827553779385821973156477721927030049052129070477352254225661959577149696

noncomputable def ep197 := BSN.cos_dyadic_bound_f 3110995302 2147483648 3 2 1048576 271758 ep194 ep70 ep195 ep196 ep73 ep195 127740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3110995302) qz291 0 2 ep194 ep70 ep195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3110995302) qz292 0 2 ep196 ep73 ep195 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67087283) qz16)

noncomputable def ep198 := @Enclosure.Real.IsNear.cos_image qz50 qz331 Bool.false 67087283 262144 825 1048576 Bool.true 127740 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 576275373456599947487 2251799813685248000 26681500010865720697 33936500000000000000000 67087283 262144 825 1048576 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 67087283 262144) (BSN.cos_reduce2 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54729208151186694209536) qz19) 226375608064910080 72057594037927936 Bool.false 127740 1048576 40 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 67087283 262144 226375608064910080 72057594037927936 40 54729208151186694209536 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 127740 1048576 54729208151186694209536 37778931862957161709568 3110995302 2147483648 271758 271492 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep199 := nat_lit 6032964074002763958119944386864299490738082127367812199262392601942837197676800

noncomputable def ep200 := nat_lit 15786414761198087139682014255925468264590001801788010874623485116689277262110976

noncomputable def ep201 := BSN.sin_dyadic_bound_f 3110995302 2147483648 3 2 1048576 271758 ep199 ep77 ep195 ep200 ep79 ep195 1040766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3110995302) qz287 0 2 ep199 ep77 ep195 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3110995302) qz288 0 2 ep200 ep79 ep195 rfl rfl rfl rfl) rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.sin_image qz50 qz331 Bool.false 67087283 262144 825 1048576 Bool.true 1040766 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 576275373456599947487 2251799813685248000 26681500010865720697 33936500000000000000000 67087283 262144 825 1048576 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 67087283 262144) (BSN.sin_reduce2 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54729208151186694209536) qz19) 226375608064910080 72057594037927936 Bool.false 1040766 1048576 40 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 67087283 262144 226375608064910080 72057594037927936 40 54729208151186694209536 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040766 1048576 54729208151186694209536 37778931862957161709568 3110995302 2147483648 271758 271492 (ep201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep191 rfl rfl) rfl)

noncomputable def ep203 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 10096473795 274877906944 388647093219 1622329406783488 Bool.false 164522728131 549755813888 194997131541 811164703391744 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 316157 1048576 1 1048576 31935 262144 56519513 71169998848 10096473795 274877906944 388647093219 1622329406783488 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 127740 1048576 113039026 142339997696 31935 262144 56519513 71169998848 (ep198 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 316157 1048576 1 1048576 520383 524288 56519513 71169998848 164522728131 549755813888 194997131541 811164703391744 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 520383 524288 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 1040766 1048576 113039026 142339997696 520383 524288 56519513 71169998848 (ep202 rfl rfl) rfl)) rfl)

noncomputable def ep204 := @ep160 10096473795 274877906944 388647093219 1622329406783488 Bool.false 164522728131 549755813888 194997131541 811164703391744 Bool.true 939755620850655559680 6837622065 274877906944 64178105076535 18656788178010112 Bool.false 10965512554865831706624 79784604567 549755813888 128404954573353 37313576356020224 (ep161 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep189 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep190 ep203) rfl rfl

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz333))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz268 qz284 qz558)

noncomputable def ep205 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 81760578579 1099511627776 17126676518485 74627152712040448 Bool.true 306689270733 1099511627776 17177111723071 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 12 qz14 rfl)

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep206 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz333) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz333) (Real.sqrt qz334) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep207 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 135746 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 106726 1000 0 1 11191020447815397 4503599627370496 500000000203619 67873000000000000000 597186424156773030111 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 46938541828353910898688 18889465931478580854784 1000000000407238 135746000000000000000 11191020447815397 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep209 := nat_lit 2243598267198112108887076110021845817636509937157222964720563964108761045278976

noncomputable def ep210 := nat_lit 3929254817735021794123413455939867911289074304007840875062454943054739415296

noncomputable def ep211 := nat_lit 6722936291958866283072981503153657717086951662863653212411566982440173657006336

noncomputable def ep212 := BSN.cos_dyadic_bound_f 2813771162 2147483648 3 2 1048576 271758 ep209 ep70 ep210 ep211 ep73 ep210 270107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2813771162) qz291 0 2 ep209 ep70 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2813771162) qz292 0 2 ep211 ep73 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 278086599) qz30)

noncomputable def ep213 := @Enclosure.Real.IsNear.cos_image qz52 qz335 Bool.false 278086599 1048576 825 1048576 Bool.false 270107 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 597186424156773030111 2251799813685248000 26681500010865720697 33936500000000000000000 278086599 1048576 825 1048576 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 278086599 1048576) (BSN.cos_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198001543078559914917888) qz32) 226375608064910080 72057594037927936 Bool.false 270107 1048576 42 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 278086599 1048576 226375608064910080 72057594037927936 42 198001543078559914917888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270107 1048576 198001543078559914917888 151115727451828646838272 2813771162 2147483648 271758 271492 (ep212 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep214 := nat_lit 4035333477102413778561438267274570577416686627439795063796965171441326089969920

noncomputable def ep215 := nat_lit 10562368884610941289518043268695210773758758856326307710432426712438527324201216

noncomputable def ep216 := BSN.sin_dyadic_bound_f 2813771162 2147483648 3 2 1048576 271758 ep214 ep77 ep210 ep215 ep79 ep210 1013189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2813771162) qz287 0 2 ep214 ep77 ep210 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2813771162) qz288 0 2 ep215 ep79 ep210 rfl rfl rfl rfl) rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.sin_image qz52 qz335 Bool.false 278086599 1048576 825 1048576 Bool.false 1013189 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 597186424156773030111 2251799813685248000 26681500010865720697 33936500000000000000000 278086599 1048576 825 1048576 (ep208 rfl) rfl) (Enclosure.sfrac_false_div 278086599 1048576) (BSN.sin_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198001543078559914917888) qz32) 226375608064910080 72057594037927936 Bool.false 1013189 1048576 42 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 278086599 1048576 226375608064910080 72057594037927936 42 198001543078559914917888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1013189 1048576 198001543078559914917888 151115727451828646838272 2813771162 2147483648 271758 271492 (ep216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz336 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep206 rfl rfl) rfl)

noncomputable def ep218 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 81760578579 1099511627776 17126676518485 74627152712040448 Bool.true 306689270733 1099511627776 17177111723071 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 302697 1048576 1 1048576 270107 1048576 56519513 71169998848 81760578579 1099511627776 17126676518485 74627152712040448 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 270107 1048576 113039026 142339997696 270107 1048576 56519513 71169998848 (ep213 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 302697 1048576 1 1048576 1013189 1048576 56519513 71169998848 306689270733 1099511627776 17177111723071 74627152712040448 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.false 1013189 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.false 1013189 1048576 113039026 142339997696 1013189 1048576 56519513 71169998848 (ep217 rfl rfl) rfl)) rfl)

noncomputable def ep219 := @ep158 81760578579 1099511627776 17126676518485 74627152712040448 Bool.true 306689270733 1099511627776 17177111723071 74627152712040448 Bool.false 14956131743520717275136 54410090319 1099511627776 273839096824625 74627152712040448 Bool.true 80880109203610939686912 147120061599 1099511627776 273987020869777 74627152712040448 (ep159 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep204 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep205 ep218) rfl rfl

noncomputable abbrev qz337 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz337))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz268 qz284 qz559)

noncomputable def ep220 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.true 34679770281 137438953472 257843438465 1166049261125632 Bool.false 7911258069 68719476736 2058346554527 9328394089005056 (BSN.cpow_neg_s_mk qz13 106726 1000 13 qz14 rfl)

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep221 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz337) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz337) (Real.sqrt qz338) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz338) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep222 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 135746 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep223 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 106726 1000 0 1 11551497052968677 4503599627370496 500000000203619 67873000000000000000 616422537237567510751 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 48450490295254733815808 18889465931478580854784 1000000000407238 135746000000000000000 11551497052968677 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep224 := nat_lit 713908224752630241392945178587214481

noncomputable def ep225 := BSN.cos_dyadic_bound_f 919201229 2147483648 2 1 1048576 271758 ep224 ep60 ep224 ep224 ep61 ep224 953976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 919201229) qz291 0 1 ep224 ep60 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 919201229) qz292 0 1 ep224 ep61 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17940257) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep226 := @Enclosure.Real.IsNear.cos_image qz54 qz339 Bool.false 17940257 65536 825 1048576 Bool.true 953976 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 616422537237567510751 2251799813685248000 26681500010865720697 33936500000000000000000 17940257 65536 825 1048576 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 17940257 65536) (BSN.cos_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4042689759491060137984) qz340) 226375608064910080 72057594037927936 Bool.false 953976 1048576 43 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 17940257 65536 226375608064910080 72057594037927936 43 4042689759491060137984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953976 1048576 4042689759491060137984 9444732965739290427392 919201229 2147483648 271758 271492 (ep225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep227 := BSN.sin_dyadic_bound_f 919201229 2147483648 2 1 1048576 271758 ep224 ep93 ep224 ep224 ep94 ep224 435248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 919201229) qz287 0 1 ep224 ep93 ep224 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 919201229) qz288 0 1 ep224 ep94 ep224 rfl rfl rfl rfl) rfl rfl

noncomputable def ep228 := @Enclosure.Real.IsNear.sin_image qz54 qz339 Bool.false 17940257 65536 825 1048576 Bool.true 435248 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 616422537237567510751 2251799813685248000 26681500010865720697 33936500000000000000000 17940257 65536 825 1048576 (ep223 rfl) rfl) (Enclosure.sfrac_false_div 17940257 65536) (BSN.sin_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4042689759491060137984) qz340) 226375608064910080 72057594037927936 Bool.false 435248 1048576 43 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 17940257 65536 226375608064910080 72057594037927936 43 4042689759491060137984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 435248 1048576 4042689759491060137984 9444732965739290427392 919201229 2147483648 271758 271492 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep221 rfl rfl) rfl)

noncomputable def ep229 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.true 34679770281 137438953472 257843438465 1166049261125632 Bool.false 7911258069 68719476736 2058346554527 9328394089005056 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz54) 290823 1048576 1 1048576 119247 131072 56519513 71169998848 34679770281 137438953472 257843438465 1166049261125632 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.true 953976 1048576 113039026 142339997696 119247 131072 56519513 71169998848 (ep226 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 290823 1048576 1 1048576 27203 65536 56519513 71169998848 7911258069 68719476736 2058346554527 9328394089005056 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 27203 65536 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 435248 1048576 113039026 142339997696 27203 65536 56519513 71169998848 (ep228 rfl rfl) rfl)) rfl)

noncomputable def ep230 := @ep156 34679770281 137438953472 257843438465 1166049261125632 Bool.false 7911258069 68719476736 2058346554527 9328394089005056 Bool.true 30652744800799700287488 223028071929 1099511627776 290341076886385 74627152712040448 Bool.true 1411493413249162936320 20539932495 1099511627776 290453793305993 74627152712040448 (ep157 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep220 ep229) rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz342))

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz268 qz284 qz560)

noncomputable def ep231 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 68280366221 549755813888 7936164253417 37313576356020224 Bool.false 260196937967 1099511627776 15902272377609 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 14 qz14 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep232 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz342) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz342) (Real.sqrt qz343) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep233 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 135746 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz560 106726 1000 0 1 11885250371606245 4503599627370496 500000000203619 67873000000000000000 126846523116004810387 450359962737049600 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 49850353174629559828480 18889465931478580854784 1000000000407238 135746000000000000000 11885250371606245 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep235 := nat_lit 1160520440529306110862284314157610000

noncomputable def ep236 := BSN.sin_dyadic_bound_f 1037918370 2147483648 2 1 1048576 271758 ep235 ep93 ep235 ep235 ep94 ep235 487294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1037918370) qz287 0 1 ep235 ep93 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1037918370) qz288 0 1 ep235 ep94 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36917197) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz561 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep237 := @Enclosure.Real.IsNear.cos_image qz56 qz344 Bool.false 36917197 131072 825 1048576 Bool.false 487294 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 126846523116004810387 450359962737049600 26681500010865720697 33936500000000000000000 36917197 131072 825 1048576 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 36917197 131072) (BSN.cos_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9129626537605143199744) qz561) 226375608064910080 72057594037927936 Bool.false 487294 1048576 44 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 36917197 131072 226375608064910080 72057594037927936 44 9129626537605143199744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487294 1048576 9129626537605143199744 18889465931478580854784 1037918370 2147483648 271758 271492 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep238 := BSN.cos_dyadic_bound_f 1037918370 2147483648 2 1 1048576 271758 ep235 ep60 ep235 ep235 ep61 ep235 928469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1037918370) qz291 0 1 ep235 ep60 ep235 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1037918370) qz292 0 1 ep235 ep61 ep235 rfl rfl rfl rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz56 qz344 Bool.false 36917197 131072 825 1048576 Bool.true 928469 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 126846523116004810387 450359962737049600 26681500010865720697 33936500000000000000000 36917197 131072 825 1048576 (ep234 rfl) rfl) (Enclosure.sfrac_false_div 36917197 131072) (BSN.sin_reduce3 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9129626537605143199744) qz561) 226375608064910080 72057594037927936 Bool.false 928469 1048576 44 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 36917197 131072 226375608064910080 72057594037927936 44 9129626537605143199744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 928469 1048576 9129626537605143199744 18889465931478580854784 1037918370 2147483648 271758 271492 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep232 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 68280366221 549755813888 7936164253417 37313576356020224 Bool.false 260196937967 1099511627776 15902272377609 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 280243 1048576 1 1048576 243647 524288 56519513 71169998848 68280366221 549755813888 7936164253417 37313576356020224 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 487294 1048576 113039026 142339997696 243647 524288 56519513 71169998848 (ep237 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 280243 1048576 1 1048576 928469 1048576 56519513 71169998848 260196937967 1099511627776 15902272377609 74627152712040448 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.true 928469 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.true 928469 1048576 113039026 142339997696 928469 1048576 56519513 71169998848 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep154 68280366221 549755813888 7936164253417 37313576356020224 Bool.false 260196937967 1099511627776 15902272377609 74627152712040448 Bool.true 47535922594405685395456 86467339487 1099511627776 306213405393219 74627152712040448 Bool.false 263505664194440459190272 7489281421 34359738368 153178032841801 37313576356020224 (ep155 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep230 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep231 ep240) rfl rfl

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz346))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz268 qz284 qz562)

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 283884663327 1099511627776 15391750090943 74627152712040448 Bool.false 2088766815 1099511627776 15321105700607 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 15 qz14 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz346) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz346) (Real.sqrt qz347) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 135746 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 106726 1000 0 1 12195965485668069 4503599627370496 500000000203619 67873000000000000000 650813306211705166047 2251799813685248000 26681500010865720697 33936500000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 51153586820399524478976 18889465931478580854784 1000000000407238 135746000000000000000 12195965485668069 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 8188433082938416913129302244519628419144480462925726696128739298443298240733440

noncomputable def ep247 := nat_lit 16146732586669937737911614748193417425710649583027930264025190419366307963136

noncomputable def ep248 := nat_lit 21419753840650769159001077549863856517165345875004381840862085949529664227123456

noncomputable def ep249 := BSN.sin_dyadic_bound_f 3357457946 2147483648 3 2 1048576 271758 ep246 ep77 ep247 ep248 ep79 ep247 1048547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3357457946) qz287 0 2 ep246 ep77 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3357457946) qz288 0 2 ep248 ep79 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303058561) qz30)

noncomputable def ep250 := @Enclosure.Real.IsNear.cos_image qz58 qz348 Bool.false 303058561 1048576 413 524288 Bool.false 1048547 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 650813306211705166047 2251799813685248000 26681500010865720697 33936500000000000000000 303058561 1048576 413 524288 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 303058561 1048576) (BSN.cos_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236260099297618587287552) qz32) 226375608064910080 72057594037927936 Bool.false 1048547 1048576 45 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 303058561 1048576 226375608064910080 72057594037927936 45 236260099297618587287552 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048547 1048576 236260099297618587287552 151115727451828646838272 3357457946 2147483648 271758 271492 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep251 := nat_lit 4556305816115418257399795297954546196158360545884527244633310805988217381724416

noncomputable def ep252 := nat_lit 13636623983172914896723562664367251753623660338487525873371882037125919529246976

noncomputable def ep253 := BSN.cos_dyadic_bound_f 3357457946 2147483648 3 2 1048576 271758 ep251 ep70 ep247 ep252 ep73 ep247 7715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3357457946) qz291 0 2 ep251 ep70 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3357457946) qz292 0 2 ep252 ep73 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz58 qz348 Bool.false 303058561 1048576 413 524288 Bool.true 7715 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 650813306211705166047 2251799813685248000 26681500010865720697 33936500000000000000000 303058561 1048576 413 524288 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 303058561 1048576) (BSN.sin_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236260099297618587287552) qz32) 226375608064910080 72057594037927936 Bool.false 7715 1048576 45 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 303058561 1048576 226375608064910080 72057594037927936 45 236260099297618587287552 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7715 1048576 236260099297618587287552 151115727451828646838272 3357457946 2147483648 271758 271492 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep243 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 283884663327 1099511627776 15391750090943 74627152712040448 Bool.false 2088766815 1099511627776 15321105700607 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 270741 1048576 1 1048576 1048547 1048576 28293693 35584999424 283884663327 1099511627776 15391750090943 74627152712040448 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 1048547 1048576 56587386 71169998848 1048547 1048576 28293693 35584999424 (ep250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 270741 1048576 1 1048576 7715 1048576 28293693 35584999424 2088766815 1099511627776 15321105700607 74627152712040448 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.true 7715 1048576 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.true 7715 1048576 56587386 71169998848 7715 1048576 28293693 35584999424 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep152 283884663327 1099511627776 15391750090943 74627152712040448 Bool.false 2088766815 1099511627776 15321105700607 74627152712040448 Bool.false 217062643086500130979840 3084645685 17179869184 160802577742081 37313576356020224 Bool.false 8306321487351425007616 241745772287 1099511627776 321677171384209 74627152712040448 (ep153 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep255) rfl rfl

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz268 qz284 qz563)

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 7101191727 34359738368 464846462193 2332098522251264 Bool.true 77330349999 549755813888 7428147667825 37313576356020224 (BSN.cpow_neg_s_mk qz13 106726 1000 16 qz14 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz351) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 0 32 1 0 1 524288 135746 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 106726 1000 0 1 3121657384082679 1125899906842624 125000000067873 16968250000000000000 166581002986803999477 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 52372720210750067441664 18889465931478580854784 1000000000542984 135746000000000000000 3121657384082679 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 2712348305949790252937981369858433601

noncomputable def ep262 := BSN.cos_dyadic_bound_f 1283324143 2147483648 2 1 1048576 271758 ep261 ep60 ep261 ep261 ep61 ep261 866848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1283324143) qz291 0 1 ep261 ep60 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1283324143) qz292 0 1 ep261 ep61 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 310281297) qz30)

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz60 qz352 Bool.false 310281297 1048576 825 1048576 Bool.false 866848 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 166581002986803999477 562949953421312000 6670375003621906899 8484125000000000000000 310281297 1048576 825 1048576 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 310281297 1048576) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90305908348517764562944) qz32) 226375608064910080 72057594037927936 Bool.false 866848 1048576 47 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 310281297 1048576 226375608064910080 72057594037927936 47 90305908348517764562944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 866848 1048576 90305908348517764562944 151115727451828646838272 1283324143 2147483648 271758 271492 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := BSN.sin_dyadic_bound_f 1283324143 2147483648 2 1 1048576 271758 ep261 ep93 ep261 ep261 ep94 ep261 589986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1283324143) qz287 0 1 ep261 ep93 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1283324143) qz288 0 1 ep261 ep94 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz60 qz352 Bool.false 310281297 1048576 825 1048576 Bool.false 589986 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 166581002986803999477 562949953421312000 6670375003621906899 8484125000000000000000 310281297 1048576 825 1048576 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 310281297 1048576) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90305908348517764562944) qz32) 226375608064910080 72057594037927936 Bool.false 589986 1048576 47 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 310281297 1048576 226375608064910080 72057594037927936 47 90305908348517764562944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 589986 1048576 90305908348517764562944 151115727451828646838272 1283324143 2147483648 271758 271492 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep258 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 7101191727 34359738368 464846462193 2332098522251264 Bool.true 77330349999 549755813888 7428147667825 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 262143 1048576 1 1048576 27089 32768 56519513 71169998848 7101191727 34359738368 464846462193 2332098522251264 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 866848 1048576 113039026 142339997696 27089 32768 56519513 71169998848 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 262143 1048576 1 1048576 294993 524288 56519513 71169998848 77330349999 549755813888 7428147667825 37313576356020224 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 294993 524288 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 589986 1048576 113039026 142339997696 294993 524288 56519513 71169998848 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep150 7101191727 34359738368 464846462193 2332098522251264 Bool.true 77330349999 549755813888 7428147667825 37313576356020224 Bool.false 227985163614943182848 13270483097 34359738368 168240121137169 37313576356020224 Bool.false 47875524793734510149632 87085072289 1099511627776 336533466719859 74627152712040448 (ep151 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep266) rfl rfl

theorem EMRow33.d7 : Enclosure.Complex.IsNear qz39 Bool.false 13270483097 34359738368 168240121137169 37313576356020224 Bool.false 87085072289 1099511627776 336533466719859 74627152712040448 := ep149 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz61 := (BSN.headSumC qz272 25)

noncomputable abbrev qz354 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq qz61 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7)) Bool.false 592372970183 549755813888 110530610523997 18656788178010112 Bool.true 71988472939 1099511627776 442127809153463 74627152712040448

noncomputable def ep269 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) Bool.false 961694400193 1099511627776 429954274605057 74627152712040448 Bool.true 96879496327 1099511627776 430022479504027 74627152712040448 Bool.false

noncomputable def ep270 := nat_lit 1302641937392828485206016

noncomputable abbrev qz355 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7)) Bool.false 961694400193 1099511627776 429954274605057 74627152712040448 Bool.true 96879496327 1099511627776 430022479504027 74627152712040448

noncomputable def ep272 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) Bool.false 975198229159 1099511627776 417592430232459 74627152712040448 Bool.false 131985938495 1099511627776 417593780769413 74627152712040448 Bool.true

noncomputable abbrev qz356 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7)) Bool.false 975198229159 1099511627776 417592430232459 74627152712040448 Bool.false 131985938495 1099511627776 417593780769413 74627152712040448

noncomputable def ep274 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) Bool.false 1209527546761 1099511627776 404885897416827 74627152712040448 Bool.false 62796886597 549755813888 202478225394735 37313576356020224 Bool.true

noncomputable abbrev qz357 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz7)) Bool.false 1209527546761 1099511627776 404885897416827 74627152712040448 Bool.false 62796886597 549755813888 202478225394735 37313576356020224

noncomputable def ep276 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) Bool.false 1263118095269 1099511627776 391921309924491 74627152712040448 Bool.true 6767354521 68719476736 12246403496075 2332098522251264 Bool.true

noncomputable abbrev qz358 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep277 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz7)) Bool.false 1263118095269 1099511627776 391921309924491 74627152712040448 Bool.true 6767354521 68719476736 12246403496075 2332098522251264

noncomputable def ep278 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz7) Bool.false 1078284775755 1099511627776 29124282693711 5740550208618496 Bool.true 67599494955 274877906944 14560994300987 2870275104309248 Bool.false

noncomputable abbrev qz359 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz7)) Bool.false 1078284775755 1099511627776 29124282693711 5740550208618496 Bool.true 67599494955 274877906944 14560994300987 2870275104309248

noncomputable def ep280 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz7) Bool.false 206759254427 274877906944 182466062320537 37313576356020224 Bool.true 247997366299 1099511627776 364966869983615 74627152712040448 Bool.false

noncomputable abbrev qz360 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep281 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz7)) Bool.false 206759254427 274877906944 182466062320537 37313576356020224 Bool.true 247997366299 1099511627776 364966869983615 74627152712040448

noncomputable def ep282 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz7) Bool.false 613393514533 1099511627776 350904542846073 74627152712040448 Bool.true 50652793059 549755813888 87739418644269 18656788178010112 Bool.false

noncomputable abbrev qz361 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep283 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz39 (@HPow.hPow Complex Complex Complex qz6 qz361 qz7)) Bool.false 613393514533 1099511627776 350904542846073 74627152712040448 Bool.true 50652793059 549755813888 87739418644269 18656788178010112

noncomputable def ep284 := @Enclosure.Complex.IsNear.addLitP qz39 (@HPow.hPow Complex Complex Complex qz6 qz361 qz7) Bool.false 13270483097 34359738368 168240121137169 37313576356020224 Bool.false 87085072289 1099511627776 336533466719859 74627152712040448 Bool.false

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz268 qz284 qz564)

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz361 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 188738055429 1099511627776 14424300571735 74627152712040448 Bool.true 188390658407 1099511627776 14424207857217 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 17 qz14 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep286 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep287 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 135746 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep288 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 106726 1000 0 1 3189913004350711 1125899906842624 125000000067873 16968250000000000000 170223327651166991093 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 53517859495200818200576 18889465931478580854784 1000000000542984 135746000000000000000 3189913004350711 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep287 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep289 := nat_lit 287850543501415114850366475292648196155812174690571667158373641809422938153216

noncomputable def ep290 := nat_lit 64875517559277741731095300924348252006677057826687263035672421206521159936

noncomputable def ep291 := nat_lit 863421879469126789067637235276095891963423169956061626949049580585855772139776

noncomputable def ep292 := BSN.cos_dyadic_bound_f 1684651622 2147483648 3 2 1048576 271758 ep289 ep70 ep290 ep291 ep73 ep290 742137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1684651622) qz291 0 2 ep289 ep70 ep290 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1684651622) qz292 0 2 ep291 ep73 ep290 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 317065655) qz30)

noncomputable def ep293 := @Enclosure.Real.IsNear.cos_image qz63 qz364 Bool.false 317065655 1048576 825 1048576 Bool.false 742137 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 170223327651166991093 562949953421312000 6670375003621906899 8484125000000000000000 317065655 1048576 825 1048576 (ep288 rfl) rfl) (Enclosure.sfrac_false_div 317065655 1048576) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118546819083370548428800) qz32) 226375608064910080 72057594037927936 Bool.false 742137 1048576 48 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 317065655 1048576 226375608064910080 72057594037927936 48 118546819083370548428800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742137 1048576 118546819083370548428800 151115727451828646838272 1684651622 2147483648 271758 271492 (ep292 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep294 := nat_lit 8054533975300975892649624985683421456

noncomputable def ep295 := BSN.sin_dyadic_bound_f 1684651622 2147483648 2 1 1048576 271758 ep294 ep93 ep294 ep294 ep94 ep294 740771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1684651622) qz287 0 1 ep294 ep93 ep294 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1684651622) qz288 0 1 ep294 ep94 ep294 rfl rfl rfl rfl) rfl rfl

noncomputable def ep296 := @Enclosure.Real.IsNear.sin_image qz63 qz364 Bool.false 317065655 1048576 825 1048576 Bool.false 740771 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 170223327651166991093 562949953421312000 6670375003621906899 8484125000000000000000 317065655 1048576 825 1048576 (ep288 rfl) rfl) (Enclosure.sfrac_false_div 317065655 1048576) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118546819083370548428800) qz32) 226375608064910080 72057594037927936 Bool.false 740771 1048576 48 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 317065655 1048576 226375608064910080 72057594037927936 48 118546819083370548428800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740771 1048576 118546819083370548428800 151115727451828646838272 1684651622 2147483648 271758 271492 (ep295 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep286 rfl rfl) rfl)

noncomputable def ep297 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 188738055429 1099511627776 14424300571735 74627152712040448 Bool.true 188390658407 1099511627776 14424207857217 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 254317 1048576 1 1048576 742137 1048576 56519513 71169998848 188738055429 1099511627776 14424300571735 74627152712040448 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 742137 1048576 113039026 142339997696 742137 1048576 56519513 71169998848 (ep293 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 254317 1048576 1 1048576 740771 1048576 56519513 71169998848 188390658407 1099511627776 14424207857217 74627152712040448 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.false 740771 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.false 740771 1048576 113039026 142339997696 740771 1048576 56519513 71169998848 (ep296 rfl rfl) rfl)) rfl)

noncomputable def ep298 := @ep284 188738055429 1099511627776 14424300571735 74627152712040448 Bool.true 188390658407 1099511627776 14424207857217 74627152712040448 Bool.false 21076040675981885702144 613393514533 1099511627776 350904542846073 74627152712040448 Bool.true 111386669895403928813568 50652793059 549755813888 87739418644269 18656788178010112 EMRow33.d7 (ep285 ep297) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz268 qz284 qz565)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz360 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.false 213643503175 1099511627776 14027581795001 74627152712040448 Bool.true 146691780181 1099511627776 14009195406539 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 18 qz14 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep300 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep301 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 135746 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep302 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 106726 1000 0 1 3254268794313975 1125899906842624 125000000067873 16968250000000000000 6946301826839065917 22517998136852480 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 54597570484265130393600 18889465931478580854784 1000000000542984 135746000000000000000 3254268794313975 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep301 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep303 := nat_lit 2787451406878599512402675530921927696

noncomputable def ep304 := BSN.cos_dyadic_bound_f 1292116958 2147483648 2 1 1048576 271758 ep303 ep60 ep303 ep303 ep61 ep303 864425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1292116958) qz291 0 1 ep303 ep60 ep303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1292116958) qz292 0 1 ep303 ep61 ep303 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323462385) qz30)

noncomputable def ep305 := @Enclosure.Real.IsNear.cos_image qz65 qz368 Bool.false 323462385 1048576 825 1048576 Bool.false 864425 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 6946301826839065917 22517998136852480 6670375003621906899 8484125000000000000000 323462385 1048576 825 1048576 (ep302 rfl) rfl) (Enclosure.sfrac_false_div 323462385 1048576) (BSN.cos_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90924647694755472343040) qz32) 226375608064910080 72057594037927936 Bool.false 864425 1048576 49 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 323462385 1048576 226375608064910080 72057594037927936 49 90924647694755472343040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 864425 1048576 90924647694755472343040 151115727451828646838272 1292116958 2147483648 271758 271492 (ep304 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep306 := BSN.sin_dyadic_bound_f 1292116958 2147483648 2 1 1048576 271758 ep303 ep93 ep303 ep303 ep94 ep303 593531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1292116958) qz287 0 1 ep303 ep93 ep303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1292116958) qz288 0 1 ep303 ep94 ep303 rfl rfl rfl rfl) rfl rfl

noncomputable def ep307 := @Enclosure.Real.IsNear.sin_image qz65 qz368 Bool.false 323462385 1048576 825 1048576 Bool.false 593531 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 6946301826839065917 22517998136852480 6670375003621906899 8484125000000000000000 323462385 1048576 825 1048576 (ep302 rfl) rfl) (Enclosure.sfrac_false_div 323462385 1048576) (BSN.sin_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90924647694755472343040) qz32) 226375608064910080 72057594037927936 Bool.false 593531 1048576 49 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 323462385 1048576 226375608064910080 72057594037927936 49 90924647694755472343040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 593531 1048576 90924647694755472343040 151115727451828646838272 1292116958 2147483648 271758 271492 (ep306 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep300 rfl rfl) rfl)

noncomputable def ep308 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.false 213643503175 1099511627776 14027581795001 74627152712040448 Bool.true 146691780181 1099511627776 14009195406539 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz65) 247151 1048576 1 1048576 864425 1048576 56519513 71169998848 213643503175 1099511627776 14027581795001 74627152712040448 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.false 864425 1048576 113039026 142339997696 864425 1048576 56519513 71169998848 (ep305 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 247151 1048576 1 1048576 593531 1048576 56519513 71169998848 146691780181 1099511627776 14009195406539 74627152712040448 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.false 593531 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.false 593531 1048576 113039026 142339997696 593531 1048576 56519513 71169998848 (ep307 rfl rfl) rfl)) rfl)

noncomputable def ep309 := @ep282 213643503175 1099511627776 14027581795001 74627152712040448 Bool.true 146691780181 1099511627776 14009195406539 74627152712040448 Bool.false 909336817571131616657408 206759254427 274877906944 182466062320537 37313576356020224 Bool.true 136337993951787207360512 247997366299 1099511627776 364966869983615 74627152712040448 (ep283 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep298 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep299 ep308) rfl rfl

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz370))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz268 qz284 qz566)

noncomputable def ep310 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz359 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 251247758047 1099511627776 13683550377169 74627152712040448 Bool.true 22400613521 1099511627776 13618981842047 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 19 qz14 rfl)

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep311 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz370) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz370) (Real.sqrt qz371) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz371) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep312 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 135746 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep313 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 106726 1000 0 1 3315143513283831 1125899906842624 125000000067873 16968250000000000000 176906003299365073653 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 55618878793361701994496 18889465931478580854784 1000000000542984 135746000000000000000 3315143513283831 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep314 := nat_lit 1329747654088109272062699776538801

noncomputable def ep315 := BSN.cos_dyadic_bound_f 190959957 2147483648 2 1 1048576 271758 ep314 ep60 ep314 ep314 ep61 ep314 1044433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 190959957) qz291 0 1 ep314 ep60 ep314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 190959957) qz292 0 1 ep314 ep61 ep314 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82378277) qz16)

noncomputable def ep316 := @Enclosure.Real.IsNear.cos_image qz67 qz372 Bool.false 82378277 262144 413 524288 Bool.false 1044433 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 176906003299365073653 562949953421312000 6670375003621906899 8484125000000000000000 82378277 262144 413 524288 (ep313 rfl) rfl) (Enclosure.sfrac_false_div 82378277 262144) (BSN.cos_reduce0 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3359403106394433388544) qz19) 226375608064910080 72057594037927936 Bool.false 1044433 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 82378277 262144 226375608064910080 72057594037927936 50 3359403106394433388544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044433 1048576 3359403106394433388544 37778931862957161709568 190959957 2147483648 271758 271492 (ep315 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep317 := BSN.sin_dyadic_bound_f 190959957 2147483648 1 0 1048576 271758 0 1 1 0 1 1 93119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 190959957) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 190959957) qz288 0 0 rfl) rfl rfl

noncomputable def ep318 := @Enclosure.Real.IsNear.sin_image qz67 qz372 Bool.false 82378277 262144 413 524288 Bool.false 93119 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 176906003299365073653 562949953421312000 6670375003621906899 8484125000000000000000 82378277 262144 413 524288 (ep313 rfl) rfl) (Enclosure.sfrac_false_div 82378277 262144) (BSN.sin_reduce0 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3359403106394433388544) qz19) 226375608064910080 72057594037927936 Bool.false 93119 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 82378277 262144 226375608064910080 72057594037927936 50 3359403106394433388544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93119 1048576 3359403106394433388544 37778931862957161709568 190959957 2147483648 271758 271492 (ep317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep311 rfl rfl) rfl)

noncomputable def ep319 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 251247758047 1099511627776 13683550377169 74627152712040448 Bool.true 22400613521 1099511627776 13618981842047 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 240559 1048576 1 1048576 1044433 1048576 28293693 35584999424 251247758047 1099511627776 13683550377169 74627152712040448 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 1044433 1048576 56587386 71169998848 1044433 1048576 28293693 35584999424 (ep316 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 240559 1048576 1 1048576 93119 1048576 28293693 35584999424 22400613521 1099511627776 13618981842047 74627152712040448 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.false 93119 1048576 28293693 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.false 93119 1048576 56587386 71169998848 93119 1048576 28293693 35584999424 (ep318 rfl rfl) rfl)) rfl)

noncomputable def ep320 := @ep280 251247758047 1099511627776 13683550377169 74627152712040448 Bool.true 22400613521 1099511627776 13618981842047 74627152712040448 Bool.false 296396662249114797342720 1078284775755 1099511627776 29124282693711 5740550208618496 Bool.true 297305722939230199480320 67599494955 274877906944 14560994300987 2870275104309248 (ep281 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep309 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep310 ep319) rfl rfl

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz374))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz268 qz284 qz567)

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz358 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 92416659757 549755813888 1663204363281 9328394089005056 Bool.false 40530076871 274877906944 6649530024369 37313576356020224 (BSN.cpow_neg_s_mk qz13 106726 1000 20 qz14 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep322 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz374) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz374) (Real.sqrt qz375) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep323 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 135746 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep324 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 106726 1000 0 1 3372893643545847 1125899906842624 125000000067873 16968250000000000000 179987723500537033461 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 56587765202795681021952 18889465931478580854784 1000000000542984 135746000000000000000 3372893643545847 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep325 := nat_lit 11142086519179758263387210245437890625

noncomputable def ep326 := BSN.sin_dyadic_bound_f 1827012975 2147483648 2 1 1048576 271758 ep325 ep93 ep325 ep325 ep94 ep325 788306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1827012975) qz287 0 1 ep325 ep93 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1827012975) qz288 0 1 ep325 ep94 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83813315) qz16)

noncomputable def ep327 := @Enclosure.Real.IsNear.cos_image qz69 qz376 Bool.false 83813315 262144 825 1048576 Bool.false 788306 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 179987723500537033461 562949953421312000 6670375003621906899 8484125000000000000000 83813315 262144 825 1048576 (ep324 rfl) rfl) (Enclosure.sfrac_false_div 83813315 262144) (BSN.cos_reduce3 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32141152170691128197120) qz19) 226375608064910080 72057594037927936 Bool.false 788306 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 83813315 262144 226375608064910080 72057594037927936 50 32141152170691128197120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 788306 1048576 32141152170691128197120 37778931862957161709568 1827012975 2147483648 271758 271492 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep328 := nat_lit 398226981276359586093505315386192322110325011967984711384531770991857462890625

noncomputable def ep329 := nat_lit 124146092000887301607363286138680390420639338310440040247570654449462890625

noncomputable def ep330 := nat_lit 1194432651645076983677301219586299605550133757227333254073100171666673462890625

noncomputable def ep331 := BSN.cos_dyadic_bound_f 1827012975 2147483648 3 2 1048576 271758 ep328 ep70 ep329 ep330 ep73 ep329 691436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1827012975) qz291 0 2 ep328 ep70 ep329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1827012975) qz292 0 2 ep330 ep73 ep329 rfl rfl rfl rfl) rfl rfl

noncomputable def ep332 := @Enclosure.Real.IsNear.sin_image qz69 qz376 Bool.false 83813315 262144 825 1048576 Bool.true 691436 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 179987723500537033461 562949953421312000 6670375003621906899 8484125000000000000000 83813315 262144 825 1048576 (ep324 rfl) rfl) (Enclosure.sfrac_false_div 83813315 262144) (BSN.sin_reduce3 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32141152170691128197120) qz19) 226375608064910080 72057594037927936 Bool.false 691436 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 83813315 262144 226375608064910080 72057594037927936 50 32141152170691128197120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 691436 1048576 32141152170691128197120 37778931862957161709568 1827012975 2147483648 271758 271492 (ep331 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz377 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep322 rfl rfl) rfl)

noncomputable def ep333 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 92416659757 549755813888 1663204363281 9328394089005056 Bool.false 40530076871 274877906944 6649530024369 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 234469 1048576 1 1048576 394153 524288 56519513 71169998848 92416659757 549755813888 1663204363281 9328394089005056 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 788306 1048576 113039026 142339997696 394153 524288 56519513 71169998848 (ep327 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 234469 1048576 1 1048576 172859 262144 56519513 71169998848 40530076871 274877906944 6649530024369 37313576356020224 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 172859 262144 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 691436 1048576 113039026 142339997696 172859 262144 56519513 71169998848 (ep332 rfl rfl) rfl)) rfl)

noncomputable def ep334 := @ep278 92416659757 549755813888 1663204363281 9328394089005056 Bool.false 40530076871 274877906944 6649530024369 37313576356020224 Bool.false 694406516501269417295872 1263118095269 1099511627776 391921309924491 74627152712040448 Bool.true 7440784985121982775296 6767354521 68719476736 12246403496075 2332098522251264 (ep279 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep320 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep321 ep333) rfl rfl

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt qz378))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz268 qz284 qz568)

noncomputable def ep335 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 13397637127 274877906944 810286718271 4664197044502528 Bool.false 116935722765 549755813888 6535769457535 37313576356020224 (BSN.cpow_neg_s_mk qz13 106726 1000 21 qz14 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep336 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz378) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz378) (Real.sqrt qz379) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep337 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 135746 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep338 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz568 106726 1000 0 1 3427826275261687 1125899906842624 125000000067873 16968250000000000000 182919093526789403381 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 57509381830540779323392 18889465931478580854784 1000000000542984 135746000000000000000 3427826275261687 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep339 := nat_lit 2495630262892189393373119932215993772970512085586210874695991434701342286185281

noncomputable def ep340 := nat_lit 4859705578882430930552465766392530599267925750042098805741412099382217966401

noncomputable def ep341 := nat_lit 7477171377518803318258254865115196257713000405258548426476491479905262422623041

noncomputable def ep342 := BSN.cos_dyadic_bound_f 2889523593 2147483648 3 2 1048576 271758 ep339 ep70 ep340 ep341 ep73 ep340 234206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2889523593) qz291 0 2 ep339 ep70 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2889523593) qz292 0 2 ep341 ep73 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170356681) qz26)

noncomputable def ep343 := @Enclosure.Real.IsNear.cos_image qz71 qz380 Bool.false 170356681 524288 825 1048576 Bool.true 234206 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 182919093526789403381 562949953421312000 6670375003621906899 8484125000000000000000 170356681 524288 825 1048576 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 170356681 524288) (BSN.cos_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101666073259653927534592) qz301) 226375608064910080 72057594037927936 Bool.false 234206 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 170356681 524288 226375608064910080 72057594037927936 51 101666073259653927534592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 234206 1048576 101666073259653927534592 75557863725914323419136 2889523593 2147483648 271758 271492 (ep342 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep344 := nat_lit 4488246708742834963327173905375674766867507413455145895408191452782910340760385

noncomputable def ep345 := nat_lit 11747063761484472396731227664743084101777990393549123470859777232937193968141121

noncomputable def ep346 := BSN.sin_dyadic_bound_f 2889523593 2147483648 3 2 1048576 271758 ep344 ep77 ep340 ep345 ep79 ep340 1022085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2889523593) qz287 0 2 ep344 ep77 ep340 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2889523593) qz288 0 2 ep345 ep79 ep340 rfl rfl rfl rfl) rfl rfl

noncomputable def ep347 := @Enclosure.Real.IsNear.sin_image qz71 qz380 Bool.false 170356681 524288 825 1048576 Bool.true 1022085 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 182919093526789403381 562949953421312000 6670375003621906899 8484125000000000000000 170356681 524288 825 1048576 (ep338 rfl) rfl) (Enclosure.sfrac_false_div 170356681 524288) (BSN.sin_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101666073259653927534592) qz301) 226375608064910080 72057594037927936 Bool.false 1022085 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 170356681 524288 226375608064910080 72057594037927936 51 101666073259653927534592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1022085 1048576 101666073259653927534592 75557863725914323419136 2889523593 2147483648 271758 271492 (ep346 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep336 rfl rfl) rfl)

noncomputable def ep348 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 13397637127 274877906944 810286718271 4664197044502528 Bool.false 116935722765 549755813888 6535769457535 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz71) 114409 524288 1 524288 117103 524288 56519513 71169998848 13397637127 274877906944 810286718271 4664197044502528 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 234206 1048576 113039026 142339997696 117103 524288 56519513 71169998848 (ep343 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 114409 524288 1 524288 1022085 1048576 56519513 71169998848 116935722765 549755813888 6535769457535 37313576356020224 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.true 1022085 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.true 1022085 1048576 113039026 142339997696 1022085 1048576 56519513 71169998848 (ep347 rfl rfl) rfl)) rfl)

noncomputable def ep349 := @ep276 13397637127 274877906944 810286718271 4664197044502528 Bool.false 116935722765 549755813888 6535769457535 37313576356020224 Bool.false 332472400444774766608384 1209527546761 1099511627776 404885897416827 74627152712040448 Bool.false 4315369187595771707392 62796886597 549755813888 202478225394735 37313576356020224 (ep277 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep334 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep335 ep348) rfl rfl

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt qz382))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz268 qz284 qz569)

noncomputable def ep350 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.true 117164658801 549755813888 794158300977 4664197044502528 Bool.false 6392165301 1099511627776 12637329979943 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 22 qz14 rfl)

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep351 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz382) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz382) (Real.sqrt qz383) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz383) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep352 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 135746 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz569 106726 1000 0 1 3480203401436407 1125899906842624 125000000067873 16968250000000000000 185714094110850986741 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz383) Bool.false 58388124189833310502912 18889465931478580854784 1000000000542984 135746000000000000000 3480203401436407 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep352 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep354 := BSN.cos_dyadic_bound_f 58566400 2147483648 1 0 1048576 271758 0 1 1 0 1 1 1048186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 58566400) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 58566400) qz292 0 0 rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10809983) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep355 := @Enclosure.Real.IsNear.cos_image qz73 qz384 Bool.false 10809983 32768 825 1048576 Bool.true 1048186 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 185714094110850986741 562949953421312000 6670375003621906899 8484125000000000000000 10809983 32768 825 1048576 (ep353 rfl) rfl) (Enclosure.sfrac_false_div 10809983 32768) (BSN.cos_reduce2 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128788876900251467776) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 1048186 1048576 52 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 10809983 32768 226375608064910080 72057594037927936 52 128788876900251467776 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048186 1048576 128788876900251467776 4722366482869645213696 58566400 2147483648 271758 271492 (ep354 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep356 := BSN.sin_dyadic_bound_f 58566400 2147483648 1 0 1048576 271758 0 1 1 0 1 1 28593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 58566400) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 58566400) qz288 0 0 rfl) rfl rfl

noncomputable def ep357 := @Enclosure.Real.IsNear.sin_image qz73 qz384 Bool.false 10809983 32768 825 1048576 Bool.true 28593 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 185714094110850986741 562949953421312000 6670375003621906899 8484125000000000000000 10809983 32768 825 1048576 (ep353 rfl) rfl) (Enclosure.sfrac_false_div 10809983 32768) (BSN.sin_reduce2 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128788876900251467776) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 28593 1048576 52 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 10809983 32768 226375608064910080 72057594037927936 52 128788876900251467776 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28593 1048576 128788876900251467776 4722366482869645213696 58566400 2147483648 271758 271492 (ep356 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz385 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep351 rfl rfl) rfl)

noncomputable def ep358 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.true 117164658801 549755813888 794158300977 4664197044502528 Bool.false 6392165301 1099511627776 12637329979943 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz73) 223557 1048576 1 1048576 524093 524288 56519513 71169998848 117164658801 549755813888 794158300977 4664197044502528 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.true 1048186 1048576 113039026 142339997696 524093 524288 56519513 71169998848 (ep355 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 223557 1048576 1 1048576 28593 1048576 56519513 71169998848 6392165301 1099511627776 12637329979943 74627152712040448 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 28593 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 28593 1048576 113039026 142339997696 28593 1048576 56519513 71169998848 (ep357 rfl rfl) rfl)) rfl)

noncomputable def ep359 := @ep274 117164658801 549755813888 794158300977 4664197044502528 Bool.false 6392165301 1099511627776 12637329979943 74627152712040448 Bool.false 536120896173442378760192 975198229159 1099511627776 417592430232459 74627152712040448 Bool.false 72560037039090234818560 131985938495 1099511627776 417593780769413 74627152712040448 (ep275 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep349 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep350 ep358) rfl rfl

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz74 := (@Inv.inv Real Real.instInv (Real.sqrt qz386))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz268 qz284 qz570)

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.true 6751914483 549755813888 6180922186299 37313576356020224 Bool.true 114432717411 549755813888 6214349367307 37313576356020224 (BSN.cpow_neg_s_mk qz13 106726 1000 23 qz14 rfl)

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep361 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz386) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz386) (Real.sqrt qz387) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz387) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep362 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 135746 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz570 106726 1000 0 1 3530250507853047 1125899906842624 125000000067873 16968250000000000000 188384757850562147061 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz387) Bool.false 59227775304360265777152 18889465931478580854784 1000000000542984 135746000000000000000 3530250507853047 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep364 := BSN.sin_dyadic_bound_f 126562074 2147483648 1 0 1048576 271758 0 1 1 0 1 1 61762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 126562074) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 126562074) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350893955) qz30)

noncomputable def ep365 := @Enclosure.Real.IsNear.cos_image qz75 qz388 Bool.false 350893955 1048576 825 1048576 Bool.true 61762 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 188384757850562147061 562949953421312000 6670375003621906899 8484125000000000000000 350893955 1048576 825 1048576 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 350893955 1048576) (BSN.cos_reduce1 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8906014222151550238720) qz32) 226375608064910080 72057594037927936 Bool.false 61762 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 350893955 1048576 226375608064910080 72057594037927936 53 8906014222151550238720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61762 1048576 8906014222151550238720 151115727451828646838272 126562074 2147483648 271758 271492 (ep364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep366 := BSN.cos_dyadic_bound_f 126562074 2147483648 1 0 1048576 271758 0 1 1 0 1 1 1046754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 126562074) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 126562074) qz292 0 0 rfl) rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.sin_image qz75 qz388 Bool.false 350893955 1048576 825 1048576 Bool.false 1046754 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 188384757850562147061 562949953421312000 6670375003621906899 8484125000000000000000 350893955 1048576 825 1048576 (ep363 rfl) rfl) (Enclosure.sfrac_false_div 350893955 1048576) (BSN.sin_reduce1 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8906014222151550238720) qz32) 226375608064910080 72057594037927936 Bool.false 1046754 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 350893955 1048576 226375608064910080 72057594037927936 53 8906014222151550238720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046754 1048576 8906014222151550238720 151115727451828646838272 126562074 2147483648 271758 271492 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz389 := (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep361 rfl rfl) rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.true 6751914483 549755813888 6180922186299 37313576356020224 Bool.true 114432717411 549755813888 6214349367307 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz75) 218643 1048576 1 1048576 30881 524288 56519513 71169998848 6751914483 549755813888 6180922186299 37313576356020224 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.true 61762 1048576 113039026 142339997696 30881 524288 56519513 71169998848 (ep365 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 218643 1048576 1 1048576 523377 524288 56519513 71169998848 114432717411 549755813888 6214349367307 37313576356020224 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.false 523377 524288 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.false 1046754 1048576 113039026 142339997696 523377 524288 56519513 71169998848 (ep367 rfl rfl) rfl)) rfl)

noncomputable def ep369 := @ep272 6751914483 549755813888 6180922186299 37313576356020224 Bool.true 114432717411 549755813888 6214349367307 37313576356020224 Bool.false 528697087689634699280384 961694400193 1099511627776 429954274605057 74627152712040448 Bool.true 53260066352309391589376 96879496327 1099511627776 430022479504027 74627152712040448 (ep273 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep360 ep368) rfl rfl

noncomputable abbrev qz390 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz76 := (@Inv.inv Real Real.instInv (Real.sqrt qz390))

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz268 qz284 qz571)

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 223051540173 1099511627776 12168167490931 74627152712040448 Bool.false 6222755847 274877906944 3026332412359 18656788178010112 (BSN.cpow_neg_s_mk qz13 106726 1000 24 qz14 rfl)

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz390) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz390) (Real.sqrt qz391) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz391) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep372 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 135746 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz571 106726 1000 0 1 3578169457974519 1125899906842624 125000000067873 16968250000000000000 190941856785894257397 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 60031721881041427759104 18889465931478580854784 1000000000542984 135746000000000000000 3578169457974519 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep374 := nat_lit 6218450168908709664099914220979764711068365844575640318181579221965162371030625

noncomputable def ep375 := nat_lit 9320922600876867844374381149122138956063404362664271040320188119583250390625

noncomputable def ep376 := nat_lit 16271326091502343715180312056896043161154950747777601537362665276762766661590625

noncomputable def ep377 := BSN.sin_dyadic_bound_f 3134601685 2147483648 3 2 1048576 271758 ep374 ep77 ep375 ep376 ep79 ep375 1042107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3134601685) qz287 0 2 ep374 ep77 ep375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3134601685) qz288 0 2 ep376 ep79 ep375 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 355656923) qz30)

noncomputable def ep378 := @Enclosure.Real.IsNear.cos_image qz77 qz392 Bool.false 355656923 1048576 825 1048576 Bool.false 1042107 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 190941856785894257397 562949953421312000 6670375003621906899 8484125000000000000000 355656923 1048576 825 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 355656923 1048576) (BSN.cos_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220577984136892337094656) qz32) 226375608064910080 72057594037927936 Bool.false 1042107 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 355656923 1048576 226375608064910080 72057594037927936 53 220577984136892337094656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1042107 1048576 220577984136892337094656 151115727451828646838272 3134601685 2147483648 271758 271492 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep379 := nat_lit 3458837170549672865764118736610590234574009204480984297229908540256016095190625

noncomputable def ep380 := nat_lit 10357869666447264861603607447533526425809900804717624349609085244528881784790625

noncomputable def ep381 := BSN.cos_dyadic_bound_f 3134601685 2147483648 3 2 1048576 271758 ep379 ep70 ep375 ep380 ep73 ep375 116292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3134601685) qz291 0 2 ep379 ep70 ep375 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3134601685) qz292 0 2 ep380 ep73 ep375 rfl rfl rfl rfl) rfl rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.sin_image qz77 qz392 Bool.false 355656923 1048576 825 1048576 Bool.true 116292 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 190941856785894257397 562949953421312000 6670375003621906899 8484125000000000000000 355656923 1048576 825 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 355656923 1048576) (BSN.sin_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220577984136892337094656) qz32) 226375608064910080 72057594037927936 Bool.false 116292 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 355656923 1048576 226375608064910080 72057594037927936 53 220577984136892337094656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 116292 1048576 220577984136892337094656 151115727451828646838272 3134601685 2147483648 271758 271492 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep371 rfl rfl) rfl)

noncomputable def ep383 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 223051540173 1099511627776 12168167490931 74627152712040448 Bool.false 6222755847 274877906944 3026332412359 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz77) 214039 1048576 1 1048576 1042107 1048576 56519513 71169998848 223051540173 1099511627776 12168167490931 74627152712040448 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 1042107 1048576 113039026 142339997696 1042107 1048576 56519513 71169998848 (ep378 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 214039 1048576 1 1048576 29073 262144 56519513 71169998848 6222755847 274877906944 3026332412359 18656788178010112 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.true 29073 262144 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.true 116292 1048576 113039026 142339997696 29073 262144 56519513 71169998848 (ep382 rfl rfl) rfl)) rfl)

noncomputable def ep384 := @ep269 223051540173 1099511627776 12168167490931 74627152712040448 Bool.false 6222755847 274877906944 3026332412359 18656788178010112 Bool.false ep270 592372970183 549755813888 110530610523997 18656788178010112 Bool.true 19788040765567104188416 71988472939 1099511627776 442127809153463 74627152712040448 (ep271 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep370 ep383) rfl rfl

theorem EMRow33.d8 : Enclosure.Complex.IsNear qz61 Bool.false 592372970183 549755813888 110530610523997 18656788178010112 Bool.true 71988472939 1099511627776 442127809153463 74627152712040448 := ep268 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep384 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow33.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow33.d10 : @Eq Nat (Nat.pow 27 1) 27 := @Eq.refl Nat 27

noncomputable def ep385 := nat_lit 3322873430957300566153362385691

noncomputable def ep386 := nat_lit 3409417312272007491892543488000

noncomputable def ep387 := nat_lit 815662534906162044306401180441838357877

noncomputable def ep388 := nat_lit 122509242855636235281695920535325219225600

noncomputable abbrev qz603 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz572 := qz603

noncomputable abbrev qz394 := qz572

noncomputable abbrev qz78 := qz394

noncomputable abbrev qz573 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz395 := qz573

noncomputable abbrev qz79 := qz395

noncomputable abbrev qz604 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz605 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz601 (@HAdd.hAdd Complex Complex Complex qz601 qz604 (@HMul.hMul Complex Complex Complex qz603 Complex.I (@HDiv.hDiv Complex Complex Complex qz605 (↑qz602) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz396 := qz574

noncomputable abbrev qz80 := (Complex.Stirling.logGammaStirling 1 qz396)

noncomputable abbrev qz575 := (@HAdd.hAdd Complex Complex Complex qz601 qz604 (@HMul.hMul Complex Complex Complex qz603 Complex.I (@HDiv.hDiv Complex Complex Complex qz605 (↑qz602) (2 : Complex))))

noncomputable abbrev qz397 := qz575

noncomputable abbrev qz81 := qz397

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz284 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz398 := (@instHSub Real Real.instSub)

noncomputable def ep389 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82))) (zetaApproximant qz5 1 27))

noncomputable def ep390 := @Enclosure.Real.IsNear.of_eq ep389 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 27))))

noncomputable def ep391 := nat_lit 44305170511235285957290068853

noncomputable def ep392 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 27))) ep391

noncomputable def ep393 := nat_lit 45458897496960099891900579840

noncomputable def ep394 := nat_lit 4071219343247055758792852066463674334353

noncomputable def ep395 := nat_lit 612546214278181176408479602676626096128000

noncomputable def ep396 := nat_lit 3589346336470160848194571

noncomputable def ep397 := nat_lit 852354328068001872973135872000

noncomputable def ep398 := nat_lit 295555470156435947464743156063227293

noncomputable def ep399 := nat_lit 25522758928257549017019983444859420672000

noncomputable def ep400 := nat_lit 37763540673315012502872470207219761109054933393112154767360

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 27)) 1048575 1048576 5764531

noncomputable def ep402 := nat_lit 3168955762194069519869113

noncomputable def ep403 := nat_lit 3251473724624640933888000

noncomputable def ep404 := nat_lit 54468834712866521757016068311

noncomputable def ep405 := nat_lit 8606803768346481910125428736000

noncomputable def ep406 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.true 1048575 1048576 11529062

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102119989) qz30)

noncomputable def ep407 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz399 Bool.false 102119989 1048576 83

noncomputable def ep408 := nat_lit 16848907596592943695033399

noncomputable def ep409 := nat_lit 53377499136000000000000000000

noncomputable def ep410 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) Bool.false 2631612085005407934709 27021597764222976000 ep408 ep409

noncomputable def ep411 := nat_lit 5983186899592943695033399

noncomputable def ep412 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82 4282258983440903493877 27021597764222976000 ep411 ep409 4003345623 65536000

noncomputable def ep413 := nat_lit 172465329602914414409089024000

noncomputable def ep414 := nat_lit 1835491936165692973109739

noncomputable def ep415 := nat_lit 8896249856000000000000000000

noncomputable def ep416 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 377841851024385660017 4503599627370496000 ep414 ep415 Bool.false 4282258983440903493877 27021597764222976000

noncomputable def ep417 := nat_lit 1802723936067834224693739

noncomputable def ep418 := nat_lit 5589970899539566195897399

noncomputable def ep419 := @Enclosure.Complex.IsNear.subLitP qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 342017878942640095017 4503599627370496000 ep417 ep415 Bool.false 4366390426117769829877 27021597764222976000 ep418

noncomputable def ep420 := nat_lit 1701648419478401720793840803152658432

noncomputable def ep421 := nat_lit 1205348747633025748493523435296653312

noncomputable abbrev qz606 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz576 := qz606

noncomputable abbrev qz400 := (@HSub.hSub Complex Complex Complex qz573 qz574 qz576)

noncomputable abbrev qz401 := (Complex.log qz574)

noncomputable abbrev qz83 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz400 qz401) qz396)

noncomputable abbrev qz402 := qz576

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz394 qz402 ↑(Real.log (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)))

noncomputable abbrev qz577 := qz605

noncomputable abbrev qz403 := qz577

noncomputable abbrev qz85 := qz403

noncomputable abbrev qz86 := (@instHMul Nat instMulNat)

noncomputable abbrev qz578 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz404 := qz578

noncomputable abbrev qz87 := qz404

noncomputable abbrev qz88 := qz396

noncomputable abbrev qz405 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz89 := qz405

noncomputable abbrev qz90 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz406 := (@instHSub Int Int.instSub)

noncomputable abbrev qz407 := (@instHMul Int Int.instMul)

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq qz80 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 342017878942640095017

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 342018174954465247017 4503599627370496000

noncomputable def ep424 := nat_lit 11751644837647410143970780512256

noncomputable def ep425 := nat_lit 37507008163486651327554397405184000

noncomputable def ep426 := @ep423 55014744852386221173 271492000000000000000000 Bool.false 1455477516331723797671 9007199254740992000 14215750039959753639 135746000000000000000000 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000 Bool.true ep424 342017878942640095017 4503599627370496000 ep417 ep415 Bool.false ep425

noncomputable def ep427 := @Enclosure.Complex.IsNear.addLitP qz83 qz84 Bool.true 346156702361675743017 4503599627370496000 27119000004928462149 135746000000000000000000

noncomputable def ep428 := nat_lit 44829006227631668857012224

noncomputable def ep429 := @ep427 Bool.false 1455477516331723797671 9007199254740992000 14215750039959753639 135746000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep428 342018174954465247017 4503599627370496000 55014744852386221173 271492000000000000000000 Bool.false 1455477516331723797671 1455477516331723797671 9007199254740992000

noncomputable abbrev qz91 := (@HMul.hMul Complex Complex Complex qz394 qz400 qz401)

noncomputable def ep430 := @Enclosure.Complex.IsNear.subLitP qz91 qz88 Bool.true 336023603200092127017 4503599627370496000 27119000004928462149 135746000000000000000000 Bool.false 1936128690162467353767

noncomputable def ep431 := nat_lit 1384626809446702972068000

noncomputable def ep432 := nat_lit 5821910065326895190684000

noncomputable def ep433 := @ep430 9007199254740992000 14215750039959753639 135746000000000000000000 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 Bool.true ep431 346156702361675743017 4503599627370496000 27119000004928462149 135746000000000000000000 Bool.false ep432 1455477516331723797671 9007199254740992000 14215750039959753639 135746000000000000000000

noncomputable abbrev qz92 := qz400

noncomputable abbrev qz93 := qz401

noncomputable def ep434 := @Enclosure.Complex.IsNear.mul qz92 qz93 Bool.true 336023603200092127017 4503599627370496000 27119000004928462149 135746000000000000000000 Bool.false 1936128690162467353767 9007199254740992000 14215750039959753639

noncomputable abbrev qz94 := (Complex.re qz400)

noncomputable abbrev qz95 := (Complex.re qz401)

noncomputable abbrev qz96 := (Complex.im qz400)

noncomputable abbrev qz97 := (Complex.im qz401)

noncomputable def ep435 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz94 qz95) (@HMul.hMul Real Real Real qz0 qz96 qz97) 250814825874175563 36028797018963968 1750000005226221 542984000000000000000 45921932054295509049 562949953421312000

noncomputable def ep436 := nat_lit 1513315774159626310490619155350290432

noncomputable def ep437 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz95 7000 4000 0 1 35830689410596509 9007199254740992 250000000746603 135746000000000000000

noncomputable def ep438 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable abbrev qz98 := (Enclosure.sfrac Bool.false 213452 4000)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz92 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz98) Bool.false 7000 4000 0 1 Bool.false 213452 4000 0

noncomputable abbrev qz408 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz99 := qz408

noncomputable abbrev qz409 := (Complex.log (Complex.mk qz99 qz98))

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq qz93 qz409 Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000

noncomputable def ep441 := nat_lit 24402996409641953613677199845903352498658332606506319734426912686080

noncomputable def ep442 := nat_lit 222920910227148403312037039370225847429488788738701915759382102016

noncomputable def ep443 := nat_lit 68316461444509836467290154302843316542439436702588046084669440

noncomputable def ep444 := BSN.log_dyadic_bound 12874756304 78410756304 4 3 ep441 1048576 271492 ep442 ep443 347490 91285512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12874756304) (BSN.artanhQ 78410756304) 0 3 ep442 ep441 ep443 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz100 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz410 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz579 := (Real.log (Enclosure.sfrac Bool.false 45642756304 16000000))

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz579 1 2 0 1 35830689410596509 4503599627370496 250000000746603 67873000000000000000 35830689410596509 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 45642756304 16000000 35830689410596509 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45642756304) qz411)) Bool.false 300569607835245160169472 37778931862957161709568 1000000002986412 271492000000000000000 35830689410596509 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 45642756304 16000000 11 91285512608 65536000000 347490 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep446 := BSN.arctan_dyadic_bound_f 9000 213452 1 0 1048576 271492 0 1 1 0 1 1 44186 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz101 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz102 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz410 BSN.pi_near_15 rfl)

noncomputable abbrev qz412 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 213452)))

noncomputable def ep447 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz412 884279719003555 562949953421312 1 2000000000000000 44186 1048576 1 271492 902359983991997595648 860557540885923 562949953421312 500000000067873 135746000000000000000 qz102 (ep446 rfl) rfl rfl

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 213452) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep448 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (ep440 (@congrArg Complex Complex qz88 (Complex.mk qz99 qz98) Complex.log (BSN.w_shift_mk qz13 Bool.false 106726 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz409 Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz409) (@HMul.hMul Real Real Real qz0 qz100 qz579) Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 9000 213452 4000 45642756304 16000000 rfl rfl rfl) (ep445 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz409) qz413 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 9000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz413 (@HSub.hSub Real Real Real qz398 qz101 qz412) Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 213452 9000 rfl rfl) ep447))))

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 213452 4000 0 1 860557540885923 562949953421312 500000000067873 135746000000000000000

noncomputable def ep450 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable def ep451 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (ep440 (@congrArg Complex Complex qz88 (Complex.mk qz99 qz98) Complex.log (BSN.w_shift_mk qz13 Bool.false 106726 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz409 Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz409) (@HMul.hMul Real Real Real qz0 qz100 qz579) Bool.false 35830689410596509 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 9000 213452 4000 45642756304 16000000 rfl rfl rfl) (ep445 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz409) qz413 Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 9000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz413 (@HSub.hSub Real Real Real qz398 qz101 qz412) Bool.false 860557540885923 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 213452 9000 rfl rfl) ep447))))

noncomputable abbrev qz103 := (@ep439 1 (BSN.w_sub_half_mk qz284 Bool.false 106726 1000 2 qz286 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 213452 4000) Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 213452 4000)))

noncomputable def ep452 := @ep435 26681500003621906899 135746000000000000000000 ep436 336023603200092127017 4503599627370496000 27119000004928462149 135746000000000000000000 (@ep437 250814825874175563 36028797018963968 1750000005226221 542984000000000000000 (ep438 qz103) ep448 rfl) (@ep449 45921932054295509049 562949953421312000 26681500003621906899 135746000000000000000000 (ep450 qz103) ep451 rfl) rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz94 qz97) (@HMul.hMul Real Real Real qz0 qz96 qz95) 6023902786201461 2251799813685248 3500000000475111 542984000000000000000 1912033079017661509767 9007199254740992000

noncomputable def ep454 := nat_lit 4359774223778507239507585874805129216

noncomputable def ep455 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz97 7000 4000 0 1 860557540885923 562949953421312 500000000067873 135746000000000000000

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz95 213452 4000 0 1 35830689410596509 9007199254740992 250000000746603 135746000000000000000

noncomputable def ep457 := @ep453 13340750039840975889 135746000000000000000000 ep454 1936128690162467353767 9007199254740992000 14215750039959753639 135746000000000000000000 (@ep455 6023902786201461 2251799813685248 3500000000475111 542984000000000000000 (ep438 qz103) ep451 rfl) (@ep456 1912033079017661509767 9007199254740992000 13340750039840975889 135746000000000000000000 (ep450 qz103) ep448 rfl) rfl

noncomputable def ep458 := @Enclosure.Complex.IsNear.of_eq qz88 (Complex.mk qz99 qz98) Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 106726 1000 2 qz14 rfl)

noncomputable abbrev qz414 := (ep458 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 213452 4000) Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 213452 4000)))

noncomputable abbrev qz104 := qz414

noncomputable def ep459 := ep433 (@ep434 135746000000000000000000 (ep452 rfl) (ep457 rfl)) qz104 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz105 := qz402

noncomputable def ep460 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz106 := (@Enclosure.Complex.IsNear.of_eq qz402 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz410 qz294))

noncomputable def ep462 := ep461 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow33.d4)

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep464 := ep463 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep465 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz105) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz105) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep466 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz105) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep467 := ep466 (@Enclosure.Complex.IsNear.re_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz105) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep469 := ep468 (@Enclosure.Complex.IsNear.im_isNear qz105 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz106) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow33.d4)

noncomputable def ep470 := @ep429 14215750039959753639 135746000000000000000000 (ep459 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep460 131072 3 1048576 (ep462 rfl) (ep464 rfl) rfl rfl) (@ep465 1 0 1 (ep467 rfl) (ep469 rfl) rfl rfl))

noncomputable abbrev qz107 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz415 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz108 := (@HMul.hMul Complex Complex Complex qz394 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz415) (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz415) (1 : Complex)))

noncomputable abbrev qz416 := (@HPow.hPow Complex Int Complex qz578 qz574 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz109 := qz416

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109)) Bool.false 2258391 34359738368 3 34359738368

noncomputable def ep472 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109) Bool.false 0 1 0 1 Bool.false

noncomputable def ep473 := @ep472 0 1 0 1 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000 Bool.false 2258391 2258391 34359738368 3 34359738368 Bool.true 40171506311 40171506311 25769803776000 53363

noncomputable def ep474 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep475 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz109 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000

noncomputable abbrev qz110 := (Complex.re qz416)

noncomputable abbrev qz111 := (Complex.im qz416)

noncomputable def ep476 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) 2258391 34359738368 3 34359738368 0 1 0

noncomputable def ep477 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 1 12 0 1 6775173 8589934592 9 8589934592 2258391

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz417 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz20)

noncomputable def ep479 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep478 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz417)

noncomputable def ep480 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363 2147483648000

noncomputable abbrev qz580 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz418 := (@HPow.hPow Complex Nat Complex qz580 qz574 1)

noncomputable abbrev qz112 := (@Inv.inv Complex Complex.instInv qz418)

noncomputable def ep481 := @Enclosure.Complex.IsNear.of_eq qz109 qz112 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363

noncomputable def ep482 := @Enclosure.Complex.IsNear.of_parts qz112 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363

noncomputable abbrev qz113 := (Complex.re qz418)

noncomputable abbrev qz114 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz115 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz116 := qz418

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_ff qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 9000 4000 0 1 752797 2147483648 1 2147483648

noncomputable def ep484 := @Enclosure.Complex.IsNear.re_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable def ep485 := @Enclosure.Complex.IsNear.of_eq qz116 qz88 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0

noncomputable def ep486 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) Bool.false 752797 2147483648 1 2147483648 752797 2147483648 1

noncomputable abbrev qz117 := (Complex.im qz418)

noncomputable abbrev qz419 := (@instHAdd Real Real.instAdd)

noncomputable def ep487 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117)) Bool.false 2852672269 1000000 0 1

noncomputable def ep488 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz113 qz113) (@HMul.hMul Real Real Real qz0 qz117 qz117) 81 16 0 1 2847609769 1000000

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ff qz113 qz113 9000 4000 0 1 9000 4000 0 1

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff qz117 qz117 213452 4000 0 1 213452 4000 0 1

noncomputable def ep491 := @Enclosure.Complex.IsNear.im_isNear qz116 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable abbrev qz118 := (ep484 (@ep485 1 (BSN.pow_one_c qz396) qz414))

noncomputable abbrev qz119 := (ep491 (@ep485 1 (BSN.pow_one_c qz396) qz414))

noncomputable def ep492 := @ep488 0 1 45642756304 2852672269 1000000 0 1 (@ep489 81 16 0 1 qz118 qz118 rfl) (@ep490 2847609769 1000000 0 1 qz119 qz119 rfl)

noncomputable def ep493 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116) 2852672269 1000000 0 1 376398 376399 1073741824 (ep487 (Enclosure.Complex.normSq_eq_mul_add_mul qz116) (ep492 rfl rfl)) rfl

noncomputable def ep494 := @Enclosure.Real.IsNear.of_eq (Complex.re qz112) (@HMul.hMul Real Real Real qz0 qz113 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.false 6775173 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz116) (@ep483 6775173 8589934592 9 8589934592 qz118 (@ep486 2147483648 (ep493 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep495 := @Enclosure.Real.IsNear.of_eq (Complex.im qz112) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116))) Bool.true 40171506311 2147483648000 53363 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz116)

noncomputable def ep496 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz117) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz116)) 213452 4000 0 1 752797 2147483648 1

noncomputable def ep497 := @ep496 2147483648 40171506311 2147483648000 53363 2147483648000 (@Enclosure.Real.IsNear.neg qz117 Bool.false 213452 4000 0 1 qz119) (@ep486 2147483648 (ep493 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 0 1 0 1 40171506311 2147483648000 53363 2147483648000 0

noncomputable def ep499 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep478 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz417)

noncomputable def ep500 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363 2147483648000

noncomputable abbrev qz120 := (@ep481 2147483648000 (BSN.zpow_one_sub_two_mul qz396 1 1 rfl rfl) (@ep482 2147483648000 ep494 (ep495 ep497)))

noncomputable def ep501 := @ep476 1 2258391 2258391 34359738368 3 34359738368 (@ep477 34359738368 3 34359738368 ep479 (ep480 qz120) rfl) (@ep498 1 0 1 ep499 (ep500 qz120) rfl) rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110) 40171506311 25769803776000 53363 25769803776000 0 1 0

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz111 1 12 0 1 40171506311 2147483648000 53363 2147483648000 40171506311

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz110 0 1 0 1 6775173 8589934592 9 8589934592 0

noncomputable def ep505 := @ep502 1 40171506311 40171506311 25769803776000 53363 25769803776000 (@ep503 25769803776000 53363 25769803776000 ep479 (ep500 qz120) rfl) (@ep504 1 0 1 ep499 (ep480 qz120) rfl) rfl

noncomputable abbrev qz121 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz294 qz294)

noncomputable def ep506 := @ep473 25769803776000 (@ep474 0 1 0 1 (BSN.stirling_sum_base qz88) qz121) (ep475 (ep501 rfl) (ep505 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep507 := @ep426 4366390426117769829877 27021597764222976000 ep418 ep409 (ep470 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep471 Bool.true 40171506311 25769803776000 53363 25769803776000 (BSN.stirling_sum_succ qz88 0 1 rfl) (ep506 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep508 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 35823972081745565 4503599627370496 250000000746603 67873000000000000000 Bool.false 876369194550691 281474976710656

noncomputable abbrev qz122 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz397 qz415))

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz122) Bool.false 35823972081745565 4503599627370496 250000000746603 67873000000000000000 Bool.false 876369194550691 281474976710656 500000000067873 67873000000000000000

noncomputable def ep510 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz122 Bool.false 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000 Bool.false

noncomputable def ep511 := nat_lit 645347309273121513613210639400960

noncomputable def ep512 := nat_lit 986703994504368425324127453184

noncomputable abbrev qz123 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz397 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep513 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz123) Bool.false 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000

noncomputable def ep514 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz123 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz420 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz98))

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq qz123 qz420 Bool.false 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000

noncomputable def ep516 := nat_lit 24253991320049509080459243425099566787237795652800840617217312686080

noncomputable def ep517 := nat_lit 219224501782567177376899845015713782770565380952215731741462102016

noncomputable def ep518 := nat_lit 65808708827878383520961946849508374790261087352999873284669440

noncomputable def ep519 := BSN.log_dyadic_bound 12794756304 78330756304 4 3 ep516 1048576 271492 ep517 ep518 345650 91125512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12794756304) (BSN.artanhQ 78330756304) 0 3 ep517 ep516 ep518 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 45562756304 16000000)) 1 2 0 1 35822786670771869 4503599627370496 250000000746603 67873000000000000000 35822786670771869 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 45562756304 16000000 35822786670771869 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45562756304) qz411)) Bool.false 300503314848730266468352 37778931862957161709568 1000000002986412 271492000000000000000 35822786670771869 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 45562756304 16000000 11 91125512608 65536000000 345650 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep519 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep521 := BSN.arctan_dyadic_bound_f 1000 213452 1 0 1048576 271492 0 1 1 0 1 1 4912 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz421 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 213452)

noncomputable def ep522 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz422)) 884279719003555 562949953421312 1 2000000000000000 4912 1048576 1 271492 924469280462666203136 881642609083811 562949953421312 500000000067873 135746000000000000000 qz102 (ep521 rfl) rfl rfl

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz273 qz397 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz423 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz98)

noncomputable def ep523 := @ep514 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000 Bool.false 35822786670771869 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 881642609083811 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz121) (ep515 (@congrArg Complex Complex qz124 qz423 Complex.log (BSN.w_shift_mk qz13 Bool.false 106726 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz420 Bool.false 35822786670771869 9007199254740992 250000000746603 135746000000000000000 Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz420) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 45562756304 16000000))) Bool.false 35822786670771869 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 1000 213452 4000 45562756304 16000000 rfl rfl rfl) (ep520 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz420) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz421)) Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 1000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz421)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz422))) Bool.false 881642609083811 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 213452 1000 rfl rfl) ep522)))) rfl rfl

noncomputable abbrev qz424 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz98))

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq qz122 qz424 Bool.false 35825157492719261 9007199254740992 250000000746603 135746000000000000000 Bool.false 871095780017571 562949953421312 500000000067873 135746000000000000000

noncomputable def ep525 := nat_lit 24298613014768343096698677332879476041102375110763543552380192686080

noncomputable def ep526 := nat_lit 220328824009716418907945241739111284061088143217925426946838102016

noncomputable def ep527 := nat_lit 66552842145329312981681278960219164711811828023476325124669440

noncomputable def ep528 := BSN.log_dyadic_bound 12818756304 78354756304 4 3 ep525 1048576 271492 ep526 ep527 346202 91173512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12818756304) (BSN.artanhQ 78354756304) 0 3 ep526 ep525 ep527 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 45586756304 16000000)) 1 2 0 1 35825157492719261 4503599627370496 250000000746603 67873000000000000000 35825157492719261 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 45586756304 16000000 35825157492719261 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45586756304) qz411)) Bool.false 300523202744684734578688 37778931862957161709568 1000000002986412 271492000000000000000 35825157492719261 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 45586756304 16000000 11 91173512608 65536000000 346202 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep528 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep530 := BSN.arctan_dyadic_bound_f 5000 213452 1 0 1048576 271492 0 1 1 0 1 1 24557 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz425 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep531 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz425 qz422)) 884279719003555 562949953421312 1 2000000000000000 24557 1048576 1 271492 913410128627704528896 871095780017571 562949953421312 500000000067873 135746000000000000000 qz102 (ep530 rfl) rfl rfl

noncomputable abbrev qz125 := (@HAdd.hAdd Complex Complex Complex qz273 qz397 qz415)

noncomputable abbrev qz426 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz98)

noncomputable def ep532 := @ep510 35825157492719261 9007199254740992 250000000746603 135746000000000000000 Bool.false 871095780017571 562949953421312 500000000067873 135746000000000000000 Bool.false ep511 35823972081745565 4503599627370496 250000000746603 67873000000000000000 Bool.false ep512 876369194550691 281474976710656 500000000067873 67873000000000000000 (ep513 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep523 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep524 (@congrArg Complex Complex qz125 qz426 Complex.log (BSN.w_shift_mk qz13 Bool.false 106726 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz424 Bool.false 35825157492719261 9007199254740992 250000000746603 135746000000000000000 Bool.false 871095780017571 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz424) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 45586756304 16000000))) Bool.false 35825157492719261 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 5000 213452 4000 45586756304 16000000 rfl rfl rfl) (ep529 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz424) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz425)) Bool.false 871095780017571 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 5000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz425)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz425 qz422))) Bool.false 871095780017571 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 213452 5000 rfl rfl) ep531)))) rfl rfl

noncomputable def ep533 := @ep419 ep409 Bool.false 35823972081745565 4503599627370496 250000000746603 67873000000000000000 Bool.false 876369194550691 281474976710656 500000000067873 67873000000000000000 Bool.true ep420 377841851024385660017 4503599627370496000 ep414 ep415 Bool.false ep421 4282258983440903493877 27021597764222976000 ep411 ep409 (@ep422 4503599627370496000 ep417 ep415 Bool.false 4366390426117769829877 27021597764222976000 ep418 ep409 (BSN.logGammaStirling_unfold 1 qz88) (ep507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep508 500000000067873 67873000000000000000 (BSN.log_sum_c_eq qz13 2) (ep509 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz126 := (@HDiv.hDiv Real Real Real qz271 qz284 (2 : Real))

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Real.log Real.pi) 106726 2000 0 1 75021 65536 1 262144 4003345623 65536000 53363 262144000 (@Enclosure.Real.IsNear.of_eq qz126 (Enclosure.sfrac Bool.false 106726 2000) Bool.false 106726 2000 0 1 (BSN.t_half_eq qz13 Bool.false 106726 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 106726 2000)) EMRow33.d5 rfl

noncomputable def ep535 := @ep412 53363 262144000 ep413 2631612085005407934709 27021597764222976000 ep408 ep409 (@ep416 ep411 ep409 (ep533 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep534 rfl rfl

noncomputable def ep536 := nat_lit 8340549090404258201570429233130167710065379754293396848459645601106378188816640

noncomputable def ep537 := nat_lit 16750993742024682954251798260363317184310964955969750305151036966975605473536

noncomputable def ep538 := nat_lit 21817174580238350565044240318157470060444253032268278816900255847808268085657856

noncomputable def ep539 := BSN.sin_dyadic_bound_f 3372912478 2147483648 3 2 1048576 271758 ep536 ep77 ep537 ep538 ep79 ep537 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372912478) qz287 0 2 ep536 ep77 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372912478) qz288 0 2 ep538 ep79 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable def ep540 := @ep407 262144 Bool.true 1048575 1048576 1 135746 (@ep410 102119989 1048576 83 262144 ep535 rfl) (Enclosure.sfrac_false_div 102119989 1048576) (BSN.cos_reduce1 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237347615300792539414528) qz32) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 102119989 1048576 226375608064910080 72057594037927936 15 237347615300792539414528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237347615300792539414528 151115727451828646838272 3372912478 2147483648 271758 271492 (ep539 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep541 := nat_lit 19508842347747845603328000

noncomputable def ep542 := nat_lit 108944795608546899730000861397

noncomputable def ep543 := nat_lit 17213607536692963820250857472000

noncomputable abbrev qz427 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 27) qz540)

noncomputable abbrev qz127 := qz427

noncomputable abbrev qz428 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable abbrev qz128 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz403 qz428 (@HSub.hSub Complex Complex Complex qz395 qz272 (1 : Complex))) qz402)

noncomputable abbrev qz129 := (@instHSub Nat instSubNat)

noncomputable abbrev qz429 := qz580

noncomputable abbrev qz130 := qz429

noncomputable abbrev qz131 := qz428

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 27) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false ep402 ep403 ep404

noncomputable def ep545 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 484032317605 549755813888 632702811089 101395587923968

noncomputable def ep546 := nat_lit 762859431105838299046740311

noncomputable def ep547 := nat_lit 1519542800998042368371230397

noncomputable def ep548 := nat_lit 1742151854220068069502497604547641344

noncomputable def ep549 := nat_lit 563789719009161249750136798710857728

noncomputable def ep550 := @ep545 Bool.true 56289009829 1099511627776 20248997345773 3244658813566976 Bool.false 306196837588216221014113 ep403 ep546 ep405 Bool.false 485982763762539132066347 ep541 ep547 ep543 Bool.false ep548 ep402 ep403 ep404 ep405 Bool.true ep549 512763762352880121170653 ep541

noncomputable def ep551 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 27) Bool.false 484032317605 549755813888 632702811089 101395587923968 Bool.true 56289009829 1099511627776 20248997345773

noncomputable abbrev qz430 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz430 qz7)) Bool.false 484032317605 549755813888 632702811089 101395587923968 Bool.true 56289009829 1099511627776 20248997345773 3244658813566976

noncomputable def ep553 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz430 qz7) Bool.false 542886521633 549755813888 113501880066979 18656788178010112 Bool.false 62190866233 549755813888 227022204689581 37313576356020224 Bool.true

noncomputable abbrev qz431 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep554 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz61 (@HPow.hPow Complex Complex Complex qz6 qz431 qz7)) Bool.false 542886521633 549755813888 113501880066979 18656788178010112 Bool.false 62190866233 549755813888 227022204689581 37313576356020224

noncomputable def ep555 := @Enclosure.Complex.IsNear.addLitP qz61 (@HPow.hPow Complex Complex Complex qz6 qz431 qz7) Bool.false 592372970183 549755813888 110530610523997 18656788178010112 Bool.true 71988472939 1099511627776 442127809153463 74627152712040448 Bool.true

noncomputable abbrev qz432 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz132 := (@Inv.inv Real Real.instInv (Real.sqrt qz432))

noncomputable abbrev qz581 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz268 qz284 qz581)

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz431 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)))) Bool.true 24743224275 274877906944 114279597807 717568776077312 Bool.false 196370205405 1099511627776 916661555823 5740550208618496 (BSN.cpow_neg_s_mk qz13 106726 1000 25 qz14 rfl)

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep557 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz432) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz432) (Real.sqrt qz433) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz433) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep558 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 135746 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep559 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz581 106726 1000 0 1 3624129903009015 1125899906842624 125000000067873 16968250000000000000 38678888802854013489 112589990684262400 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz433) Bool.false 60802810194841294602240 18889465931478580854784 1000000000542984 135746000000000000000 3624129903009015 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep558 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep560 := nat_lit 1129588434978006098895563968106948556482251715388985327136819087288401873226881

noncomputable def ep561 := nat_lit 997735548037403921711116411993918993028334993794651573025161580041286864001

noncomputable def ep562 := nat_lit 3386769833837943488843269671496857831460698476179366678264406938705123045952641

noncomputable def ep563 := BSN.cos_dyadic_bound_f 2370701807 2147483648 3 2 1048576 271758 ep560 ep70 ep561 ep562 ep73 ep561 471940 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2370701807) qz291 0 2 ep560 ep70 ep561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2370701807) qz292 0 2 ep562 ep73 ep561 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 360225223) qz30)

noncomputable def ep564 := @Enclosure.Real.IsNear.cos_image qz133 qz434 Bool.false 360225223 1048576 825 1048576 Bool.true 471940 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 38678888802854013489 112589990684262400 6670375003621906899 8484125000000000000000 360225223 1048576 825 1048576 (ep559 rfl) rfl) (Enclosure.sfrac_false_div 360225223 1048576) (BSN.cos_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166823309017011261014016) qz32) 226375608064910080 72057594037927936 Bool.false 471940 1048576 54 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 360225223 1048576 226375608064910080 72057594037927936 54 166823309017011261014016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 471940 1048576 166823309017011261014016 151115727451828646838272 2370701807 2147483648 271758 271492 (ep563 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep565 := nat_lit 2032460994521981054874646249462912266473630419705137867587854227855090342317185

noncomputable def ep566 := nat_lit 5321496747146461251655588845831065781442224271142550693516625097062312622574721

noncomputable def ep567 := BSN.sin_dyadic_bound_f 2370701807 2147483648 3 2 1048576 271758 ep565 ep77 ep561 ep566 ep79 ep561 936367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2370701807) qz287 0 2 ep565 ep77 ep561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2370701807) qz288 0 2 ep566 ep79 ep561 rfl rfl rfl rfl) rfl rfl

noncomputable def ep568 := @Enclosure.Real.IsNear.sin_image qz133 qz434 Bool.false 360225223 1048576 825 1048576 Bool.true 936367 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 38678888802854013489 112589990684262400 6670375003621906899 8484125000000000000000 360225223 1048576 825 1048576 (ep559 rfl) rfl) (Enclosure.sfrac_false_div 360225223 1048576) (BSN.sin_reduce2 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166823309017011261014016) qz32) 226375608064910080 72057594037927936 Bool.false 936367 1048576 54 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 360225223 1048576 226375608064910080 72057594037927936 54 166823309017011261014016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 936367 1048576 166823309017011261014016 151115727451828646838272 2370701807 2147483648 271758 271492 (ep567 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz435 := (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep557 rfl rfl) rfl)

noncomputable def ep569 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133))) Bool.true 24743224275 274877906944 114279597807 717568776077312 Bool.false 196370205405 1099511627776 916661555823 5740550208618496 (@Enclosure.Real.IsNear.mulLit_ft qz132 (Real.cos qz133) 209715 1048576 1 1048576 117985 262144 56519513 71169998848 24743224275 274877906944 114279597807 717568776077312 qz435 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.true 471940 1048576 113039026 142339997696 117985 262144 56519513 71169998848 (ep564 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 (@Neg.neg Real Real.instNeg (Real.sin qz133)) 209715 1048576 1 1048576 936367 1048576 56519513 71169998848 196370205405 1099511627776 916661555823 5740550208618496 qz435 (@Enclosure.Real.IsNear.neg (Real.sin qz133) Bool.true 936367 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz133) Bool.true 936367 1048576 113039026 142339997696 936367 1048576 56519513 71169998848 (ep568 rfl rfl) rfl)) rfl)

noncomputable def ep570 := @ep555 24743224275 274877906944 114279597807 717568776077312 Bool.false 196370205405 1099511627776 916661555823 5740550208618496 Bool.false 149227510774587616919552 542886521633 549755813888 113501880066979 18656788178010112 Bool.false 136759161129290606575616 62190866233 549755813888 227022204689581 37313576356020224 EMRow33.d8 (ep556 ep569) rfl rfl

noncomputable abbrev qz436 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz134 := (@Inv.inv Real Real.instInv (Real.sqrt qz436))

noncomputable abbrev qz582 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz268 qz284 qz582)

noncomputable def ep571 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz430 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135)))) Bool.true 14713551007 137438953472 2915437173397 18656788178010112 Bool.true 180670742295 1099511627776 11682529573617 74627152712040448 (BSN.cpow_neg_s_mk qz13 106726 1000 26 qz14 rfl)

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep572 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz436) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz436) (Real.sqrt qz437) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz437) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep573 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 135746 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz582 106726 1000 0 1 3668288609262839 1125899906842624 125000000067873 16968250000000000000 195750885056092877557 562949953421312000 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz437) Bool.false 61543670347942250676224 18889465931478580854784 1000000000542984 135746000000000000000 3668288609262839 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep573 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep575 := nat_lit 2364455933429385755533636224077554081

noncomputable def ep576 := BSN.sin_dyadic_bound_f 1240031753 2147483648 2 1 1048576 271758 ep575 ep93 ep575 ep575 ep94 ep575 572392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1240031753) qz287 0 1 ep575 ep93 ep575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1240031753) qz288 0 1 ep575 ep94 ep575 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91153609) qz16)

noncomputable def ep577 := @Enclosure.Real.IsNear.cos_image qz135 qz438 Bool.false 91153609 262144 825 1048576 Bool.true 572392 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 195750885056092877557 562949953421312000 6670375003621906899 8484125000000000000000 91153609 262144 825 1048576 (ep574 rfl) rfl) (Enclosure.sfrac_false_div 91153609 262144) (BSN.cos_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21814869302547346096128) qz19) 226375608064910080 72057594037927936 Bool.false 572392 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 91153609 262144 226375608064910080 72057594037927936 55 21814869302547346096128 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 572392 1048576 21814869302547346096128 37778931862957161709568 1240031753 2147483648 271758 271492 (ep576 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep578 := BSN.cos_dyadic_bound_f 1240031753 2147483648 2 1 1048576 271758 ep575 ep60 ep575 ep575 ep61 ep575 878565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1240031753) qz291 0 1 ep575 ep60 ep575 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1240031753) qz292 0 1 ep575 ep61 ep575 rfl rfl rfl rfl) rfl rfl

noncomputable def ep579 := @Enclosure.Real.IsNear.sin_image qz135 qz438 Bool.false 91153609 262144 825 1048576 Bool.false 878565 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 195750885056092877557 562949953421312000 6670375003621906899 8484125000000000000000 91153609 262144 825 1048576 (ep574 rfl) rfl) (Enclosure.sfrac_false_div 91153609 262144) (BSN.sin_reduce1 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21814869302547346096128) qz19) 226375608064910080 72057594037927936 Bool.false 878565 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 91153609 262144 226375608064910080 72057594037927936 55 21814869302547346096128 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 878565 1048576 21814869302547346096128 37778931862957161709568 1240031753 2147483648 271758 271492 (ep578 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz439 := (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep572 rfl rfl) rfl)

noncomputable def ep580 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135))) Bool.true 14713551007 137438953472 2915437173397 18656788178010112 Bool.true 180670742295 1099511627776 11682529573617 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz135) 205643 1048576 1 1048576 71549 131072 56519513 71169998848 14713551007 137438953472 2915437173397 18656788178010112 qz439 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 572392 1048576 113039026 142339997696 71549 131072 56519513 71169998848 (ep577 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135)) 205643 1048576 1 1048576 878565 1048576 56519513 71169998848 180670742295 1099511627776 11682529573617 74627152712040448 qz439 (@Enclosure.Real.IsNear.neg (Real.sin qz135) Bool.false 878565 1048576 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz135) Bool.false 878565 1048576 113039026 142339997696 878565 1048576 56519513 71169998848 (ep579 rfl rfl) rfl)) rfl)

noncomputable def ep581 := @ep553 14713551007 137438953472 2915437173397 18656788178010112 Bool.true 180670742295 1099511627776 11682529573617 74627152712040448 Bool.false 66524895178257921474560 484032317605 549755813888 632702811089 101395587923968 Bool.true 30945210411491526705152 56289009829 1099511627776 20248997345773 3244658813566976 (ep554 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep570 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep571 ep580) rfl rfl

noncomputable def ep582 := @Enclosure.Complex.IsNear.mul qz127 (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 306196837588216221014113 ep403 ep546 ep405 Bool.false

noncomputable abbrev qz136 := (Complex.re qz427)

noncomputable abbrev qz137 := (Complex.im qz427)

noncomputable def ep583 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 7471338944494834879925 78035369390991382413312 588679716336579304477075

noncomputable def ep584 := nat_lit 7650492238530206142333714432

noncomputable def ep585 := nat_lit 4877210586936961400832000

noncomputable def ep586 := nat_lit 12574343778398322688753867

noncomputable def ep587 := nat_lit 1075850471043310238765678592000

noncomputable def ep588 := nat_lit 35841274991324771516734345003624959170926608384

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 105195195313 549755813888 5738200174251 37313576356020224 923306487425

noncomputable abbrev qz440 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz138 := (@Inv.inv Real Real.instInv (Real.sqrt qz440))

noncomputable abbrev qz441 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz544 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable abbrev qz139 := (Real.cos qz441)

noncomputable abbrev qz140 := (Real.sin qz441)

noncomputable abbrev qz583 := (@Neg.neg Real Real.instNeg qz140)

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz138 qz139) (@HMul.hMul Real Real Real qz0 qz138 qz583)) Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (BSN.cpow_neg_s_mk qz13 106726 1000 27 qz14 rfl)

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15)

noncomputable def ep591 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz440) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz440) (Real.sqrt qz442) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz442) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep592 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 135746 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz141 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz141 106726 1000 0 1 3710780868205815 1125899906842624 125000000067873 16968250000000000000 39603679894013381169 112589990684262400 6670375003621906899 8484125000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz442) Bool.false 62256572154556490711040 18889465931478580854784 1000000000542984 135746000000000000000 3710780868205815 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep592 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep594 := nat_lit 6288623557494842303072777726250020707364078221111565834271003034384000000000000

noncomputable def ep595 := nat_lit 9532155348727260520091353208627673805469089346762251878906250000000000000000

noncomputable def ep596 := nat_lit 16454771541921885705300936615936085618839921577302200205762969256720000000000000

noncomputable def ep597 := BSN.sin_dyadic_bound_f 3143394500 2147483648 3 2 1048576 271758 ep594 ep77 ep595 ep596 ep79 ep595 1042574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3143394500) qz287 0 2 ep594 ep77 ep595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3143394500) qz288 0 2 ep596 ep79 ep595 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz142 := qz441

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 368838011) qz30)

noncomputable def ep598 := @Enclosure.Real.IsNear.cos_image qz142 qz443 Bool.false 368838011 1048576 825 1048576 Bool.false 1042574 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 39603679894013381169 112589990684262400 6670375003621906899 8484125000000000000000 368838011 1048576 825 1048576 (ep593 rfl) rfl) (Enclosure.sfrac_false_div 368838011 1048576) (BSN.cos_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 221196723483130044874752) qz32) 226375608064910080 72057594037927936 Bool.false 1042574 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 368838011 1048576 226375608064910080 72057594037927936 55 221196723483130044874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1042574 1048576 221196723483130044874752 151115727451828646838272 3143394500 2147483648 271758 271492 (ep597 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep599 := nat_lit 3497916267652124506382694893787179359115807495882764242096737796880000000000000

noncomputable def ep600 := nat_lit 10474684492258918998107901974944282729736484308954768222532400890640000000000000

noncomputable def ep601 := BSN.cos_dyadic_bound_f 3143394500 2147483648 3 2 1048576 271758 ep599 ep70 ep595 ep600 ep73 ep595 112024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3143394500) qz291 0 2 ep599 ep70 ep595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3143394500) qz292 0 2 ep600 ep73 ep595 rfl rfl rfl rfl) rfl rfl

noncomputable def ep602 := @Enclosure.Real.IsNear.sin_image qz142 qz443 Bool.false 368838011 1048576 825 1048576 Bool.true 112024 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 39603679894013381169 112589990684262400 6670375003621906899 8484125000000000000000 368838011 1048576 825 1048576 (ep593 rfl) rfl) (Enclosure.sfrac_false_div 368838011 1048576) (BSN.sin_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 221196723483130044874752) qz32) 226375608064910080 72057594037927936 Bool.false 112024 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 368838011 1048576 226375608064910080 72057594037927936 55 221196723483130044874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112024 1048576 221196723483130044874752 151115727451828646838272 3143394500 2147483648 271758 271492 (ep601 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz444 := (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep591 rfl rfl) rfl)

noncomputable def ep603 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz138 qz139) (@HMul.hMul Real Real Real qz0 qz138 qz583) Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (@Enclosure.Real.IsNear.mulLit_ff qz138 qz139 201799 1048576 1 1048576 521287 524288 56519513 71169998848 105195195313 549755813888 5738200174251 37313576356020224 qz444 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 1042574 1048576 113039026 142339997696 521287 524288 56519513 71169998848 (ep598 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz138 qz583 201799 1048576 1 1048576 14003 131072 56519513 71169998848 2825791397 137438953472 356663785261 2332098522251264 qz444 (@Enclosure.Real.IsNear.neg qz140 Bool.true 14003 131072 56519513 71169998848 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 112024 1048576 113039026 142339997696 14003 131072 56519513 71169998848 (ep602 rfl rfl) rfl)) rfl)

noncomputable def ep604 := @ep589 1845291630312 0 1 7471338944494834879925 78035369390991382413312 588679716336579304477075 ep584 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (ep590 ep603))

noncomputable def ep605 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 923306487425 1845291630312 0 1 Bool.false

noncomputable def ep606 := @Enclosure.Complex.IsNear.addLitP qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 2840922269 5695344538 0 1 Bool.true 720400500

noncomputable def ep607 := @ep606 2847672269 0 1 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1 Bool.false 1846612974850 923306487425 1845291630312 0 1 Bool.false 35255454290647 35255454290647 461322907578000 0 1

noncomputable abbrev qz143 := (@HDiv.hDiv Complex Complex Complex qz403 qz428 (@HSub.hSub Complex Complex Complex qz395 qz272 (1 : Complex)))

noncomputable def ep608 := @Enclosure.Complex.IsNear.addLitP qz143 qz105 Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1

noncomputable def ep609 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (Enclosure.sfrac Bool.true 54000000 45562756304) (Enclosure.sfrac Bool.true 11526408000 45562756304)) Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1

noncomputable def ep610 := @ep608 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 45454756304 2840922269 5695344538 0 1 Bool.true 11526408000 720400500 2847672269 0 1 (ep609 (BSN.N_div_s_sub_one_mk qz13 106726 1000 27 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 54000000 45562756304) (Enclosure.sfrac Bool.true 11526408000 45562756304) Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1 (Enclosure.Real.IsNear.const Bool.true 54000000 45562756304) (Enclosure.Real.IsNear.const Bool.true 11526408000 45562756304))) qz106 rfl

noncomputable abbrev qz144 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz145 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz429 qz428 1))

noncomputable def ep611 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145)) Bool.false 1 648 0 1

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145) Bool.false 0 1 0 1 Bool.false

noncomputable def ep613 := @ep612 0 1 0 1 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1 Bool.false 1 1 648 0 1 Bool.false 53363 53363 162000 0

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep615 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1

noncomputable def ep616 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz145)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz145)) 1 648 0 1 0 1 0

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz145) 1 24 0 1 1 27 0 1 1

noncomputable def ep618 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow33.d9 rfl) qz417

noncomputable def ep621 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep622 := ep621 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz100 qz13) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 106726 1000 qz14) (@Enclosure.Complex.IsNear.mk qz100 qz13 Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 qz410 qz18))

noncomputable def ep623 := @ep619 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 106726 1000 0 1 0 1 0

noncomputable def ep625 := @ep624 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep626 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 53363 6000 0 1 0 1 0 1 53363

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 106726 1000 0 1 53363 6000 0

noncomputable def ep628 := @ep627 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep629 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep630 := @ep629 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep631 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 (@ep618 1 24 0 1 (ep623 rfl) (ep625 rfl) rfl rfl) (@ep626 53363 6000 0 1 (ep628 rfl) (ep630 rfl) rfl rfl)

noncomputable def ep632 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 ep631

noncomputable abbrev qz146 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz429 qz428 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 27) qz283) Bool.false 1 27 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 27 1 27 EMRow33.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 27) qz283 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 27) qz294))

noncomputable def ep633 := @ep617 648 0 1 ep632 (@Enclosure.Complex.IsNear.re_isNear qz145 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz146)

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz145) 53363 6000 0 1 0 1 0 1 0

noncomputable def ep635 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 ep631

noncomputable def ep636 := @ep634 1 0 1 ep635 (@Enclosure.Complex.IsNear.im_isNear qz145 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz146)

noncomputable def ep637 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz145)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz145)) 0 1 0 1 53363 162000 0

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz145) 1 24 0 1 0 1 0 1 0

noncomputable def ep639 := @ep638 1 0 1 ep632 (@Enclosure.Complex.IsNear.im_isNear qz145 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz146)

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz145) 53363 6000 0 1 1 27 0 1 53363

noncomputable def ep641 := @ep640 162000 0 1 ep635 (@Enclosure.Complex.IsNear.re_isNear qz145 Bool.false 1 27 0 1 Bool.false 0 1 0 1 qz146)

noncomputable def ep642 := @ep613 1 (@ep614 0 1 0 1 (BSN.bern_sum_base qz5 27) qz121) (ep615 (@ep616 1 1 1 648 0 1 (ep633 rfl) (ep636 rfl) rfl rfl) (@ep637 1 53363 53363 162000 0 1 (ep639 rfl) (ep641 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep643 := ep607 (ep610 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep611 Bool.false 53363 162000 0 1 (BSN.bern_sum_succ qz5 27 0 1 1 rfl rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 2825791397 137438953472 356663785261 2332098522251264 35255454290647

noncomputable def ep645 := @ep644 461322907578000 0 1 7663427648602848474143 ep585 ep586 ep587 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (ep590 ep603))

noncomputable def ep646 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 923306487425 1845291630312 0 1 Bool.false

noncomputable def ep647 := nat_lit 22478094883765420111058933

noncomputable def ep648 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 285284953842550387241347 ep541 ep647

noncomputable def ep649 := nat_lit 1912623059632551535583428608000

noncomputable def ep650 := nat_lit 4303401884173240955062714368

noncomputable def ep651 := nat_lit 9480961121966160545073580939741775743540002816

noncomputable def ep652 := @Enclosure.Real.IsNear.mulLit_ff qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 105195195313 549755813888 5738200174251 37313576356020224 35255454290647

noncomputable def ep653 := @ep652 461322907578000 0 1 285284953842550387241347 ep541 ep647 ep649 (@Enclosure.Complex.IsNear.re_isNear qz127 Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (ep590 ep603))

noncomputable def ep654 := @Enclosure.Real.IsNear.mulLit_ff qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz128 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz131 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 2825791397 137438953472 356663785261 2332098522251264 923306487425

noncomputable def ep655 := @ep654 1845291630312 0 1 200697809919988744825 19508842347747845603328 329309986761038396842925 ep650 (@Enclosure.Complex.IsNear.im_isNear qz127 Bool.false 105195195313 549755813888 5738200174251 37313576356020224 Bool.false 2825791397 137438953472 356663785261 2332098522251264 (ep590 ep603))

noncomputable abbrev qz445 := (ep643 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep656 := @ep582 485982763762539132066347 ep541 ep547 ep543 (@ep583 ep584 7663427648602848474143 ep585 ep586 ep587 ep588 306196837588216221014113 ep403 ep546 ep405 (ep604 (@ep605 35255454290647 461322907578000 0 1 qz445) rfl) (ep645 (@ep646 35255454290647 461322907578000 0 1 qz445) rfl) rfl rfl) (@ep648 ep649 200697809919988744825 19508842347747845603328 329309986761038396842925 ep650 ep651 485982763762539132066347 ep541 ep547 ep543 (ep653 (@ep646 35255454290647 461322907578000 0 1 qz445) rfl) (ep655 (@ep605 35255454290647 461322907578000 0 1 qz445) rfl) rfl rfl)

noncomputable def ep657 := @ep550 ep542 ep543 (@ep551 3244658813566976 (BSN.head_sum_c_eq qz5 27) (ep552 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep581 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep656 rfl rfl rfl

noncomputable def ep658 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 27) Bool.false ep402 ep403 ep404 ep405 Bool.true 512763762352880121170653 ep541 ep542 ep543 (@ep544 ep405 Bool.true 512763762352880121170653 ep541 ep542 ep543 (BSN.zetaApproximant_eq_folded' qz5 1 27 rfl) (ep657 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep659 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 27)) 21 131072 5764531

noncomputable def ep660 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.false 168 1048576 11529062

noncomputable def ep661 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz399 Bool.false 102119989 1048576 83

noncomputable def ep662 := nat_lit 4641083269665487748852128150965810202118238070143429249279870239266643707330816

noncomputable def ep663 := nat_lit 13889747821512413880647880856376703971986092280518348247229308643865979911045376

noncomputable def ep664 := BSN.cos_dyadic_bound_f 3372912478 2147483648 3 2 1048576 271758 ep662 ep70 ep537 ep663 ep73 ep537 168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372912478) qz291 0 2 ep662 ep70 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372912478) qz292 0 2 ep663 ep73 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable def ep665 := @ep661 262144 Bool.false 168 1048576 1 135746 (@ep410 102119989 1048576 83 262144 ep535 rfl) (Enclosure.sfrac_false_div 102119989 1048576) (BSN.sin_reduce1 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237347615300792539414528) qz32) 226375608064910080 72057594037927936 Bool.false 168 1048576 15 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 102119989 1048576 226375608064910080 72057594037927936 15 237347615300792539414528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 168 1048576 237347615300792539414528 151115727451828646838272 3372912478 2147483648 271758 271492 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 27) Bool.false ep402 ep403 ep404 ep405 Bool.true 512763762352880121170653 ep541 ep542 ep543 (@ep544 ep405 Bool.true 512763762352880121170653 ep541 ep542 ep543 (BSN.zetaApproximant_eq_folded' qz5 1 27 rfl) (ep657 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow33.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 27 qz13) Bool.true ep385 ep386 ep387 ep388 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 27 qz13) ep389 Bool.true ep385 ep386 ep387 ep388 (@Eq.refl Real ep389) (@ep390 Bool.true ep385 ep386 ep387 ep388 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) (zetaApproximant qz5 1 27)) (@ep392 ep393 ep394 ep395 ep396 ep397 ep398 ep399 ep400 ep385 ep386 ep387 ep388 (@ep401 17792499712 ep402 ep403 ep404 ep405 ep391 ep393 ep394 ep395 (@ep406 35584999424 1048575 1048576 5764531 17792499712 (ep540 rfl rfl) rfl) ep658 rfl) (@ep659 17792499712 512763762352880121170653 ep541 ep542 ep543 ep396 ep397 ep398 ep399 (@ep660 35584999424 21 131072 5764531 17792499712 (ep665 rfl rfl) rfl) ep666 rfl) rfl rfl))

noncomputable abbrev qz607 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 108936 1000)))

noncomputable abbrev qz584 := qz607

noncomputable abbrev qz446 := qz584

noncomputable abbrev qz147 := (BSN.headSumC qz446 9)

noncomputable abbrev qz148 := qz446

noncomputable abbrev qz585 := (@Neg.neg Complex Complex.instNeg qz607)

noncomputable abbrev qz447 := qz585

noncomputable abbrev qz149 := qz447

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq qz147 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz149)) Bool.false 4167506520365 1099511627776 204455775738633 74627152712040448 Bool.true 440662229 137438953472 12766117245077 4664197044502528

noncomputable def ep668 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 8) (@HPow.hPow Complex Complex Complex qz6 qz276 qz149) Bool.false 3799919578055 1099511627776 182982188019687 74627152712040448 Bool.false 960515577 8589934592 714173561919 291512315281408 Bool.false

noncomputable def ep669 := nat_lit 2291110938986807421829120

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz149)) Bool.false 3799919578055 1099511627776 182982188019687 74627152712040448 Bool.false 960515577 8589934592 714173561919 291512315281408

noncomputable def ep671 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 7) (@HPow.hPow Complex Complex Complex qz6 qz277 qz149) Bool.false 3832306464405 1099511627776 160092292041871 74627152712040448 Bool.true 145683306297 549755813888 39968282208821 18656788178010112 Bool.true

noncomputable def ep672 := nat_lit 2089027880342572069027840

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz149)) Bool.false 3832306464405 1099511627776 160092292041871 74627152712040448 Bool.true 145683306297 549755813888 39968282208821 18656788178010112

noncomputable def ep674 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 6) (@HPow.hPow Complex Complex Complex qz6 qz278 qz149) Bool.false 106885167975 34359738368 2602098210613 1435137552154624 Bool.true 56578662447 549755813888 1299298162031 717568776077312 Bool.false

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz149)) Bool.false 106885167975 34359738368 2602098210613 1435137552154624 Bool.true 56578662447 549755813888 1299298162031 717568776077312

noncomputable def ep676 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 5) (@HPow.hPow Complex Complex Complex qz6 qz279 qz149) Bool.false 3015515041013 1099511627776 108173460009827 74627152712040448 Bool.true 98071611725 274877906944 27002388188881 18656788178010112 Bool.false

noncomputable def ep677 := nat_lit 3760687520809709941555200

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz149)) Bool.false 3015515041013 1099511627776 108173460009827 74627152712040448 Bool.true 98071611725 274877906944 27002388188881 18656788178010112

noncomputable def ep679 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 4) (@HPow.hPow Complex Complex Complex qz6 qz280 qz149) Bool.false 2479108622721 1099511627776 5989736202739 5740550208618496 Bool.true 16992418405 68719476736 747658823273 717568776077312 Bool.false

noncomputable def ep680 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz149)) Bool.false 2479108622721 1099511627776 5989736202739 5740550208618496 Bool.true 16992418405 68719476736 747658823273 717568776077312

noncomputable def ep681 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz149) Bool.false 1872258253141 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 34359738368 2676275836229 4664197044502528 Bool.false

noncomputable def ep682 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz149)) Bool.false 1872258253141 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 34359738368 2676275836229 4664197044502528

noncomputable def ep683 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz149) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep684 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz148)

noncomputable abbrev qz608 := (Enclosure.sfrac Bool.false 108936 1000)

noncomputable abbrev qz586 := qz608

noncomputable abbrev qz448 := qz586

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz268 qz448 (Real.log qz285))

noncomputable abbrev qz151 := qz448

noncomputable abbrev qz449 := (@Eq.refl Real qz586)

noncomputable abbrev qz152 := qz449

noncomputable def ep685 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 772746625365 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 34359738368 2676275836229 4664197044502528 (BSN.cpow_neg_s_mk qz151 108936 1000 2 qz152 rfl)

noncomputable def ep686 := nat_lit 3148042166480788516562434671905761

noncomputable def ep687 := BSN.cos_dyadic_bound_f 236870041 2147483648 2 1 1048576 271758 ep686 ep60 ep686 ep686 ep61 ep686 1042203 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 236870041) qz291 0 1 ep686 ep60 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 236870041) qz292 0 1 ep686 ep61 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz153 := (Enclosure.Real.IsNear.const Bool.false 108936 1000)

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79176427) qz30)

noncomputable def ep688 := @Enclosure.Real.IsNear.cos_image qz150 qz450 Bool.false 79176427 1048576 843 1048576 Bool.false 1042203 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 309282921 4096000 13617 16968250 79176427 1048576 843 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz17 108936 1000 0 1 363408 524288 1 135746 309282921 4096000 13617 16968250 qz153 qz290 rfl) rfl) (Enclosure.sfrac_false_div 79176427 1048576) (BSN.cos_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16668247370257613717504) qz32) 226375608064910080 72057594037927936 Bool.false 1042203 1048576 12 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 79176427 1048576 226375608064910080 72057594037927936 12 16668247370257613717504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042203 1048576 16668247370257613717504 151115727451828646838272 236870041 2147483648 271758 271492 (ep687 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep689 := BSN.sin_dyadic_bound_f 236870041 2147483648 1 0 1048576 271758 0 1 1 0 1 1 115424 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 236870041) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 236870041) qz288 0 0 rfl) rfl rfl

noncomputable def ep690 := @Enclosure.Real.IsNear.sin_image qz150 qz450 Bool.false 79176427 1048576 843 1048576 Bool.false 115424 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 309282921 4096000 13617 16968250 79176427 1048576 843 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz17 108936 1000 0 1 363408 524288 1 135746 309282921 4096000 13617 16968250 qz153 qz290 rfl) rfl) (Enclosure.sfrac_false_div 79176427 1048576) (BSN.sin_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16668247370257613717504) qz32) 226375608064910080 72057594037927936 Bool.false 115424 1048576 12 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 79176427 1048576 226375608064910080 72057594037927936 12 16668247370257613717504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 115424 1048576 16668247370257613717504 151115727451828646838272 236870041 2147483648 271758 271492 (ep689 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep691 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 772746625365 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 34359738368 2676275836229 4664197044502528 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz150) 741455 1048576 1 1048576 1042203 1048576 57741227 71169998848 772746625365 1099511627776 42883316650731 74627152712040448 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 1042203 1048576 115482454 142339997696 1042203 1048576 57741227 71169998848 (ep688 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 741455 1048576 1 1048576 3607 32768 57741227 71169998848 2674428185 34359738368 2676275836229 4664197044502528 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 3607 32768 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 115424 1048576 115482454 142339997696 3607 32768 57741227 71169998848 (ep690 rfl rfl) rfl)) rfl)

noncomputable def ep692 := @ep683 772746625365 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 34359738368 2676275836229 4664197044502528 Bool.false 1872258253141 1872258253141 1099511627776 42883316650731 74627152712040448 Bool.true 2674428185 2674428185 34359738368 2676275836229 4664197044502528 (ep684 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep685 ep691) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz448 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep693 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 151712592395 274877906944 8745813496219 18656788178010112 Bool.true 11643562035 68719476736 4367013030091 9328394089005056 (BSN.cpow_neg_s_mk qz151 108936 1000 3 qz152 rfl)

noncomputable def ep694 := nat_lit 167398774219988792747397998913152016

noncomputable def ep695 := BSN.cos_dyadic_bound_f 639643614 2147483648 2 1 1048576 271758 ep694 ep60 ep694 ep694 ep61 ep694 1002404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 639643614) qz291 0 1 ep694 ep60 ep694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 639643614) qz292 0 1 ep694 ep61 ep694 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125491875) qz30)

noncomputable def ep696 := @Enclosure.Real.IsNear.cos_image qz154 qz451 Bool.false 125491875 1048576 421 524288 Bool.false 1002404 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 7843242213 65536000 13617 16968250 125491875 1048576 421 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz23 108936 1000 0 1 575989 524288 1 135746 7843242213 65536000 13617 16968250 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 125491875 1048576) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45010917844188051537920) qz32) 226375608064910080 72057594037927936 Bool.false 1002404 1048576 19 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 125491875 1048576 226375608064910080 72057594037927936 19 45010917844188051537920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002404 1048576 45010917844188051537920 151115727451828646838272 639643614 2147483648 271758 271492 (ep695 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep697 := BSN.sin_dyadic_bound_f 639643614 2147483648 2 1 1048576 271758 ep694 ep93 ep694 ep694 ep94 ep694 307728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 639643614) qz287 0 1 ep694 ep93 ep694 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 639643614) qz288 0 1 ep694 ep94 ep694 rfl rfl rfl rfl) rfl rfl

noncomputable def ep698 := @Enclosure.Real.IsNear.sin_image qz154 qz451 Bool.false 125491875 1048576 421 524288 Bool.false 307728 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 7843242213 65536000 13617 16968250 125491875 1048576 421 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz23 108936 1000 0 1 575989 524288 1 135746 7843242213 65536000 13617 16968250 qz153 qz297 rfl) rfl) (Enclosure.sfrac_false_div 125491875 1048576) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45010917844188051537920) qz32) 226375608064910080 72057594037927936 Bool.false 307728 1048576 19 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 125491875 1048576 226375608064910080 72057594037927936 19 45010917844188051537920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 307728 1048576 45010917844188051537920 151115727451828646838272 639643614 2147483648 271758 271492 (ep697 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep699 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 151712592395 274877906944 8745813496219 18656788178010112 Bool.true 11643562035 68719476736 4367013030091 9328394089005056 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz154) 605395 1048576 1 1048576 250601 262144 28836677 35584999424 151712592395 274877906944 8745813496219 18656788178010112 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 1002404 1048576 57673354 71169998848 250601 262144 28836677 35584999424 (ep696 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 605395 1048576 1 1048576 19233 65536 28836677 35584999424 11643562035 68719476736 4367013030091 9328394089005056 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 19233 65536 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 307728 1048576 57673354 71169998848 19233 65536 28836677 35584999424 (ep698 rfl rfl) rfl)) rfl)

noncomputable def ep700 := @ep681 151712592395 274877906944 8745813496219 18656788178010112 Bool.true 11643562035 68719476736 4367013030091 9328394089005056 Bool.false 681452189300371042074624 2479108622721 1099511627776 5989736202739 5740550208618496 Bool.true 583855050635387863040 16992418405 68719476736 747658823273 717568776077312 (ep682 (BSN.head_sum_c_succ qz148 2 3 rfl rfl) (ep692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep693 ep699) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz268 qz448 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz280 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 134101604573 274877906944 7576722343555 18656788178010112 Bool.true 30101938105 274877906944 7563258783783 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 4 qz152 rfl)

noncomputable def ep702 := nat_lit 50559691708812276839022130879700625

noncomputable def ep703 := BSN.cos_dyadic_bound_f 474188595 2147483648 2 1 1048576 271758 ep702 ep60 ep702 ep702 ep61 ep702 1023116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 474188595) qz291 0 1 ep702 ep60 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 474188595) qz292 0 1 ep702 ep61 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158353073) qz30)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz155 qz452 Bool.false 158353073 1048576 421 524288 Bool.false 1023116 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 9897067089 65536000 13617 16968250 158353073 1048576 421 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz27 108936 1000 0 1 726817 524288 1 135746 9897067089 65536000 13617 16968250 qz153 qz300 rfl) rfl) (Enclosure.sfrac_false_div 158353073 1048576) (BSN.cos_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33368055966703839870976) qz32) 226375608064910080 72057594037927936 Bool.false 1023116 1048576 24 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 158353073 1048576 226375608064910080 72057594037927936 24 33368055966703839870976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023116 1048576 33368055966703839870976 151115727451828646838272 474188595 2147483648 271758 271492 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := BSN.sin_dyadic_bound_f 474188595 2147483648 2 1 1048576 271758 ep702 ep93 ep702 ep702 ep94 ep702 229660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 474188595) qz287 0 1 ep702 ep93 ep702 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 474188595) qz288 0 1 ep702 ep94 ep702 rfl rfl rfl rfl) rfl rfl

noncomputable def ep706 := @Enclosure.Real.IsNear.sin_image qz155 qz452 Bool.false 158353073 1048576 421 524288 Bool.false 229660 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 9897067089 65536000 13617 16968250 158353073 1048576 421 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz27 108936 1000 0 1 726817 524288 1 135746 9897067089 65536000 13617 16968250 qz153 qz300 rfl) rfl) (Enclosure.sfrac_false_div 158353073 1048576) (BSN.sin_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33368055966703839870976) qz32) 226375608064910080 72057594037927936 Bool.false 229660 1048576 24 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 158353073 1048576 226375608064910080 72057594037927936 24 33368055966703839870976 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 229660 1048576 33368055966703839870976 151115727451828646838272 474188595 2147483648 271758 271492 (ep705 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep707 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 134101604573 274877906944 7576722343555 18656788178010112 Bool.true 30101938105 274877906944 7563258783783 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz155) 524287 1048576 1 1048576 255779 262144 28836677 35584999424 134101604573 274877906944 7576722343555 18656788178010112 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 1023116 1048576 57673354 71169998848 255779 262144 28836677 35584999424 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 524287 1048576 1 1048576 57415 262144 28836677 35584999424 30101938105 274877906944 7563258783783 18656788178010112 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 57415 262144 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 229660 1048576 57673354 71169998848 57415 262144 28836677 35584999424 (ep706 rfl rfl) rfl)) rfl)

noncomputable def ep708 := @ep679 134101604573 274877906944 7576722343555 18656788178010112 Bool.true 30101938105 274877906944 7563258783783 18656788178010112 Bool.false 828898462831803757494272 3015515041013 1099511627776 108173460009827 74627152712040448 Bool.true 6739429840398162329600 98071611725 274877906944 27002388188881 18656788178010112 (ep680 (BSN.head_sum_c_succ qz148 3 4 rfl rfl) (ep700 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep701 ep707) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz448 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep709 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 404810334187 1099511627776 27135646942049 74627152712040448 Bool.false 139564561003 549755813888 6779364023925 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 5 qz152 rfl)

noncomputable def ep710 := nat_lit 1196982326169923094106407407473719205883269567514456348791564277174795143445025

noncomputable def ep711 := nat_lit 346195744122181571761333233201442870637823482162783753127358194498367093281

noncomputable def ep712 := nat_lit 3134393204002172190591072480053605107903720962614360215996652622190513733728801

noncomputable def ep713 := BSN.sin_dyadic_bound_f 2076898227 2147483648 3 2 1048576 271758 ep710 ep77 ep711 ep712 ep79 ep711 863251 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2076898227) qz287 0 2 ep710 ep77 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2076898227) qz288 0 2 ep712 ep79 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22980267) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep714 := @Enclosure.Real.IsNear.cos_image qz156 qz453 Bool.false 22980267 131072 843 1048576 Bool.false 863251 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 359066673 2048000 13617 16968250 22980267 131072 843 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz31 108936 1000 0 1 843808 524288 1 135746 359066673 2048000 13617 16968250 qz153 qz304 rfl) rfl) (Enclosure.sfrac_false_div 22980267 131072) (BSN.cos_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18268590006871957438464) qz561) 226375608064910080 72057594037927936 Bool.false 863251 1048576 27 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 22980267 131072 226375608064910080 72057594037927936 27 18268590006871957438464 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 863251 1048576 18268590006871957438464 18889465931478580854784 2076898227 2147483648 271758 271492 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep715 := nat_lit 665144045980678244091009152255711311210988792388992542107814535405774353955361

noncomputable def ep716 := nat_lit 1994739746453790369129504790300731047891690730202652058817188889828326327679521

noncomputable def ep717 := BSN.cos_dyadic_bound_f 2076898227 2147483648 3 2 1048576 271758 ep715 ep70 ep711 ep716 ep73 ep711 595238 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2076898227) qz291 0 2 ep715 ep70 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2076898227) qz292 0 2 ep716 ep73 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable def ep718 := @Enclosure.Real.IsNear.sin_image qz156 qz453 Bool.false 22980267 131072 843 1048576 Bool.true 595238 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 359066673 2048000 13617 16968250 22980267 131072 843 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz31 108936 1000 0 1 843808 524288 1 135746 359066673 2048000 13617 16968250 qz153 qz304 rfl) rfl) (Enclosure.sfrac_false_div 22980267 131072) (BSN.sin_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18268590006871957438464) qz561) 226375608064910080 72057594037927936 Bool.false 595238 1048576 27 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 22980267 131072 226375608064910080 72057594037927936 27 18268590006871957438464 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 595238 1048576 18268590006871957438464 18889465931478580854784 2076898227 2147483648 271758 271492 (ep717 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep719 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 404810334187 1099511627776 27135646942049 74627152712040448 Bool.false 139564561003 549755813888 6779364023925 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz156) 468937 1048576 1 1048576 863251 1048576 57741227 71169998848 404810334187 1099511627776 27135646942049 74627152712040448 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 863251 1048576 115482454 142339997696 863251 1048576 57741227 71169998848 (ep714 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 468937 1048576 1 1048576 297619 524288 57741227 71169998848 139564561003 549755813888 6779364023925 18656788178010112 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 297619 524288 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 595238 1048576 115482454 142339997696 297619 524288 57741227 71169998848 (ep718 rfl rfl) rfl)) rfl)

noncomputable def ep720 := @ep676 404810334187 1099511627776 27135646942049 74627152712040448 Bool.false 139564561003 549755813888 6779364023925 18656788178010112 Bool.false ep677 106885167975 34359738368 2602098210613 1435137552154624 Bool.true 15552224311122453331968 56578662447 549755813888 1299298162031 717568776077312 (ep678 (BSN.head_sum_c_succ qz148 4 5 rfl rfl) (ep708 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep709 ep719) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz268 qz448 qz547)

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 411981089205 1099511627776 24783185089995 74627152712040448 Bool.true 44552321925 274877906944 6186529996015 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 6 qz152 rfl)

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz547 108936 1000 0 1 4034681531866359 2251799813685248 250000000067873 33936500000000000000 54940258419424210503 281474976710656000 3404250000924226641 4242062500000000000000 qz153 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000271492 135746000000000000000 4034681531866359 2251799813685248 250000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep114 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep723 := nat_lit 590849831673033457611520765180691361

noncomputable def ep724 := BSN.cos_dyadic_bound_f 876736887 2147483648 2 1 1048576 271758 ep723 ep60 ep723 ep723 ep61 ep723 962395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 876736887) qz291 0 1 ep723 ep60 ep723 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 876736887) qz292 0 1 ep723 ep61 ep723 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204668411) qz30)

noncomputable def ep725 := @Enclosure.Real.IsNear.cos_image qz157 qz454 Bool.false 204668411 1048576 843 1048576 Bool.false 962395 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 54940258419424210503 281474976710656000 3404250000924226641 4242062500000000000000 204668411 1048576 843 1048576 (ep722 rfl) rfl) (Enclosure.sfrac_false_div 204668411 1048576) (BSN.cos_reduce0 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61694873769945933545472) qz32) 226375608064910080 72057594037927936 Bool.false 962395 1048576 31 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 204668411 1048576 226375608064910080 72057594037927936 31 61694873769945933545472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 962395 1048576 61694873769945933545472 151115727451828646838272 876736887 2147483648 271758 271492 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep726 := BSN.sin_dyadic_bound_f 876736887 2147483648 2 1 1048576 271758 ep723 ep93 ep723 ep723 ep94 ep723 416300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 876736887) qz287 0 1 ep723 ep93 ep723 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 876736887) qz288 0 1 ep723 ep94 ep723 rfl rfl rfl rfl) rfl rfl

noncomputable def ep727 := @Enclosure.Real.IsNear.sin_image qz157 qz454 Bool.false 204668411 1048576 843 1048576 Bool.false 416300 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 54940258419424210503 281474976710656000 3404250000924226641 4242062500000000000000 204668411 1048576 843 1048576 (ep722 rfl) rfl) (Enclosure.sfrac_false_div 204668411 1048576) (BSN.sin_reduce0 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61694873769945933545472) qz32) 226375608064910080 72057594037927936 Bool.false 416300 1048576 31 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 204668411 1048576 226375608064910080 72057594037927936 31 61694873769945933545472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 416300 1048576 61694873769945933545472 151115727451828646838272 876736887 2147483648 271758 271492 (ep726 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep728 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 411981089205 1099511627776 24783185089995 74627152712040448 Bool.true 44552321925 274877906944 6186529996015 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz157) 428079 1048576 1 1048576 962395 1048576 57741227 71169998848 411981089205 1099511627776 24783185089995 74627152712040448 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 962395 1048576 115482454 142339997696 962395 1048576 57741227 71169998848 (ep725 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 428079 1048576 1 1048576 104075 262144 57741227 71169998848 44552321925 274877906944 6186529996015 18656788178010112 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 104075 262144 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 416300 1048576 115482454 142339997696 104075 262144 57741227 71169998848 (ep727 rfl rfl) rfl)) rfl)

noncomputable def ep729 := @ep674 411981089205 1099511627776 24783185089995 74627152712040448 Bool.true 44552321925 274877906944 6186529996015 18656788178010112 Bool.false 131677047462950904791040 3832306464405 1099511627776 160092292041871 74627152712040448 Bool.true 40045122311601015226368 145683306297 549755813888 39968282208821 18656788178010112 (ep675 (BSN.head_sum_c_succ qz148 5 6 rfl rfl) (ep720 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep721 ep728) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz268 qz448 qz548)

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 16193443175 549755813888 2861236997227 9328394089005056 Bool.false 207156303225 549755813888 5738825753995 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 7 qz152 rfl)

noncomputable def ep731 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz548 108936 1000 0 1 4381796493761783 2251799813685248 250000000067873 33936500000000000000 59666922855554199111 281474976710656000 3404250000924226641 4242062500000000000000 qz153 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 250000000067873 33936500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 36757173121942042968064 18889465931478580854784 1000000000271492 135746000000000000000 4381796493761783 2251799813685248 250000000067873 33936500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep732 := nat_lit 3784585842226532083196581668206323802382398941335485709385459565784318994841856

noncomputable def ep733 := nat_lit 11153614257489325940215166793116130232056285811890814679782926059872703774976

noncomputable def ep734 := nat_lit 11331450298164617597709314671032739146683084252382675498796812845233211576975616

noncomputable def ep735 := BSN.cos_dyadic_bound_f 3205730082 2147483648 3 2 1048576 271758 ep732 ep70 ep733 ep734 ep73 ep733 81718 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3205730082) qz291 0 2 ep732 ep70 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3205730082) qz292 0 2 ep734 ep73 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217067) (@Nat.cast Real Real.instNatCast 1024))

noncomputable def ep736 := @Enclosure.Real.IsNear.cos_image qz158 qz455 Bool.false 217067 1024 843 1048576 Bool.true 81718 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 59666922855554199111 281474976710656000 3404250000924226641 4242062500000000000000 217067 1024 843 1048576 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 217067 1024) (BSN.cos_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220296093827105030144) (@Nat.cast Real Real.instNatCast 147573952589676412928)) 226375608064910080 72057594037927936 Bool.false 81718 1048576 33 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 217067 1024 226375608064910080 72057594037927936 33 220296093827105030144 147573952589676412928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 81718 1048576 220296093827105030144 147573952589676412928 3205730082 2147483648 271758 271492 (ep735 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep737 := nat_lit 6803331624601766289001674869336889940102673065754361625150000877563876027695360

noncomputable def ep738 := nat_lit 17800191260397262324434514387741095156083671661851695318292258513332262361661696

noncomputable def ep739 := BSN.sin_dyadic_bound_f 3205730082 2147483648 3 2 1048576 271758 ep737 ep77 ep733 ep738 ep79 ep733 1045386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3205730082) qz287 0 2 ep737 ep77 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3205730082) qz288 0 2 ep738 ep79 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable def ep740 := @Enclosure.Real.IsNear.sin_image qz158 qz455 Bool.false 217067 1024 843 1048576 Bool.true 1045386 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 59666922855554199111 281474976710656000 3404250000924226641 4242062500000000000000 217067 1024 843 1048576 (ep731 rfl) rfl) (Enclosure.sfrac_false_div 217067 1024) (BSN.sin_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220296093827105030144) (@Nat.cast Real Real.instNatCast 147573952589676412928)) 226375608064910080 72057594037927936 Bool.false 1045386 1048576 33 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 217067 1024 226375608064910080 72057594037927936 33 220296093827105030144 147573952589676412928 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045386 1048576 220296093827105030144 147573952589676412928 3205730082 2147483648 271758 271492 (ep739 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep741 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 16193443175 549755813888 2861236997227 9328394089005056 Bool.false 207156303225 549755813888 5738825753995 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz158) 396325 1048576 1 1048576 40859 524288 57741227 71169998848 16193443175 549755813888 2861236997227 9328394089005056 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 81718 1048576 115482454 142339997696 40859 524288 57741227 71169998848 (ep736 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 396325 1048576 1 1048576 522693 524288 57741227 71169998848 207156303225 549755813888 5738825753995 18656788178010112 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 522693 524288 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 1045386 1048576 115482454 142339997696 522693 524288 57741227 71169998848 (ep740 rfl rfl) rfl)) rfl)

noncomputable def ep742 := @ep671 16193443175 549755813888 2861236997227 9328394089005056 Bool.false 207156303225 549755813888 5738825753995 18656788178010112 Bool.false ep672 3799919578055 1099511627776 182982188019687 74627152712040448 Bool.false 33795137458287163736064 960515577 8589934592 714173561919 291512315281408 (ep673 (BSN.head_sum_c_succ qz148 6 7 rfl rfl) (ep729 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep730 ep741) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz268 qz448 qz549)

noncomputable def ep743 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 183793471155 549755813888 10736793859473 37313576356020224 Bool.true 15808911461 137438953472 1339340254373 4664197044502528 (BSN.cpow_neg_s_mk qz151 108936 1000 8 qz152 rfl)

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz549 108936 1000 0 1 9364972152248037 4503599627370496 500000000203619 67873000000000000000 127522825797161519829 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 39279540158062550581248 18889465931478580854784 1000000000407238 135746000000000000000 9364972152248037 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep140 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep745 := nat_lit 256437814783419770179653249787322001

noncomputable def ep746 := BSN.cos_dyadic_bound_f 711615693 2147483648 2 1 1048576 271758 ep745 ep60 ep745 ep745 ep61 ep745 991530 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 711615693) qz291 0 1 ep745 ep60 ep745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 711615693) qz292 0 1 ep745 ep61 ep745 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59382443) qz16)

noncomputable def ep747 := @Enclosure.Real.IsNear.cos_image qz159 qz456 Bool.false 59382443 262144 843 1048576 Bool.false 991530 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 127522825797161519829 562949953421312000 6808500002772679923 8484125000000000000000 59382443 262144 843 1048576 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 59382443 262144) (BSN.cos_reduce0 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12518875667029521596416) qz19) 226375608064910080 72057594037927936 Bool.false 991530 1048576 36 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 59382443 262144 226375608064910080 72057594037927936 36 12518875667029521596416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 991530 1048576 12518875667029521596416 37778931862957161709568 711615693 2147483648 271758 271492 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep748 := BSN.sin_dyadic_bound_f 711615693 2147483648 2 1 1048576 271758 ep745 ep93 ep745 ep745 ep94 ep745 341144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 711615693) qz287 0 1 ep745 ep93 ep745 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 711615693) qz288 0 1 ep745 ep94 ep745 rfl rfl rfl rfl) rfl rfl

noncomputable def ep749 := @Enclosure.Real.IsNear.sin_image qz159 qz456 Bool.false 59382443 262144 843 1048576 Bool.false 341144 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 127522825797161519829 562949953421312000 6808500002772679923 8484125000000000000000 59382443 262144 843 1048576 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 59382443 262144) (BSN.sin_reduce0 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12518875667029521596416) qz19) 226375608064910080 72057594037927936 Bool.false 341144 1048576 36 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 59382443 262144 226375608064910080 72057594037927936 36 12518875667029521596416 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 341144 1048576 12518875667029521596416 37778931862957161709568 711615693 2147483648 271758 271492 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 183793471155 549755813888 10736793859473 37313576356020224 Bool.true 15808911461 137438953472 1339340254373 4664197044502528 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz159) 370727 1048576 1 1048576 495765 524288 57741227 71169998848 183793471155 549755813888 10736793859473 37313576356020224 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 991530 1048576 115482454 142339997696 495765 524288 57741227 71169998848 (ep747 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 370727 1048576 1 1048576 42643 131072 57741227 71169998848 15808911461 137438953472 1339340254373 4664197044502528 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 42643 131072 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 341144 1048576 115482454 142339997696 42643 131072 57741227 71169998848 (ep749 rfl rfl) rfl)) rfl)

noncomputable def ep751 := @ep668 183793471155 549755813888 10736793859473 37313576356020224 Bool.true 15808911461 137438953472 1339340254373 4664197044502528 Bool.false ep669 4167506520365 1099511627776 204455775738633 74627152712040448 Bool.true 3785259724274925568 440662229 137438953472 12766117245077 4664197044502528 (ep670 (BSN.head_sum_c_succ qz148 7 8 rfl rfl) (ep742 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep743 ep750) rfl rfl

theorem EMRow33.d12 : Enclosure.Complex.IsNear qz147 Bool.false 4167506520365 1099511627776 204455775738633 74627152712040448 Bool.true 440662229 137438953472 12766117245077 4664197044502528 := ep667 (BSN.head_sum_c_succ qz148 8 9 rfl rfl) (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz160 := (BSN.headSumC qz446 17)

noncomputable abbrev qz587 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz149)

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq qz160 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 16) qz587) Bool.false 2492766653827 549755813888 171835320825145 37313576356020224 Bool.false 151694378923 1099511627776 343298272521691 74627152712040448

noncomputable def ep753 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 16) qz587 Bool.false 296065792283 68719476736 41058723730577 9328394089005056 Bool.false 269229862975 1099511627776 328131324501231 74627152712040448 Bool.false

noncomputable abbrev qz588 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz149)

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 15) qz588) Bool.false 296065792283 68719476736 41058723730577 9328394089005056 Bool.false 269229862975 1099511627776 328131324501231 74627152712040448

noncomputable def ep755 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 15) qz588 Bool.false 2233163689753 549755813888 19548059093801 4664197044502528 Bool.false 183774256699 1099511627776 312476926058569 74627152712040448 Bool.false

noncomputable def ep756 := nat_lit 1302111124807489717010432

noncomputable abbrev qz589 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz149)

noncomputable def ep757 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 14) qz589) Bool.false 2233163689753 549755813888 19548059093801 4664197044502528 Bool.false 183774256699 1099511627776 312476926058569 74627152712040448

noncomputable def ep758 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 14) qz589 Bool.false 4456794913861 1099511627776 296585004381333 74627152712040448 Bool.true 109927133133 1099511627776 296224161106229 74627152712040448 Bool.false

noncomputable def ep759 := nat_lit 4910778887221158562758656

noncomputable abbrev qz590 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz149)

noncomputable def ep760 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 13) qz590) Bool.false 4456794913861 1099511627776 296585004381333 74627152712040448 Bool.true 109927133133 1099511627776 296224161106229 74627152712040448

noncomputable def ep761 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 13) qz590 Bool.false 4756450208371 1099511627776 279742274574627 74627152712040448 Bool.true 26674486299 549755813888 69859540312437 18656788178010112 Bool.true

noncomputable def ep762 := nat_lit 2450148915201552907501568

noncomputable abbrev qz591 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz149)

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 12) qz591) Bool.false 4756450208371 1099511627776 279742274574627 74627152712040448 Bool.true 26674486299 549755813888 69859540312437 18656788178010112

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 12) qz591 Bool.false 4480802212291 1099511627776 262202312775461 74627152712040448 Bool.false 104008365549 1099511627776 261924723472379 74627152712040448 Bool.false

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 11) (@HPow.hPow Complex Complex Complex qz6 qz318 qz149)) Bool.false 4480802212291 1099511627776 262202312775461 74627152712040448 Bool.false 104008365549 1099511627776 261924723472379 74627152712040448

noncomputable def ep766 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 11) (@HPow.hPow Complex Complex Complex qz6 qz318 qz149) Bool.false 2388571087687 549755813888 60970835819277 18656788178010112 Bool.true 44599967673 1099511627776 243637469194355 74627152712040448 Bool.true

noncomputable def ep767 := nat_lit 2463347067089189662097408

noncomputable def ep768 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 10) (@HPow.hPow Complex Complex Complex qz6 qz319 qz149)) Bool.false 2388571087687 549755813888 60970835819277 18656788178010112 Bool.true 44599967673 1099511627776 243637469194355 74627152712040448

noncomputable def ep769 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 10) (@HPow.hPow Complex Complex Complex qz6 qz319 qz149) Bool.false 2235434002995 549755813888 1080272810195 358784388038656 Bool.true 209186157357 1099511627776 17267682505439 5740550208618496 Bool.false

noncomputable def ep770 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 10) (@HAdd.hAdd Complex Complex Complex qz4 qz147 (@HPow.hPow Complex Complex Complex qz6 qz320 qz149)) Bool.false 2235434002995 549755813888 1080272810195 358784388038656 Bool.true 209186157357 1099511627776 17267682505439 5740550208618496

noncomputable def ep771 := @Enclosure.Complex.IsNear.addLitP qz147 (@HPow.hPow Complex Complex Complex qz6 qz320 qz149) Bool.false 4167506520365 1099511627776 204455775738633 74627152712040448 Bool.true 440662229 137438953472 12766117245077 4664197044502528 Bool.false

noncomputable def ep772 := nat_lit 4915771358837704218378240

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz268 qz448 qz555)

noncomputable def ep773 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz320 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 303361485625 1099511627776 20240968781927 74627152712040448 Bool.true 205660859525 1099511627776 20221996649475 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 9 qz152 rfl)

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz555 108936 1000 0 1 9895417793173221 4503599627370496 500000000203619 67873000000000000000 134745904089639750357 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 41504390431577613533184 18889465931478580854784 1000000000407238 135746000000000000000 9895417793173221 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep167 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep775 := nat_lit 2679306671623717507607283302105760000

noncomputable def ep776 := BSN.cos_dyadic_bound_f 1279397820 2147483648 2 1 1048576 271758 ep775 ep60 ep775 ep775 ep61 ep775 867925 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1279397820) qz291 0 1 ep775 ep60 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1279397820) qz292 0 1 ep775 ep61 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62745951) qz16)

noncomputable def ep777 := @Enclosure.Real.IsNear.cos_image qz161 qz457 Bool.false 62745951 262144 843 1048576 Bool.false 867925 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 134745904089639750357 562949953421312000 6808500002772679923 8484125000000000000000 62745951 262144 843 1048576 (ep774 rfl) rfl) (Enclosure.sfrac_false_div 62745951 262144) (BSN.cos_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22507404477133049823232) qz19) 226375608064910080 72057594037927936 Bool.false 867925 1048576 38 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 62745951 262144 226375608064910080 72057594037927936 38 22507404477133049823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 867925 1048576 22507404477133049823232 37778931862957161709568 1279397820 2147483648 271758 271492 (ep776 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep778 := BSN.sin_dyadic_bound_f 1279397820 2147483648 2 1 1048576 271758 ep775 ep93 ep775 ep775 ep94 ep775 588401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1279397820) qz287 0 1 ep775 ep93 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1279397820) qz288 0 1 ep775 ep94 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable def ep779 := @Enclosure.Real.IsNear.sin_image qz161 qz457 Bool.false 62745951 262144 843 1048576 Bool.false 588401 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 134745904089639750357 562949953421312000 6808500002772679923 8484125000000000000000 62745951 262144 843 1048576 (ep774 rfl) rfl) (Enclosure.sfrac_false_div 62745951 262144) (BSN.sin_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22507404477133049823232) qz19) 226375608064910080 72057594037927936 Bool.false 588401 1048576 38 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 62745951 262144 226375608064910080 72057594037927936 38 22507404477133049823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 588401 1048576 22507404477133049823232 37778931862957161709568 1279397820 2147483648 271758 271492 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 303361485625 1099511627776 20240968781927 74627152712040448 Bool.true 205660859525 1099511627776 20221996649475 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz161) 349525 1048576 1 1048576 867925 1048576 57741227 71169998848 303361485625 1099511627776 20240968781927 74627152712040448 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 867925 1048576 115482454 142339997696 867925 1048576 57741227 71169998848 (ep777 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 349525 1048576 1 1048576 588401 1048576 57741227 71169998848 205660859525 1099511627776 20221996649475 74627152712040448 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 588401 1048576 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 588401 1048576 115482454 142339997696 588401 1048576 57741227 71169998848 (ep779 rfl rfl) rfl)) rfl)

noncomputable def ep781 := @ep771 303361485625 1099511627776 20240968781927 74627152712040448 Bool.true 205660859525 1099511627776 20221996649475 74627152712040448 Bool.false ep772 2235434002995 549755813888 1080272810195 358784388038656 Bool.true 28750326547975193493504 209186157357 1099511627776 17267682505439 5740550208618496 EMRow33.d12 (ep773 ep780) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz268 qz448 qz556)

noncomputable def ep782 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz319 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.false 38284271173 137438953472 4796649689137 18656788178010112 Bool.false 41146547421 274877906944 598674894489 2332098522251264 (BSN.cpow_neg_s_mk qz151 108936 1000 10 qz152 rfl)

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz556 108936 1000 0 1 10369917190100709 4503599627370496 500000000203619 67873000000000000000 141207162377601354453 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 43494585150108164161536 18889465931478580854784 1000000000407238 135746000000000000000 10369917190100709 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep784 := nat_lit 1845840189485549877534310027064337855594009148234037078619847033482635618017825

noncomputable def ep785 := nat_lit 822997159768651253242473038710212978279365700252680900839175388586662158881

noncomputable def ep786 := nat_lit 4833010881822529005798895590724877848400428796145878484450621660873000594170401

noncomputable def ep787 := BSN.sin_dyadic_bound_f 2314327373 2147483648 3 2 1048576 271758 ep784 ep77 ep785 ep786 ep79 ep785 923656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2314327373) qz287 0 2 ep784 ep77 ep785 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2314327373) qz288 0 2 ep786 ep79 ep785 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65754709) qz16)

noncomputable def ep788 := @Enclosure.Real.IsNear.cos_image qz162 qz458 Bool.false 65754709 262144 421 524288 Bool.false 923656 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 141207162377601354453 562949953421312000 6808500002772679923 8484125000000000000000 65754709 262144 421 524288 (ep783 rfl) rfl) (Enclosure.sfrac_false_div 65754709 262144) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40714077717894495469568) qz19) 226375608064910080 72057594037927936 Bool.false 923656 1048576 39 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 65754709 262144 226375608064910080 72057594037927936 39 40714077717894495469568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923656 1048576 40714077717894495469568 37778931862957161709568 2314327373 2147483648 271758 271492 (ep787 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep789 := nat_lit 1025832548451869332520502225275170014431462578219021790744732429885280526524961

noncomputable def ep790 := nat_lit 3075851651036070695055021729748089617337829003256560010432518938878668255257121

noncomputable def ep791 := BSN.cos_dyadic_bound_f 2314327373 2147483648 3 2 1048576 271758 ep789 ep70 ep785 ep790 ep73 ep785 496356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2314327373) qz291 0 2 ep789 ep70 ep785 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2314327373) qz292 0 2 ep790 ep73 ep785 rfl rfl rfl rfl) rfl rfl

noncomputable def ep792 := @Enclosure.Real.IsNear.sin_image qz162 qz458 Bool.false 65754709 262144 421 524288 Bool.true 496356 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 141207162377601354453 562949953421312000 6808500002772679923 8484125000000000000000 65754709 262144 421 524288 (ep783 rfl) rfl) (Enclosure.sfrac_false_div 65754709 262144) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40714077717894495469568) qz19) 226375608064910080 72057594037927936 Bool.false 496356 1048576 39 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 65754709 262144 226375608064910080 72057594037927936 39 40714077717894495469568 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496356 1048576 40714077717894495469568 37778931862957161709568 2314327373 2147483648 271758 271492 (ep791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep793 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.false 38284271173 137438953472 4796649689137 18656788178010112 Bool.false 41146547421 274877906944 598674894489 2332098522251264 (@Enclosure.Real.IsNear.mulLit_ff qz47 (Real.cos qz162) 331589 1048576 1 1048576 115457 131072 28836677 35584999424 38284271173 137438953472 4796649689137 18656788178010112 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.false 923656 1048576 57673354 71169998848 115457 131072 28836677 35584999424 (ep788 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 331589 1048576 1 1048576 124089 262144 28836677 35584999424 41146547421 274877906944 598674894489 2332098522251264 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.true 124089 262144 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.true 496356 1048576 57673354 71169998848 124089 262144 28836677 35584999424 (ep792 rfl rfl) rfl)) rfl)

noncomputable def ep794 := @ep769 38284271173 137438953472 4796649689137 18656788178010112 Bool.false 41146547421 274877906944 598674894489 2332098522251264 Bool.false 328282710585178025099264 2388571087687 549755813888 60970835819277 18656788178010112 Bool.true 12259545763724302221312 44599967673 1099511627776 243637469194355 74627152712040448 (ep770 (BSN.head_sum_c_succ qz148 9 10 rfl rfl) (ep781 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep782 ep793) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz268 qz448 qz557)

noncomputable def ep795 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz318 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.true 296339963083 1099511627776 796476934711 3244658813566976 Bool.false 74304166611 549755813888 99387251511 405582351695872 (BSN.cpow_neg_s_mk qz151 108936 1000 11 qz152 rfl)

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz557 108936 1000 0 1 10799156221662949 4503599627370496 500000000203619 67873000000000000000 147052110270384376533 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 45294944137145793642496 18889465931478580854784 1000000000407238 135746000000000000000 10799156221662949 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep797 := nat_lit 992884720388610825999709072144204816

noncomputable def ep798 := BSN.cos_dyadic_bound_f 998216414 2147483648 2 1 1048576 271758 ep797 ep60 ep797 ep797 ep61 ep797 937319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998216414) qz291 0 1 ep797 ep60 ep797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998216414) qz292 0 1 ep797 ep61 ep797 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 273905899) qz30)

noncomputable def ep799 := @Enclosure.Real.IsNear.cos_image qz163 qz459 Bool.false 273905899 1048576 843 1048576 Bool.true 937319 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 147052110270384376533 562949953421312000 6808500002772679923 8484125000000000000000 273905899 1048576 843 1048576 (ep796 rfl) rfl) (Enclosure.sfrac_false_div 273905899 1048576) (BSN.cos_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70243235494371574939648) qz32) 226375608064910080 72057594037927936 Bool.false 937319 1048576 41 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 273905899 1048576 226375608064910080 72057594037927936 41 70243235494371574939648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937319 1048576 70243235494371574939648 151115727451828646838272 998216414 2147483648 271758 271492 (ep798 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep800 := BSN.sin_dyadic_bound_f 998216414 2147483648 2 1 1048576 271758 ep797 ep93 ep797 ep797 ep94 ep797 470046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998216414) qz287 0 1 ep797 ep93 ep797 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998216414) qz288 0 1 ep797 ep94 ep797 rfl rfl rfl rfl) rfl rfl

noncomputable def ep801 := @Enclosure.Real.IsNear.sin_image qz163 qz459 Bool.false 273905899 1048576 843 1048576 Bool.true 470046 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 147052110270384376533 562949953421312000 6808500002772679923 8484125000000000000000 273905899 1048576 843 1048576 (ep796 rfl) rfl) (Enclosure.sfrac_false_div 273905899 1048576) (BSN.sin_reduce2 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70243235494371574939648) qz32) 226375608064910080 72057594037927936 Bool.false 470046 1048576 41 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 273905899 1048576 226375608064910080 72057594037927936 41 70243235494371574939648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470046 1048576 70243235494371574939648 151115727451828646838272 998216414 2147483648 271758 271492 (ep800 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep802 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.true 296339963083 1099511627776 796476934711 3244658813566976 Bool.false 74304166611 549755813888 99387251511 405582351695872 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz163) 316157 1048576 1 1048576 937319 1048576 57741227 71169998848 296339963083 1099511627776 796476934711 3244658813566976 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 937319 1048576 115482454 142339997696 937319 1048576 57741227 71169998848 (ep799 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 316157 1048576 1 1048576 235023 524288 57741227 71169998848 74304166611 549755813888 99387251511 405582351695872 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 235023 524288 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 470046 1048576 115482454 142339997696 235023 524288 57741227 71169998848 (ep801 rfl rfl) rfl)) rfl)

noncomputable def ep803 := @ep766 296339963083 1099511627776 796476934711 3244658813566976 Bool.false 74304166611 549755813888 99387251511 405582351695872 Bool.false ep767 4480802212291 1099511627776 262202312775461 74627152712040448 Bool.false 57179203653551114944512 104008365549 1099511627776 261924723472379 74627152712040448 (ep768 (BSN.head_sum_c_succ qz148 10 11 rfl rfl) (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep795 ep802) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz268 qz448 qz558)

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz591 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 17227999755 68719476736 8769980899583 37313576356020224 Bool.true 157357338147 1099511627776 17513437777369 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 12 qz152 rfl)

noncomputable def ep805 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz558 108936 1000 0 1 11191020447815397 4503599627370496 500000000203619 67873000000000000000 152388125437902260949 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 46938541828353910898688 18889465931478580854784 1000000000407238 135746000000000000000 11191020447815397 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep806 := nat_lit 1539754792874567397023868883094811201

noncomputable def ep807 := BSN.cos_dyadic_bound_f 1113942801 2147483648 2 1 1048576 271758 ep806 ep60 ep806 ep806 ep61 ep806 910640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1113942801) qz291 0 1 ep806 ep60 ep806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1113942801) qz292 0 1 ep806 ep61 ep806 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141922501) qz26)

noncomputable def ep808 := @Enclosure.Real.IsNear.cos_image qz164 qz460 Bool.false 141922501 524288 843 1048576 Bool.false 910640 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 152388125437902260949 562949953421312000 6808500002772679923 8484125000000000000000 141922501 524288 843 1048576 (ep805 rfl) rfl) (Enclosure.sfrac_false_div 141922501 524288) (BSN.cos_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39193378015523993812992) qz301) 226375608064910080 72057594037927936 Bool.false 910640 1048576 43 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 141922501 524288 226375608064910080 72057594037927936 43 39193378015523993812992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 910640 1048576 39193378015523993812992 75557863725914323419136 1113942801 2147483648 271758 271492 (ep807 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep809 := BSN.sin_dyadic_bound_f 1113942801 2147483648 2 1 1048576 271758 ep806 ep93 ep806 ep806 ep94 ep806 519851 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1113942801) qz287 0 1 ep806 ep93 ep806 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1113942801) qz288 0 1 ep806 ep94 ep806 rfl rfl rfl rfl) rfl rfl

noncomputable def ep810 := @Enclosure.Real.IsNear.sin_image qz164 qz460 Bool.false 141922501 524288 843 1048576 Bool.false 519851 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 152388125437902260949 562949953421312000 6808500002772679923 8484125000000000000000 141922501 524288 843 1048576 (ep805 rfl) rfl) (Enclosure.sfrac_false_div 141922501 524288) (BSN.sin_reduce0 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39193378015523993812992) qz301) 226375608064910080 72057594037927936 Bool.false 519851 1048576 43 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 141922501 524288 226375608064910080 72057594037927936 43 39193378015523993812992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 519851 1048576 39193378015523993812992 75557863725914323419136 1113942801 2147483648 271758 271492 (ep809 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep811 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 17227999755 68719476736 8769980899583 37313576356020224 Bool.true 157357338147 1099511627776 17513437777369 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz164) 302697 1048576 1 1048576 56915 65536 57741227 71169998848 17227999755 68719476736 8769980899583 37313576356020224 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 910640 1048576 115482454 142339997696 56915 65536 57741227 71169998848 (ep808 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 302697 1048576 1 1048576 519851 1048576 57741227 71169998848 157357338147 1099511627776 17513437777369 74627152712040448 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 519851 1048576 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 519851 1048576 115482454 142339997696 519851 1048576 57741227 71169998848 (ep810 rfl rfl) rfl)) rfl)

noncomputable def ep812 := @ep764 17227999755 68719476736 8769980899583 37313576356020224 Bool.true 157357338147 1099511627776 17513437777369 74627152712040448 Bool.false 326860769440093286957056 4756450208371 1099511627776 279742274574627 74627152712040448 Bool.true 58657815701404199682048 26674486299 549755813888 69859540312437 18656788178010112 (ep765 (BSN.head_sum_c_succ qz148 11 12 rfl rfl) (ep803 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep804 ep811) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz448 qz559)

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq qz590 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 149827647255 549755813888 8421364903353 37313576356020224 Bool.true 56578160535 1099511627776 16785999856481 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 13 qz152 rfl)

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz559 108936 1000 0 1 11551497052968677 4503599627370496 500000000203619 67873000000000000000 157296735370274474709 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 48450490295254733815808 18889465931478580854784 1000000000407238 135746000000000000000 11551497052968677 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep222 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep815 := nat_lit 5027129078545467275300924802620857079513392321956705569426288576816466812739840

noncomputable def ep816 := nat_lit 6095141820678660330948778316540522944942763005891822100423264966602208583936

noncomputable def ep817 := nat_lit 13156422118957029794776124080065941028243263036448499255572927653144819028992256

noncomputable def ep818 := BSN.sin_dyadic_bound_f 2972507622 2147483648 3 2 1048576 271758 ep815 ep77 ep816 ep817 ep79 ep816 1030370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2972507622) qz287 0 2 ep815 ep77 ep816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2972507622) qz288 0 2 ep817 ep79 ep816 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 292988001) qz30)

noncomputable def ep819 := @Enclosure.Real.IsNear.cos_image qz165 qz461 Bool.false 292988001 1048576 421 524288 Bool.true 1030370 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 157296735370274474709 562949953421312000 6808500002772679923 8484125000000000000000 292988001 1048576 421 524288 (ep814 rfl) rfl) (Enclosure.sfrac_false_div 292988001 1048576) (BSN.cos_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209171628482054389235712) qz32) 226375608064910080 72057594037927936 Bool.false 1030370 1048576 44 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 292988001 1048576 226375608064910080 72057594037927936 44 209171628482054389235712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1030370 1048576 209171628482054389235712 151115727451828646838272 2972507622 2147483648 271758 271492 (ep818 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep820 := nat_lit 2795558440001116779758713236263383054371859184645232792837015104883193655337216

noncomputable def ep821 := nat_lit 8374485036361993018614242152157068117225692027923914734310198784716376548843776

noncomputable def ep822 := BSN.cos_dyadic_bound_f 2972507622 2147483648 3 2 1048576 271758 ep820 ep70 ep816 ep821 ep73 ep816 194545 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2972507622) qz291 0 2 ep820 ep70 ep816 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2972507622) qz292 0 2 ep821 ep73 ep816 rfl rfl rfl rfl) rfl rfl

noncomputable def ep823 := @Enclosure.Real.IsNear.sin_image qz165 qz461 Bool.false 292988001 1048576 421 524288 Bool.false 194545 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 157296735370274474709 562949953421312000 6808500002772679923 8484125000000000000000 292988001 1048576 421 524288 (ep814 rfl) rfl) (Enclosure.sfrac_false_div 292988001 1048576) (BSN.sin_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209171628482054389235712) qz32) 226375608064910080 72057594037927936 Bool.false 194545 1048576 44 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 292988001 1048576 226375608064910080 72057594037927936 44 209171628482054389235712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 194545 1048576 209171628482054389235712 151115727451828646838272 2972507622 2147483648 271758 271492 (ep822 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep824 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 149827647255 549755813888 8421364903353 37313576356020224 Bool.true 56578160535 1099511627776 16785999856481 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz165) 290823 1048576 1 1048576 515185 524288 28836677 35584999424 149827647255 549755813888 8421364903353 37313576356020224 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 1030370 1048576 57673354 71169998848 515185 524288 28836677 35584999424 (ep819 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 290823 1048576 1 1048576 194545 1048576 28836677 35584999424 56578160535 1099511627776 16785999856481 74627152712040448 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 194545 1048576 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 194545 1048576 57673354 71169998848 194545 1048576 28836677 35584999424 (ep823 rfl rfl) rfl)) rfl)

noncomputable def ep825 := @ep761 149827647255 549755813888 8421364903353 37313576356020224 Bool.true 56578160535 1099511627776 16785999856481 74627152712040448 Bool.false ep762 4456794913861 1099511627776 296585004381333 74627152712040448 Bool.true 60433080543906946351104 109927133133 1099511627776 296224161106229 74627152712040448 (ep763 (BSN.head_sum_c_succ qz148 12 13 rfl rfl) (ep812 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep813 ep824) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz448 qz560)

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq qz589 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 9532465645 1099511627776 16183941119483 74627152712040448 Bool.false 36712673729 137438953472 4063191238085 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 14 qz152 rfl)

noncomputable def ep827 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz560 108936 1000 0 1 11885250371606245 4503599627370496 500000000203619 67873000000000000000 32368290862032447633 112589990684262400 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 49850353174629559828480 18889465931478580854784 1000000000407238 135746000000000000000 11885250371606245 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep233 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep828 := BSN.sin_dyadic_bound_f 69676570 2147483648 1 0 1048576 271758 0 1 1 0 1 1 34015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 69676570) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 69676570) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 301453199) qz30)

noncomputable def ep829 := @Enclosure.Real.IsNear.cos_image qz166 qz462 Bool.false 301453199 1048576 843 1048576 Bool.false 34015 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 32368290862032447633 112589990684262400 6808500002772679923 8484125000000000000000 301453199 1048576 843 1048576 (ep827 rfl) rfl) (Enclosure.sfrac_false_div 301453199 1048576) (BSN.cos_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4903052737786452901888) qz32) 226375608064910080 72057594037927936 Bool.false 34015 1048576 45 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 301453199 1048576 226375608064910080 72057594037927936 45 4903052737786452901888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 34015 1048576 4903052737786452901888 151115727451828646838272 69676570 2147483648 271758 271492 (ep828 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep830 := BSN.cos_dyadic_bound_f 69676570 2147483648 1 0 1048576 271758 0 1 1 0 1 1 1048024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 69676570) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 69676570) qz292 0 0 rfl) rfl rfl

noncomputable def ep831 := @Enclosure.Real.IsNear.sin_image qz166 qz462 Bool.false 301453199 1048576 843 1048576 Bool.true 1048024 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 32368290862032447633 112589990684262400 6808500002772679923 8484125000000000000000 301453199 1048576 843 1048576 (ep827 rfl) rfl) (Enclosure.sfrac_false_div 301453199 1048576) (BSN.sin_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4903052737786452901888) qz32) 226375608064910080 72057594037927936 Bool.false 1048024 1048576 45 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 301453199 1048576 226375608064910080 72057594037927936 45 4903052737786452901888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048024 1048576 4903052737786452901888 151115727451828646838272 69676570 2147483648 271758 271492 (ep830 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep832 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 9532465645 1099511627776 16183941119483 74627152712040448 Bool.false 36712673729 137438953472 4063191238085 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz166) 280243 1048576 1 1048576 34015 1048576 57741227 71169998848 9532465645 1099511627776 16183941119483 74627152712040448 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 34015 1048576 115482454 142339997696 34015 1048576 57741227 71169998848 (ep829 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 280243 1048576 1 1048576 131003 131072 57741227 71169998848 36712673729 137438953472 4063191238085 18656788178010112 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 131003 131072 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 1048024 1048576 115482454 142339997696 131003 131072 57741227 71169998848 (ep831 rfl rfl) rfl)) rfl)

noncomputable def ep833 := @ep758 9532465645 1099511627776 16183941119483 74627152712040448 Bool.false 36712673729 137438953472 4063191238085 18656788178010112 Bool.false ep759 2233163689753 549755813888 19548059093801 4664197044502528 Bool.false 25257741515805245308928 183774256699 1099511627776 312476926058569 74627152712040448 (ep760 (BSN.head_sum_c_succ qz148 13 14 rfl rfl) (ep825 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep826 ep832) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz448 qz562)

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq qz588 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 135362648511 549755813888 1962605542975 9328394089005056 Bool.false 21363901569 274877906944 7827199221331 37313576356020224 (BSN.cpow_neg_s_mk qz151 108936 1000 15 qz152 rfl)

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz562 108936 1000 0 1 12195965485668069 4503599627370496 500000000203619 67873000000000000000 166072462018342095573 562949953421312000 6808500002772679923 8484125000000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 500000000203619 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 51153586820399524478976 18889465931478580854784 1000000000407238 135746000000000000000 12195965485668069 4503599627370496 500000000203619 67873000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep836 := nat_lit 3505945932698409673409010195828581569608079692059668815694794665151802511947905

noncomputable def ep837 := nat_lit 2966693148507442031272302524354180194331616161985670999391822700968322496641

noncomputable def ep838 := nat_lit 9177436130064918048020585832606854485801767053036870097582589743405534056773761

noncomputable def ep839 := BSN.sin_dyadic_bound_f 2716652433 2147483648 3 2 1048576 271758 ep836 ep77 ep837 ep838 ep79 ep837 999942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2716652433) qz287 0 2 ep836 ep77 ep837 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2716652433) qz288 0 2 ep838 ep79 ep837 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309334065) qz30)

noncomputable def ep840 := @Enclosure.Real.IsNear.cos_image qz167 qz463 Bool.false 309334065 1048576 843 1048576 Bool.false 999942 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 166072462018342095573 562949953421312000 6808500002772679923 8484125000000000000000 309334065 1048576 843 1048576 (ep835 rfl) rfl) (Enclosure.sfrac_false_div 309334065 1048576) (BSN.cos_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191167420119319807262720) qz32) 226375608064910080 72057594037927936 Bool.false 999942 1048576 46 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 309334065 1048576 226375608064910080 72057594037927936 46 191167420119319807262720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 999942 1048576 191167420119319807262720 151115727451828646838272 2716652433 2147483648 271758 271492 (ep839 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep841 := nat_lit 1949066270676230903907793354360036063201969436105142973607948957395876205525121

noncomputable def ep842 := nat_lit 5841265425731677827660835458031399829217245075991457578825063226785691971582081

noncomputable def ep843 := BSN.cos_dyadic_bound_f 2716652433 2147483648 3 2 1048576 271758 ep841 ep70 ep837 ep842 ep73 ep837 315636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2716652433) qz291 0 2 ep841 ep70 ep837 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2716652433) qz292 0 2 ep842 ep73 ep837 rfl rfl rfl rfl) rfl rfl

noncomputable def ep844 := @Enclosure.Real.IsNear.sin_image qz167 qz463 Bool.false 309334065 1048576 843 1048576 Bool.true 315636 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 166072462018342095573 562949953421312000 6808500002772679923 8484125000000000000000 309334065 1048576 843 1048576 (ep835 rfl) rfl) (Enclosure.sfrac_false_div 309334065 1048576) (BSN.sin_reduce3 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191167420119319807262720) qz32) 226375608064910080 72057594037927936 Bool.false 315636 1048576 46 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 309334065 1048576 226375608064910080 72057594037927936 46 191167420119319807262720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 315636 1048576 191167420119319807262720 151115727451828646838272 2716652433 2147483648 271758 271492 (ep843 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep845 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 135362648511 549755813888 1962605542975 9328394089005056 Bool.false 21363901569 274877906944 7827199221331 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz167) 270741 1048576 1 1048576 499971 524288 57741227 71169998848 135362648511 549755813888 1962605542975 9328394089005056 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 999942 1048576 115482454 142339997696 499971 524288 57741227 71169998848 (ep840 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz57 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 270741 1048576 1 1048576 78909 262144 57741227 71169998848 21363901569 274877906944 7827199221331 37313576356020224 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 78909 262144 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 315636 1048576 115482454 142339997696 78909 262144 57741227 71169998848 (ep844 rfl rfl) rfl)) rfl)

noncomputable def ep846 := @ep755 135362648511 549755813888 1962605542975 9328394089005056 Bool.false 21363901569 274877906944 7827199221331 37313576356020224 Bool.false ep756 296065792283 68719476736 41058723730577 9328394089005056 Bool.false 74005341221387920998400 269229862975 1099511627776 328131324501231 74627152712040448 (ep757 (BSN.head_sum_c_succ qz148 14 15 rfl rfl) (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep834 ep845) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz448 qz563)

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq qz587 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 124240315563 549755813888 7600425902837 37313576356020224 Bool.true 29383871013 274877906944 3791737005115 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 16 qz152 rfl)

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz563 108936 1000 0 1 3121657384082679 1125899906842624 125000000067873 16968250000000000000 42507608599053839943 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 52372720210750067441664 18889465931478580854784 1000000000542984 135746000000000000000 3121657384082679 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep849 := nat_lit 810472460897114743408745917422823696

noncomputable def ep850 := BSN.cos_dyadic_bound_f 948821606 2147483648 2 1 1048576 271758 ep849 ep60 ep849 ep849 ep61 ep849 947882 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 948821606) qz291 0 1 ep849 ep60 ep849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 948821606) qz292 0 1 ep849 ep61 ep849 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 316706363) qz30)

noncomputable def ep851 := @Enclosure.Real.IsNear.cos_image qz168 qz464 Bool.false 316706363 1048576 843 1048576 Bool.false 947882 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 42507608599053839943 140737488355328000 1702125000924226641 2121031250000000000000 316706363 1048576 843 1048576 (ep848 rfl) rfl) (Enclosure.sfrac_false_div 316706363 1048576) (BSN.cos_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66767384929220140466176) qz32) 226375608064910080 72057594037927936 Bool.false 947882 1048576 48 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 316706363 1048576 226375608064910080 72057594037927936 48 66767384929220140466176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947882 1048576 66767384929220140466176 151115727451828646838272 948821606 2147483648 271758 271492 (ep850 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep852 := BSN.sin_dyadic_bound_f 948821606 2147483648 2 1 1048576 271758 ep849 ep93 ep849 ep849 ep94 ep849 448364 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 948821606) qz287 0 1 ep849 ep93 ep849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 948821606) qz288 0 1 ep849 ep94 ep849 rfl rfl rfl rfl) rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.sin_image qz168 qz464 Bool.false 316706363 1048576 843 1048576 Bool.false 448364 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 42507608599053839943 140737488355328000 1702125000924226641 2121031250000000000000 316706363 1048576 843 1048576 (ep848 rfl) rfl) (Enclosure.sfrac_false_div 316706363 1048576) (BSN.sin_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66767384929220140466176) qz32) 226375608064910080 72057594037927936 Bool.false 448364 1048576 48 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 316706363 1048576 226375608064910080 72057594037927936 48 66767384929220140466176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448364 1048576 66767384929220140466176 151115727451828646838272 948821606 2147483648 271758 271492 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 124240315563 549755813888 7600425902837 37313576356020224 Bool.true 29383871013 274877906944 3791737005115 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz168) 262143 1048576 1 1048576 473941 524288 57741227 71169998848 124240315563 549755813888 7600425902837 37313576356020224 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 947882 1048576 115482454 142339997696 473941 524288 57741227 71169998848 (ep851 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 262143 1048576 1 1048576 112091 262144 57741227 71169998848 29383871013 274877906944 3791737005115 18656788178010112 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 112091 262144 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 448364 1048576 115482454 142339997696 112091 262144 57741227 71169998848 (ep853 rfl rfl) rfl)) rfl)

noncomputable def ep855 := @ep753 124240315563 549755813888 7600425902837 37313576356020224 Bool.true 29383871013 274877906944 3791737005115 18656788178010112 Bool.false 171301620075941091868672 2492766653827 549755813888 171835320825145 37313576356020224 Bool.false 41697433373524268941312 151694378923 1099511627776 343298272521691 74627152712040448 (ep754 (BSN.head_sum_c_succ qz148 15 16 rfl rfl) (ep846 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep847 ep854) rfl rfl

theorem EMRow33.d13 : Enclosure.Complex.IsNear qz160 Bool.false 2492766653827 549755813888 171835320825145 37313576356020224 Bool.false 151694378923 1099511627776 343298272521691 74627152712040448 := ep752 (BSN.head_sum_c_succ qz148 16 17 rfl rfl) (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz169 := (BSN.headSumC qz446 25)

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq qz169 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 24) (@HPow.hPow Complex Complex Complex qz6 qz354 qz149)) Bool.false 5732092807383 1099511627776 451543792841821 74627152712040448 Bool.true 131548070893 1099511627776 451155193310605 74627152712040448

noncomputable def ep857 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 24) (@HPow.hPow Complex Complex Complex qz6 qz354 qz149) Bool.false 693829219221 137438953472 109781829725859 18656788178010112 Bool.false 528118681 1099511627776 438754378962907 74627152712040448 Bool.false

noncomputable def ep858 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz149)) Bool.false 693829219221 137438953472 109781829725859 18656788178010112 Bool.false 528118681 1099511627776 438754378962907 74627152712040448

noncomputable def ep859 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz149) Bool.false 2849618546217 549755813888 213228207684161 37313576356020224 Bool.false 175110181321 1099511627776 426075410893679 74627152712040448 Bool.true

noncomputable def ep860 := nat_lit 1525746588448465713364992

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz149)) Bool.false 2849618546217 549755813888 213228207684161 37313576356020224 Bool.false 175110181321 1099511627776 426075410893679 74627152712040448

noncomputable def ep862 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz149) Bool.false 2947960376289 549755813888 25843011751265 4664197044502528 Bool.false 11892448759 274877906944 103282043945537 18656788178010112 Bool.true

noncomputable def ep863 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz149)) Bool.false 2947960376289 549755813888 25843011751265 4664197044502528 Bool.false 11892448759 274877906944 103282043945537 18656788178010112

noncomputable def ep864 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz149) Bool.false 2921786114087 549755813888 12507649523741 2332098522251264 Bool.true 23322858477 137438953472 99944229359441 18656788178010112 Bool.false

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz149)) Bool.false 2921786114087 549755813888 12507649523741 2332098522251264 Bool.true 23322858477 137438953472 99944229359441 18656788178010112

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz149) Bool.false 350968399011 68719476736 14871388097291 2870275104309248 Bool.true 278380529413 1099511627776 29709820997195 5740550208618496 Bool.false

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz149)) Bool.false 350968399011 68719476736 14871388097291 2870275104309248 Bool.true 278380529413 1099511627776 29709820997195 5740550208618496

noncomputable def ep868 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz149) Bool.false 2687750830031 549755813888 23294654704023 4664197044502528 Bool.true 25090439199 137438953472 93082965057827 18656788178010112 Bool.false

noncomputable def ep869 := nat_lit 1543575342778085114118144

noncomputable def ep870 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz149)) Bool.false 2687750830031 549755813888 23294654704023 4664197044502528 Bool.true 25090439199 137438953472 93082965057827 18656788178010112

noncomputable def ep871 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz149) Bool.false 5178330771037 1099511627776 358389468146289 74627152712040448 Bool.true 32539976753 1099511627776 358014813665907 74627152712040448 Bool.false

noncomputable def ep872 := nat_lit 5910426580367359829082112

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 18) (@HAdd.hAdd Complex Complex Complex qz4 qz160 (@HPow.hPow Complex Complex Complex qz6 qz361 qz149)) Bool.false 5178330771037 1099511627776 358389468146289 74627152712040448 Bool.true 32539976753 1099511627776 358014813665907 74627152712040448

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP qz160 (@HPow.hPow Complex Complex Complex qz6 qz361 qz149) Bool.false 2492766653827 549755813888 171835320825145 37313576356020224 Bool.false 151694378923 1099511627776 343298272521691 74627152712040448 Bool.false

noncomputable def ep875 := nat_lit 2846817447612720512761856

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz448 qz564)

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz361 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 192797463383 1099511627776 14718826495999 74627152712040448 Bool.true 46058588919 274877906944 1839567643027 9328394089005056 (BSN.cpow_neg_s_mk qz151 108936 1000 17 qz152 rfl)

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz564 108936 1000 0 1 3189913004350711 1125899906842624 125000000067873 16968250000000000000 43437045380243631687 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 53517859495200818200576 18889465931478580854784 1000000000542984 135746000000000000000 3189913004350711 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep287 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep878 := nat_lit 257174553898381162771088089370286100468374774448580891108818580282243264839936

noncomputable def ep879 := nat_lit 51787336659829062669242129188196127559813038181897473307659710332037529856

noncomputable def ep880 := nat_lit 771420087021823830187925783852481909150004697269378878379840421426065719460096

noncomputable def ep881 := BSN.cos_dyadic_bound_f 1637864414 2147483648 3 2 1048576 271758 ep878 ep70 ep879 ep880 ep73 ep879 758099 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1637864414) qz291 0 2 ep878 ep70 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1637864414) qz292 0 2 ep880 ep73 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323631207) qz30)

noncomputable def ep882 := @Enclosure.Real.IsNear.cos_image qz170 qz465 Bool.false 323631207 1048576 421 524288 Bool.false 758099 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 43437045380243631687 140737488355328000 1702125000924226641 2121031250000000000000 323631207 1048576 421 524288 (ep877 rfl) rfl) (Enclosure.sfrac_false_div 323631207 1048576) (BSN.cos_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115254461976097612365824) qz32) 226375608064910080 72057594037927936 Bool.false 758099 1048576 49 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 323631207 1048576 226375608064910080 72057594037927936 49 115254461976097612365824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 758099 1048576 115254461976097612365824 151115727451828646838272 1637864414 2147483648 271758 271492 (ep881 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep883 := nat_lit 7196341894311933166827998047839052816

noncomputable def ep884 := BSN.sin_dyadic_bound_f 1637864414 2147483648 2 1 1048576 271758 ep883 ep93 ep883 ep883 ep94 ep883 724428 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1637864414) qz287 0 1 ep883 ep93 ep883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1637864414) qz288 0 1 ep883 ep94 ep883 rfl rfl rfl rfl) rfl rfl

noncomputable def ep885 := @Enclosure.Real.IsNear.sin_image qz170 qz465 Bool.false 323631207 1048576 421 524288 Bool.false 724428 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 43437045380243631687 140737488355328000 1702125000924226641 2121031250000000000000 323631207 1048576 421 524288 (ep877 rfl) rfl) (Enclosure.sfrac_false_div 323631207 1048576) (BSN.sin_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115254461976097612365824) qz32) 226375608064910080 72057594037927936 Bool.false 724428 1048576 49 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 323631207 1048576 226375608064910080 72057594037927936 49 115254461976097612365824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 724428 1048576 115254461976097612365824 151115727451828646838272 1637864414 2147483648 271758 271492 (ep884 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep886 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 192797463383 1099511627776 14718826495999 74627152712040448 Bool.true 46058588919 274877906944 1839567643027 9328394089005056 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz170) 254317 1048576 1 1048576 758099 1048576 28836677 35584999424 192797463383 1099511627776 14718826495999 74627152712040448 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 758099 1048576 57673354 71169998848 758099 1048576 28836677 35584999424 (ep882 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 254317 1048576 1 1048576 181107 262144 28836677 35584999424 46058588919 274877906944 1839567643027 9328394089005056 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 181107 262144 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 724428 1048576 57673354 71169998848 181107 262144 28836677 35584999424 (ep885 rfl rfl) rfl)) rfl)

noncomputable def ep887 := @ep874 192797463383 1099511627776 14718826495999 74627152712040448 Bool.true 46058588919 274877906944 1839567643027 9328394089005056 Bool.false ep875 5178330771037 1099511627776 358389468146289 74627152712040448 Bool.true 8944520701871057272832 32539976753 1099511627776 358014813665907 74627152712040448 EMRow33.d13 (ep876 ep886) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz448 qz565)

noncomputable def ep888 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz360 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 197170889025 1099511627776 14325007118079 74627152712040448 Bool.true 168183536839 1099511627776 14317046565401 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 18 qz152 rfl)

noncomputable def ep889 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz565 108936 1000 0 1 3254268794313975 1125899906842624 125000000067873 16968250000000000000 1772535126886935903 5629499534213120 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 54597570484265130393600 18889465931478580854784 1000000000542984 135746000000000000000 3254268794313975 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep301 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep890 := nat_lit 189052109071954109208971269910038263642447892371927753000691036646965436557921

noncomputable def ep891 := nat_lit 27988328658988070549423596740466419177502454591637262038164570774647417441

noncomputable def ep892 := nat_lit 567100350558544351485814962536633858088988672206599984477996780799347014838881

noncomputable def ep893 := BSN.cos_dyadic_bound_f 1516603733 2147483648 3 2 1048576 271758 ep890 ep70 ep891 ep892 ep73 ep891 797775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1516603733) qz291 0 2 ep890 ep70 ep891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1516603733) qz292 0 2 ep892 ep73 ep891 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 330160395) qz30)

noncomputable def ep894 := @Enclosure.Real.IsNear.cos_image qz171 qz466 Bool.false 330160395 1048576 843 1048576 Bool.false 797775 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1772535126886935903 5629499534213120 1702125000924226641 2121031250000000000000 330160395 1048576 843 1048576 (ep889 rfl) rfl) (Enclosure.sfrac_false_div 330160395 1048576) (BSN.cos_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106721500169634253373440) qz32) 226375608064910080 72057594037927936 Bool.false 797775 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 330160395 1048576 226375608064910080 72057594037927936 50 106721500169634253373440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 797775 1048576 106721500169634253373440 151115727451828646838272 1516603733 2147483648 271758 271492 (ep893 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep895 := nat_lit 5290399669116509249351575061056313521

noncomputable def ep896 := BSN.sin_dyadic_bound_f 1516603733 2147483648 2 1 1048576 271758 ep895 ep93 ep895 ep895 ep94 ep895 680489 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1516603733) qz287 0 1 ep895 ep93 ep895 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1516603733) qz288 0 1 ep895 ep94 ep895 rfl rfl rfl rfl) rfl rfl

noncomputable def ep897 := @Enclosure.Real.IsNear.sin_image qz171 qz466 Bool.false 330160395 1048576 843 1048576 Bool.false 680489 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1772535126886935903 5629499534213120 1702125000924226641 2121031250000000000000 330160395 1048576 843 1048576 (ep889 rfl) rfl) (Enclosure.sfrac_false_div 330160395 1048576) (BSN.sin_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106721500169634253373440) qz32) 226375608064910080 72057594037927936 Bool.false 680489 1048576 50 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 330160395 1048576 226375608064910080 72057594037927936 50 106721500169634253373440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 680489 1048576 106721500169634253373440 151115727451828646838272 1516603733 2147483648 271758 271492 (ep896 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep898 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 197170889025 1099511627776 14325007118079 74627152712040448 Bool.true 168183536839 1099511627776 14317046565401 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz171) 247151 1048576 1 1048576 797775 1048576 57741227 71169998848 197170889025 1099511627776 14325007118079 74627152712040448 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 797775 1048576 115482454 142339997696 797775 1048576 57741227 71169998848 (ep894 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 247151 1048576 1 1048576 680489 1048576 57741227 71169998848 168183536839 1099511627776 14317046565401 74627152712040448 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 680489 1048576 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 680489 1048576 115482454 142339997696 680489 1048576 57741227 71169998848 (ep897 rfl rfl) rfl)) rfl)

noncomputable def ep899 := @ep871 197170889025 1099511627776 14325007118079 74627152712040448 Bool.true 168183536839 1099511627776 14317046565401 74627152712040448 Bool.false ep872 2687750830031 549755813888 23294654704023 4664197044502528 Bool.true 220697837162457980731392 25090439199 137438953472 93082965057827 18656788178010112 (ep873 (BSN.head_sum_c_succ qz148 17 18 rfl rfl) (ep887 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep888 ep898) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz448 qz566)

noncomputable def ep900 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz359 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 119996362057 549755813888 6970807632599 37313576356020224 Bool.true 77657015821 1099511627776 13895812732227 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 19 qz152 rfl)

noncomputable def ep901 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz566 108936 1000 0 1 3315143513283831 1125899906842624 125000000067873 16968250000000000000 45142309220385926727 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 55618878793361701994496 18889465931478580854784 1000000000542984 135746000000000000000 3315143513283831 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep902 := nat_lit 203989892938841987489521415732307601

noncomputable def ep903 := BSN.cos_dyadic_bound_f 672050893 2147483648 2 1 1048576 271758 ep902 ep60 ep902 ep902 ep61 ep902 997646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 672050893) qz291 0 1 ep902 ep60 ep902 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 672050893) qz292 0 1 ep902 ep61 ep902 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 336336413) qz30)

noncomputable def ep904 := @Enclosure.Real.IsNear.cos_image qz172 qz467 Bool.false 336336413 1048576 421 524288 Bool.false 997646 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 45142309220385926727 140737488355328000 1702125000924226641 2121031250000000000000 336336413 1048576 421 524288 (ep901 rfl) rfl) (Enclosure.sfrac_false_div 336336413 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47291377390420876066816) qz32) 226375608064910080 72057594037927936 Bool.false 997646 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 336336413 1048576 226375608064910080 72057594037927936 51 47291377390420876066816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997646 1048576 47291377390420876066816 151115727451828646838272 672050893 2147483648 271758 271492 (ep903 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep905 := BSN.sin_dyadic_bound_f 672050893 2147483648 2 1 1048576 271758 ep902 ep93 ep902 ep902 ep94 ep902 322819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 672050893) qz287 0 1 ep902 ep93 ep902 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 672050893) qz288 0 1 ep902 ep94 ep902 rfl rfl rfl rfl) rfl rfl

noncomputable def ep906 := @Enclosure.Real.IsNear.sin_image qz172 qz467 Bool.false 336336413 1048576 421 524288 Bool.false 322819 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 45142309220385926727 140737488355328000 1702125000924226641 2121031250000000000000 336336413 1048576 421 524288 (ep901 rfl) rfl) (Enclosure.sfrac_false_div 336336413 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47291377390420876066816) qz32) 226375608064910080 72057594037927936 Bool.false 322819 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 336336413 1048576 226375608064910080 72057594037927936 51 47291377390420876066816 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 322819 1048576 47291377390420876066816 151115727451828646838272 672050893 2147483648 271758 271492 (ep905 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep907 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 119996362057 549755813888 6970807632599 37313576356020224 Bool.true 77657015821 1099511627776 13895812732227 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz172) 240559 1048576 1 1048576 498823 524288 28836677 35584999424 119996362057 549755813888 6970807632599 37313576356020224 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 997646 1048576 57673354 71169998848 498823 524288 28836677 35584999424 (ep904 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 240559 1048576 1 1048576 322819 1048576 28836677 35584999424 77657015821 1099511627776 13895812732227 74627152712040448 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 322819 1048576 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 322819 1048576 57673354 71169998848 322819 1048576 28836677 35584999424 (ep906 rfl rfl) rfl)) rfl)

noncomputable def ep908 := @ep868 119996362057 549755813888 6970807632599 37313576356020224 Bool.true 77657015821 1099511627776 13895812732227 74627152712040448 Bool.false ep869 350968399011 68719476736 14871388097291 2870275104309248 Bool.true 38260328629504034471936 278380529413 1099511627776 29709820997195 5740550208618496 (ep870 (BSN.head_sum_c_succ qz148 18 19 rfl rfl) (ep899 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep900 ep907) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz268 qz448 qz567)

noncomputable def ep909 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz358 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 114038921999 549755813888 6794347115073 37313576356020224 Bool.false 91797661597 1099511627776 13549244474229 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 20 qz152 rfl)

noncomputable def ep910 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz567 108936 1000 0 1 3372893643545847 1125899906842624 125000000067873 16968250000000000000 45928692744163798599 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 56587765202795681021952 18889465931478580854784 1000000000542984 135746000000000000000 3372893643545847 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep911 := nat_lit 2727673096275532962494004435724790490310714254351241689362453995926170483564800

noncomputable def ep912 := nat_lit 1796428375361092317437322057798097597841761817325771502615842348972443443456

noncomputable def ep913 := nat_lit 7140997225256763609446541667376111507083936385120438889706953863622586358046976

noncomputable def ep914 := BSN.sin_dyadic_bound_f 2551533286 2147483648 3 2 1048576 271758 ep911 ep77 ep912 ep913 ep79 ep912 972742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2551533286) qz287 0 2 ep911 ep77 ep912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2551533286) qz288 0 2 ep913 ep79 ep912 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 342195427) qz30)

noncomputable def ep915 := @Enclosure.Real.IsNear.cos_image qz173 qz468 Bool.false 342195427 1048576 421 524288 Bool.false 972742 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 45928692744163798599 140737488355328000 1702125000924226641 2121031250000000000000 342195427 1048576 421 524288 (ep910 rfl) rfl) (Enclosure.sfrac_false_div 342195427 1048576) (BSN.cos_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179548193132680035958784) qz32) 226375608064910080 72057594037927936 Bool.false 972742 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 342195427 1048576 226375608064910080 72057594037927936 51 179548193132680035958784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 972742 1048576 179548193132680035958784 151115727451828646838272 2551533286 2147483648 271758 271492 (ep914 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep916 := nat_lit 1516172354986567686859974607428349426882770924336167948091414816558526910177536

noncomputable def ep917 := nat_lit 4544924208208980875945049178169452085452629249373852301269012764977635843645696

noncomputable def ep918 := BSN.cos_dyadic_bound_f 2551533286 2147483648 3 2 1048576 271758 ep916 ep70 ep912 ep917 ep73 ep912 391513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2551533286) qz291 0 2 ep916 ep70 ep912 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2551533286) qz292 0 2 ep917 ep73 ep912 rfl rfl rfl rfl) rfl rfl

noncomputable def ep919 := @Enclosure.Real.IsNear.sin_image qz173 qz468 Bool.false 342195427 1048576 421 524288 Bool.true 391513 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 45928692744163798599 140737488355328000 1702125000924226641 2121031250000000000000 342195427 1048576 421 524288 (ep910 rfl) rfl) (Enclosure.sfrac_false_div 342195427 1048576) (BSN.sin_reduce3 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179548193132680035958784) qz32) 226375608064910080 72057594037927936 Bool.false 391513 1048576 51 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 342195427 1048576 226375608064910080 72057594037927936 51 179548193132680035958784 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 391513 1048576 179548193132680035958784 151115727451828646838272 2551533286 2147483648 271758 271492 (ep918 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep920 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 114038921999 549755813888 6794347115073 37313576356020224 Bool.false 91797661597 1099511627776 13549244474229 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz173) 234469 1048576 1 1048576 486371 524288 28836677 35584999424 114038921999 549755813888 6794347115073 37313576356020224 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 972742 1048576 57673354 71169998848 486371 524288 28836677 35584999424 (ep915 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 234469 1048576 1 1048576 391513 1048576 28836677 35584999424 91797661597 1099511627776 13549244474229 74627152712040448 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 391513 1048576 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 391513 1048576 57673354 71169998848 391513 1048576 28836677 35584999424 (ep919 rfl rfl) rfl)) rfl)

noncomputable def ep921 := @ep866 114038921999 549755813888 6794347115073 37313576356020224 Bool.false 91797661597 1099511627776 13549244474229 74627152712040448 Bool.false 200783612894569438380032 2921786114087 549755813888 12507649523741 2332098522251264 Bool.true 205150032707484402057216 23322858477 137438953472 99944229359441 18656788178010112 (ep867 (BSN.head_sum_c_succ qz148 19 20 rfl rfl) (ep908 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep909 ep920) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 qz448 qz568)

noncomputable def ep922 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 13087131101 274877906944 827712703783 4664197044502528 Bool.false 58538165713 274877906944 208613411631 1166049261125632 (BSN.cpow_neg_s_mk qz151 108936 1000 21 qz152 rfl)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz568 108936 1000 0 1 3427826275261687 1125899906842624 125000000067873 16968250000000000000 46676710390238391879 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 57509381830540779323392 18889465931478580854784 1000000000542984 135746000000000000000 3427826275261687 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep337 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep924 := nat_lit 49774821795372267525801086364800016

noncomputable def ep925 := BSN.sin_dyadic_bound_f 472337502 2147483648 2 1 1048576 271758 ep924 ep93 ep924 ep924 ep94 ep924 228778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 472337502) qz287 0 1 ep924 ep93 ep924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 472337502) qz288 0 1 ep924 ep94 ep924 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21735537) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep926 := @Enclosure.Real.IsNear.cos_image qz174 qz469 Bool.false 21735537 65536 843 1048576 Bool.false 228778 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 46676710390238391879 140737488355328000 1702125000924226641 2121031250000000000000 21735537 65536 843 1048576 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 21735537 65536) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2077362304773294915584) qz340) 226375608064910080 72057594037927936 Bool.false 228778 1048576 52 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 21735537 65536 226375608064910080 72057594037927936 52 2077362304773294915584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 228778 1048576 2077362304773294915584 9444732965739290427392 472337502 2147483648 271758 271492 (ep925 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep927 := BSN.cos_dyadic_bound_f 472337502 2147483648 2 1 1048576 271758 ep924 ep60 ep924 ep924 ep61 ep924 1023314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 472337502) qz291 0 1 ep924 ep60 ep924 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 472337502) qz292 0 1 ep924 ep61 ep924 rfl rfl rfl rfl) rfl rfl

noncomputable def ep928 := @Enclosure.Real.IsNear.sin_image qz174 qz469 Bool.false 21735537 65536 843 1048576 Bool.true 1023314 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 46676710390238391879 140737488355328000 1702125000924226641 2121031250000000000000 21735537 65536 843 1048576 (ep923 rfl) rfl) (Enclosure.sfrac_false_div 21735537 65536) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2077362304773294915584) qz340) 226375608064910080 72057594037927936 Bool.false 1023314 1048576 52 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 21735537 65536 226375608064910080 72057594037927936 52 2077362304773294915584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1023314 1048576 2077362304773294915584 9444732965739290427392 472337502 2147483648 271758 271492 (ep927 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep929 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 13087131101 274877906944 827712703783 4664197044502528 Bool.false 58538165713 274877906944 208613411631 1166049261125632 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz174) 114409 524288 1 524288 114389 524288 57741227 71169998848 13087131101 274877906944 827712703783 4664197044502528 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 228778 1048576 115482454 142339997696 114389 524288 57741227 71169998848 (ep926 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz70 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 114409 524288 1 524288 511657 524288 57741227 71169998848 58538165713 274877906944 208613411631 1166049261125632 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 511657 524288 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 1023314 1048576 115482454 142339997696 511657 524288 57741227 71169998848 (ep928 rfl rfl) rfl)) rfl)

noncomputable def ep930 := @ep864 13087131101 274877906944 827712703783 4664197044502528 Bool.false 58538165713 274877906944 208613411631 1166049261125632 Bool.false 810329177988166966050816 2947960376289 549755813888 25843011751265 4664197044502528 Bool.false 1634485711656345141248 11892448759 274877906944 103282043945537 18656788178010112 (ep865 (BSN.head_sum_c_succ qz148 20 21 rfl rfl) (ep921 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep922 ep929) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz268 qz448 qz569)

noncomputable def ep931 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 12292728759 68719476736 6484113674041 37313576356020224 Bool.false 127540386285 1099511627776 12947235111531 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 22 qz152 rfl)

noncomputable def ep932 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz569 108936 1000 0 1 3480203401436407 1125899906842624 125000000067873 16968250000000000000 47389929717359554119 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz383) Bool.false 58388124189833310502912 18889465931478580854784 1000000000542984 135746000000000000000 3480203401436407 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep352 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep933 := nat_lit 2329495010646102759992769154178093056

noncomputable def ep934 := BSN.cos_dyadic_bound_f 1235422328 2147483648 2 1 1048576 271758 ep933 ep60 ep933 ep933 ep61 ep933 879792 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1235422328) qz291 0 1 ep933 ep60 ep933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1235422328) qz292 0 1 ep933 ep61 ep933 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176541245) qz26)

noncomputable def ep935 := @Enclosure.Real.IsNear.cos_image qz175 qz470 Bool.false 176541245 524288 843 1048576 Bool.true 879792 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 47389929717359554119 140737488355328000 1702125000924226641 2121031250000000000000 176541245 524288 843 1048576 (ep932 rfl) rfl) (Enclosure.sfrac_false_div 176541245 524288) (BSN.cos_reduce2 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43467558877736814510080) qz301) 226375608064910080 72057594037927936 Bool.false 879792 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 176541245 524288 226375608064910080 72057594037927936 53 43467558877736814510080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 879792 1048576 43467558877736814510080 75557863725914323419136 1235422328 2147483648 271758 271492 (ep934 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep936 := BSN.sin_dyadic_bound_f 1235422328 2147483648 2 1 1048576 271758 ep933 ep93 ep933 ep933 ep94 ep933 570505 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1235422328) qz287 0 1 ep933 ep93 ep933 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1235422328) qz288 0 1 ep933 ep94 ep933 rfl rfl rfl rfl) rfl rfl

noncomputable def ep937 := @Enclosure.Real.IsNear.sin_image qz175 qz470 Bool.false 176541245 524288 843 1048576 Bool.true 570505 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 47389929717359554119 140737488355328000 1702125000924226641 2121031250000000000000 176541245 524288 843 1048576 (ep932 rfl) rfl) (Enclosure.sfrac_false_div 176541245 524288) (BSN.sin_reduce2 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43467558877736814510080) qz301) 226375608064910080 72057594037927936 Bool.false 570505 1048576 53 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q2 176541245 524288 226375608064910080 72057594037927936 53 43467558877736814510080 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 570505 1048576 43467558877736814510080 75557863725914323419136 1235422328 2147483648 271758 271492 (ep936 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep938 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 12292728759 68719476736 6484113674041 37313576356020224 Bool.false 127540386285 1099511627776 12947235111531 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz175) 223557 1048576 1 1048576 54987 65536 57741227 71169998848 12292728759 68719476736 6484113674041 37313576356020224 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 879792 1048576 115482454 142339997696 54987 65536 57741227 71169998848 (ep935 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz72 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 223557 1048576 1 1048576 570505 1048576 57741227 71169998848 127540386285 1099511627776 12947235111531 74627152712040448 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 570505 1048576 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 570505 1048576 115482454 142339997696 570505 1048576 57741227 71169998848 (ep937 rfl rfl) rfl)) rfl)

noncomputable def ep939 := @ep862 12292728759 68719476736 6484113674041 37313576356020224 Bool.false 127540386285 1099511627776 12947235111531 74627152712040448 Bool.false 195824295393233272307712 2849618546217 549755813888 213228207684161 37313576356020224 Bool.false 48133920126100804993024 175110181321 1099511627776 426075410893679 74627152712040448 (ep863 (BSN.head_sum_c_succ qz148 21 22 rfl rfl) (ep930 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep931 ep938) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz268 qz448 qz570)

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 74301669333 549755813888 6335451767557 37313576356020224 Bool.true 10911378915 68719476736 3169742017307 18656788178010112 (BSN.cpow_neg_s_mk qz151 108936 1000 23 qz152 rfl)

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz570 108936 1000 0 1 3530250507853047 1125899906842624 125000000067873 16968250000000000000 48071421165434940999 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz387) Bool.false 59227775304360265777152 18889465931478580854784 1000000000542984 135746000000000000000 3530250507853047 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep362 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep942 := nat_lit 5259417037983377740863346153107650625

noncomputable def ep943 := BSN.sin_dyadic_bound_f 1514378385 2147483648 2 1 1048576 271758 ep942 ep93 ep942 ep942 ep94 ep942 679662 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1514378385) qz287 0 1 ep942 ep93 ep942 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1514378385) qz288 0 1 ep942 ep94 ep942 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358159997) qz30)

noncomputable def ep944 := @Enclosure.Real.IsNear.cos_image qz176 qz471 Bool.false 358159997 1048576 843 1048576 Bool.true 679662 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 48071421165434940999 140737488355328000 1702125000924226641 2121031250000000000000 358159997 1048576 843 1048576 (ep941 rfl) rfl) (Enclosure.sfrac_false_div 358159997 1048576) (BSN.cos_reduce1 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106564905210134893953024) qz32) 226375608064910080 72057594037927936 Bool.false 679662 1048576 54 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 358159997 1048576 226375608064910080 72057594037927936 54 106564905210134893953024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 679662 1048576 106564905210134893953024 151115727451828646838272 1514378385 2147483648 271758 271492 (ep943 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep945 := nat_lit 187944783690055414507311182522436827478296163423518080672090635446475971690625

noncomputable def ep946 := nat_lit 27661467579429846658173539474191074762844153726729953914935179907062890625

noncomputable def ep947 := nat_lit 563779028135007383828617200488362100285362801963100782108442035979613789290625

noncomputable def ep948 := BSN.cos_dyadic_bound_f 1514378385 2147483648 3 2 1048576 271758 ep945 ep70 ep946 ep947 ep73 ep946 798480 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1514378385) qz291 0 2 ep945 ep70 ep946 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1514378385) qz292 0 2 ep947 ep73 ep946 rfl rfl rfl rfl) rfl rfl

noncomputable def ep949 := @Enclosure.Real.IsNear.sin_image qz176 qz471 Bool.false 358159997 1048576 843 1048576 Bool.false 798480 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 48071421165434940999 140737488355328000 1702125000924226641 2121031250000000000000 358159997 1048576 843 1048576 (ep941 rfl) rfl) (Enclosure.sfrac_false_div 358159997 1048576) (BSN.sin_reduce1 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106564905210134893953024) qz32) 226375608064910080 72057594037927936 Bool.false 798480 1048576 54 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 358159997 1048576 226375608064910080 72057594037927936 54 106564905210134893953024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 798480 1048576 106564905210134893953024 151115727451828646838272 1514378385 2147483648 271758 271492 (ep948 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep950 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 74301669333 549755813888 6335451767557 37313576356020224 Bool.true 10911378915 68719476736 3169742017307 18656788178010112 (@Enclosure.Real.IsNear.mulLit_ft qz74 (Real.cos qz176) 218643 1048576 1 1048576 339831 524288 57741227 71169998848 74301669333 549755813888 6335451767557 37313576356020224 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 679662 1048576 115482454 142339997696 339831 524288 57741227 71169998848 (ep944 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 218643 1048576 1 1048576 49905 65536 57741227 71169998848 10911378915 68719476736 3169742017307 18656788178010112 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 49905 65536 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 798480 1048576 115482454 142339997696 49905 65536 57741227 71169998848 (ep949 rfl rfl) rfl)) rfl)

noncomputable def ep951 := @ep859 74301669333 549755813888 6335451767557 37313576356020224 Bool.true 10911378915 68719476736 3169742017307 18656788178010112 Bool.false ep860 693829219221 137438953472 109781829725859 18656788178010112 Bool.false 36292039412826505216 528118681 1099511627776 438754378962907 74627152712040448 (ep861 (BSN.head_sum_c_succ qz148 22 23 rfl rfl) (ep939 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep940 ep950) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz268 qz448 qz571)

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz354 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 181459053615 1099511627776 12416473938385 74627152712040448 Bool.true 66038094787 549755813888 6200407173849 37313576356020224 (BSN.cpow_neg_s_mk qz151 108936 1000 24 qz152 rfl)

noncomputable def ep953 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz571 108936 1000 0 1 3578169457974519 1125899906842624 125000000067873 16968250000000000000 48723933509239025223 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 60031721881041427759104 18889465931478580854784 1000000000542984 135746000000000000000 3578169457974519 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep954 := nat_lit 3332825766096630115784112435569000625

noncomputable def ep955 := BSN.cos_dyadic_bound_f 1351148715 2147483648 2 1 1048576 271758 ep954 ep60 ep954 ep954 ep61 ep954 847785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1351148715) qz291 0 1 ep954 ep60 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1351148715) qz292 0 1 ep954 ep61 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 363021593) qz30)

noncomputable def ep956 := @Enclosure.Real.IsNear.cos_image qz177 qz472 Bool.false 363021593 1048576 843 1048576 Bool.false 847785 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 48723933509239025223 140737488355328000 1702125000924226641 2121031250000000000000 363021593 1048576 843 1048576 (ep953 rfl) rfl) (Enclosure.sfrac_false_div 363021593 1048576) (BSN.cos_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95078638292150041706496) qz32) 226375608064910080 72057594037927936 Bool.false 847785 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 363021593 1048576 226375608064910080 72057594037927936 55 95078638292150041706496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 847785 1048576 95078638292150041706496 151115727451828646838272 1351148715 2147483648 271758 271492 (ep955 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep957 := BSN.sin_dyadic_bound_f 1351148715 2147483648 2 1 1048576 271758 ep954 ep93 ep954 ep954 ep94 ep954 617066 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1351148715) qz287 0 1 ep954 ep93 ep954 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1351148715) qz288 0 1 ep954 ep94 ep954 rfl rfl rfl rfl) rfl rfl

noncomputable def ep958 := @Enclosure.Real.IsNear.sin_image qz177 qz472 Bool.false 363021593 1048576 843 1048576 Bool.false 617066 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 48723933509239025223 140737488355328000 1702125000924226641 2121031250000000000000 363021593 1048576 843 1048576 (ep953 rfl) rfl) (Enclosure.sfrac_false_div 363021593 1048576) (BSN.sin_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95078638292150041706496) qz32) 226375608064910080 72057594037927936 Bool.false 617066 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 363021593 1048576 226375608064910080 72057594037927936 55 95078638292150041706496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 617066 1048576 95078638292150041706496 151115727451828646838272 1351148715 2147483648 271758 271492 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 181459053615 1099511627776 12416473938385 74627152712040448 Bool.true 66038094787 549755813888 6200407173849 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz177) 214039 1048576 1 1048576 847785 1048576 57741227 71169998848 181459053615 1099511627776 12416473938385 74627152712040448 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 847785 1048576 115482454 142339997696 847785 1048576 57741227 71169998848 (ep956 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz76 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 214039 1048576 1 1048576 308533 524288 57741227 71169998848 66038094787 549755813888 6200407173849 37313576356020224 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 308533 524288 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 617066 1048576 115482454 142339997696 308533 524288 57741227 71169998848 (ep958 rfl rfl) rfl)) rfl)

noncomputable def ep960 := @ep857 181459053615 1099511627776 12416473938385 74627152712040448 Bool.true 66038094787 549755813888 6200407173849 37313576356020224 Bool.false 787812836651097995083776 5732092807383 1099511627776 451543792841821 74627152712040448 Bool.true 72319316779177537961984 131548070893 1099511627776 451155193310605 74627152712040448 (ep858 (BSN.head_sum_c_succ qz148 23 24 rfl rfl) (ep951 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep952 ep959) rfl rfl

theorem EMRow33.d14 : Enclosure.Complex.IsNear qz169 Bool.false 5732092807383 1099511627776 451543792841821 74627152712040448 Bool.true 131548070893 1099511627776 451155193310605 74627152712040448 := ep856 (BSN.head_sum_c_succ qz148 24 25 rfl rfl) (ep960 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow33.d15 : @Eq Nat (Nat.pow 28 1) 28 := @Eq.refl Nat 28

noncomputable def ep961 := nat_lit 26733334940015104383460491227683

noncomputable def ep962 := nat_lit 5130775420554115790338523136000

noncomputable def ep963 := nat_lit 11510897447570119585823066678020088207

noncomputable def ep964 := nat_lit 1378776556841552099229144205459088998400

noncomputable abbrev qz592 := (@HAdd.hAdd Complex Complex Complex qz601 (@HAdd.hAdd Complex Complex Complex qz601 qz604 (@HMul.hMul Complex Complex Complex qz603 Complex.I (@HDiv.hDiv Complex Complex Complex qz605 (↑qz608) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz473 := qz592

noncomputable abbrev qz178 := (Complex.Stirling.logGammaStirling 1 qz473)

noncomputable abbrev qz593 := (@HAdd.hAdd Complex Complex Complex qz601 qz604 (@HMul.hMul Complex Complex Complex qz603 Complex.I (@HDiv.hDiv Complex Complex Complex qz605 (↑qz608) (2 : Complex))))

noncomputable abbrev qz474 := qz593

noncomputable abbrev qz179 := qz474

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz448 (2 : Real)) (Real.log Real.pi))

noncomputable def ep965 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180))) (zetaApproximant qz148 1 28))

noncomputable def ep966 := @Enclosure.Real.IsNear.of_eq ep965 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 28))))

noncomputable def ep967 := nat_lit 22277784879984018786267644019

noncomputable def ep968 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 28))) ep967

noncomputable def ep969 := nat_lit 4275646183795096491948769280

noncomputable def ep970 := nat_lit 2464576072161201146275064385214452697

noncomputable def ep971 := nat_lit 295452119323189735549102329741233356800

noncomputable def ep972 := nat_lit 6915965718160060681595117

noncomputable def ep973 := nat_lit 28627332453542709618298641057926863

noncomputable def ep974 := nat_lit 4136329670524656297687432616377266995200

noncomputable def ep975 := nat_lit 114302281516391695848386889574272931671276689530888115978240

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.re (zetaApproximant qz148 1 28)) 1048575 1048576 23533235

noncomputable def ep977 := nat_lit 21267201086980733534208000

noncomputable def ep978 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) Bool.false 1048575 1048576 47066470

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52706861) qz26)

noncomputable def ep979 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) qz475 Bool.false 52706861 524288 339

noncomputable def ep980 := nat_lit 1431877900060456786030047

noncomputable def ep981 := nat_lit 4448124928000000000000000000

noncomputable def ep982 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) Bool.false 226374245542357661781 2251799813685248000 ep980 ep981

noncomputable def ep983 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180 73355302876058490897 450359962737049600 507651259060456786030047 ep981 1021560957 16384000

noncomputable def ep984 := nat_lit 741783127793197586123980800

noncomputable def ep985 := nat_lit 1871700576170608151155179

noncomputable def ep986 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 15427284275663609457 180143985094819840 ep985 ep415 Bool.false 73355302876058490897 450359962737049600

noncomputable def ep987 := nat_lit 1838932576072749402739179

noncomputable def ep988 := @Enclosure.Complex.IsNear.subLitP qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 13986943030806730217 180143985094819840 ep987 ep415 Bool.false 74757750426383897297 450359962737049600 474883259056008661102047

noncomputable def ep989 := nat_lit 69478311715217343843015137188380672

noncomputable def ep990 := nat_lit 20647682168641680820517516378898432

noncomputable abbrev qz476 := (@HSub.hSub Complex Complex Complex qz573 qz592 qz576)

noncomputable abbrev qz477 := (Complex.log qz592)

noncomputable abbrev qz181 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz476 qz477) qz473)

noncomputable abbrev qz182 := qz473

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq qz178 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz181 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 13986943030806730217

noncomputable def ep992 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz181 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 13986954396557923817 180143985094819840

noncomputable def ep993 := nat_lit 480587703106640214229679865856

noncomputable def ep994 := nat_lit 32108209320384889443163779891200

noncomputable def ep995 := @ep992 56119744852536220503 271492000000000000000000 Bool.false 74758438281646133969 450359962737049600 7246000020392374977 67873000000000000000000 Bool.false 2167845 34359738368 3 34359738368 Bool.true 655989897 429496729600 4539 2147483648000 Bool.true ep993 13986943030806730217 180143985094819840 ep987 ep415 Bool.false ep994

noncomputable def ep996 := @Enclosure.Complex.IsNear.addLitP qz181 qz84 Bool.true 14152495492846343657 180143985094819840 13835750002501730907 67873000000000000000000

noncomputable def ep997 := nat_lit 1833298086665640190541824

noncomputable def ep998 := @ep996 Bool.false 74758438281646133969 450359962737049600 7246000020392374977 67873000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep997 13986954396557923817 180143985094819840 56119744852536220503 271492000000000000000000 Bool.false 74758438281646133969 74758438281646133969 450359962737049600

noncomputable abbrev qz183 := (@HMul.hMul Complex Complex Complex qz394 qz476 qz477)

noncomputable def ep999 := @Enclosure.Complex.IsNear.subLitP qz183 qz182 Bool.true 13747171526382999017 180143985094819840 13835750002501730907 67873000000000000000000 Bool.false 496443223660038757909

noncomputable def ep1000 := nat_lit 1495168765632922679380000

noncomputable def ep1001 := @ep999 2251799813685248000 7246000020392374977 67873000000000000000000 Bool.false 9000 4000 0 1 Bool.false 217872 4000 0 1 Bool.true 56609981971385374628000 14152495492846343657 180143985094819840 13835750002501730907 67873000000000000000000 Bool.false ep1000 74758438281646133969 450359962737049600 7246000020392374977 67873000000000000000000

noncomputable abbrev qz184 := qz476

noncomputable abbrev qz185 := qz477

noncomputable def ep1002 := @Enclosure.Complex.IsNear.mul qz184 qz185 Bool.true 13747171526382999017 180143985094819840 13835750002501730907 67873000000000000000000 Bool.false 496443223660038757909 2251799813685248000 7246000020392374977

noncomputable abbrev qz186 := (Complex.re qz476)

noncomputable abbrev qz187 := (Complex.re qz477)

noncomputable abbrev qz188 := (Complex.im qz476)

noncomputable abbrev qz189 := (Complex.im qz477)

noncomputable def ep1003 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz186 qz187) (@HMul.hMul Real Real Real qz0 qz188 qz189) 252104845071332939 36028797018963968 1750000005226221 542984000000000000000 468990492241864491 5629499534213120

noncomputable def ep1004 := nat_lit 15477939140904191773485340565700608

noncomputable def ep1005 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 7000 4000 0 1 36014977867333277 9007199254740992 250000000746603 135746000000000000000

noncomputable def ep1006 := @Enclosure.Complex.IsNear.re_isNear qz184 Bool.false 7000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable abbrev qz190 := (Enclosure.sfrac Bool.false 217872 4000)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz190) Bool.false 7000 4000 0 1 Bool.false 217872 4000 0

noncomputable abbrev qz478 := (Complex.log (Complex.mk qz99 qz190))

noncomputable def ep1008 := @Enclosure.Complex.IsNear.of_eq qz185 qz478 Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1009 := nat_lit 28186485605114653279788827848682179689932239458239576687991513415680

noncomputable def ep1010 := nat_lit 324839288243988827346945215827999839625881106646917219481274023936

noncomputable def ep1011 := nat_lit 156441113016275734593584902220316132234147662612970596456202240

noncomputable def ep1012 := BSN.log_dyadic_bound 14781208384 80317208384 4 3 ep1009 1048576 271492 ep1010 ep1011 390398 95098416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14781208384) (BSN.artanhQ 80317208384) 0 3 ep1010 ep1009 ep1011 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz594 := (Real.log (Enclosure.sfrac Bool.false 47549208384 16000000))

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_ff qz100 qz594 1 2 0 1 36014977867333277 4503599627370496 250000000746603 67873000000000000000 36014977867333277 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 47549208384 16000000 36014977867333277 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47549208384) qz411)) Bool.false 302115531457734866108416 37778931862957161709568 1000000002986412 271492000000000000000 36014977867333277 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 47549208384 16000000 11 95098416768 65536000000 390398 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep1012 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1014 := BSN.arctan_dyadic_bound_f 9000 217872 1 0 1048576 271492 0 1 1 0 1 1 43290 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz479 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 217872)))

noncomputable def ep1015 := @Enclosure.Real.IsNear.subLit_ff_p qz101 qz479 884279719003555 562949953421312 1 2000000000000000 43290 1048576 1 271492 902864387150263091200 861038577223075 562949953421312 500000000067873 135746000000000000000 qz102 (ep1014 rfl) rfl rfl

noncomputable abbrev qz480 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217872) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1016 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (ep1008 (@congrArg Complex Complex qz182 (Complex.mk qz99 qz190) Complex.log (BSN.w_shift_mk qz151 Bool.false 108936 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz100 qz594) Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 9000 217872 4000 47549208384 16000000 rfl rfl rfl) (ep1013 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz480 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 9000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz480 (@HSub.hSub Real Real Real qz398 qz101 qz479) Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 217872 9000 rfl rfl) ep1015))))

noncomputable def ep1017 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz189 217872 4000 0 1 861038577223075 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1018 := @Enclosure.Complex.IsNear.im_isNear qz184 Bool.false 7000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable def ep1019 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (ep1008 (@congrArg Complex Complex qz182 (Complex.mk qz99 qz190) Complex.log (BSN.w_shift_mk qz151 Bool.false 108936 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz478 Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz478) (@HMul.hMul Real Real Real qz0 qz100 qz594) Bool.false 36014977867333277 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 9000 217872 4000 47549208384 16000000 rfl rfl rfl) (ep1013 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz478) qz480 Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 9000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz480 (@HSub.hSub Real Real Real qz398 qz101 qz479) Bool.false 861038577223075 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 217872 9000 rfl rfl) ep1015))))

noncomputable abbrev qz191 := (@ep1007 1 (BSN.w_sub_half_mk qz448 Bool.false 108936 1000 2 qz449 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 217872 4000) Bool.false 7000 4000 0 1 Bool.false 217872 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 217872 4000)))

noncomputable def ep1020 := @ep1003 6808500000924226641 33936500000000000000000 ep1004 13747171526382999017 180143985094819840 13835750002501730907 67873000000000000000000 (@ep1005 252104845071332939 36028797018963968 1750000005226221 542984000000000000000 (ep1006 qz191) ep1016 rfl) (@ep1017 468990492241864491 5629499534213120 6808500000924226641 33936500000000000000000 (ep1018 qz191) ep1019 rfl) rfl

noncomputable def ep1021 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz186 qz189) (@HMul.hMul Real Real Real qz0 qz188 qz187) 6027270040561525 2251799813685248 3500000000475111 542984000000000000000 490415953619477232909 2251799813685248000

noncomputable def ep1022 := nat_lit 1117890758542979176758832709796626432

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz189 7000 4000 0 1 861038577223075 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz187 217872 4000 0 1 36014977867333277 9007199254740992 250000000746603 135746000000000000000

noncomputable def ep1025 := @ep1021 3404250010166493051 33936500000000000000000 ep1022 496443223660038757909 2251799813685248000 7246000020392374977 67873000000000000000000 (@ep1023 6027270040561525 2251799813685248 3500000000475111 542984000000000000000 (ep1006 qz191) ep1019 rfl) (@ep1024 490415953619477232909 2251799813685248000 3404250010166493051 33936500000000000000000 (ep1018 qz191) ep1016 rfl) rfl

noncomputable def ep1026 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk qz99 qz190) Bool.false 9000 4000 0 1 Bool.false 217872 4000 0 1 (BSN.w_shift_mk qz151 Bool.false 108936 1000 2 qz152 rfl)

noncomputable abbrev qz481 := (ep1026 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 217872 4000) Bool.false 9000 4000 0 1 Bool.false 217872 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 217872 4000)))

noncomputable abbrev qz192 := qz481

noncomputable def ep1027 := ep1001 (@ep1002 67873000000000000000000 (ep1020 rfl) (ep1025 rfl)) qz192 rfl rfl rfl rfl rfl rfl

noncomputable def ep1028 := @ep998 7246000020392374977 67873000000000000000000 (ep1027 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz105 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep460 131072 3 1048576 (ep462 rfl) (ep464 rfl) rfl rfl) (@ep465 1 0 1 (ep467 rfl) (ep469 rfl) rfl rfl))

noncomputable abbrev qz482 := (@HPow.hPow Complex Int Complex qz578 qz592 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz193 := qz482

noncomputable def ep1029 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz193)) Bool.false 2167845 34359738368 3 34359738368

noncomputable def ep1030 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz193) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1031 := @ep1030 0 1 0 1 Bool.false 2167845 34359738368 3 34359738368 Bool.true 655989897 429496729600 4539 2147483648000 Bool.false 2167845 2167845 34359738368 3 34359738368 Bool.true 655989897 655989897 429496729600 4539

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz182 (@HSub.hSub Int Int Int qz406 qz89 (@HMul.hMul Int Int Int qz407 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1033 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108) qz193 Bool.false 2167845 34359738368 3 34359738368 Bool.true 655989897 429496729600 4539 2147483648000

noncomputable abbrev qz194 := (Complex.re qz482)

noncomputable abbrev qz195 := (Complex.im qz482)

noncomputable def ep1034 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz194) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz195) 2167845 34359738368 3 34359738368 0 1 0

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz194 1 12 0 1 6503535 8589934592 9 8589934592 2167845

noncomputable def ep1036 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 6503535 8589934592 9 8589934592 Bool.true 1967969691 107374182400 13617 536870912000

noncomputable abbrev qz483 := (@HPow.hPow Complex Nat Complex qz580 qz592 1)

noncomputable abbrev qz196 := (@Inv.inv Complex Complex.instInv qz483)

noncomputable def ep1037 := @Enclosure.Complex.IsNear.of_eq qz193 qz196 Bool.false 6503535 8589934592 9 8589934592 Bool.true 1967969691 107374182400 13617

noncomputable def ep1038 := @Enclosure.Complex.IsNear.of_parts qz196 Bool.false 6503535 8589934592 9 8589934592 Bool.true 1967969691 107374182400 13617

noncomputable abbrev qz197 := (Complex.re qz483)

noncomputable abbrev qz198 := qz483

noncomputable def ep1039 := @Enclosure.Real.IsNear.mulLit_ff qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198)) 9000 4000 0 1 722615 2147483648 1 2147483648

noncomputable def ep1040 := @Enclosure.Complex.IsNear.re_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz198 qz182 Bool.false 9000 4000 0 1 Bool.false 217872 4000 0

noncomputable def ep1042 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198)) Bool.false 722615 2147483648 1 2147483648 722615 2147483648 1

noncomputable abbrev qz199 := (Complex.im qz483)

noncomputable def ep1043 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199)) Bool.false 742956381 250000 0 1

noncomputable def ep1044 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199) 81 16 0 1 185422689 62500

noncomputable def ep1045 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1046 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 217872 4000 0 1 217872 4000 0 1

noncomputable def ep1047 := @Enclosure.Complex.IsNear.im_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 217872 4000 0 1

noncomputable abbrev qz200 := (ep1040 (@ep1041 1 (BSN.pow_one_c qz473) qz481))

noncomputable abbrev qz201 := (ep1047 (@ep1041 1 (BSN.pow_one_c qz473) qz481))

noncomputable def ep1048 := @ep1044 0 1 2971825524 742956381 250000 0 1 (@ep1045 81 16 0 1 qz200 qz200 rfl) (@ep1046 185422689 62500 0 1 qz201 qz201 rfl)

noncomputable def ep1049 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198) 742956381 250000 0 1 361307 361308 1073741824 (ep1043 (Enclosure.Complex.normSq_eq_mul_add_mul qz198) (ep1048 rfl rfl)) rfl

noncomputable def ep1050 := @Enclosure.Real.IsNear.of_eq (Complex.re qz196) (@HMul.hMul Real Real Real qz0 qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198))) Bool.false 6503535 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz198) (@ep1039 6503535 8589934592 9 8589934592 qz200 (@ep1042 2147483648 (ep1049 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1051 := @Enclosure.Real.IsNear.of_eq (Complex.im qz196) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198))) Bool.true 1967969691 107374182400 13617 536870912000 (Enclosure.Complex.inv_im_eq_mul qz198)

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz114 Complex (fun (x : Complex) => Real) qz115 Complex.normSq qz198)) 217872 4000 0 1 722615 2147483648 1

noncomputable def ep1053 := @ep1052 2147483648 1967969691 107374182400 13617 536870912000 (@Enclosure.Real.IsNear.neg qz199 Bool.false 217872 4000 0 1 qz201) (@ep1042 2147483648 (ep1049 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1054 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz195 0 1 0 1 1967969691 107374182400 13617 536870912000 0

noncomputable def ep1055 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 6503535 8589934592 9 8589934592 Bool.true 1967969691 107374182400 13617 536870912000

noncomputable abbrev qz202 := (@ep1037 536870912000 (BSN.zpow_one_sub_two_mul qz473 1 1 rfl rfl) (@ep1038 536870912000 ep1050 (ep1051 ep1053)))

noncomputable def ep1056 := @ep1034 1 2167845 2167845 34359738368 3 34359738368 (@ep1035 34359738368 3 34359738368 ep479 (ep1036 qz202) rfl) (@ep1054 1 0 1 ep499 (ep1055 qz202) rfl) rfl

noncomputable def ep1057 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz194) 655989897 429496729600 4539 2147483648000 0 1 0

noncomputable def ep1058 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz195 1 12 0 1 1967969691 107374182400 13617 536870912000 655989897

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz107)) qz108)) qz194 0 1 0 1 6503535 8589934592 9 8589934592 0

noncomputable def ep1060 := @ep1057 1 655989897 655989897 429496729600 4539 2147483648000 (@ep1058 429496729600 4539 2147483648000 ep479 (ep1055 qz202) rfl) (@ep1059 1 0 1 ep499 (ep1036 qz202) rfl) rfl

noncomputable def ep1061 := @ep1031 2147483648000 (@ep1032 0 1 0 1 (BSN.stirling_sum_base qz182) qz121) (ep1033 (ep1056 rfl) (ep1060 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1062 := @ep995 74757750426383897297 450359962737049600 474883259056008661102047 ep981 (ep1028 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1029 Bool.true 655989897 429496729600 4539 2147483648000 (BSN.stirling_sum_succ qz182 0 1 rfl) (ep1061 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1063 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz151 2) Bool.false 36008531121421981 4503599627370496 250000000746603 67873000000000000000 Bool.false 876529718953379 281474976710656

noncomputable abbrev qz203 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz474 qz415))

noncomputable def ep1064 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 1) qz203) Bool.false 36008531121421981 4503599627370496 250000000746603 67873000000000000000 Bool.false 876529718953379 281474976710656 500000000067873 67873000000000000000

noncomputable def ep1065 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 1) qz203 Bool.false 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000 Bool.false

noncomputable def ep1066 := nat_lit 648672029362379768350253781090304

noncomputable def ep1067 := nat_lit 986884728914400812385746026496

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz474 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 0) qz204) Bool.false 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1069 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 0) qz204 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz484 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz190))

noncomputable def ep1070 := @Enclosure.Complex.IsNear.of_eq qz204 qz484 Bool.false 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1071 := nat_lit 28018453524893305644363184271211022133738686364492823571421913415680

noncomputable def ep1072 := nat_lit 319995306887877471064617236529747364118692992977899473991354023936

noncomputable def ep1073 := nat_lit 151429141631443991164890372286733957426182360989953943656202240

noncomputable def ep1074 := BSN.log_dyadic_bound 14701208384 80237208384 4 3 ep1071 1048576 271492 ep1072 ep1073 388632 94938416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14701208384) (BSN.artanhQ 80237208384) 0 3 ep1072 ep1071 ep1073 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 47469208384 16000000)) 1 2 0 1 36007392955088541 4503599627370496 250000000746603 67873000000000000000 36007392955088541 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 47469208384 16000000 36007392955088541 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47469208384) qz411)) Bool.false 302051904602199375740928 37778931862957161709568 1000000002986412 271492000000000000000 36007392955088541 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 47469208384 16000000 11 94938416768 65536000000 388632 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep1074 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1076 := BSN.arctan_dyadic_bound_f 1000 217872 1 0 1048576 271492 0 1 1 0 1 1 4812 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz485 := (@Nat.cast Real Real.instNatCast 217872)

noncomputable def ep1077 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz485)) 884279719003555 562949953421312 1 2000000000000000 4812 1048576 1 271492 924525575458008334336 881696296175011 562949953421312 500000000067873 135746000000000000000 qz102 (ep1076 rfl) rfl rfl

noncomputable abbrev qz205 := (@HAdd.hAdd Complex Complex Complex qz273 qz474 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz486 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz190)

noncomputable def ep1078 := @ep1069 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000 Bool.false 36007392955088541 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 881696296175011 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz151) qz121) (ep1070 (@congrArg Complex Complex qz205 qz486 Complex.log (BSN.w_shift_mk qz151 Bool.false 108936 1000 0 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz484 Bool.false 36007392955088541 9007199254740992 250000000746603 135746000000000000000 Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz484) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 47469208384 16000000))) Bool.false 36007392955088541 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 1000 217872 4000 47469208384 16000000 rfl rfl rfl) (ep1075 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz484) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz485 qz421)) Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 1000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz485 qz421)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz485))) Bool.false 881696296175011 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 217872 1000 rfl rfl) ep1077)))) rfl rfl

noncomputable abbrev qz487 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz190))

noncomputable def ep1079 := @Enclosure.Complex.IsNear.of_eq qz203 qz487 Bool.false 36009669287755421 9007199254740992 250000000746603 135746000000000000000 Bool.false 871363141731747 562949953421312 500000000067873 135746000000000000000

noncomputable def ep1080 := nat_lit 28068775260152363103135491978130891293472617596112324706392793415680

noncomputable def ep1081 := nat_lit 321442974472602406048748701223795146543382053282211837638330023936

noncomputable def ep1082 := nat_lit 152918474053102564867825544509463359545614850830458939496202240

noncomputable def ep1083 := BSN.log_dyadic_bound 14725208384 80261208384 4 3 ep1080 1048576 271492 ep1081 ep1082 389162 94986416768 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 14725208384) (BSN.artanhQ 80261208384) 0 3 ep1081 ep1080 ep1082 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_ff qz100 (Real.log (Enclosure.sfrac Bool.false 47493208384 16000000)) 1 2 0 1 36009669287755421 4503599627370496 250000000746603 67873000000000000000 36009669287755421 9007199254740992 250000000746603 135746000000000000000 qz410 (BSN.isNear_log_sfrac 47493208384 16000000 36009669287755421 4503599627370496 250000000746603 67873000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47493208384) qz411)) Bool.false 302070999864619426643968 37778931862957161709568 1000000002986412 271492000000000000000 36009669287755421 4503599627370496 250000000746603 67873000000000000000 (BSN.log_rat_reduce_isNear 47493208384 16000000 11 94986416768 65536000000 389162 1048576 24973259072661432 36028797018963968 271492 1000000000000000 rfl rfl rfl rfl (ep1083 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1085 := BSN.arctan_dyadic_bound_f 5000 217872 1 0 1048576 271492 0 1 1 0 1 1 24059 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 217872) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 217872) 0 0 rfl) rfl rfl rfl

noncomputable def ep1086 := @Enclosure.Real.IsNear.subLit_ff_p qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz425 qz485)) 884279719003555 562949953421312 1 2000000000000000 24059 1048576 1 271492 913690477704508342272 871363141731747 562949953421312 500000000067873 135746000000000000000 qz102 (ep1085 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 qz474 qz415)

noncomputable abbrev qz488 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz190)

noncomputable def ep1087 := @ep1065 36009669287755421 9007199254740992 250000000746603 135746000000000000000 Bool.false 871363141731747 562949953421312 500000000067873 135746000000000000000 Bool.false ep1066 36008531121421981 4503599627370496 250000000746603 67873000000000000000 Bool.false ep1067 876529718953379 281474976710656 500000000067873 67873000000000000000 (ep1068 (BSN.log_sum_c_succ qz151 0 1 rfl) (ep1078 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1079 (@congrArg Complex Complex qz206 qz488 Complex.log (BSN.w_shift_mk qz151 Bool.false 108936 1000 1 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz487 Bool.false 36009669287755421 9007199254740992 250000000746603 135746000000000000000 Bool.false 871363141731747 562949953421312 500000000067873 135746000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz487) (@HMul.hMul Real Real Real qz0 qz100 (Real.log (Enclosure.sfrac Bool.false 47493208384 16000000))) Bool.false 36009669287755421 9007199254740992 250000000746603 135746000000000000000 (Enclosure.clog_re_eq 5000 217872 4000 47493208384 16000000 rfl rfl rfl) (ep1084 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz487) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz485 qz425)) Bool.false 871363141731747 562949953421312 500000000067873 135746000000000000000 (Enclosure.clog_im_eq 5000 217872 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz485 qz425)) (@HSub.hSub Real Real Real qz398 qz101 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz425 qz485))) Bool.false 871363141731747 562949953421312 500000000067873 135746000000000000000 (BSN.arctan_recip 217872 5000 rfl rfl) ep1086)))) rfl rfl

noncomputable def ep1088 := @ep988 ep981 Bool.false 36008531121421981 4503599627370496 250000000746603 67873000000000000000 Bool.false 876529718953379 281474976710656 500000000067873 67873000000000000000 Bool.true ep989 15427284275663609457 180143985094819840 ep985 ep415 Bool.false ep990 73355302876058490897 450359962737049600 507651259060456786030047 ep981 (@ep991 180143985094819840 ep987 ep415 Bool.false 74757750426383897297 450359962737049600 474883259056008661102047 ep981 (BSN.logGammaStirling_unfold 1 qz182) (ep1062 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1063 500000000067873 67873000000000000000 (BSN.log_sum_c_eq qz151 2) (ep1064 (BSN.log_sum_c_succ qz151 1 2 rfl) (ep1087 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz207 := (@HDiv.hDiv Real Real Real qz271 qz448 (2 : Real))

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Real.log Real.pi) 108936 2000 0 1 75021 65536 1 262144 1021560957 16384000 13617 65536000 (@Enclosure.Real.IsNear.of_eq qz207 (Enclosure.sfrac Bool.false 108936 2000) Bool.false 108936 2000 0 1 (BSN.t_half_eq qz151 Bool.false 108936 1000 qz152) (Enclosure.Real.IsNear.const Bool.false 108936 2000)) EMRow33.d5 rfl

noncomputable def ep1090 := @ep983 13617 65536000 ep984 226374245542357661781 2251799813685248000 ep980 ep981 (@ep986 507651259060456786030047 ep981 (ep1088 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1089 rfl rfl

noncomputable def ep1091 := nat_lit 8331101231426220027978624872771621451345198620644890628105515103934899418103745

noncomputable def ep1092 := nat_lit 16713141343084639299080705526487481920615214218157626332451574646613997584321

noncomputable def ep1093 := nat_lit 21792491472513201133459791619739933592318333659621505964309522722782599622754241

noncomputable def ep1094 := BSN.sin_dyadic_bound_f 3371958809 2147483648 3 2 1048576 271758 ep1091 ep77 ep1092 ep1093 ep79 ep1092 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3371958809) qz287 0 2 ep1091 ep77 ep1092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3371958809) qz288 0 2 ep1093 ep79 ep1092 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1095 := @ep979 1048576 Bool.false 1048575 1048576 1 135746 (@ep982 52706861 524288 339 1048576 ep1090 rfl) (Enclosure.sfrac_false_div 52706861 524288) (BSN.cos_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118640253431451612086272) qz301) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 52706861 524288 226375608064910080 72057594037927936 15 118640253431451612086272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118640253431451612086272 75557863725914323419136 3371958809 2147483648 271758 271492 (ep1094 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1096 := nat_lit 9786177483661872463872000

noncomputable def ep1097 := nat_lit 6148163292062669222939636123

noncomputable def ep1098 := nat_lit 929904114088015177636537958400

noncomputable abbrev qz489 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 28) qz585)

noncomputable abbrev qz208 := qz489

noncomputable abbrev qz490 := (@Nat.cast Complex Complex.instNatCast 28)

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz403 qz490 (@HSub.hSub Complex Complex Complex qz395 qz446 (1 : Complex))) qz402)

noncomputable abbrev qz210 := qz490

noncomputable def ep1099 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz148 1 28) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz149) (@HMul.hMul Complex Complex Complex qz78 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false 531144288200272245339333 101939348788144504832000 140717579643505396160959

noncomputable def ep1100 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz149) (@HMul.hMul Complex Complex Complex qz78 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 5727903306599 1099511627776 487278356923769 74627152712040448

noncomputable def ep1101 := nat_lit 340275217391691736547328000

noncomputable def ep1102 := nat_lit 81360071073159658240848923

noncomputable def ep1103 := nat_lit 291999660451503102979702228154056704

noncomputable def ep1104 := nat_lit 93702986056008245807023648669696

noncomputable def ep1105 := @ep1100 Bool.true 419290217 4294967296 121719068554371 18656788178010112 Bool.false 45742084168765905979 50969674394072252416000 29652585852100695931969 ep1101 Bool.false 933545058283277837139599 ep1096 ep1102 ep1098 Bool.false ep1103 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 Bool.true ep1104 21816926555709970604401 ep1096

noncomputable def ep1106 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 28, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz149) (BSN.headSumC qz148 28) Bool.false 5727903306599 1099511627776 487278356923769 74627152712040448 Bool.true 419290217 4294967296 121719068554371

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 27) (@HPow.hPow Complex Complex Complex qz6 qz131 qz149)) Bool.false 5727903306599 1099511627776 487278356923769 74627152712040448 Bool.true 419290217 4294967296 121719068554371 18656788178010112

noncomputable def ep1108 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 27) (@HPow.hPow Complex Complex Complex qz6 qz131 qz149) Bool.false 2797653517935 549755813888 10339027754491 1622329406783488 Bool.false 28782896639 549755813888 10330050600019 1622329406783488 Bool.false

noncomputable def ep1109 := nat_lit 3148948144191099646246912

noncomputable def ep1110 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz148 26) (@HPow.hPow Complex Complex Complex qz6 qz430 qz149)) Bool.false 2797653517935 549755813888 10339027754491 1622329406783488 Bool.false 28782896639 549755813888 10330050600019 1622329406783488

noncomputable def ep1111 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz148 26) (@HPow.hPow Complex Complex Complex qz6 qz430 qz149) Bool.false 2905157097759 549755813888 231832066915841 37313576356020224 Bool.false 18492895133 274877906944 28957295851169 4664197044502528 Bool.true

noncomputable def ep1112 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz148 26) (@HAdd.hAdd Complex Complex Complex qz4 qz169 (@HPow.hPow Complex Complex Complex qz6 qz431 qz149)) Bool.false 2905157097759 549755813888 231832066915841 37313576356020224 Bool.false 18492895133 274877906944 28957295851169 4664197044502528

noncomputable def ep1113 := @Enclosure.Complex.IsNear.addLitP qz169 (@HPow.hPow Complex Complex Complex qz6 qz431 qz149) Bool.false 5732092807383 1099511627776 451543792841821 74627152712040448 Bool.true 131548070893 1099511627776 451155193310605 74627152712040448 Bool.false

noncomputable def ep1114 := nat_lit 6388508019003996103507968

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz448 qz581)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz431 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 78221388135 1099511627776 932333922297 5740550208618496 Bool.false 205519651425 1099511627776 935503100623 5740550208618496 (BSN.cpow_neg_s_mk qz151 108936 1000 25 qz152 rfl)

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz581 108936 1000 0 1 3624129903009015 1125899906842624 125000000067873 16968250000000000000 9869955377854751451 28147497671065600 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz433) Bool.false 60802810194841294602240 18889465931478580854784 1000000000542984 135746000000000000000 3624129903009015 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep558 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1117 := nat_lit 372020966224472340202673483589796096

noncomputable def ep1118 := BSN.sin_dyadic_bound_f 780983492 2147483648 2 1 1048576 271758 ep1117 ep93 ep1117 ep1117 ep94 ep1117 372989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 780983492) qz287 0 1 ep1117 ep93 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 780983492) qz288 0 1 ep1117 ep94 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183842245) qz26)

noncomputable def ep1119 := @Enclosure.Real.IsNear.cos_image qz211 qz491 Bool.false 183842245 524288 421 524288 Bool.false 372989 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 9869955377854751451 28147497671065600 1702125000924226641 2121031250000000000000 183842245 524288 421 524288 (ep1116 rfl) rfl) (Enclosure.sfrac_false_div 183842245 524288) (BSN.cos_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27478413809340351774720) qz301) 226375608064910080 72057594037927936 Bool.false 372989 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 183842245 524288 226375608064910080 72057594037927936 55 27478413809340351774720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 372989 1048576 27478413809340351774720 75557863725914323419136 780983492 2147483648 271758 271492 (ep1118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1120 := BSN.cos_dyadic_bound_f 780983492 2147483648 2 1 1048576 271758 ep1117 ep60 ep1117 ep1117 ep61 ep1117 979995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 780983492) qz291 0 1 ep1117 ep60 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 780983492) qz292 0 1 ep1117 ep61 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1121 := @Enclosure.Real.IsNear.sin_image qz211 qz491 Bool.false 183842245 524288 421 524288 Bool.true 979995 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 9869955377854751451 28147497671065600 1702125000924226641 2121031250000000000000 183842245 524288 421 524288 (ep1116 rfl) rfl) (Enclosure.sfrac_false_div 183842245 524288) (BSN.sin_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27478413809340351774720) qz301) 226375608064910080 72057594037927936 Bool.false 979995 1048576 55 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 183842245 524288 226375608064910080 72057594037927936 55 27478413809340351774720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 979995 1048576 27478413809340351774720 75557863725914323419136 780983492 2147483648 271758 271492 (ep1120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz132 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz132 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 78221388135 1099511627776 932333922297 5740550208618496 Bool.false 205519651425 1099511627776 935503100623 5740550208618496 (@Enclosure.Real.IsNear.mulLit_ff qz132 (Real.cos qz211) 209715 1048576 1 1048576 372989 1048576 28836677 35584999424 78221388135 1099511627776 932333922297 5740550208618496 qz435 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 372989 1048576 57673354 71169998848 372989 1048576 28836677 35584999424 (ep1119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz132 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 209715 1048576 1 1048576 979995 1048576 28836677 35584999424 205519651425 1099511627776 935503100623 5740550208618496 qz435 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 979995 1048576 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 979995 1048576 57673354 71169998848 979995 1048576 28836677 35584999424 (ep1121 rfl rfl) rfl)) rfl)

noncomputable def ep1123 := @ep1113 78221388135 1099511627776 932333922297 5740550208618496 Bool.false 205519651425 1099511627776 935503100623 5740550208618496 Bool.false ep1114 2905157097759 549755813888 231832066915841 37313576356020224 Bool.false 81332612919902792056832 18492895133 274877906944 28957295851169 4664197044502528 EMRow33.d14 (ep1115 ep1122) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz448 qz582)

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz430 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.true 6718973739 34359738368 1491392859363 9328394089005056 Bool.true 8202893627 549755813888 5932796991085 37313576356020224 (BSN.cpow_neg_s_mk qz151 108936 1000 26 qz152 rfl)

noncomputable def ep1125 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz582 108936 1000 0 1 3668288609262839 1125899906842624 125000000067873 16968250000000000000 49951085992332078663 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz437) Bool.false 61543670347942250676224 18889465931478580854784 1000000000542984 135746000000000000000 3668288609262839 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep573 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1126 := nat_lit 6837265920335911575725190178674084922826540255657564651131668213679753317580800

noncomputable def ep1127 := nat_lit 11264973903973739588402981338604505439551153638324611661040814887734089875456

noncomputable def ep1128 := nat_lit 17888886500273334738994274212455338931929284516069667572179350668866832067198976

noncomputable def ep1129 := BSN.sin_dyadic_bound_f 3209713536 2147483648 3 2 1048576 271758 ep1126 ep77 ep1127 ep1128 ep79 ep1127 1045536 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3209713536) qz287 0 2 ep1126 ep77 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3209713536) qz288 0 2 ep1128 ep79 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23260287) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1130 := @Enclosure.Real.IsNear.cos_image qz212 qz492 Bool.false 23260287 65536 421 524288 Bool.true 1045536 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 49951085992332078663 140737488355328000 1702125000924226641 2121031250000000000000 23260287 65536 421 524288 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 23260287 65536) (BSN.cos_reduce1 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14116469421447277707264) qz340) 226375608064910080 72057594037927936 Bool.false 1045536 1048576 56 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 23260287 65536 226375608064910080 72057594037927936 56 14116469421447277707264 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045536 1048576 14116469421447277707264 9444732965739290427392 3209713536 2147483648 271758 271492 (ep1129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1131 := nat_lit 3803487721921716981886618090969426959543433988093457966922500480883300327489536

noncomputable def ep1132 := nat_lit 11387933217957203466483048310231071867751199657003724677445419812874432802717696

noncomputable def ep1133 := BSN.cos_dyadic_bound_f 3209713536 2147483648 3 2 1048576 271758 ep1131 ep70 ep1127 ep1132 ep73 ep1127 79778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3209713536) qz291 0 2 ep1131 ep70 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3209713536) qz292 0 2 ep1132 ep73 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1134 := @Enclosure.Real.IsNear.sin_image qz212 qz492 Bool.false 23260287 65536 421 524288 Bool.false 79778 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 49951085992332078663 140737488355328000 1702125000924226641 2121031250000000000000 23260287 65536 421 524288 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 23260287 65536) (BSN.sin_reduce1 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14116469421447277707264) qz340) 226375608064910080 72057594037927936 Bool.false 79778 1048576 56 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q1 23260287 65536 226375608064910080 72057594037927936 56 14116469421447277707264 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 79778 1048576 14116469421447277707264 9444732965739290427392 3209713536 2147483648 271758 271492 (ep1133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1135 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.true 6718973739 34359738368 1491392859363 9328394089005056 Bool.true 8202893627 549755813888 5932796991085 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz212) 205643 1048576 1 1048576 32673 32768 28836677 35584999424 6718973739 34359738368 1491392859363 9328394089005056 qz439 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.true 1045536 1048576 57673354 71169998848 32673 32768 28836677 35584999424 (ep1130 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz134 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 205643 1048576 1 1048576 39889 524288 28836677 35584999424 8202893627 549755813888 5932796991085 37313576356020224 qz439 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 39889 524288 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 79778 1048576 57673354 71169998848 39889 524288 28836677 35584999424 (ep1134 rfl rfl) rfl)) rfl)

noncomputable def ep1136 := @ep1111 6718973739 34359738368 1491392859363 9328394089005056 Bool.true 8202893627 549755813888 5932796991085 37313576356020224 Bool.false 96126642920561395630080 2797653517935 549755813888 10339027754491 1622329406783488 Bool.false 7911782383913812361216 28782896639 549755813888 10330050600019 1622329406783488 (ep1112 (BSN.head_sum_c_succ qz148 25 26 rfl rfl) (ep1123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1124 ep1135) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz448 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable def ep1137 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz131 qz149) (Complex.mk (@HMul.hMul Real Real Real qz0 qz138 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz138 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 132596270729 1099511627776 11683080217183 74627152712040448 Bool.true 82452044415 549755813888 5846973308305 37313576356020224 (BSN.cpow_neg_s_mk qz151 108936 1000 27 qz152 rfl)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz141 108936 1000 0 1 3710780868205815 1125899906842624 125000000067873 16968250000000000000 10105940616471716571 28147497671065600 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz442) Bool.false 62256572154556490711040 18889465931478580854784 1000000000542984 135746000000000000000 3710780868205815 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep592 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1139 := nat_lit 484652903336903012390493412659431128365714758577429795694298950410156147876096

noncomputable def ep1140 := nat_lit 183854635793537740761386615522861280056083743907488012476322959071434383616

noncomputable def ep1141 := nat_lit 1453591000739121961689957464747247662537032108244474411057944205312325574861056

noncomputable def ep1142 := BSN.cos_dyadic_bound_f 1918930842 2147483648 3 2 1048576 271758 ep1139 ep70 ep1140 ep1141 ep73 ep1140 657071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1918930842) qz291 0 2 ep1139 ep70 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1918930842) qz292 0 2 ep1141 ep73 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz493 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376475625) qz30)

noncomputable def ep1143 := @Enclosure.Real.IsNear.cos_image qz213 qz493 Bool.false 376475625 1048576 421 524288 Bool.false 657071 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 10105940616471716571 28147497671065600 1702125000924226641 2121031250000000000000 376475625 1048576 421 524288 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 376475625 1048576) (BSN.cos_reduce0 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135032753532564154613760) qz32) 226375608064910080 72057594037927936 Bool.false 657071 1048576 57 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 376475625 1048576 226375608064910080 72057594037927936 57 135032753532564154613760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 657071 1048576 135032753532564154613760 151115727451828646838272 1918930842 2147483648 271758 271492 (ep1142 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1144 := nat_lit 872228142297790592110279033494557742034241698444247641839757052371023918670080

noncomputable def ep1145 := nat_lit 2284109369941023918232355223679661834683875550816226938512497280942756512276736

noncomputable def ep1146 := BSN.sin_dyadic_bound_f 1918930842 2147483648 3 2 1048576 271758 ep1144 ep77 ep1140 ep1145 ep79 ep1140 817170 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1918930842) qz287 0 2 ep1144 ep77 ep1140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1918930842) qz288 0 2 ep1145 ep79 ep1140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1147 := @Enclosure.Real.IsNear.sin_image qz213 qz493 Bool.false 376475625 1048576 421 524288 Bool.false 817170 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 10105940616471716571 28147497671065600 1702125000924226641 2121031250000000000000 376475625 1048576 421 524288 (ep1138 rfl) rfl) (Enclosure.sfrac_false_div 376475625 1048576) (BSN.sin_reduce0 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135032753532564154613760) qz32) 226375608064910080 72057594037927936 Bool.false 817170 1048576 57 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q0 376475625 1048576 226375608064910080 72057594037927936 57 135032753532564154613760 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 817170 1048576 135032753532564154613760 151115727451828646838272 1918930842 2147483648 271758 271492 (ep1146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1148 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz138 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz138 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 132596270729 1099511627776 11683080217183 74627152712040448 Bool.true 82452044415 549755813888 5846973308305 37313576356020224 (@Enclosure.Real.IsNear.mulLit_ff qz138 (Real.cos qz213) 201799 1048576 1 1048576 657071 1048576 28836677 35584999424 132596270729 1099511627776 11683080217183 74627152712040448 qz444 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 657071 1048576 57673354 71169998848 657071 1048576 28836677 35584999424 (ep1143 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz138 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 201799 1048576 1 1048576 408585 524288 28836677 35584999424 82452044415 549755813888 5846973308305 37313576356020224 qz444 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 408585 524288 28836677 35584999424 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 817170 1048576 57673354 71169998848 408585 524288 28836677 35584999424 (ep1147 rfl rfl) rfl)) rfl)

noncomputable def ep1149 := @ep1108 132596270729 1099511627776 11683080217183 74627152712040448 Bool.true 82452044415 549755813888 5846973308305 37313576356020224 Bool.false ep1109 5727903306599 1099511627776 487278356923769 74627152712040448 Bool.true 29504926016270225113088 419290217 4294967296 121719068554371 18656788178010112 (ep1110 (BSN.head_sum_c_succ qz148 26 27 rfl rfl) (ep1136 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1137 ep1148) rfl rfl

noncomputable def ep1150 := @Enclosure.Complex.IsNear.mul qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 45742084168765905979 50969674394072252416000 29652585852100695931969 ep1101 Bool.false

noncomputable def ep1151 := nat_lit 1427921645756420578631285

noncomputable abbrev qz214 := (Complex.re qz489)

noncomputable abbrev qz215 := (Complex.im qz489)

noncomputable def ep1152 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 175699709909121382297 13048236644882496618496 ep1151

noncomputable def ep1153 := nat_lit 18598082281760303552730759168

noncomputable def ep1154 := nat_lit 1631029580610312077312000

noncomputable def ep1155 := nat_lit 8032086940666460759433861

noncomputable def ep1156 := nat_lit 774920095073345981363781632000

noncomputable def ep1157 := nat_lit 19099313243654105896158138287484203788402688

noncomputable def ep1158 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 14796236721 549755813888 5726184126905 37313576356020224 249367050397

noncomputable abbrev qz494 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz586 (Real.log (Enclosure.sfrac Bool.false 28 1)))

noncomputable abbrev qz216 := (Real.cos qz494)

noncomputable abbrev qz217 := (Real.sin qz494)

noncomputable abbrev qz495 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable abbrev qz595 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1159 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz495 qz216) (@HMul.hMul Real Real Real qz0 qz495 qz595)) Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (BSN.cpow_neg_s_mk qz151 108936 1000 28 qz152 rfl)

noncomputable abbrev qz496 := (Real.sqrt (@Nat.cast Real Real.instNatCast 28))

noncomputable abbrev qz497 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz15)

noncomputable def ep1160 := @Enclosure.Real.IsNear.inv_image qz496 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq qz496 (Real.sqrt qz497) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz497) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1161 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 135746 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_ff qz151 (Real.log (Enclosure.sfrac Bool.false 28 1)) 108936 1000 0 1 3751726938922231 1125899906842624 125000000067873 16968250000000000000 51087265727304019527 140737488355328000 1702125000924226641 2121031250000000000000 qz153 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 125000000067873 16968250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz497) Bool.false 62943533227317076688896 18889465931478580854784 1000000000542984 135746000000000000000 3751726938922231 1125899906842624 125000000067873 16968250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 135746 1000000000000000 rfl rfl rfl rfl (ep1161 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1163 := BSN.sin_dyadic_bound_f 306882483 2147483648 1 0 1048576 271758 0 1 1 0 1 1 149334 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 306882483) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 306882483) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz218 := qz494

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190314895) qz26)

noncomputable def ep1164 := @Enclosure.Real.IsNear.cos_image qz218 qz498 Bool.false 190314895 524288 843 1048576 Bool.false 149334 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 51087265727304019527 140737488355328000 1702125000924226641 2121031250000000000000 190314895 524288 843 1048576 (ep1162 rfl) rfl) (Enclosure.sfrac_false_div 190314895 524288) (BSN.cos_reduce3 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10797467499444253491200) qz301) 226375608064910080 72057594037927936 Bool.false 149334 1048576 57 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 190314895 524288 226375608064910080 72057594037927936 57 10797467499444253491200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 149334 1048576 10797467499444253491200 75557863725914323419136 306882483 2147483648 271758 271492 (ep1163 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1165 := nat_lit 8869280652865947585210479182693521

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 306882483 2147483648 2 1 1048576 271758 ep1165 ep60 ep1165 ep1165 ep61 ep1165 1037887 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 306882483) qz291 0 1 ep1165 ep60 ep1165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 306882483) qz292 0 1 ep1165 ep61 ep1165 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1167 := @Enclosure.Real.IsNear.sin_image qz218 qz498 Bool.false 190314895 524288 843 1048576 Bool.true 1037887 1048576 1 135746 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 51087265727304019527 140737488355328000 1702125000924226641 2121031250000000000000 190314895 524288 843 1048576 (ep1162 rfl) rfl) (Enclosure.sfrac_false_div 190314895 524288) (BSN.sin_reduce3 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10797467499444253491200) qz301) 226375608064910080 72057594037927936 Bool.false 1037887 1048576 57 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 190314895 524288 226375608064910080 72057594037927936 57 10797467499444253491200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037887 1048576 10797467499444253491200 75557863725914323419136 306882483 2147483648 271758 271492 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz495 qz216) (@HMul.hMul Real Real Real qz0 qz495 qz595) Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (@Enclosure.Real.IsNear.mulLit_ff qz495 qz216 198163 1048576 1 1048576 74667 524288 57741227 71169998848 14796236721 549755813888 5726184126905 37313576356020224 (@Enclosure.Real.IsNear.recentre' qz495 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep1160 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 149334 1048576 115482454 142339997696 74667 524288 57741227 71169998848 (ep1164 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz495 qz595 198163 1048576 1 1048576 1037887 1048576 57741227 71169998848 205670801581 1099511627776 11512677011579 74627152712040448 (@Enclosure.Real.IsNear.recentre' qz495 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep1160 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 1037887 1048576 57741227 71169998848 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 1037887 1048576 115482454 142339997696 1037887 1048576 57741227 71169998848 (ep1167 rfl rfl) rfl)) rfl)

noncomputable def ep1169 := @ep1158 498426688032 0 1 175699709909121382297 13048236644882496618496 ep1151 ep1153 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (ep1159 ep1168))

noncomputable def ep1170 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 249367050397 498426688032 0 1 Bool.false

noncomputable def ep1171 := @Enclosure.Complex.IsNear.addLitP qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 739956381 1483412762 0 1 Bool.true 190638000

noncomputable def ep1172 := @ep1171 741706381 0 1 Bool.false 1 672 0 1 Bool.false 4539 14000 0 1 Bool.false 498734100794 249367050397 498426688032 0 1 Bool.false 697673263359 697673263359 10383889334000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz403 qz490 (@HSub.hSub Complex Complex Complex qz395 qz446 (1 : Complex)))

noncomputable def ep1173 := @Enclosure.Complex.IsNear.addLitP qz219 qz105 Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1

noncomputable def ep1174 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 56000000 47469208384) (Enclosure.sfrac Bool.true 12200832000 47469208384)) Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1

noncomputable def ep1175 := @ep1173 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 47357208384 739956381 1483412762 0 1 Bool.true 12200832000 190638000 741706381 0 1 (ep1174 (BSN.N_div_s_sub_one_mk qz151 108936 1000 28 qz152 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 56000000 47469208384) (Enclosure.sfrac Bool.true 12200832000 47469208384) Bool.true 56000000 47469208384 0 1 Bool.true 12200832000 47469208384 0 1 (Enclosure.Real.IsNear.const Bool.true 56000000 47469208384) (Enclosure.Real.IsNear.const Bool.true 12200832000 47469208384))) qz106 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz429 qz490 1))

noncomputable def ep1176 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 672 0 1

noncomputable def ep1177 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1178 := @ep1177 0 1 0 1 Bool.false 1 672 0 1 Bool.false 4539 14000 0 1 Bool.false 1 1 672 0 1 Bool.false 4539 4539 14000 0

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1180 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 672 0 1 Bool.false 4539 14000 0 1

noncomputable def ep1181 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 672 0 1 0 1 0

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 28 0 1 1

noncomputable def ep1183 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1184 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1185 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz148 Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 (BSN.ascPochhammer_one_eval qz148)

noncomputable def ep1186 := ep1185 (@Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk qz100 qz151) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_crit_mk qz151 Bool.false 108936 1000 qz152) (@Enclosure.Complex.IsNear.mk qz100 qz151 Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 qz410 qz153))

noncomputable def ep1187 := @ep1184 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1188 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 108936 1000 0 1 0 1 0

noncomputable def ep1189 := @ep1188 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1190 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) 4539 500 0 1 0 1 0 1 4539

noncomputable def ep1191 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 108936 1000 0 1 4539 500 0

noncomputable def ep1192 := @ep1191 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1193 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1194 := @ep1193 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep620) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1195 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 (@ep1183 1 24 0 1 (ep1187 rfl) (ep1189 rfl) rfl rfl) (@ep1190 4539 500 0 1 (ep1192 rfl) (ep1194 rfl) rfl rfl)

noncomputable def ep1196 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 ep1195

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz429 qz490 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 28) qz283) Bool.false 1 28 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 28 1 28 EMRow33.d15 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 28) qz283 Bool.false 1 28 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 28) qz294))

noncomputable def ep1197 := @ep1182 672 0 1 ep1196 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 4539 500 0 1 0 1 0 1 0

noncomputable def ep1199 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4539 500 0 1 ep1195

noncomputable def ep1200 := @ep1198 1 0 1 ep1199 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1201 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 4539 14000 0

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1203 := @ep1202 1 0 1 ep1196 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1204 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz107)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 4539 500 0 1 1 28 0 1 4539

noncomputable def ep1205 := @ep1204 14000 0 1 ep1199 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 28 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1206 := @ep1178 1 (@ep1179 0 1 0 1 (BSN.bern_sum_base qz148 28) qz121) (ep1180 (@ep1181 1 1 1 672 0 1 (ep1197 rfl) (ep1200 rfl) rfl rfl) (@ep1201 1 4539 4539 14000 0 1 (ep1203 rfl) (ep1205 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1207 := ep1172 (ep1175 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1176 Bool.false 4539 14000 0 1 (BSN.bern_sum_succ qz148 28 0 1 1 rfl rfl) (ep1206 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1208 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 205670801581 1099511627776 11512677011579 74627152712040448 697673263359

noncomputable def ep1209 := @ep1208 10383889334000 0 1 20498717045239663795797 ep1154 ep1155 ep1156 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (ep1159 ep1168))

noncomputable def ep1210 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 249367050397 498426688032 0 1 Bool.false

noncomputable def ep1211 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 1474705536938905657977 815514790305156038656000 799001113282463508514779

noncomputable def ep1212 := nat_lit 77492009507334598136378163200

noncomputable def ep1213 := nat_lit 2870882308550803845546863

noncomputable def ep1214 := nat_lit 37196164563520607105461518336

noncomputable def ep1215 := nat_lit 6090558419570415982073311870702156359298711552

noncomputable def ep1216 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 14796236721 549755813888 5726184126905 37313576356020224 697673263359

noncomputable def ep1217 := @ep1216 10383889334000 0 1 1474705536938905657977 815514790305156038656000 799001113282463508514779 ep1212 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (ep1159 ep1168))

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz130 qz210 (@HSub.hSub Nat Nat Nat qz129 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 205670801581 1099511627776 11512677011579 74627152712040448 249367050397

noncomputable def ep1219 := @ep1218 498426688032 0 1 7326788734720087753951 78289419869294979710976 ep1213 ep1214 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.false 14796236721 549755813888 5726184126905 37313576356020224 Bool.false 205670801581 1099511627776 11512677011579 74627152712040448 (ep1159 ep1168))

noncomputable abbrev qz499 := (ep1207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1220 := @ep1150 933545058283277837139599 ep1096 ep1102 ep1098 (@ep1152 ep1153 20498717045239663795797 ep1154 ep1155 ep1156 ep1157 45742084168765905979 50969674394072252416000 29652585852100695931969 ep1101 (ep1169 (@ep1170 697673263359 10383889334000 0 1 qz499) rfl) (ep1209 (@ep1210 697673263359 10383889334000 0 1 qz499) rfl) rfl rfl) (@ep1211 ep1212 7326788734720087753951 78289419869294979710976 ep1213 ep1214 ep1215 933545058283277837139599 ep1096 ep1102 ep1098 (ep1217 (@ep1210 697673263359 10383889334000 0 1 qz499) rfl) (ep1219 (@ep1170 697673263359 10383889334000 0 1 qz499) rfl) rfl rfl)

noncomputable def ep1221 := @ep1105 ep1097 ep1098 (@ep1106 18656788178010112 (BSN.head_sum_c_eq qz148 28) (ep1107 (BSN.head_sum_c_succ qz148 27 28 rfl rfl) (ep1149 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1220 rfl rfl rfl

noncomputable def ep1222 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz148 1 28) Bool.false 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 Bool.true 21816926555709970604401 ep1096 ep1097 ep1098 (@ep1099 ep977 Bool.true 21816926555709970604401 ep1096 ep1097 ep1098 (BSN.zetaApproximant_eq_folded' qz148 1 28 rfl) (ep1221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1223 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) (Complex.im (zetaApproximant qz148 1 28)) 317 524288 23533235

noncomputable def ep1224 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180)) Bool.true 634 1048576 47066470

noncomputable def ep1225 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) qz475 Bool.false 52706861 524288 339

noncomputable def ep1226 := nat_lit 4635817635833715410787716353996006353823161551121898182873042424251217008984001

noncomputable def ep1227 := nat_lit 13874026624814976953764987650935044097628254224929379295954224123460423031783361

noncomputable def ep1228 := BSN.cos_dyadic_bound_f 3371958809 2147483648 3 2 1048576 271758 ep1226 ep70 ep1092 ep1227 ep73 ep1092 634 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3371958809) qz291 0 2 ep1226 ep70 ep1092 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3371958809) qz292 0 2 ep1227 ep73 ep1092 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1229 := @ep1225 1048576 Bool.true 634 1048576 1 135746 (@ep982 52706861 524288 339 1048576 ep1090 rfl) (Enclosure.sfrac_false_div 52706861 524288) (BSN.sin_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118640253431451612086272) qz301) 226375608064910080 72057594037927936 Bool.false 634 1048576 15 1000000000000000 271492 135746 (BSN.sin_reduce_arg_pos_rat_q3 52706861 524288 226375608064910080 72057594037927936 15 118640253431451612086272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 634 1048576 118640253431451612086272 75557863725914323419136 3371958809 2147483648 271758 271492 (ep1228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1230 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz148 1 28) Bool.false 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 Bool.true 21816926555709970604401 ep1096 ep1097 ep1098 (@ep1099 ep977 Bool.true 21816926555709970604401 ep1096 ep1097 ep1098 (BSN.zetaApproximant_eq_folded' qz148 1 28 rfl) (ep1221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow33.d16 : Enclosure.Real.IsNear (hardyZApproximantEM 1 28 qz151) Bool.false ep961 ep962 ep963 ep964 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 28 qz151) ep965 Bool.false ep961 ep962 ep963 ep964 (@Eq.refl Real ep965) (@ep966 Bool.false ep961 ep962 ep963 ep964 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz178 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz179 (@Nat.cast Complex Complex.instNatCast j))))) qz180) (zetaApproximant qz148 1 28)) (@ep968 ep969 ep970 ep971 ep972 ep962 ep973 ep974 ep975 ep961 ep962 ep963 ep964 (@ep976 71169998848 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 ep967 ep969 ep970 ep971 (@ep978 142339997696 1048575 1048576 23533235 71169998848 (ep1095 rfl rfl) rfl) ep1222 rfl) (@ep1223 71169998848 21816926555709970604401 ep1096 ep1097 ep1098 ep972 ep962 ep973 ep974 (@ep1224 142339997696 317 524288 23533235 71169998848 (ep1229 rfl rfl) rfl) ep1230 rfl) rfl rfl))

theorem EMRow33.d17 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow33.d18 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow33.d19 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow33.d20 : @Eq Nat (Nat.pow 27 (Nat.succ (Nat.mul 2 3))) 10460353203 := @Eq.refl Nat 10460353203

noncomputable abbrev qz596 := (@HAdd.hAdd Complex Complex Complex qz601 qz600 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz500 := qz596

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz500) (@HAdd.hAdd Real Real Real qz419 (Complex.re qz272) qz295))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz501 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 27) (@HSub.hSub Complex Complex Complex qz573 qz540 qz541))

noncomputable abbrev qz225 := qz501

noncomputable def ep1231 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 9051218531 618475290624 20350883 206158430208 508294228753738617 1008806316530991104 100498242487

noncomputable def ep1232 := nat_lit 323498347277345586791927775232

noncomputable def ep1233 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27)) 26561 1769472 1 1769472 1022313 1048576 6857 1048576 9051218531 618475290624

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz268 (2 : Real) Real.pi)

noncomputable abbrev qz597 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz502 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz597 qz226 2))

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz502 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1235 := nat_lit 781950621441006189802102638025

noncomputable def ep1236 := nat_lit 19807040628566084398385987584

noncomputable def ep1237 := nat_lit 26986075409044041160201671

noncomputable def ep1238 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz503 := (@HPow.hPow Real Nat Real qz597 qz226 1)

noncomputable def ep1239 := @Enclosure.Real.IsNear.mulLit_ff qz503 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1235 ep1236 ep1237 ep1238

noncomputable def ep1240 := ep1239 (@Enclosure.Real.IsNear.of_eq qz503 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz504 := (@HPow.hPow Real Nat Real qz597 qz226 2)

noncomputable def ep1241 := @Enclosure.Real.IsNear.inv_image qz504 ep1235 ep1236 ep1237 ep1238 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz504 (@HMul.hMul Real Real Real qz0 qz503 qz226) Bool.false ep1235 ep1236 ep1237 ep1238 (BSN.pow_succ_r qz226 1 2 rfl) ep1240) rfl rfl rfl

noncomputable def ep1242 := ep1234 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz502 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1241 rfl rfl rfl) rfl)

noncomputable def ep1243 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))))) Bool.false 1022313 1048576 6857 1048576

noncomputable def ep1244 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))))) Bool.false 1022313 1048576 6857 1048576

noncomputable def ep1245 := nat_lit 1651596438758413818832336127482766721761261

noncomputable def ep1246 := nat_lit 1737466119469605208519895820709920768000000

noncomputable def ep1247 := nat_lit 1259185877152726940606499450354624885209050976096796275013493

noncomputable def ep1248 := nat_lit 98769428142430935257790406012379626896069418517086076928000000

noncomputable def ep1249 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27)))) ep1245 ep1246 ep1247 ep1248 507728 514585

noncomputable def ep1250 := nat_lit 10042280622742996090473261232900440045488651406769

noncomputable def ep1251 := nat_lit 10572081381924435343333482614112472786796544000000

noncomputable def ep1252 := nat_lit 916776859669708175500365275966615038477746293829854083380163

noncomputable def ep1253 := nat_lit 74077071106823201443342804509284720172052063887814557696000000

noncomputable def ep1254 := nat_lit 262926675982280921057484132470586743607148446409

noncomputable def ep1255 := nat_lit 380594929749279672360005374108049020324675584000000

noncomputable def ep1256 := nat_lit 110450192779348119818037247197414501716167752970972491519827

noncomputable def ep1257 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))) ep1250 ep1251 ep1252 ep1253 ep1254 ep1255 ep1256

noncomputable def ep1258 := nat_lit 296308284427292805773371218037138880688208255551258230784000000

noncomputable def ep1259 := nat_lit 3824820770351386667780457848817888574147844906578157470898962547159018894810535281622717038592000000

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27)) ep402 ep403 ep404 ep405 ep402 ep403 ep404 ep405 ep1250

noncomputable def ep1261 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27)) 512763762352880121170653 ep541 ep542 ep543 512763762352880121170653 ep541 ep542 ep543 ep1254

noncomputable def ep1262 := @ep1231 1008806316530991104 ep1232 4707520526096713537 9079256848778919936 299053759623973 3026418949592973312 (@ep1233 20350883 206158430208 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz502) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow33.d17 EMRow33.d18 rfl) (ep1242 rfl)) (ep1243 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 27)) (@ep1244 1022313 1048576 6857 1048576 (@ep1249 524288 (@ep1257 ep1258 ep1259 ep1245 ep1246 ep1247 ep1248 (@ep1260 ep1251 ep1252 ep1253 ep658 ep658 rfl) (@ep1261 ep1255 ep1256 ep1258 ep666 ep666 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz500)

noncomputable abbrev qz598 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1263 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz598) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 508294228753738617 1008806316530991104 100498242487 1008806316530991104 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz13 3)

noncomputable def ep1264 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz598) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 111970483 3670016 1 3670016 4539537699 274877906944 857 274877906944

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz598 111970483 1048576 1 1048576 2 7 0 1 111970483 3670016

noncomputable abbrev qz505 := (Complex.re qz596)

noncomputable abbrev qz506 := (Complex.im qz596)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz268 qz505 qz505) (@HMul.hMul Real Real Real qz268 qz506 qz506))

noncomputable abbrev qz229 := qz500

noncomputable def ep1266 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 111970483 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1267 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 111970483 1048576 1 1048576 111970483

noncomputable def ep1268 := @Enclosure.Real.IsNear.sqrt_image qz228 2850672269 250000 0 1 55985241 55985242 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz505 qz505)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz506 qz506)

noncomputable def ep1269 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 2847609769 250000 0 1

noncomputable abbrev qz232 := qz505

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz507 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz507 qz13) Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 106726 1000 3 qz14)

noncomputable abbrev qz508 := (ep1271 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1272 := @ep1270 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz508)

noncomputable def ep1273 := ep1272 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz508)

noncomputable abbrev qz233 := qz506

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 106726 1000 0 1 106726 1000 0 1 2847609769 250000

noncomputable def ep1275 := @ep1274 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz508)

noncomputable def ep1276 := ep1275 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz508)

noncomputable def ep1277 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 4539537699 274877906944

noncomputable def ep1278 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 9079075398 549755813888

noncomputable def ep1279 := nat_lit 322870159911115195280022433432328047844698757439280039497542713

noncomputable def ep1280 := nat_lit 1183816326238031363744984714500189245921305359810560000000000000000

noncomputable def ep1281 := nat_lit 11009655031606835237797428000576210212784678582621767101498114518711823777225763

noncomputable def ep1282 := nat_lit 106961143523147100465103706210213753588203860185363975067267663239577600000000000000000000

noncomputable def ep1283 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1279 ep1280 ep1281 ep1282

noncomputable def ep1284 := nat_lit 1042481063200450820029803794352084008922911754065417628609

noncomputable def ep1285 := nat_lit 913438523331814323877303020447676887284957839360000000000000000

noncomputable def ep1286 := nat_lit 6883820256889451696246956378868800446113406205766737480152381833900832908839

noncomputable def ep1287 := nat_lit 6685071470196693779068981638138359599262741261585248441704228952473600000000000000000000

noncomputable def ep1288 := nat_lit 321519104453207411017263807714847746969134663806011258250865449

noncomputable def ep1289 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1284 ep1285 ep1286 ep1287 ep1288

noncomputable def ep1290 := nat_lit 10899513907496604010657476698514309405646864083329499301815676409369410450684339

noncomputable def ep1291 := nat_lit 294922042097115819070503658200590792222153520886148522789740717122258568226328846047364192354569662525792583680000000000000000

noncomputable def ep1292 := nat_lit 32287475330233716185231215647

noncomputable def ep1293 := nat_lit 30223145490365729367654400000000

noncomputable def ep1294 := nat_lit 39405058395634530216377264701493083

noncomputable def ep1295 := nat_lit 81762286356221067817107831851581440000000000

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1292 ep1293 ep1294 ep1295 ep1292 ep1293 ep1294

noncomputable def ep1297 := nat_lit 17930953807681492407789776417357

noncomputable def ep1298 := nat_lit 1088033237653166257235558400000000

noncomputable def ep1299 := nat_lit 1011120337036258591352088749181105667

noncomputable def ep1300 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1292 ep1293 ep1294 ep1295 Bool.false ep1297 ep1298 ep1299

noncomputable def ep1301 := nat_lit 327049145424884271268431327406325760000000000

noncomputable def ep1302 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1292 ep1293 ep1294 ep1295 Bool.false ep1297 ep1298 ep1299 ep1301

noncomputable def ep1303 := nat_lit 1003983274036012003205200817

noncomputable def ep1304 := nat_lit 1450710983537555009647411200000

noncomputable def ep1305 := nat_lit 56597267671388499386403432385927

noncomputable def ep1306 := nat_lit 436065527233179028357908436541767680000000

noncomputable def ep1307 := nat_lit 319222761235903797512037396007

noncomputable def ep1308 := nat_lit 181338872942194376205926400000000

noncomputable def ep1309 := nat_lit 57586141414498373162853242258263541

noncomputable abbrev qz234 := (Complex.re qz501)

noncomputable abbrev qz235 := (Complex.im qz501)

noncomputable def ep1310 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1303 ep1304 ep1305 ep1306 ep1307 ep1308 ep1309

noncomputable def ep1311 := nat_lit 163524572712442135634215663703162880000000000

noncomputable def ep1312 := nat_lit 281038770553607388836724740148700615626863936534898278400000

noncomputable def ep1313 := nat_lit 3633879393609825236315903637848064

noncomputable def ep1314 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 8542516807 120000000 0 1 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 ep1303

noncomputable def ep1315 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 8542516807 120000000 0 1 0 1 0 1 8542516807

noncomputable def ep1316 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 25627550421 500000 0 1 8542516807 120000000 0

noncomputable def ep1317 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow33.d19 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz20)

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 qz542)

noncomputable abbrev qz236 := qz509

noncomputable def ep1318 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1

noncomputable abbrev qz237 := (Complex.re qz509)

noncomputable abbrev qz238 := (Complex.im qz509)

noncomputable def ep1319 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 2847422269 100000 0 1 2847609769 125000 0 1

noncomputable def ep1320 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 2847422269 250000 0 1 5 2 0 1 2847422269 100000

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz510

noncomputable def ep1321 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1

noncomputable abbrev qz240 := (Complex.re qz510)

noncomputable abbrev qz241 := (Complex.im qz510)

noncomputable def ep1322 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 2847609769 250000 0 1

noncomputable def ep1323 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1324 := @ep1323 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable abbrev qz511 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1325 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz511 qz13) Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 106726 1000 1 qz14)

noncomputable abbrev qz512 := (ep1325 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1326 := ep1324 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz512)

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 106726 1000 0 1 106726 1000 0 1 2847609769 250000

noncomputable def ep1328 := @ep1327 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep1329 := ep1328 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz512)

noncomputable def ep1330 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 (@ep1322 11389689076 2847422269 250000 0 1 (ep1326 rfl) (ep1329 rfl) rfl rfl)

noncomputable def ep1331 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 53363 1000 0 1 160089 1000 0 1

noncomputable def ep1332 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 106726 1000 0 1 53363 1000

noncomputable def ep1333 := @ep1332 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep1334 := ep1333 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz512)

noncomputable def ep1335 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 106726 1000 0 1 3 2 0 1 160089 1000

noncomputable def ep1336 := @ep1335 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep622)

noncomputable def ep1337 := ep1336 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz512)

noncomputable abbrev qz242 := (ep1321 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1330 (@ep1331 213452000 53363 250 0 1 (ep1334 rfl) (ep1337 rfl) rfl rfl)))

noncomputable def ep1338 := @ep1320 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz242)

noncomputable abbrev qz513 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1339 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz513 qz13) Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 106726 1000 2 qz14)

noncomputable abbrev qz514 := (ep1339 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1340 := ep1338 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz514)

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 53363 250 0 1 106726 1000 0 1 2847609769 125000

noncomputable def ep1342 := @ep1341 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz242)

noncomputable def ep1343 := ep1342 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz514)

noncomputable def ep1344 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 (@ep1319 640688760525000 25627550421 500000 0 1 (ep1340 rfl) (ep1343 rfl) rfl rfl)

noncomputable def ep1345 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 151946994540647 125000000 0 1 53363 100 0 1

noncomputable def ep1346 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 2847422269 250000 0 1 106726 1000 0 1 151946994540647 125000000

noncomputable def ep1347 := @ep1346 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz242)

noncomputable def ep1348 := ep1347 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz514)

noncomputable def ep1349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 53363 250 0 1 5 2 0 1 53363 100

noncomputable def ep1350 := @ep1349 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz242)

noncomputable def ep1351 := ep1350 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz514)

noncomputable abbrev qz243 := (ep1318 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1344 (@ep1345 15188029079064700 151880290790647 125000000 0 1 (ep1348 rfl) (ep1351 rfl) rfl rfl)))

noncomputable def ep1352 := @ep1316 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz243)

noncomputable def ep1353 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 151880290790647 125000000 0 1 0 1 0

noncomputable def ep1354 := @ep1353 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz243)

noncomputable def ep1355 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 151880290790647 90000000000 0 1 0 1 0 1 151880290790647

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 151880290790647 125000000 0 1 151880290790647 90000000000 0

noncomputable def ep1357 := @ep1356 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz243)

noncomputable def ep1358 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 25627550421 500000 0 1 0 1 0

noncomputable def ep1359 := @ep1358 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz243)

noncomputable def ep1360 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 (@ep1315 8542516807 120000000 0 1 (ep1352 rfl) (ep1354 rfl) rfl rfl) (@ep1355 151880290790647 90000000000 0 1 (ep1357 rfl) (ep1359 rfl) rfl rfl)

noncomputable def ep1361 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 ep1360

noncomputable def ep1362 := nat_lit 1816939696804912618157951818924032

noncomputable def ep1363 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 Bool.false 157635378284166075 151115727451828646838272 379154800894314642803 ep1362

noncomputable abbrev qz515 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10460353203)))

noncomputable def ep1364 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz515 qz139) (@HMul.hMul Real Real Real qz0 qz515 qz583)) Bool.false 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 Bool.false 157635378284166075 151115727451828646838272 379154800894314642803

noncomputable abbrev qz516 := (Real.sqrt (@Nat.cast Real Real.instNatCast 10460353203))

noncomputable abbrev qz517 := (@Nat.cast Real Real.instNatCast 10460353203)

noncomputable def ep1365 := @Enclosure.Real.IsNear.inv_image qz516 56226753128282463 549755813888 1 549755813888 2687612 2687613 274877906944 (@Enclosure.Real.IsNear.of_eq qz516 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz517 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 10460353203) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz517 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_enclosure 10460353203 1 28113376564141231 28113376564141232 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1366 := nat_lit 4508811874125000000000000000

noncomputable def ep1367 := nat_lit 9017623748250000000000000

noncomputable def ep1368 := nat_lit 32640387355024858926381268992

noncomputable def ep1369 := nat_lit 9903520314283042199192993792

noncomputable def ep1370 := nat_lit 72140989986000000000000000

noncomputable def ep1371 := nat_lit 165384128016192829869617185803053619675

noncomputable def ep1372 := nat_lit 3756250787496183507247588531701759465

noncomputable def ep1373 := nat_lit 191591553670487038802158425

noncomputable def ep1374 := BSN.log_dyadic_bound 11 43 10 9 ep1371 274877906944 72140989986 ep1372 ep1373 143829354570 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 11) (BSN.artanhQ 43) 0 9 ep1372 ep1371 ep1373 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1375 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz141 106726 1000 0 1 3710782420401399 1125899906842624 125036070494993 ep1367 198018482299879854837 562949953421312000 6672299829824311459 ep1366 qz18 (BSN.isNear_log_sfrac 27 1 3710782420401399 1125899906842624 125036070494993 ep1367 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz442) Bool.false ep1368 ep1369 1000288563959944 ep1370 3710782420401399 1125899906842624 125036070494993 ep1367 (BSN.log_rat_reduce_isNear 27 1 4 54 32 143829354570 274877906944 24973259072661432 36028797018963968 72140989986 1000000000000000 rfl rfl rfl rfl (ep1374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1376 := nat_lit 7248903906577449621307523072

noncomputable def ep1377 := nat_lit 4951760157141521099596496896

noncomputable def ep1378 := nat_lit 90906304083996292465524778785500796001788077013540563944279595817088868114933433375458673879454257378086952923322261842151706296640771130526696964091454789343083351467637988744702590396710497465705966001304603176989745382300806410736520567781299018858496

noncomputable def ep1379 := nat_lit 2371728904138043385318735560374504222700605579872037175997883585289299297944925459400262945270439995320386160994569494400873352117161187529222914467416668525224467727137180455887633346091077280717708110065332645507572399051088361938793378954328561156096000

noncomputable def ep1380 := nat_lit 2966199767040626144858737880697456790582920901167916249831692592617358012406168300955635062951099429898806811888813480781521238658078347998878712994482379961708143663844051601954044211328117782608120873589973862485042641955339950104374505701376

noncomputable def ep1381 := nat_lit 739542907029212010943066515758393944199152872690190730431978673190200681277369721849631210587909141417838186434784696084102508785571747644104286309633770769088771096550759565685175039361912431016653530978009940011261001973630617349684506039037214698045440

noncomputable def ep1382 := nat_lit 135188547535868472963167926941346740693934518052706119031879364361490059982860751185814987880415079733262011176690461180849781070678187689165706124642750105937794660446819285985595100727191405000909362273723960793931626745912036630511222600396727985897472000

noncomputable def ep1383 := BSN.sin_dyadic_bound_f 1648209924173318 1125899906842624 5 4 549755813888 144422880344 ep1378 ep1379 ep1380 ep1381 ep1382 ep1380 546618085159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 1648209924173318) (BSN.sinEvenQ 1125899906842624) 0 4 ep1378 ep1379 ep1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 1648209924173318) (BSN.sinOddQ 1125899906842624) 0 4 ep1381 ep1382 ep1380 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz518 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12086089007561) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1384 := @Enclosure.Real.IsNear.cos_image qz142 qz518 Bool.false 12086089007561 34359738368 407 274877906944 Bool.false 546618085159 549755813888 1 72140989986 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 198018482299879854837 562949953421312000 6672299829824311459 ep1366 12086089007561 34359738368 407 274877906944 (ep1375 rfl) rfl) (Enclosure.sfrac_false_div 12086089007561 34359738368) (BSN.cos_reduce3 qz518 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1376) (@Nat.cast Real Real.instNatCast ep1377)) 226375608064910080 72057594037927936 Bool.false 546618085159 549755813888 55 1000000000000000 144281979972 72140989986 (BSN.sin_reduce_arg_pos_rat_q3 12086089007561 34359738368 226375608064910080 72057594037927936 55 ep1376 ep1377 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 546618085159 549755813888 ep1376 ep1377 1648209924173318 1125899906842624 144422880344 144281979972 (ep1383 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1385 := nat_lit 26769600706433326612816658999530762011475463435247404023618877946537175005597851424755614620765068319306841755195330886812536197431603790873709357979885548598268361012185043590027847460273673943077869721815927997595452306305363010964935284062146705555456

noncomputable def ep1386 := nat_lit 139513464949296669724631503551441424864741504698355127999875505017017605761466203494133114427672940901199185940857029082404314830421246325248406733377451089719086336890422379758096079181828075336335771180313685029857199944181668349340786997313444773888000

noncomputable def ep1387 := nat_lit 272553430077606932851988905773857489981593436442966067560563466011158196860083243519091874261432680984544442195795859401412217740287792822664881774025371131695424358488645805617630736610589436005759950228716862547428543885761823331963746416011172894539776

noncomputable def ep1388 := nat_lit 21345560137242390467868620043370538004305450218848334583980952267603693681504329134602366507433959957883475448951125449607860169054450687763006230206750016727020209544234624102988700114819695526459372990587993809568151591459795257449140410588957050404864000

noncomputable def ep1389 := BSN.cos_dyadic_bound_f 1648209924173318 1125899906842624 5 4 549755813888 144422880344 ep1385 ep1386 ep1380 ep1387 ep1388 ep1380 58652569254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 1648209924173318) (BSN.cosEvenQ 1125899906842624) 0 4 ep1385 ep1386 ep1380 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 1648209924173318) (BSN.cosOddQ 1125899906842624) 0 4 ep1387 ep1388 ep1380 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1390 := @Enclosure.Real.IsNear.sin_image qz142 qz518 Bool.false 12086089007561 34359738368 407 274877906944 Bool.true 58652569254 549755813888 1 72140989986 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 198018482299879854837 562949953421312000 6672299829824311459 ep1366 12086089007561 34359738368 407 274877906944 (ep1375 rfl) rfl) (Enclosure.sfrac_false_div 12086089007561 34359738368) (BSN.sin_reduce3 qz518 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1376) (@Nat.cast Real Real.instNatCast ep1377)) 226375608064910080 72057594037927936 Bool.false 58652569254 549755813888 55 1000000000000000 144281979972 72140989986 (BSN.sin_reduce_arg_pos_rat_q3 12086089007561 34359738368 226375608064910080 72057594037927936 55 ep1376 ep1377 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 58652569254 549755813888 ep1376 ep1377 1648209924173318 1125899906842624 144422880344 144281979972 (ep1389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1391 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz515 qz139) (@HMul.hMul Real Real Real qz0 qz515 qz583) Bool.false 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 Bool.false 157635378284166075 151115727451828646838272 379154800894314642803 ep1362 (@Enclosure.Real.IsNear.mulLit_ff qz515 qz139 5375225 549755813888 1 549755813888 546618085159 549755813888 14818130415623 9914982166109871931392 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 (@Enclosure.Real.IsNear.recentre' qz515 Bool.false 5375225 549755813888 1 549755813888 5375225 549755813888 1 549755813888 (ep1365 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 546618085159 549755813888 29636260831246 19829964332219743862784 546618085159 549755813888 14818130415623 9914982166109871931392 (ep1384 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz515 qz583 5375225 549755813888 1 549755813888 29326284627 274877906944 14818130415623 9914982166109871931392 157635378284166075 151115727451828646838272 379154800894314642803 ep1362 (@Enclosure.Real.IsNear.recentre' qz515 Bool.false 5375225 549755813888 1 549755813888 5375225 549755813888 1 549755813888 (ep1365 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz140 Bool.true 29326284627 274877906944 14818130415623 9914982166109871931392 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 58652569254 549755813888 29636260831246 19829964332219743862784 29326284627 274877906944 14818130415623 9914982166109871931392 (ep1390 rfl rfl) rfl)) rfl)

noncomputable def ep1392 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 151880290790647 90000000000 0 1 157635378284166075 151115727451828646838272 379154800894314642803 ep1362 ep1307

noncomputable def ep1393 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 ep1360

noncomputable def ep1394 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 Bool.false 157635378284166075 151115727451828646838272 379154800894314642803 ep1362

noncomputable def ep1395 := nat_lit 17954704911603886902222967

noncomputable def ep1396 := nat_lit 241785163922925834941235200000

noncomputable def ep1397 := nat_lit 3238936259094421466890829090021

noncomputable def ep1398 := nat_lit 218032763616589514178954218270883840000000

noncomputable def ep1399 := nat_lit 17850157635579274916729773065857

noncomputable def ep1400 := nat_lit 1006261932647616959151752505546074167

noncomputable def ep1401 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1395 ep1396 ep1397 ep1398 ep1399 ep1298 ep1400

noncomputable def ep1402 := nat_lit 4335438605684680808147875440992116813598233064884299366400000

noncomputable def ep1403 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 8542516807 120000000 0 1 157635378284166075 151115727451828646838272 379154800894314642803 ep1362 ep1395

noncomputable def ep1404 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 151880290790647 90000000000 0 1 2938195196798785775 302231454903657293676544 6625362167857950740161 ep1313 ep1399

noncomputable abbrev qz519 := (@ep1364 ep1362 (BSN.cpow_neg_s_sub_mk qz13 106726 1000 27 3 10460353203 qz14 rfl EMRow33.d20) ep1391)

noncomputable def ep1405 := ep1302 (@ep1310 ep1311 ep1312 ep1292 ep1293 ep1294 ep1295 (@ep1314 ep1304 ep1305 ep1306 ep1361 (ep1363 qz519) rfl) (@ep1392 ep1308 ep1309 ep1311 ep1393 (ep1394 qz519) rfl) rfl rfl) (@ep1401 ep1301 ep1402 ep1297 ep1298 ep1299 ep1301 (@ep1403 ep1396 ep1397 ep1398 ep1361 (ep1394 qz519) rfl) (@ep1404 ep1298 ep1400 ep1301 ep1393 (ep1363 qz519) rfl) rfl rfl)

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1297 ep1298 ep1299 ep1301 ep1297 ep1298 ep1299

noncomputable def ep1407 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1292 ep1293 ep1294 ep1295 Bool.false ep1297 ep1298 ep1299

noncomputable def ep1408 := @ep1264 508294228753738617 1008806316530991104 100498242487 1008806316530991104 (@ep1265 1 3670016 (ep1266 (@ep1267 1048576 1 1048576 (ep1268 (@ep1269 11402689076 2850672269 250000 0 1 (ep1273 rfl) (ep1276 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1277 857 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1278 1714 549755813888 4539537699 274877906944 857 274877906944 (@ep1283 4539536842 4539538556 274877906944 (@ep1289 ep1280 ep1290 ep1282 ep1291 ep1279 ep1280 ep1281 ep1282 (@ep1296 ep1295 ep1284 ep1285 ep1286 ep1287 (@ep1300 ep1301 ep1405) (@ep1300 ep1301 ep1405) rfl) (@ep1406 ep1301 ep1288 ep1280 ep1290 ep1282 (@ep1407 ep1301 ep1405) (@ep1407 ep1301 ep1405) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow33.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 4707520526096713537 9079256848778919936 299053759623973 3026418949592973312 := ep1262 (ep1263 ep1408) rfl rfl

theorem EMRow33.d22 : @Eq Nat (Nat.pow 28 (Nat.succ (Nat.mul 2 3))) 13492928512 := @Eq.refl Nat 13492928512

noncomputable abbrev qz599 := (@HAdd.hAdd Complex Complex Complex qz601 qz607 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz520 := qz599

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz520) (@HAdd.hAdd Real Real Real qz419 (Complex.re qz446) qz295))

noncomputable abbrev qz521 := (@HPow.hPow Complex Complex Complex qz539 (@Nat.cast Complex Complex.instNatCast 28) (@HSub.hSub Complex Complex Complex qz573 qz585 qz541))

noncomputable abbrev qz245 := qz521

noncomputable def ep1409 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 145115784451 1855425871872 190095953 1855425871872 69394646983781205 144115188075855872 108936930643

noncomputable def ep1410 := nat_lit 149670011952063123488906412032

noncomputable def ep1411 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28)) 26561 1769472 1 1769472 5463491 1048576 6951 1048576 145115784451 1855425871872

noncomputable def ep1412 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 28)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 28)) (Complex.im (zetaApproximant qz148 1 28))))) Bool.false 5463491 1048576 6951 1048576

noncomputable def ep1413 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 28)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 28)) (Complex.im (zetaApproximant qz148 1 28))))) Bool.false 5463491 1048576 6951 1048576

noncomputable def ep1414 := nat_lit 140215347508194526518274061001032587670893

noncomputable def ep1415 := nat_lit 5164807648687634418211206946420162560000

noncomputable def ep1416 := nat_lit 1493107804137081634877992534912836807451077884159846502426547

noncomputable def ep1417 := nat_lit 21618041534945408689126538999025826168919246152101003264000000

noncomputable def ep1418 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 28)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 28)) (Complex.im (zetaApproximant qz148 1 28)))) ep1414 ep1415 ep1416 ep1417 2728270 2735221

noncomputable def ep1419 := nat_lit 282114254887773862353951661613065988540316884889

noncomputable def ep1420 := nat_lit 10391630831350978525885619568878471348224000000

noncomputable def ep1421 := nat_lit 15228419741438789583351634685765722249945993253200121

noncomputable def ep1422 := nat_lit 220719394932148353054691532925269303781419384832000000

noncomputable def ep1423 := nat_lit 475978284337242921090355211796223521240568801

noncomputable def ep1424 := nat_lit 95769269741730618094561869946783991945232384000000

noncomputable def ep1425 := nat_lit 105485554242999500262224585502542029729033118226085657117

noncomputable def ep1426 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz148 1 28)) (Complex.re (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz148 1 28)) (Complex.im (zetaApproximant qz148 1 28))) ep1419 ep1420 ep1421 ep1422 ep1423 ep1424 ep1425

noncomputable def ep1427 := nat_lit 1441202768996360579275102599935055077927949743473400217600000

noncomputable def ep1428 := nat_lit 27017881120525175058575945872180895006913594427028996277460478071406268189936564877184204800000000

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz148 1 28)) (Complex.re (zetaApproximant qz148 1 28)) 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 531144288200272245339333 101939348788144504832000 140717579643505396160959 ep977 ep1419

noncomputable def ep1430 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz148 1 28)) (Complex.im (zetaApproximant qz148 1 28)) 21816926555709970604401 ep1096 ep1097 ep1098 21816926555709970604401 ep1096 ep1097 ep1098 ep1423

noncomputable def ep1431 := @ep1409 1008806316530991104 ep1410 2177985326155076087 3891110078048108544 2793562053308353 27237770546336759808 (@ep1411 190095953 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz502) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow33.d17 EMRow33.d18 rfl) (ep1242 rfl)) (ep1412 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz148 1 28)) (@ep1413 5463491 1048576 6951 1048576 (@ep1418 524288 (@ep1426 ep1427 ep1428 ep1414 ep1415 ep1416 ep1417 (@ep1429 ep1420 ep1421 ep1422 ep1222 ep1222 rfl) (@ep1430 ep1424 ep1425 ep1427 ep1230 ep1230 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz520)

noncomputable def ep1432 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz598) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 69394646983781205 144115188075855872 108936930643 1008806316530991104 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz151 3)

noncomputable def ep1433 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz598) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 114286617 3670016 1 3670016 4250388555 274877906944 229 68719476736

noncomputable def ep1434 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz598 114286617 1048576 1 1048576 2 7 0 1 114286617 3670016

noncomputable abbrev qz522 := (Complex.re qz599)

noncomputable abbrev qz523 := (Complex.im qz599)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz268 qz522 qz522) (@HMul.hMul Real Real Real qz268 qz523 qz523))

noncomputable abbrev qz248 := qz520

noncomputable def ep1435 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 114286617 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1436 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 114286617 1048576 1 1048576 114286617

noncomputable def ep1437 := @Enclosure.Real.IsNear.sqrt_image qz247 742456381 62500 0 1 57143308 57143309 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz522 qz522)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz523 qz523)

noncomputable def ep1438 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 185422689 15625 0 1

noncomputable abbrev qz251 := qz522

noncomputable def ep1439 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1440 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz507 qz151) Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 108936 1000 3 qz152)

noncomputable abbrev qz524 := (ep1440 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz151 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz153))

noncomputable def ep1441 := @ep1439 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz524)

noncomputable def ep1442 := ep1441 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz524)

noncomputable abbrev qz252 := qz523

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 108936 1000 0 1 108936 1000 0 1 185422689 15625

noncomputable def ep1444 := @ep1443 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz524)

noncomputable def ep1445 := ep1444 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 108936 1000 0 1 qz524)

noncomputable def ep1446 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 4250388555 274877906944

noncomputable def ep1447 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 8500777110 549755813888

noncomputable def ep1448 := nat_lit 1365013471211967286820815868521982704527441186707205954483597

noncomputable def ep1449 := nat_lit 5708990770823839524233143877797980545530986496000000000000000000

noncomputable def ep1450 := nat_lit 390309901979003222957719727803584166925958576990723094565846313672166083

noncomputable def ep1451 := nat_lit 3790336439767552488960143625355242840262726734070378460191129600000000000000000000

noncomputable def ep1452 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1448 ep1449 ep1450 ep1451

noncomputable def ep1453 := nat_lit 1319130620157466689313583361133395649081077687691249341776841

noncomputable def ep1454 := nat_lit 376980502709211335183715743953446390896654045397396499090739057349606339

noncomputable def ep1455 := nat_lit 11470712763625149376808126847146763861590874753989153176689

noncomputable def ep1456 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1453 ep1449 ep1454 ep1451 ep1455

noncomputable def ep1457 := nat_lit 1427247692705959881058285969449495136382746624000000000000000000

noncomputable def ep1458 := nat_lit 52067965897624561617203061914600687614470826536432013574637720009999

noncomputable def ep1459 := nat_lit 14806001717842001910000561036543917344776276304962415860121600000000000000000000

noncomputable def ep1460 := nat_lit 1948212327299833500674269950966101339280760740871206983323665065599221714806827908011843998835486415126528000000000000000000

noncomputable def ep1461 := nat_lit 1148534117977113768819299272029

noncomputable def ep1462 := nat_lit 75557863725914323419136000000000

noncomputable def ep1463 := nat_lit 201412182825641666022220301409657

noncomputable def ep1464 := nat_lit 61565708310451139395491347824640000000000

noncomputable def ep1465 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1461 ep1462 ep1463 ep1464 ep1461 ep1462 ep1463

noncomputable def ep1466 := nat_lit 107101413452975257066036763367

noncomputable def ep1467 := nat_lit 37778931862957161709568000000000

noncomputable def ep1468 := nat_lit 596645201143418716952571559893

noncomputable def ep1469 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1461 ep1462 ep1463 ep1464 Bool.false ep1466 ep1467 ep1468

noncomputable def ep1470 := nat_lit 961964192350799053054552309760000000000

noncomputable def ep1471 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.true ep1461 ep1462 ep1463 ep1464 Bool.false ep1466 ep1467 ep1468 ep1470

noncomputable def ep1472 := nat_lit 55032268070182240780017759

noncomputable def ep1473 := nat_lit 604462909807314587353088000000

noncomputable def ep1474 := nat_lit 9889631066772264074022904977

noncomputable def ep1475 := nat_lit 492525666483609115163930782597120000000

noncomputable def ep1476 := nat_lit 18053330491966977326825023311

noncomputable def ep1477 := nat_lit 1180591620717411303424000000000

noncomputable def ep1478 := nat_lit 7149142105081969036177408510269

noncomputable abbrev qz253 := (Complex.re qz521)

noncomputable abbrev qz254 := (Complex.im qz521)

noncomputable def ep1479 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1472 ep1473 ep1474 ep1475 ep1476 ep1477 ep1478

noncomputable def ep1480 := nat_lit 2198775296801826406981833850880000000000

noncomputable def ep1481 := nat_lit 10847598046334745806876619151357826378021273881018368000000

noncomputable def ep1482 := nat_lit 49252566648360911516393078259712

noncomputable def ep1483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 2224994143 30000000 0 1 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 ep1472

noncomputable def ep1484 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) 2224994143 30000000 0 1 0 1 0 1 2224994143

noncomputable def ep1485 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6674982429 125000 0 1 2224994143 30000000 0

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz538 qz584 qz542)

noncomputable abbrev qz255 := qz525

noncomputable def ep1486 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1

noncomputable abbrev qz256 := (Complex.re qz525)

noncomputable abbrev qz257 := (Complex.im qz525)

noncomputable def ep1487 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 741643881 25000 0 1 370845378 15625 0 1

noncomputable def ep1488 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 741643881 62500 0 1 5 2 0 1 741643881 25000

noncomputable abbrev qz526 := (@HAdd.hAdd Complex Complex Complex qz538 qz584 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz526

noncomputable def ep1489 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1

noncomputable abbrev qz259 := (Complex.re qz526)

noncomputable abbrev qz260 := (Complex.im qz526)

noncomputable def ep1490 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 185422689 15625 0 1

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1492 := @ep1491 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1493 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz511 qz151) Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 108936 1000 1 qz152)

noncomputable abbrev qz527 := (ep1493 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz151 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz153))

noncomputable def ep1494 := ep1492 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz527)

noncomputable def ep1495 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 108936 1000 0 1 108936 1000 0 1 185422689 15625

noncomputable def ep1496 := @ep1495 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1497 := ep1496 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz527)

noncomputable def ep1498 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 (@ep1490 741643881 741643881 62500 0 1 (ep1494 rfl) (ep1497 rfl) rfl rfl)

noncomputable def ep1499 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 13617 250 0 1 40851 250 0 1

noncomputable def ep1500 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 108936 1000 0 1 13617 250

noncomputable def ep1501 := @ep1500 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1502 := ep1501 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz527)

noncomputable def ep1503 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 108936 1000 0 1 3 2 0 1 40851 250

noncomputable def ep1504 := @ep1503 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 108936 1000 0 1 ep1186)

noncomputable def ep1505 := ep1504 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 108936 1000 0 1 qz527)

noncomputable abbrev qz261 := (ep1489 (BSN.ascPochhammer_succ_eval_c 1 2 qz446 rfl) (ep1498 (@ep1499 13617000 27234 125 0 1 (ep1502 rfl) (ep1505 rfl) rfl rfl)))

noncomputable def ep1506 := @ep1488 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz261)

noncomputable def ep1507 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz513 qz151) Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 108936 1000 2 qz152)

noncomputable abbrev qz528 := (ep1507 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz151 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz153))

noncomputable def ep1508 := ep1506 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz528)

noncomputable def ep1509 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 27234 125 0 1 108936 1000 0 1 370845378 15625

noncomputable def ep1510 := @ep1509 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz261)

noncomputable def ep1511 := ep1510 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz528)

noncomputable def ep1512 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 (@ep1487 20859320090625 6674982429 125000 0 1 (ep1508 rfl) (ep1511 rfl) rfl rfl)

noncomputable def ep1513 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 10098964727577 7812500 0 1 13617 25 0 1

noncomputable def ep1514 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 741643881 62500 0 1 108936 1000 0 1 10098964727577 7812500

noncomputable def ep1515 := @ep1514 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz261)

noncomputable def ep1516 := ep1515 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz528)

noncomputable def ep1517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 27234 125 0 1 5 2 0 1 13617 25

noncomputable def ep1518 := @ep1517 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 741643881 62500 0 1 Bool.false 27234 125 0 1 qz261)

noncomputable def ep1519 := ep1518 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 108936 1000 0 1 qz528)

noncomputable abbrev qz262 := (ep1486 (BSN.ascPochhammer_succ_eval_c 2 3 qz446 rfl) (ep1512 (@ep1513 252367735376925 10094709415077 7812500 0 1 (ep1516 rfl) (ep1519 rfl) rfl rfl)))

noncomputable def ep1520 := @ep1485 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz262)

noncomputable def ep1521 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10094709415077 7812500 0 1 0 1 0

noncomputable def ep1522 := @ep1521 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz262)

noncomputable def ep1523 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) 1121634379453 625000000 0 1 0 1 0 1 1121634379453

noncomputable def ep1524 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10094709415077 7812500 0 1 1121634379453 625000000 0

noncomputable def ep1525 := @ep1524 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz262)

noncomputable def ep1526 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6674982429 125000 0 1 0 1 0

noncomputable def ep1527 := @ep1526 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1317) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6674982429 125000 0 1 Bool.true 10094709415077 7812500 0 1 qz262)

noncomputable def ep1528 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 (@ep1484 2224994143 30000000 0 1 (ep1520 rfl) (ep1522 rfl) rfl rfl) (@ep1523 1121634379453 625000000 0 1 (ep1525 rfl) (ep1527 rfl) rfl rfl)

noncomputable def ep1529 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 ep1528

noncomputable def ep1530 := nat_lit 24626283324180455758196539129856

noncomputable def ep1531 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 Bool.false 80477786802376935 9444732965739290427392 44617029980820754311 ep1530

noncomputable abbrev qz529 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 13492928512)))

noncomputable def ep1532 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz529 qz216) (@HMul.hMul Real Real Real qz0 qz529 qz595)) Bool.false 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 Bool.false 80477786802376935 9444732965739290427392 44617029980820754311

noncomputable abbrev qz530 := (Real.sqrt (@Nat.cast Real Real.instNatCast 13492928512))

noncomputable abbrev qz531 := (@Nat.cast Real Real.instNatCast 13492928512)

noncomputable def ep1533 := @Enclosure.Real.IsNear.inv_image qz530 63859121627945993 549755813888 1 549755813888 2366392 2366393 274877906944 (@Enclosure.Real.IsNear.of_eq qz530 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz531 qz15)) Bool.false 63859121627945993 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 13492928512) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz531 qz15)) Bool.false 63859121627945993 549755813888 1 549755813888 63859121627945993 549755813888 1 549755813888 (BSN.sqrt_enclosure 13492928512 1 31929560813972996 31929560813972997 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1534 := nat_lit 5092596031250000000000000

noncomputable def ep1535 := nat_lit 33000555057847457572949327872

noncomputable def ep1536 := nat_lit 83437093376000000000000000

noncomputable def ep1537 := nat_lit 250155354990189459982334648674104115200

noncomputable def ep1538 := nat_lit 6494602839761417488672768362345922560

noncomputable def ep1539 := nat_lit 917424756442668995916595200

noncomputable def ep1540 := BSN.log_dyadic_bound 12 44 10 9 ep1537 274877906944 83437093376 ep1538 ep1539 153826016480 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 12) (BSN.artanhQ 44) 0 9 ep1538 ep1537 ep1539 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1541 := @Enclosure.Real.IsNear.mulLit_ff qz151 (Real.log (Enclosure.sfrac Bool.false 28 1)) 108936 1000 0 1 3751728747584759 1125899906842624 488444213073 40740768250000000000000 51087290355861663303 140737488355328000 6651144849415041 ep1534 qz153 (BSN.isNear_log_sfrac 28 1 3751728747584759 1125899906842624 488444213073 40740768250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz497) Bool.false ep1535 ep1369 1000333748373504 ep1536 3751728747584759 1125899906842624 488444213073 40740768250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 153826016480 274877906944 24973259072661432 36028797018963968 83437093376 1000000000000000 rfl rfl rfl rfl (ep1540 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1542 := nat_lit 1416986086323275281125605376

noncomputable def ep1543 := nat_lit 673446482937064215730206708590581675959946944488727837456

noncomputable def ep1544 := nat_lit 192832565311078833065035451080939512302664359253935140236165120

noncomputable def ep1545 := nat_lit 1349827957177551831455248157566576586118650514777545981653155840

noncomputable def ep1546 := BSN.sin_dyadic_bound_f 161092667249622 1125899906842624 2 1 549755813888 167037149826 ep1543 ep1544 ep1543 ep1543 ep1545 ep1543 78390425727 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 161092667249622) (BSN.sinEvenQ 1125899906842624) 0 1 ep1543 ep1544 ep1543 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 161092667249622) (BSN.sinOddQ 1125899906842624) 0 1 ep1543 ep1545 ep1543 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz532 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24944965994073) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1547 := @Enclosure.Real.IsNear.cos_image qz218 qz532 Bool.false 24944965994073 68719476736 719 549755813888 Bool.false 78390425727 549755813888 1 83437093376 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 51087290355861663303 140737488355328000 6651144849415041 ep1534 24944965994073 68719476736 719 549755813888 (ep1541 rfl) rfl) (Enclosure.sfrac_false_div 24944965994073 68719476736) (BSN.cos_reduce3 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1542) (@Nat.cast Real Real.instNatCast ep1369)) 226375608064910080 72057594037927936 Bool.false 78390425727 549755813888 57 1000000000000000 166874186752 83437093376 (BSN.sin_reduce_arg_pos_rat_q3 24944965994073 68719476736 226375608064910080 72057594037927936 57 ep1542 ep1369 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 78390425727 549755813888 ep1542 ep1369 161092667249622 1125899906842624 167037149826 166874186752 (ep1546 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1548 := nat_lit 1818074234192854192960490790260454181638820467778763897638750713330759917306989336108291826323022336254172963500270838016

noncomputable def ep1549 := nat_lit 104116315084464154334926661015161438772973737566874292037332185255718912119719036967467300644255157363495615893941178932920320

noncomputable def ep1550 := nat_lit 453530165380301523861282882468320193897316671769440878702836626651913643369477655657029161866086768032418356551936

noncomputable def ep1551 := nat_lit 5454221795518231818278424648215597608276073608702948154034494734319026448093681269369564164910743276588982825664099410176

noncomputable def ep1552 := nat_lit 4685234178800886945071699745682264744783818190509343141679948336507351045387356663536028528991482081357302715227353051981414400

noncomputable def ep1553 := BSN.cos_dyadic_bound_f 161092667249622 1125899906842624 3 2 549755813888 167037149826 ep1548 ep1549 ep1550 ep1551 ep1552 ep1550 544138214112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 161092667249622) (BSN.cosEvenQ 1125899906842624) 0 2 ep1548 ep1549 ep1550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 161092667249622) (BSN.cosOddQ 1125899906842624) 0 2 ep1551 ep1552 ep1550 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1554 := @Enclosure.Real.IsNear.sin_image qz218 qz532 Bool.false 24944965994073 68719476736 719 549755813888 Bool.true 544138214112 549755813888 1 83437093376 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 51087290355861663303 140737488355328000 6651144849415041 ep1534 24944965994073 68719476736 719 549755813888 (ep1541 rfl) rfl) (Enclosure.sfrac_false_div 24944965994073 68719476736) (BSN.sin_reduce3 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1542) (@Nat.cast Real Real.instNatCast ep1369)) 226375608064910080 72057594037927936 Bool.false 544138214112 549755813888 57 1000000000000000 166874186752 83437093376 (BSN.sin_reduce_arg_pos_rat_q3 24944965994073 68719476736 226375608064910080 72057594037927936 57 ep1542 ep1369 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 544138214112 549755813888 ep1542 ep1369 161092667249622 1125899906842624 167037149826 166874186752 (ep1553 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1555 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz529 qz216) (@HMul.hMul Real Real Real qz0 qz529 qz595) Bool.false 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 Bool.false 80477786802376935 9444732965739290427392 44617029980820754311 ep1530 (@Enclosure.Real.IsNear.mulLit_ff qz529 qz216 4732785 549755813888 1 549755813888 78390425727 549755813888 118244191311 89589896830804557824 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 (@Enclosure.Real.IsNear.recentre' qz529 Bool.false 4732785 549755813888 1 549755813888 4732785 549755813888 1 549755813888 (ep1533 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 78390425727 549755813888 60541025951232 45870027177371933605888 78390425727 549755813888 118244191311 89589896830804557824 (ep1547 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz529 qz595 4732785 549755813888 1 549755813888 17004319191 17179869184 118244191311 89589896830804557824 80477786802376935 9444732965739290427392 44617029980820754311 ep1530 (@Enclosure.Real.IsNear.recentre' qz529 Bool.false 4732785 549755813888 1 549755813888 4732785 549755813888 1 549755813888 (ep1533 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 17004319191 17179869184 118244191311 89589896830804557824 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 544138214112 549755813888 60541025951232 45870027177371933605888 17004319191 17179869184 118244191311 89589896830804557824 (ep1554 rfl rfl) rfl)) rfl)

noncomputable def ep1556 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 1121634379453 625000000 0 1 80477786802376935 9444732965739290427392 44617029980820754311 ep1530 ep1476

noncomputable def ep1557 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2224994143 30000000 0 1 Bool.false 1121634379453 625000000 0 1 ep1528

noncomputable def ep1558 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 Bool.false 80477786802376935 9444732965739290427392 44617029980820754311 ep1530

noncomputable def ep1559 := nat_lit 11937506951792758590219447

noncomputable def ep1560 := nat_lit 18889465931478580854784000000

noncomputable def ep1561 := nat_lit 33090876795127193558272333491

noncomputable def ep1562 := nat_lit 246262833241804557581965391298560000000

noncomputable def ep1563 := nat_lit 83226399549389739885597869367

noncomputable def ep1564 := nat_lit 2136612405314071392528321175743

noncomputable def ep1565 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1559 ep1560 ep1561 ep1562 ep1563 ep1467 ep1564

noncomputable def ep1566 := nat_lit 4397550593603652813963667701760000000000

noncomputable def ep1567 := nat_lit 2023088500633177874933767954329121359824347597897728000000

noncomputable def ep1568 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 2224994143 30000000 0 1 80477786802376935 9444732965739290427392 44617029980820754311 ep1530 ep1559

noncomputable def ep1569 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1121634379453 625000000 0 1 371005031024359695 302231454903657293676544 13334369123468201517 ep1482 ep1563

noncomputable abbrev qz533 := (@ep1532 ep1530 (BSN.cpow_neg_s_sub_mk qz151 108936 1000 28 3 13492928512 qz152 rfl EMRow33.d22) ep1555)

noncomputable def ep1570 := ep1471 (@ep1479 ep1480 ep1481 ep1461 ep1462 ep1463 ep1464 (@ep1483 ep1473 ep1474 ep1475 ep1529 (ep1531 qz533) rfl) (@ep1556 ep1477 ep1478 ep1480 ep1557 (ep1558 qz533) rfl) rfl rfl) (@ep1565 ep1566 ep1567 ep1466 ep1467 ep1468 ep1470 (@ep1568 ep1560 ep1561 ep1562 ep1529 (ep1558 qz533) rfl) (@ep1569 ep1467 ep1564 ep1566 ep1557 (ep1531 qz533) rfl) rfl rfl)

noncomputable def ep1571 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1466 ep1467 ep1468 ep1470 ep1466 ep1467 ep1468

noncomputable def ep1572 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1461 ep1462 ep1463 ep1464 Bool.false ep1466 ep1467 ep1468

noncomputable def ep1573 := @ep1433 69394646983781205 144115188075855872 108936930643 1008806316530991104 (@ep1434 1 3670016 (ep1435 (@ep1436 1048576 1 1048576 (ep1437 (@ep1438 742456381 742456381 62500 0 1 (ep1442 rfl) (ep1445 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1446 229 68719476736 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1447 1832 549755813888 4250388555 274877906944 229 68719476736 (@ep1452 4250387639 4250389471 274877906944 (@ep1456 ep1457 ep1458 ep1459 ep1460 ep1448 ep1449 ep1450 ep1451 (@ep1465 ep1464 ep1453 ep1449 ep1454 ep1451 (@ep1469 ep1470 ep1570) (@ep1469 ep1470 ep1570) rfl) (@ep1571 ep1470 ep1455 ep1457 ep1458 ep1459 (@ep1572 ep1470 ep1570) (@ep1572 ep1470 ep1570) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow33.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 2177985326155076087 3891110078048108544 2793562053308353 27237770546336759808 := ep1431 (ep1432 ep1573) rfl rfl

noncomputable def EMRow33.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz534 := (EMRow33.d3 qz544 qz586 (@Enclosure.dec_le_dec qz544 qz586 106726 1000 108936 1000 (@Eq.refl Real qz544) (@Eq.refl Real qz586) rfl rfl rfl) 27 28 1 1)

noncomputable abbrev qz263 := qz534

noncomputable def ep1574 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz13 106726 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 27 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz534)

noncomputable def ep1575 := @Enclosure.Real.IsNear.neg_val qz264 ep385 ep386

noncomputable def ep1576 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 27 qz13) Bool.true

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz534)

noncomputable def ep1577 := BSN.mul_neg_of_neg_pos_r qz264 qz265 (@ep1575 ep387 ep388 (@ep1576 ep385 ep386 ep387 ep388 (@Eq.refl Real (hardyZApproximantEM 1 27 qz13)) EMRow33.d11) rfl rfl rfl)

noncomputable def ep1578 := @Enclosure.Real.IsNear.pos_val qz265 ep961 ep962

noncomputable def ep1579 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 28 qz151) Bool.false

noncomputable def ep1580 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 27 qz13)

noncomputable def ep1581 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 27 qz13) Bool.true

noncomputable def ep1582 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 27 qz13) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 4707520526096713537 9079256848778919936 299053759623973 3026418949592973312 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1583 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 28 qz151)

noncomputable def ep1584 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 28 qz151) Bool.false

noncomputable def ep1585 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 28 qz151) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 2177985326155076087 3891110078048108544 2793562053308353 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz148 1 28))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz148 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1586 := @List.cons EMRow33.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1574 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 28 rfl) (ep1577 (@ep1578 ep963 ep964 (@ep1579 ep961 ep962 ep963 ep964 (@Eq.refl Real (hardyZApproximantEM 1 28 qz151)) EMRow33.d16) rfl rfl rfl)) (ep1580 (hardyZErrorBoundEM 1 27 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 27 qz13 rfl) (@ep1581 Bool.false ep385 ep386 ep387 ep388 4707520526096713537 9079256848778919936 299053759623973 3026418949592973312 (@ep1576 ep385 ep386 ep387 ep388 (@Eq.refl Real (hardyZApproximantEM 1 27 qz13)) EMRow33.d11) (ep1582 EMRow33.d21) rfl rfl rfl rfl rfl)) (ep1583 (hardyZErrorBoundEM 1 28 qz151) (BSN.hardyZErrorBoundEM_le_strong 1 28 qz151 rfl) (@ep1584 Bool.false ep961 ep962 ep963 ep964 2177985326155076087 3891110078048108544 2793562053308353 27237770546336759808 (@ep1579 ep961 ep962 ep963 ep964 (@Eq.refl Real (hardyZApproximantEM 1 28 qz151)) EMRow33.d16) (ep1585 EMRow33.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow33.d0)

noncomputable abbrev qz535 := (@Enclosure.dec_le_dec qz544 qz586 106726 1000 108936 1000 (@Eq.refl Real qz544) (@Eq.refl Real qz586) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1586 (@List.IsChain.singleton EMRow33.d1 EMRow33.d24 (EMRow33.d2 qz284 qz448 qz535))))

noncomputable abbrev qz536 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1587 := And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz266)) (@Option.some Real qz13))

noncomputable def ep1588 := ep1587 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz266)) (@Option.some Real qz151))

noncomputable def ep1589 := @And.intro (@Eq Nat (@List.length qz536 qz266) 1) ep1588

noncomputable def ep1590 := @And.intro (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz266)) (@Option.some Real qz13))

noncomputable def ep1591 := @ep1590 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz266)) (@Option.some Real qz151))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1586 (@List.IsChain.singleton EMRow33.d1 EMRow33.d24 (EMRow33.d2 qz284 qz448 qz535)))

theorem EMRow33.d25 : Zeta.Certificates.BatchSpec 1 106726 1000 108936 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz151)))) qz267 (ep1589 (@Eq.refl Nat 1) (ep1591 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz151))))

theorem solution : Zeta.Certificates.BatchSpec 1 106726 1000 108936 1000 := EMRow33.d25
#print axioms solution
#check solution
