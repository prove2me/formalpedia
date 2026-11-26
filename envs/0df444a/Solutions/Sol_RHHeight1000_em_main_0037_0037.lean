-- Prove2me | solution 1 for RHHeight1000.em_main_0037_0037
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:40:38.849635+00:00
-- url     : https://prove2.me/submissions/b4c2507d-3e44-4e4e-b6b5-97a2538b415e

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow37.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow37.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow37.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow37.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow37.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 50000000027881 13940500000000000000 4138529546116343 2251799813685248 50000000027881 13940500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 278810 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 50000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000557620 278810000000000000000 4138529546116343 2251799813685248 50000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 278810 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 50000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000557620 278810000000000000000 4138529546116343 2251799813685248 50000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow37.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 278810 1200336 1048576 1 278810 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 278810 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 278810 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 278810 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 278810 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 278810 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 278810 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow37.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz578 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 115476 1000)))

noncomputable abbrev qz530 := qz578

noncomputable abbrev qz272 := qz530

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz579 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz531 := qz579

noncomputable abbrev qz273 := qz531

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz532 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz532

noncomputable abbrev qz6 := qz274

noncomputable abbrev qz533 := (@Neg.neg Complex Complex.instNeg qz578)

noncomputable abbrev qz275 := qz533

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz276 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz276) Bool.false 819227130201 1099511627776 432859201831267 153277418470113280 Bool.false 284046628153 549755813888 108267891353463 38319354617528320

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz276 Bool.false 46226191741 68719476736 48441181062663 19159677308764160 Bool.false 474294827105 549755813888 96907167154001 38319354617528320 Bool.false

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz277) Bool.false 46226191741 68719476736 48441181062663 19159677308764160 Bool.false 474294827105 549755813888 96907167154001 38319354617528320

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz277 Bool.false 176409540589 274877906944 42379321167341 19159677308764160 Bool.false 267202332205 549755813888 42375006861401 19159677308764160 Bool.false

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz278) Bool.false 176409540589 274877906944 42379321167341 19159677308764160 Bool.false 267202332205 549755813888 42375006861401 19159677308764160

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz278 Bool.false 299520899293 1099511627776 286534893431363 153277418470113280 Bool.false 343208744087 1099511627776 286570368658143 153277418470113280 Bool.false

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz279) Bool.false 299520899293 1099511627776 286534893431363 153277418470113280 Bool.false 343208744087 1099511627776 286570368658143 153277418470113280

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz279 Bool.false 365842164345 549755813888 2863827161967 1915967730876416 Bool.false 108647394561 1099511627776 45840078216251 30655483694022656 Bool.true

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz280) Bool.false 365842164345 549755813888 2863827161967 1915967730876416 Bool.false 108647394561 1099511627776 45840078216251 30655483694022656

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz280 Bool.false 1276241836971 1099511627776 164824741611157 153277418470113280 Bool.false 46014815945 274877906944 82521851476791 76638709235056640 Bool.true

noncomputable abbrev qz534 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz534

noncomputable abbrev qz8 := qz281

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 1276241836971 1099511627776 164824741611157 153277418470113280 Bool.false 46014815945 274877906944 82521851476791 76638709235056640

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 261493902739 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 1099511627776 90848828826491 153277418470113280 Bool.false

noncomputable abbrev qz535 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz535

noncomputable abbrev qz9 := qz282

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 261493902739 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 1099511627776 90848828826491 153277418470113280

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz283

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz536 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz536))

noncomputable abbrev qz580 := (Enclosure.sfrac Bool.false 115476 1000)

noncomputable abbrev qz537 := qz580

noncomputable abbrev qz284 := qz537

noncomputable abbrev qz285 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log qz285))

noncomputable abbrev qz13 := qz284

noncomputable abbrev qz286 := (@Eq.refl Real qz537)

noncomputable abbrev qz14 := qz286

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 13384004205 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 1099511627776 90848828826491 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz536) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz536) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz536 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz536 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 139405 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 3877973906883556729407773225325863418533684564047112823913034709972787567190625

noncomputable def ep57 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep58 := nat_lit 11709158672275637561595252019160332925451143969978497168142757239641250390625

noncomputable def ep59 := nat_lit 11610503403306118913100129171939269589750151404201381477402818615439080200790625

noncomputable def ep60 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz287 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz288 := (BSN.cosOddQ 2147483648)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 3225267285 2147483648 3 2 1048576 279083 ep56 ep57 ep58 ep59 ep60 ep58 72204 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3225267285) qz287 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3225267285) qz288 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz17 := (Real.log qz285)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 115476 1000)

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20982451) qz16)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 139405 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 139405 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz12 qz289 Bool.false 20982451 262144 435 524288 Bool.true 72204 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 655701597 8192000 28869 34851250 20982451 262144 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 115476 1000 0 1 363408 524288 1 139405 655701597 8192000 28869 34851250 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 20982451 262144) (BSN.cos_reduce2 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56739502129040716726272) qz291) 226375608064910080 72057594037927936 Bool.false 72204 1048576 12 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 20982451 262144 226375608064910080 72057594037927936 12 56739502129040716726272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 72204 1048576 56739502129040716726272 37778931862957161709568 3225267285 2147483648 279083 278810 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 6970985705452581602884715603971225887020271300108820285308948272159304620630625

noncomputable def ep64 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep65 := nat_lit 18238385828811172213407862840465046307935694410047897466108347677267331029590625

noncomputable def ep66 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz292 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz293 := (BSN.sinOddQ 2147483648)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 3225267285 2147483648 3 2 1048576 279083 ep63 ep64 ep58 ep65 ep66 ep58 1046087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3225267285) qz292 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3225267285) qz293 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz12 qz289 Bool.false 20982451 262144 435 524288 Bool.true 1046087 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 655701597 8192000 28869 34851250 20982451 262144 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 115476 1000 0 1 363408 524288 1 139405 655701597 8192000 28869 34851250 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 20982451 262144) (BSN.sin_reduce2 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56739502129040716726272) qz291) 226375608064910080 72057594037927936 Bool.false 1046087 1048576 12 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 20982451 262144 226375608064910080 72057594037927936 12 56739502129040716726272 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046087 1048576 56739502129040716726272 37778931862957161709568 3225267285 2147483648 279083 278810 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 13384004205 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 1099511627776 90848828826491 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 741455 1048576 1 1048576 18051 262144 61165463 73088368640 13384004205 274877906944 22678266166719 38319354617528320 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 72204 1048576 61165463 73088368640 18051 262144 61165463 73088368640 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 1046087 1048576 61165463 73088368640 775626436585 1099511627776 90848828826491 153277418470113280 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 1046087 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 1046087 1048576 61165463 73088368640 1046087 1048576 61165463 73088368640 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz19 := qz295

noncomputable def ep70 := @ep51 13384004205 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 1099511627776 90848828826491 153277418470113280 Bool.false 261493902739 261493902739 274877906944 22678266166719 38319354617528320 Bool.false 775626436585 775626436585 1099511627776 90848828826491 153277418470113280 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz19)) (ep53 ep69) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz20 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz21 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz20 (Real.cos qz21)) (@HMul.hMul Real Real Real qz0 qz20 (@Neg.neg Real Real.instNeg (Real.sin qz21)))) Bool.false 230266226015 1099511627776 74111676944281 153277418470113280 Bool.true 591567172805 1099511627776 74194874127091 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 3 qz14 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 139405 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 1575502919866163000091122699787189237371726343813835052910313128385762308360801

noncomputable def ep75 := nat_lit 1939594580282112117722998315466583072551821724429838824670971399075090369121

noncomputable def ep76 := nat_lit 4722629570437924776037922102730634545970075387992645481081597442359136744344161

noncomputable def ep77 := BSN.cos_dyadic_bound_f 2576106837 2147483648 3 2 1048576 279083 ep74 ep57 ep75 ep76 ep60 ep75 380357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2576106837) qz287 0 2 ep74 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2576106837) qz288 0 2 ep76 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz22 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz23 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133025811) qz22)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 139405 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 139405 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz21 qz297 Bool.false 133025811 1048576 435 524288 Bool.false 380357 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 16628226441 131072000 28869 34851250 133025811 1048576 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 115476 1000 0 1 575989 524288 1 139405 16628226441 131072000 28869 34851250 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 133025811 1048576) (BSN.cos_reduce0 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181277403026564728225792) qz24) 226375608064910080 72057594037927936 Bool.false 380357 1048576 20 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 133025811 1048576 226375608064910080 72057594037927936 20 181277403026564728225792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 380357 1048576 181277403026564728225792 151115727451828646838272 2576106837 2147483648 279083 278810 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 2834353580094867710469842460964567360811065961485359224178826853975112082754145

noncomputable def ep80 := nat_lit 7420166699499434869706607305253587667625803140145911562371269711479171975187041

noncomputable def ep81 := BSN.sin_dyadic_bound_f 2576106837 2147483648 3 2 1048576 279083 ep79 ep64 ep75 ep80 ep66 ep75 977159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2576106837) qz292 0 2 ep79 ep64 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2576106837) qz293 0 2 ep80 ep66 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz21 qz297 Bool.false 133025811 1048576 435 524288 Bool.false 977159 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 16628226441 131072000 28869 34851250 133025811 1048576 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 115476 1000 0 1 575989 524288 1 139405 16628226441 131072000 28869 34851250 qz18 qz298 rfl) rfl) (Enclosure.sfrac_false_div 133025811 1048576) (BSN.sin_reduce0 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181277403026564728225792) qz24) 226375608064910080 72057594037927936 Bool.false 977159 1048576 20 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 133025811 1048576 226375608064910080 72057594037927936 20 181277403026564728225792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 977159 1048576 181277403026564728225792 151115727451828646838272 2576106837 2147483648 279083 278810 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz20 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz20 (Real.cos qz21)) (@HMul.hMul Real Real Real qz0 qz20 (@Neg.neg Real Real.instNeg (Real.sin qz21))) Bool.false 230266226015 1099511627776 74111676944281 153277418470113280 Bool.true 591567172805 1099511627776 74194874127091 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz20 (Real.cos qz21) 605395 1048576 1 1048576 380357 1048576 61165463 73088368640 230266226015 1099511627776 74111676944281 153277418470113280 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz21) Bool.false 380357 1048576 61165463 73088368640 380357 1048576 61165463 73088368640 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz20 (@Neg.neg Real Real.instNeg (Real.sin qz21)) 605395 1048576 1 1048576 977159 1048576 61165463 73088368640 591567172805 1099511627776 74194874127091 153277418470113280 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz21) Bool.false 977159 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz21) Bool.false 977159 1048576 61165463 73088368640 977159 1048576 61165463 73088368640 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 230266226015 1099511627776 74111676944281 153277418470113280 Bool.true 591567172805 1099511627776 74194874127091 153277418470113280 Bool.false 350810684900954156826624 1276241836971 1099511627776 164824741611157 153277418470113280 Bool.false 202375300725999958753280 46014815945 274877906944 82521851476791 76638709235056640 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz538 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz538))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 544557508281 1099511627776 64281431346203 153277418470113280 Bool.true 75411869219 1099511627776 64156688127673 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 4 qz14 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz538) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz538) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz538 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 318077276165597140789031982421875

noncomputable def ep88 := nat_lit 49379992292270016474244603430625

noncomputable def ep89 := nat_lit 20095619060363156210525625

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 14 13 ep87 524288 139405 ep88 ep89 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 5778819226927683807545388081671663019455494460047916019821034141952568889180160

noncomputable def ep92 := nat_lit 8051276174151772708002885790604034553121172280082868126873347198517904408576

noncomputable def ep93 := nat_lit 15121967337671497578234487922621948995011717878338693503516342095363889531191296

noncomputable def ep94 := BSN.sin_dyadic_bound_f 3077748232 2147483648 3 2 1048576 279083 ep91 ep64 ep92 ep93 ep66 ep92 1038663 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3077748232) qz292 0 2 ep91 ep64 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3077748232) qz293 0 2 ep93 ep66 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz300 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167859839) qz22)

noncomputable abbrev qz301 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 139405 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 139405 rfl rfl rfl (ep90 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz26 qz300 Bool.false 167859839 1048576 435 524288 Bool.true 1038663 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 20982479973 131072000 28869 34851250 167859839 1048576 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 115476 1000 0 1 726817 524288 1 139405 20982479973 131072000 28869 34851250 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 167859839 1048576) (BSN.cos_reduce1 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216577278038500104470528) qz24) 226375608064910080 72057594037927936 Bool.false 1038663 1048576 25 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 167859839 1048576 226375608064910080 72057594037927936 25 216577278038500104470528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1038663 1048576 216577278038500104470528 151115727451828646838272 3077748232 2147483648 279083 278810 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := nat_lit 3214033471037225125395439105724525692832217443262212396845851566506324007059456

noncomputable def ep97 := nat_lit 9625997860763371830770311545592369009390409985226471454283808005121936212361216

noncomputable def ep98 := BSN.cos_dyadic_bound_f 3077748232 2147483648 3 2 1048576 279083 ep96 ep57 ep92 ep97 ep60 ep92 143837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3077748232) qz287 0 2 ep96 ep57 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3077748232) qz288 0 2 ep97 ep60 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz26 qz300 Bool.false 167859839 1048576 435 524288 Bool.false 143837 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 20982479973 131072000 28869 34851250 167859839 1048576 435 524288 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz27 115476 1000 0 1 726817 524288 1 139405 20982479973 131072000 28869 34851250 qz18 qz301 rfl) rfl) (Enclosure.sfrac_false_div 167859839 1048576) (BSN.sin_reduce1 qz300 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216577278038500104470528) qz24) 226375608064910080 72057594037927936 Bool.false 143837 1048576 25 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 167859839 1048576 226375608064910080 72057594037927936 25 216577278038500104470528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143837 1048576 216577278038500104470528 151115727451828646838272 3077748232 2147483648 279083 278810 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep86 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 544557508281 1099511627776 64281431346203 153277418470113280 Bool.true 75411869219 1099511627776 64156688127673 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz26) 524287 1048576 1 1048576 1038663 1048576 61165463 73088368640 544557508281 1099511627776 64281431346203 153277418470113280 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 1038663 1048576 61165463 73088368640 1038663 1048576 61165463 73088368640 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 143837 1048576 61165463 73088368640 75411869219 1099511627776 64156688127673 153277418470113280 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 143837 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 143837 1048576 61165463 73088368640 143837 1048576 61165463 73088368640 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep47 544557508281 1099511627776 64281431346203 153277418470113280 Bool.true 75411869219 1099511627776 64156688127673 153277418470113280 Bool.false 804495427256131717693440 365842164345 549755813888 2863827161967 1915967730876416 Bool.false 29864768411846609731584 108647394561 1099511627776 45840078216251 30655483694022656 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep100) rfl rfl

noncomputable abbrev qz539 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz539))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz284 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 432163429397 1099511627776 57428720474003 153277418470113280 Bool.false 117280674763 549755813888 7171247197111 19159677308764160 (BSN.cpow_neg_s_mk qz13 115476 1000 5 qz14 rfl)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz539) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz539) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz539 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 11734546589655452485523914939250625

noncomputable def ep105 := nat_lit 2429970938528035899633153341031900

noncomputable def ep106 := nat_lit 824199001261152424427520000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 17 16 ep104 524288 139405 ep105 ep106 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep105 ep104 ep106 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep108 := nat_lit 1300422286959022925086371079530168576

noncomputable def ep109 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep110 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep111 := BSN.cos_dyadic_bound_f 1067876676 2147483648 2 1 1048576 279083 ep108 ep109 ep108 ep108 ep110 ep108 921581 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1067876676) qz287 0 1 ep108 ep109 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1067876676) qz288 0 1 ep108 ep110 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194879145) qz22)

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 139405 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 139405 rfl rfl rfl (ep107 rfl)))

noncomputable def ep112 := @Enclosure.Real.IsNear.cos_image qz29 qz303 Bool.false 194879145 1048576 869 1048576 Bool.true 921581 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 761246661 4096000 28869 34851250 194879145 1048576 869 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz30 115476 1000 0 1 843808 524288 1 139405 761246661 4096000 28869 34851250 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 194879145 1048576) (BSN.cos_reduce2 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75145140668991537152000) qz24) 226375608064910080 72057594037927936 Bool.false 921581 1048576 29 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 194879145 1048576 226375608064910080 72057594037927936 29 75145140668991537152000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 921581 1048576 75145140668991537152000 151115727451828646838272 1067876676 2147483648 279083 278810 (ep111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep113 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep114 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep115 := BSN.sin_dyadic_bound_f 1067876676 2147483648 2 1 1048576 279083 ep108 ep113 ep108 ep108 ep114 ep108 500198 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1067876676) qz292 0 1 ep108 ep113 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1067876676) qz293 0 1 ep108 ep114 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable def ep116 := @Enclosure.Real.IsNear.sin_image qz29 qz303 Bool.false 194879145 1048576 869 1048576 Bool.true 500198 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 761246661 4096000 28869 34851250 194879145 1048576 869 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz30 115476 1000 0 1 843808 524288 1 139405 761246661 4096000 28869 34851250 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 194879145 1048576) (BSN.sin_reduce2 qz303 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75145140668991537152000) qz24) 226375608064910080 72057594037927936 Bool.false 500198 1048576 29 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 194879145 1048576 226375608064910080 72057594037927936 29 75145140668991537152000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 500198 1048576 75145140668991537152000 151115727451828646838272 1067876676 2147483648 279083 278810 (ep115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep117 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 432163429397 1099511627776 57428720474003 153277418470113280 Bool.false 117280674763 549755813888 7171247197111 19159677308764160 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 468937 1048576 1 1048576 921581 1048576 122191521 146176737280 432163429397 1099511627776 57428720474003 153277418470113280 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 921581 1048576 122191521 146176737280 921581 1048576 122191521 146176737280 (ep112 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 250099 524288 122191521 146176737280 117280674763 549755813888 7171247197111 19159677308764160 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 250099 524288 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 500198 1048576 122191521 146176737280 250099 524288 122191521 146176737280 (ep116 rfl rfl) rfl)) rfl)

noncomputable def ep118 := @ep45 432163429397 1099511627776 57428720474003 153277418470113280 Bool.false 117280674763 549755813888 7171247197111 19159677308764160 Bool.false 164663355767288898781184 299520899293 1099511627776 286534893431363 153277418470113280 Bool.false 188681002439026992480256 343208744087 1099511627776 286570368658143 153277418470113280 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep117) rfl rfl

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz306))

noncomputable abbrev qz540 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz267 qz284 qz540)

noncomputable def ep119 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.false 406117263063 1099511627776 10499935181473 30655483694022656 Bool.false 191195920323 1099511627776 10485937246613 30655483694022656 (BSN.cpow_neg_s_mk qz13 115476 1000 6 qz14 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep120 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz306) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz306) (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep121 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 139405 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep122 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz540 115476 1000 0 1 4034681531866359 2251799813685248 100000000027881 13940500000000000000 116477221143449917971 562949953421312000 2886900000804896589 3485125000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000278810 139405000000000000000 4034681531866359 2251799813685248 100000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep123 := nat_lit 2237593980624781286983914811807258435580991955781454245982707329095520978206720

noncomputable def ep124 := nat_lit 1209178916181868846109863910565242647107191827999044017815782113551262416896

noncomputable def ep125 := nat_lit 5858407469105370821111789489354285509854900621229905525354436500399662422818816

noncomputable def ep126 := BSN.sin_dyadic_bound_f 2428350216 2147483648 3 2 1048576 279083 ep123 ep64 ep124 ep125 ep66 ep124 948697 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2428350216) qz292 0 2 ep123 ep64 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2428350216) qz293 0 2 ep125 ep66 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz33 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108477865) qz33)

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep127 := @Enclosure.Real.IsNear.cos_image qz32 qz308 Bool.false 108477865 524288 435 524288 Bool.false 948697 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 116477221143449917971 562949953421312000 2886900000804896589 3485125000000000000000 108477865 524288 435 524288 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 108477865 524288) (BSN.cos_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85439977593542583255040) qz309) 226375608064910080 72057594037927936 Bool.false 948697 1048576 32 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 108477865 524288 226375608064910080 72057594037927936 32 85439977593542583255040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948697 1048576 85439977593542583255040 75557863725914323419136 2428350216 2147483648 279083 278810 (ep126 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep128 := nat_lit 1243645179865403767811557057186505905388154282913251933998311085992423326744576

noncomputable def ep129 := nat_lit 3728517181763847565742451443738387230870248465083757713959301693750167455399936

noncomputable def ep130 := BSN.cos_dyadic_bound_f 2428350216 2147483648 3 2 1048576 279083 ep128 ep57 ep124 ep129 ep60 ep124 446637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2428350216) qz287 0 2 ep128 ep57 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2428350216) qz288 0 2 ep129 ep60 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz32 qz308 Bool.false 108477865 524288 435 524288 Bool.true 446637 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 116477221143449917971 562949953421312000 2886900000804896589 3485125000000000000000 108477865 524288 435 524288 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 108477865 524288) (BSN.sin_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85439977593542583255040) qz309) 226375608064910080 72057594037927936 Bool.false 446637 1048576 32 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 108477865 524288 226375608064910080 72057594037927936 32 85439977593542583255040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 446637 1048576 85439977593542583255040 75557863725914323419136 2428350216 2147483648 279083 278810 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep120 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.false 406117263063 1099511627776 10499935181473 30655483694022656 Bool.false 191195920323 1099511627776 10485937246613 30655483694022656 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz32) 428079 1048576 1 1048576 948697 1048576 61165463 73088368640 406117263063 1099511627776 10499935181473 30655483694022656 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.false 948697 1048576 61165463 73088368640 948697 1048576 61165463 73088368640 (ep127 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 428079 1048576 1 1048576 446637 1048576 61165463 73088368640 191195920323 1099511627776 10485937246613 30655483694022656 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 446637 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 446637 1048576 61165463 73088368640 446637 1048576 61165463 73088368640 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep43 406117263063 1099511627776 10499935181473 30655483694022656 Bool.false 191195920323 1099511627776 10485937246613 30655483694022656 Bool.false 775857364512910927200256 176409540589 274877906944 42379321167341 19159677308764160 Bool.false 587584142456526114652160 267202332205 549755813888 42375006861401 19159677308764160 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep118 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep119 ep132) rfl rfl

noncomputable abbrev qz311 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz311))

noncomputable abbrev qz541 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz284 qz541)

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 8495226375 274877906944 432989992523 1368548379197440 Bool.false 51773123725 137438953472 1736736204457 5474193516789760 (BSN.cpow_neg_s_mk qz13 115476 1000 7 qz14 rfl)

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz311) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz311) (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 139405 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz541 115476 1000 0 1 4381796493761783 2251799813685248 100000000027881 13940500000000000000 126498082978408913427 562949953421312000 2886900000804896589 3485125000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000278810 139405000000000000000 4381796493761783 2251799813685248 100000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep138 := BSN.sin_dyadic_bound_f 175791983 2147483648 1 0 1048576 279083 0 1 1 0 1 1 85740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 175791983) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 175791983) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14726315) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep139 := @Enclosure.Real.IsNear.cos_image qz35 qz313 Bool.false 14726315 65536 435 524288 Bool.false 85740 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 126498082978408913427 562949953421312000 2886900000804896589 3485125000000000000000 14726315 65536 435 524288 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 14726315 65536) (BSN.cos_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 773141318999044259840) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 85740 1048576 35 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 14726315 65536 226375608064910080 72057594037927936 35 773141318999044259840 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 85740 1048576 773141318999044259840 9444732965739290427392 175791983 2147483648 279083 278810 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep140 := nat_lit 954984363500728204465037111699521

noncomputable def ep141 := BSN.cos_dyadic_bound_f 175791983 2147483648 2 1 1048576 279083 ep140 ep109 ep140 ep140 ep110 ep140 1045064 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 175791983) qz287 0 1 ep140 ep109 ep140 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 175791983) qz288 0 1 ep140 ep110 ep140 rfl rfl rfl rfl) rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.sin_image qz35 qz313 Bool.false 14726315 65536 435 524288 Bool.true 1045064 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 126498082978408913427 562949953421312000 2886900000804896589 3485125000000000000000 14726315 65536 435 524288 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 14726315 65536) (BSN.sin_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 773141318999044259840) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 1045064 1048576 35 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 14726315 65536 226375608064910080 72057594037927936 35 773141318999044259840 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045064 1048576 773141318999044259840 9444732965739290427392 175791983 2147483648 279083 278810 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep135 rfl rfl) rfl)

noncomputable def ep143 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 8495226375 274877906944 432989992523 1368548379197440 Bool.false 51773123725 137438953472 1736736204457 5474193516789760 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 396325 1048576 1 1048576 21435 262144 61165463 73088368640 8495226375 274877906944 432989992523 1368548379197440 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 85740 1048576 61165463 73088368640 21435 262144 61165463 73088368640 (ep139 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 396325 1048576 1 1048576 130633 131072 61165463 73088368640 51773123725 137438953472 1736736204457 5474193516789760 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 130633 131072 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 1045064 1048576 61165463 73088368640 130633 131072 61165463 73088368640 (ep142 rfl rfl) rfl)) rfl)

noncomputable def ep144 := @ep41 8495226375 274877906944 432989992523 1368548379197440 Bool.false 51773123725 137438953472 1736736204457 5474193516789760 Bool.false 50826235327032397398016 46226191741 68719476736 48441181062663 19159677308764160 Bool.false 65186584674494379458560 474294827105 549755813888 96907167154001 38319354617528320 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep143) rfl rfl

noncomputable abbrev qz315 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz315))

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz284 qz542)

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq qz276 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 79608062345 1099511627776 45329753329963 153277418470113280 Bool.true 23781024869 68719476736 5680362099731 19159677308764160 (BSN.cpow_neg_s_mk qz13 115476 1000 8 qz14 rfl)

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep146 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz315) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz315) (Real.sqrt qz316) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep147 := BSN.log_dyadic_bound 0 16 1 0 1 524288 139405 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep148 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz542 115476 1000 0 1 9364972152248037 4503599627370496 200000000083643 27881000000000000000 270357381063248580153 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 39279540158062550581248 18889465931478580854784 1000000000418215 139405000000000000000 9364972152248037 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep149 := nat_lit 2639981307443859030916853871653467694305161969202021312581622063296452493377536

noncomputable def ep150 := nat_lit 5436927596118708343296962307125386530408488201206840748978532172996458643456

noncomputable def ep151 := nat_lit 7909070067139339676063967690346152309854668931203650256246909125543364562845696

noncomputable def ep152 := BSN.cos_dyadic_bound_f 2930347964 2147483648 3 2 1048576 279083 ep149 ep57 ep150 ep151 ep60 ep150 214735 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2930347964) qz287 0 2 ep149 ep57 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2930347964) qz288 0 2 ep151 ep60 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62947483) qz16)

noncomputable def ep153 := @Enclosure.Real.IsNear.cos_image qz37 qz317 Bool.false 62947483 262144 869 1048576 Bool.false 214735 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 270357381063248580153 1125899906842624000 5773800002414689767 6970250000000000000000 62947483 262144 869 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 62947483 262144) (BSN.cos_reduce0 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51551226560436435419136) qz291) 226375608064910080 72057594037927936 Bool.false 214735 1048576 38 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 62947483 262144 226375608064910080 72057594037927936 38 51551226560436435419136 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 214735 1048576 51551226560436435419136 37778931862957161709568 2930347964 2147483648 279083 278810 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep154 := nat_lit 4747616811322051288975699399130541540524964754002672890047736888195217321164800

noncomputable def ep155 := nat_lit 12425431861164037371904350963511310551754246327205046493674298036040717765246976

noncomputable def ep156 := BSN.sin_dyadic_bound_f 2930347964 2147483648 3 2 1048576 279083 ep154 ep64 ep150 ep155 ep66 ep150 1026352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2930347964) qz292 0 2 ep154 ep64 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2930347964) qz293 0 2 ep155 ep66 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable def ep157 := @Enclosure.Real.IsNear.sin_image qz37 qz317 Bool.false 62947483 262144 869 1048576 Bool.false 1026352 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 270357381063248580153 1125899906842624000 5773800002414689767 6970250000000000000000 62947483 262144 869 1048576 (ep148 rfl) rfl) (Enclosure.sfrac_false_div 62947483 262144) (BSN.sin_reduce0 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51551226560436435419136) qz291) 226375608064910080 72057594037927936 Bool.false 1026352 1048576 38 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 62947483 262144 226375608064910080 72057594037927936 38 51551226560436435419136 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1026352 1048576 51551226560436435419136 37778931862957161709568 2930347964 2147483648 279083 278810 (ep156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep146 rfl rfl) rfl)

noncomputable def ep158 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 79608062345 1099511627776 45329753329963 153277418470113280 Bool.true 23781024869 68719476736 5680362099731 19159677308764160 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 370727 1048576 1 1048576 214735 1048576 122191521 146176737280 79608062345 1099511627776 45329753329963 153277418470113280 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 214735 1048576 122191521 146176737280 214735 1048576 122191521 146176737280 (ep153 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 370727 1048576 1 1048576 64147 65536 122191521 146176737280 23781024869 68719476736 5680362099731 19159677308764160 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 64147 65536 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 1026352 1048576 122191521 146176737280 64147 65536 122191521 146176737280 (ep157 rfl rfl) rfl)) rfl)

noncomputable def ep159 := @ep39 79608062345 1099511627776 45329753329963 153277418470113280 Bool.true 23781024869 68719476736 5680362099731 19159677308764160 Bool.false 56296859715347662503936 819227130201 1099511627776 432859201831267 153277418470113280 Bool.false 19519535655299326148608 284046628153 549755813888 108267891353463 38319354617528320 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep144 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep145 ep158) rfl rfl

theorem EMRow37.d6 : Enclosure.Complex.IsNear qz3 Bool.false 819227130201 1099511627776 432859201831267 153277418470113280 Bool.false 284046628153 549755813888 108267891353463 38319354617528320 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep159 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz38 := (BSN.headSumC qz272 17)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq qz38 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz39) Bool.false 750794019435 1099511627776 727489420375173 153277418470113280 Bool.false 265414407243 1099511627776 727652336028423 153277418470113280

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz39 Bool.false 121561333281 274877906944 10863756527971 2394959663595520 Bool.false 23846705553 137438953472 347772162279607 76638709235056640 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz40) Bool.false 121561333281 274877906944 10863756527971 2394959663595520 Bool.false 23846705553 137438953472 347772162279607 76638709235056640

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz40 Bool.false 450535948929 1099511627776 662141911400577 153277418470113280 Bool.true 90863868603 1099511627776 662279189359087 153277418470113280 Bool.false

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz41) Bool.false 450535948929 1099511627776 662141911400577 153277418470113280 Bool.true 90863868603 1099511627776 662279189359087 153277418470113280

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz41 Bool.false 23261454087 34359738368 156938076684507 38319354617528320 Bool.true 23679092281 274877906944 157008458086857 38319354617528320 Bool.true

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz42) Bool.false 23261454087 34359738368 156938076684507 38319354617528320 Bool.true 23679092281 274877906944 157008458086857 38319354617528320

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz42 Bool.false 137527390749 274877906944 9251921303571 2394959663595520 Bool.false 140354989307 1099511627776 592384924800839 153277418470113280 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz43) Bool.false 137527390749 274877906944 9251921303571 2394959663595520 Bool.false 140354989307 1099511627776 592384924800839 153277418470113280

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz43 Bool.false 176178165285 274877906944 39647473787309 10948387033579520 Bool.true 34211838967 274877906944 39662152297379 10948387033579520 Bool.true

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz44) Bool.false 176178165285 274877906944 39647473787309 10948387033579520 Bool.true 34211838967 274877906944 39662152297379 10948387033579520

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz44 Bool.false 404647103969 1099511627776 516300496422293 153277418470113280 Bool.false 4086898493 1099511627776 516576162281923 153277418470113280 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz45) Bool.false 404647103969 1099511627776 516300496422293 153277418470113280 Bool.false 4086898493 1099511627776 516576162281923 153277418470113280

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz45 Bool.false 274578950413 549755813888 14864875942459 4789919327191040 Bool.false 160164482403 549755813888 237939748805599 76638709235056640 Bool.true

noncomputable abbrev qz319 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep174 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz319) Bool.false 274578950413 549755813888 14864875942459 4789919327191040 Bool.false 160164482403 549755813888 237939748805599 76638709235056640

noncomputable def ep175 := @Enclosure.Complex.IsNear.addLitP qz3 qz319 Bool.false 819227130201 1099511627776 432859201831267 153277418470113280 Bool.false 284046628153 549755813888 108267891353463 38319354617528320 Bool.true

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz320))

noncomputable abbrev qz543 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz284 qz543)

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq qz319 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 270069229375 1099511627776 42816828327421 153277418470113280 Bool.true 61941072875 274877906944 21403966098673 76638709235056640 (BSN.cpow_neg_s_mk qz13 115476 1000 9 qz14 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep177 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz320) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz320) (Real.sqrt qz321) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep178 := BSN.log_dyadic_bound 1 17 2 1 867 524288 139405 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz543 115476 1000 0 1 9895417793173221 4503599627370496 200000000083643 27881000000000000000 285670816271117717049 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 41504390431577613533184 18889465931478580854784 1000000000418215 139405000000000000000 9895417793173221 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep180 := nat_lit 10017863410861996109142954800033304576

noncomputable def ep181 := BSN.sin_dyadic_bound_f 1779073032 2147483648 2 1 1048576 279083 ep180 ep113 ep180 ep180 ep114 ep180 772675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1779073032) qz292 0 1 ep180 ep113 ep180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1779073032) qz293 0 1 ep180 ep114 ep180 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8314115) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep182 := @Enclosure.Real.IsNear.cos_image qz47 qz322 Bool.false 8314115 32768 869 1048576 Bool.true 772675 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 285670816271117717049 1125899906842624000 5773800002414689767 6970250000000000000000 8314115 32768 869 1048576 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 8314115 32768) (BSN.cos_reduce1 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3912222972867709501440) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 772675 1048576 40 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 8314115 32768 226375608064910080 72057594037927936 40 3912222972867709501440 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 772675 1048576 3912222972867709501440 4722366482869645213696 1779073032 2147483648 279083 278810 (ep181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep183 := nat_lit 358035096245891204136815929154395400999984237745959371665782829630140926918656

noncomputable def ep184 := nat_lit 100357587318687546663434183993252610230395527624700351666003438794782539776

noncomputable def ep185 := nat_lit 1073904573563036237317120919095199697779491922182628714294016482012833215676416

noncomputable def ep186 := BSN.cos_dyadic_bound_f 1779073032 2147483648 3 2 1048576 279083 ep183 ep57 ep184 ep185 ep60 ep184 708860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1779073032) qz287 0 2 ep183 ep57 ep184 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1779073032) qz288 0 2 ep185 ep60 ep184 rfl rfl rfl rfl) rfl rfl

noncomputable def ep187 := @Enclosure.Real.IsNear.sin_image qz47 qz322 Bool.false 8314115 32768 869 1048576 Bool.false 708860 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 285670816271117717049 1125899906842624000 5773800002414689767 6970250000000000000000 8314115 32768 869 1048576 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 8314115 32768) (BSN.sin_reduce1 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3912222972867709501440) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 708860 1048576 40 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 8314115 32768 226375608064910080 72057594037927936 40 3912222972867709501440 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 708860 1048576 3912222972867709501440 4722366482869645213696 1779073032 2147483648 279083 278810 (ep186 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep177 rfl rfl) rfl)

noncomputable def ep188 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 270069229375 1099511627776 42816828327421 153277418470113280 Bool.true 61941072875 274877906944 21403966098673 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 349525 1048576 1 1048576 772675 1048576 122191521 146176737280 270069229375 1099511627776 42816828327421 153277418470113280 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 772675 1048576 122191521 146176737280 772675 1048576 122191521 146176737280 (ep182 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 349525 1048576 1 1048576 177215 262144 122191521 146176737280 61941072875 274877906944 21403966098673 76638709235056640 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 177215 262144 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 708860 1048576 122191521 146176737280 177215 262144 122191521 146176737280 (ep187 rfl rfl) rfl)) rfl)

noncomputable def ep189 := @ep175 270069229375 1099511627776 42816828327421 153277418470113280 Bool.true 61941072875 274877906944 21403966098673 76638709235056640 Bool.false 603805497443246434942976 274578950413 549755813888 14864875942459 4789919327191040 Bool.false 44025677689705759506432 160164482403 549755813888 237939748805599 76638709235056640 EMRow37.d6 (ep176 ep188) rfl rfl

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz324))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz284 qz544)

noncomputable def ep190 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.true 144510796857 1099511627776 1160699036103 4379354813431808 Bool.true 316242066313 1099511627776 1162761847735 4379354813431808 (BSN.cpow_neg_s_mk qz13 115476 1000 10 qz14 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep191 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz324) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz324) (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep192 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 139405 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 115476 1000 0 1 10369917190100709 4503599627370496 200000000083643 27881000000000000000 299369139361017368121 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000418215 139405000000000000000 10369917190100709 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep194 := nat_lit 717871613760411557268812437323296161

noncomputable def ep195 := BSN.sin_dyadic_bound_f 920474359 2147483648 2 1 1048576 279083 ep194 ep113 ep194 ep194 ep114 ep194 435813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 920474359) qz292 0 1 ep194 ep113 ep194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 920474359) qz293 0 1 ep194 ep114 ep194 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 278809237) qz22)

noncomputable def ep196 := @Enclosure.Real.IsNear.cos_image qz49 qz326 Bool.false 278809237 1048576 435 524288 Bool.true 435813 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 299369139361017368121 1125899906842624000 5773800002414689767 6970250000000000000000 278809237 1048576 435 524288 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 278809237 1048576) (BSN.cos_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64772624757049098502144) qz24) 226375608064910080 72057594037927936 Bool.false 435813 1048576 42 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 278809237 1048576 226375608064910080 72057594037927936 42 64772624757049098502144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 435813 1048576 64772624757049098502144 151115727451828646838272 920474359 2147483648 279083 278810 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep197 := BSN.cos_dyadic_bound_f 920474359 2147483648 2 1 1048576 279083 ep194 ep109 ep194 ep194 ep110 ep194 953717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 920474359) qz287 0 1 ep194 ep109 ep194 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 920474359) qz288 0 1 ep194 ep110 ep194 rfl rfl rfl rfl) rfl rfl

noncomputable def ep198 := @Enclosure.Real.IsNear.sin_image qz49 qz326 Bool.false 278809237 1048576 435 524288 Bool.false 953717 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 299369139361017368121 1125899906842624000 5773800002414689767 6970250000000000000000 278809237 1048576 435 524288 (ep193 rfl) rfl) (Enclosure.sfrac_false_div 278809237 1048576) (BSN.sin_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64772624757049098502144) qz24) 226375608064910080 72057594037927936 Bool.false 953717 1048576 42 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 278809237 1048576 226375608064910080 72057594037927936 42 64772624757049098502144 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953717 1048576 64772624757049098502144 151115727451828646838272 920474359 2147483648 279083 278810 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep191 rfl rfl) rfl)

noncomputable def ep199 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.true 144510796857 1099511627776 1160699036103 4379354813431808 Bool.true 316242066313 1099511627776 1162761847735 4379354813431808 (@Enclosure.Real.IsNear.mulLit_ft qz48 (Real.cos qz49) 331589 1048576 1 1048576 435813 1048576 61165463 73088368640 144510796857 1099511627776 1160699036103 4379354813431808 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.true 435813 1048576 61165463 73088368640 435813 1048576 61165463 73088368640 (ep196 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 331589 1048576 1 1048576 953717 1048576 61165463 73088368640 316242066313 1099511627776 1162761847735 4379354813431808 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 953717 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 953717 1048576 61165463 73088368640 953717 1048576 61165463 73088368640 (ep198 rfl rfl) rfl)) rfl)

noncomputable def ep200 := @ep173 144510796857 1099511627776 1160699036103 4379354813431808 Bool.true 316242066313 1099511627776 1162761847735 4379354813431808 Bool.false 222457097979899750121472 404647103969 1099511627776 516300496422293 153277418470113280 Bool.false 2246796207296855670784 4086898493 1099511627776 516576162281923 153277418470113280 (ep174 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep189 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep190 ep199) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz545 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz284 qz545)

noncomputable def ep201 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 300065557171 1099511627776 38764136600033 153277418470113280 Bool.true 140934254361 1099511627776 38693969881383 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 11 qz14 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep202 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz329) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep203 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 139405 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz545 115476 1000 0 1 10799156221662949 4503599627370496 200000000083643 27881000000000000000 311760840963187674681 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 45294944137145793642496 18889465931478580854784 1000000000418215 139405000000000000000 10799156221662949 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep205 := nat_lit 790611622847980475366322091810466721

noncomputable def ep206 := BSN.cos_dyadic_bound_f 942954633 2147483648 2 1 1048576 279083 ep205 ep109 ep205 ep205 ep110 ep205 949103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 942954633) qz287 0 1 ep205 ep109 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 942954633) qz288 0 1 ep205 ep110 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290349909) qz22)

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz51 qz330 Bool.false 290349909 1048576 869 1048576 Bool.false 949103 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 311760840963187674681 1125899906842624000 5773800002414689767 6970250000000000000000 290349909 1048576 869 1048576 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 290349909 1048576) (BSN.cos_reduce0 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66354533342914772205568) qz24) 226375608064910080 72057594037927936 Bool.false 949103 1048576 44 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 290349909 1048576 226375608064910080 72057594037927936 44 66354533342914772205568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 949103 1048576 66354533342914772205568 151115727451828646838272 942954633 2147483648 279083 278810 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := BSN.sin_dyadic_bound_f 942954633 2147483648 2 1 1048576 279083 ep205 ep113 ep205 ep205 ep114 ep205 445773 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 942954633) qz292 0 1 ep205 ep113 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 942954633) qz293 0 1 ep205 ep114 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable def ep209 := @Enclosure.Real.IsNear.sin_image qz51 qz330 Bool.false 290349909 1048576 869 1048576 Bool.false 445773 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 311760840963187674681 1125899906842624000 5773800002414689767 6970250000000000000000 290349909 1048576 869 1048576 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 290349909 1048576) (BSN.sin_reduce0 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66354533342914772205568) qz24) 226375608064910080 72057594037927936 Bool.false 445773 1048576 44 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 290349909 1048576 226375608064910080 72057594037927936 44 66354533342914772205568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 445773 1048576 66354533342914772205568 151115727451828646838272 942954633 2147483648 279083 278810 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep202 rfl rfl) rfl)

noncomputable def ep210 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 300065557171 1099511627776 38764136600033 153277418470113280 Bool.true 140934254361 1099511627776 38693969881383 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 316157 1048576 1 1048576 949103 1048576 122191521 146176737280 300065557171 1099511627776 38764136600033 153277418470113280 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 949103 1048576 122191521 146176737280 949103 1048576 122191521 146176737280 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 316157 1048576 1 1048576 445773 1048576 122191521 146176737280 140934254361 1099511627776 38693969881383 153277418470113280 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.false 445773 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.false 445773 1048576 122191521 146176737280 445773 1048576 122191521 146176737280 (ep209 rfl rfl) rfl)) rfl)

noncomputable def ep211 := @ep171 300065557171 1099511627776 38764136600033 153277418470113280 Bool.true 140934254361 1099511627776 38693969881383 153277418470113280 Bool.false 774839765164398099824640 176178165285 274877906944 39647473787309 10948387033579520 Bool.true 150465259007266225389568 34211838967 274877906944 39662152297379 10948387033579520 (ep172 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep200 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep201 ep210) rfl rfl

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz332))

noncomputable abbrev qz546 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz284 qz546)

noncomputable def ep212 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.true 4831346817 34359738368 18529165203109 76638709235056640 Bool.false 277202345175 1099511627776 37114792637533 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 12 qz14 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep213 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz332) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz332) (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep214 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 139405 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz546 115476 1000 0 1 11191020447815397 4503599627370496 200000000083643 27881000000000000000 323073569307982695993 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000418215 139405000000000000000 11191020447815397 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep216 := nat_lit 967478094873269648226615863008207361955581056757644162338112058209368256086016

noncomputable def ep217 := nat_lit 732094728408916858200509465790241011292449741521992068841262376886154100736

noncomputable def ep218 := nat_lit 2900970095162991110963446570093041603844158270789888502876653649874332460056576

noncomputable def ep219 := BSN.cos_dyadic_bound_f 2280714428 2147483648 3 2 1048576 279083 ep216 ep57 ep217 ep218 ep60 ep217 510752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2280714428) qz287 0 2 ep216 ep57 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2280714428) qz288 0 2 ep218 ep60 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75221427) qz16)

noncomputable def ep220 := @Enclosure.Real.IsNear.cos_image qz53 qz334 Bool.false 75221427 262144 869 1048576 Bool.true 510752 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 323073569307982695993 1125899906842624000 5773800002414689767 6970250000000000000000 75221427 262144 869 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 75221427 262144) (BSN.cos_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40122752535925520072704) qz291) 226375608064910080 72057594037927936 Bool.false 510752 1048576 45 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 75221427 262144 226375608064910080 72057594037927936 45 40122752535925520072704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 510752 1048576 40122752535925520072704 37778931862957161709568 2280714428 2147483648 279083 278810 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep221 := nat_lit 1740874894989158233321348145842141058711011942370541898553528694875353937674240

noncomputable def ep222 := nat_lit 4558248952554180936166444319022899525462938739960383651909689299872873206317056

noncomputable def ep223 := BSN.sin_dyadic_bound_f 2280714428 2147483648 3 2 1048576 279083 ep221 ep64 ep217 ep222 ep66 ep217 915775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2280714428) qz292 0 2 ep221 ep64 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2280714428) qz293 0 2 ep222 ep66 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.sin_image qz53 qz334 Bool.false 75221427 262144 869 1048576 Bool.true 915775 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 323073569307982695993 1125899906842624000 5773800002414689767 6970250000000000000000 75221427 262144 869 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 75221427 262144) (BSN.sin_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40122752535925520072704) qz291) 226375608064910080 72057594037927936 Bool.false 915775 1048576 45 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 75221427 262144 226375608064910080 72057594037927936 45 40122752535925520072704 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 915775 1048576 40122752535925520072704 37778931862957161709568 2280714428 2147483648 279083 278810 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep213 rfl rfl) rfl)

noncomputable def ep225 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.true 4831346817 34359738368 18529165203109 76638709235056640 Bool.false 277202345175 1099511627776 37114792637533 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz53) 302697 1048576 1 1048576 15961 32768 122191521 146176737280 4831346817 34359738368 18529165203109 76638709235056640 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.true 510752 1048576 122191521 146176737280 15961 32768 122191521 146176737280 (ep220 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 302697 1048576 1 1048576 915775 1048576 122191521 146176737280 277202345175 1099511627776 37114792637533 153277418470113280 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.true 915775 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.true 915775 1048576 122191521 146176737280 915775 1048576 122191521 146176737280 (ep224 rfl rfl) rfl)) rfl)

noncomputable def ep226 := @ep169 4831346817 34359738368 18529165203109 76638709235056640 Bool.false 277202345175 1099511627776 37114792637533 153277418470113280 Bool.false 4725405164569343557632 137527390749 274877906944 9251921303571 2394959663595520 Bool.false 38580485689855661047808 140354989307 1099511627776 592384924800839 153277418470113280 (ep170 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep212 ep225) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz336))

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz284 qz547)

noncomputable def ep227 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 48564241947 274877906944 8907335827371 38319354617528320 Bool.true 235071358431 1099511627776 35648907546589 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 13 qz14 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep228 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz336) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz336) (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep229 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 139405 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz547 115476 1000 0 1 11551497052968677 4503599627370496 200000000083643 27881000000000000000 333480168422152736313 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000418215 139405000000000000000 11551497052968677 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep231 := nat_lit 456234750445617800423717539383107676734921206249146453708495334928439365358721

noncomputable def ep232 := nat_lit 162932973874001508351069220028624402839001955119805070216402914236244186241

noncomputable def ep233 := nat_lit 1368378385389105398254450479709265781399085614837199750985053198956845607703681

noncomputable def ep234 := BSN.cos_dyadic_bound_f 1890171119 2147483648 3 2 1048576 279083 ep231 ep57 ep232 ep233 ep60 ep232 667956 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1890171119) qz287 0 2 ep231 ep57 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1890171119) qz288 0 2 ep233 ep60 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 310577609) qz22)

noncomputable def ep235 := @Enclosure.Real.IsNear.cos_image qz55 qz338 Bool.false 310577609 1048576 869 1048576 Bool.false 667956 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 333480168422152736313 1125899906842624000 5773800002414689767 6970250000000000000000 310577609 1048576 869 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 310577609 1048576) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133008967957650769707008) qz24) 226375608064910080 72057594037927936 Bool.false 667956 1048576 47 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 310577609 1048576 226375608064910080 72057594037927936 47 133008967957650769707008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 667956 1048576 133008967957650769707008 151115727451828646838272 1890171119 2147483648 279083 278810 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep236 := nat_lit 12764520119221149488480049961695289921

noncomputable def ep237 := BSN.sin_dyadic_bound_f 1890171119 2147483648 2 1 1048576 279083 ep236 ep113 ep236 ep236 ep114 ep236 808297 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1890171119) qz292 0 1 ep236 ep113 ep236 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1890171119) qz293 0 1 ep236 ep114 ep236 rfl rfl rfl rfl) rfl rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.sin_image qz55 qz338 Bool.false 310577609 1048576 869 1048576 Bool.false 808297 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 333480168422152736313 1125899906842624000 5773800002414689767 6970250000000000000000 310577609 1048576 869 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 310577609 1048576) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 133008967957650769707008) qz24) 226375608064910080 72057594037927936 Bool.false 808297 1048576 47 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 310577609 1048576 226375608064910080 72057594037927936 47 133008967957650769707008 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 808297 1048576 133008967957650769707008 151115727451828646838272 1890171119 2147483648 279083 278810 (ep237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep228 rfl rfl) rfl)

noncomputable def ep239 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 48564241947 274877906944 8907335827371 38319354617528320 Bool.true 235071358431 1099511627776 35648907546589 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 290823 1048576 1 1048576 166989 262144 122191521 146176737280 48564241947 274877906944 8907335827371 38319354617528320 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 667956 1048576 122191521 146176737280 166989 262144 122191521 146176737280 (ep235 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 290823 1048576 1 1048576 808297 1048576 122191521 146176737280 235071358431 1099511627776 35648907546589 153277418470113280 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 808297 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 808297 1048576 122191521 146176737280 808297 1048576 122191521 146176737280 (ep238 rfl rfl) rfl)) rfl)

noncomputable def ep240 := @ep167 48564241947 274877906944 8907335827371 38319354617528320 Bool.true 235071358431 1099511627776 35648907546589 153277418470113280 Bool.false 51152478495268115841024 23261454087 34359738368 156938076684507 38319354617528320 Bool.true 104141749192561707188224 23679092281 274877906944 157008458086857 38319354617528320 (ep168 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep227 ep239) rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz284 qz548)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.true 293830581855 1099511627776 34389604662549 153277418470113280 Bool.false 3852500521 1099511627776 34245357011659 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 14 qz14 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep242 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz341) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep243 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 139405 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz548 115476 1000 0 1 11885250371606245 4503599627370496 200000000083643 27881000000000000000 68623058595580137381 225179981368524800 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 49850353174629559828480 18889465931478580854784 1000000000418215 139405000000000000000 11885250371606245 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep245 := BSN.cos_dyadic_bound_f 28156194 2147483648 1 0 1048576 279083 0 1 1 0 1 1 1048485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 28156194) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 28156194) qz288 0 0 rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159775509) qz33)

noncomputable def ep246 := @Enclosure.Real.IsNear.cos_image qz57 qz342 Bool.false 159775509 524288 869 1048576 Bool.true 1048485 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 68623058595580137381 225179981368524800 5773800002414689767 6970250000000000000000 159775509 524288 869 1048576 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 159775509 524288) (BSN.cos_reduce2 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 990658030300810969088) qz309) 226375608064910080 72057594037927936 Bool.false 1048485 1048576 48 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 159775509 524288 226375608064910080 72057594037927936 48 990658030300810969088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048485 1048576 990658030300810969088 75557863725914323419136 28156194 2147483648 279083 278810 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep247 := BSN.sin_dyadic_bound_f 28156194 2147483648 1 0 1048576 279083 0 1 1 0 1 1 13747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 28156194) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 28156194) qz293 0 0 rfl) rfl rfl

noncomputable def ep248 := @Enclosure.Real.IsNear.sin_image qz57 qz342 Bool.false 159775509 524288 869 1048576 Bool.true 13747 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 68623058595580137381 225179981368524800 5773800002414689767 6970250000000000000000 159775509 524288 869 1048576 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 159775509 524288) (BSN.sin_reduce2 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 990658030300810969088) qz309) 226375608064910080 72057594037927936 Bool.false 13747 1048576 48 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 159775509 524288 226375608064910080 72057594037927936 48 990658030300810969088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13747 1048576 990658030300810969088 75557863725914323419136 28156194 2147483648 279083 278810 (ep247 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep242 rfl rfl) rfl)

noncomputable def ep249 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.true 293830581855 1099511627776 34389604662549 153277418470113280 Bool.false 3852500521 1099511627776 34245357011659 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz57) 280243 1048576 1 1048576 1048485 1048576 122191521 146176737280 293830581855 1099511627776 34389604662549 153277418470113280 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.true 1048485 1048576 122191521 146176737280 1048485 1048576 122191521 146176737280 (ep246 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 280243 1048576 1 1048576 13747 1048576 122191521 146176737280 3852500521 1099511627776 34245357011659 153277418470113280 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.true 13747 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.true 13747 1048576 122191521 146176737280 13747 1048576 122191521 146176737280 (ep248 rfl rfl) rfl)) rfl)

noncomputable def ep250 := @ep165 293830581855 1099511627776 34389604662549 153277418470113280 Bool.false 3852500521 1099511627776 34245357011659 153277418470113280 Bool.false 15480297330579049807872 450535948929 1099511627776 662141911400577 153277418470113280 Bool.true 24976470018427277279232 90863868603 1099511627776 662279189359087 153277418470113280 (ep166 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep240 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep241 ep249) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz284 qz549)

noncomputable def ep251 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 35709384195 1099511627776 33138506389567 153277418470113280 Bool.false 281637513027 1099511627776 33265135200127 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 15 qz14 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep252 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep253 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 139405 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 115476 1000 0 1 12195965485668069 4503599627370496 200000000083643 27881000000000000000 352085327605751483961 1125899906842624000 5773800002414689767 6970250000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000418215 139405000000000000000 12195965485668069 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep255 := BSN.sin_dyadic_bound_f 270840824 2147483648 1 0 1048576 279083 0 1 1 0 1 1 131895 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 270840824) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 270840824) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 327905013) qz22)

noncomputable def ep256 := @Enclosure.Real.IsNear.cos_image qz59 qz346 Bool.false 327905013 1048576 435 524288 Bool.false 131895 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 352085327605751483961 1125899906842624000 5773800002414689767 6970250000000000000000 327905013 1048576 435 524288 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 327905013 1048576) (BSN.cos_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19058728659005437116416) qz24) 226375608064910080 72057594037927936 Bool.false 131895 1048576 49 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 327905013 1048576 226375608064910080 72057594037927936 49 19058728659005437116416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 131895 1048576 19058728659005437116416 151115727451828646838272 270840824 2147483648 279083 278810 (ep255 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep257 := nat_lit 5380919632912331052493016641048576

noncomputable def ep258 := BSN.cos_dyadic_bound_f 270840824 2147483648 2 1 1048576 279083 ep257 ep109 ep257 ep257 ep110 ep257 1040247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 270840824) qz287 0 1 ep257 ep109 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 270840824) qz288 0 1 ep257 ep110 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable def ep259 := @Enclosure.Real.IsNear.sin_image qz59 qz346 Bool.false 327905013 1048576 435 524288 Bool.true 1040247 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 352085327605751483961 1125899906842624000 5773800002414689767 6970250000000000000000 327905013 1048576 435 524288 (ep254 rfl) rfl) (Enclosure.sfrac_false_div 327905013 1048576) (BSN.sin_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19058728659005437116416) qz24) 226375608064910080 72057594037927936 Bool.false 1040247 1048576 49 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 327905013 1048576 226375608064910080 72057594037927936 49 19058728659005437116416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040247 1048576 19058728659005437116416 151115727451828646838272 270840824 2147483648 279083 278810 (ep258 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep252 rfl rfl) rfl)

noncomputable def ep260 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 35709384195 1099511627776 33138506389567 153277418470113280 Bool.false 281637513027 1099511627776 33265135200127 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 270741 1048576 1 1048576 131895 1048576 61165463 73088368640 35709384195 1099511627776 33138506389567 153277418470113280 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 131895 1048576 61165463 73088368640 131895 1048576 61165463 73088368640 (ep256 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 270741 1048576 1 1048576 1040247 1048576 61165463 73088368640 281637513027 1099511627776 33265135200127 153277418470113280 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.true 1040247 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.true 1040247 1048576 61165463 73088368640 1040247 1048576 61165463 73088368640 (ep259 rfl rfl) rfl)) rfl)

noncomputable def ep261 := @ep163 35709384195 1099511627776 33138506389567 153277418470113280 Bool.false 281637513027 1099511627776 33265135200127 153277418470113280 Bool.false 534632397721652611252224 121561333281 274877906944 10863756527971 2394959663595520 Bool.false 209757840317392065921024 23846705553 137438953472 347772162279607 76638709235056640 (ep164 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep251 ep260) rfl rfl

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz348))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz284 qz550)

noncomputable def ep262 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 264548686311 1099511627776 32209002585029 153277418470113280 Bool.false 74640762819 1099511627776 32108011469209 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 16 qz14 rfl)

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep263 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz348) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz348) (Real.sqrt qz349) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep264 := BSN.log_dyadic_bound 0 32 1 0 1 524288 139405 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 115476 1000 0 1 3121657384082679 1125899906842624 50000000027881 6970250000000000000 90119127021082860051 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 52372720210750067441664 18889465931478580854784 1000000000557620 139405000000000000000 3121657384082679 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep264 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep266 := nat_lit 3859915890958281857847193811302765934974445757425345080392188934146650978717825

noncomputable def ep267 := nat_lit 3595371307535441009244270754374940937166290890039537096653862745186266058881

noncomputable def ep268 := nat_lit 10103482446583299866061016876952541830082422036577744531442102859272831942070401

noncomputable def ep269 := BSN.sin_dyadic_bound_f 2782710127 2147483648 3 2 1048576 279083 ep266 ep64 ep267 ep268 ep66 ep267 1009177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2782710127) qz292 0 2 ep266 ep64 ep267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2782710127) qz293 0 2 ep268 ep66 ep267 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 335719909) qz22)

noncomputable def ep270 := @Enclosure.Real.IsNear.cos_image qz61 qz350 Bool.false 335719909 1048576 435 524288 Bool.false 1009177 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 90119127021082860051 281474976710656000 1443450000804896589 1742562500000000000000 335719909 1048576 435 524288 (ep265 rfl) rfl) (Enclosure.sfrac_false_div 335719909 1048576) (BSN.cos_reduce3 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195815817083174579601408) qz24) 226375608064910080 72057594037927936 Bool.false 1009177 1048576 50 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 335719909 1048576 226375608064910080 72057594037927936 50 195815817083174579601408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1009177 1048576 195815817083174579601408 151115727451828646838272 2782710127 2147483648 279083 278810 (ep269 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep271 := nat_lit 2145995660002394561474771793281258826513432661187431505594173346857111106424961

noncomputable def ep272 := nat_lit 6430796237392112802405826838335026597665965401782215442589212315080960787157121

noncomputable def ep273 := BSN.cos_dyadic_bound_f 2782710127 2147483648 3 2 1048576 279083 ep271 ep57 ep267 ep272 ep60 ep267 284733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2782710127) qz287 0 2 ep271 ep57 ep267 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2782710127) qz288 0 2 ep272 ep60 ep267 rfl rfl rfl rfl) rfl rfl

noncomputable def ep274 := @Enclosure.Real.IsNear.sin_image qz61 qz350 Bool.false 335719909 1048576 435 524288 Bool.true 284733 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 90119127021082860051 281474976710656000 1443450000804896589 1742562500000000000000 335719909 1048576 435 524288 (ep265 rfl) rfl) (Enclosure.sfrac_false_div 335719909 1048576) (BSN.sin_reduce3 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195815817083174579601408) qz24) 226375608064910080 72057594037927936 Bool.false 284733 1048576 50 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 335719909 1048576 226375608064910080 72057594037927936 50 195815817083174579601408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 284733 1048576 195815817083174579601408 151115727451828646838272 2782710127 2147483648 279083 278810 (ep273 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep263 rfl rfl) rfl)

noncomputable def ep275 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 264548686311 1099511627776 32209002585029 153277418470113280 Bool.false 74640762819 1099511627776 32108011469209 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 262143 1048576 1 1048576 1009177 1048576 61165463 73088368640 264548686311 1099511627776 32209002585029 153277418470113280 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 1009177 1048576 61165463 73088368640 1009177 1048576 61165463 73088368640 (ep270 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 262143 1048576 1 1048576 284733 1048576 61165463 73088368640 74640762819 1099511627776 32108011469209 153277418470113280 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 284733 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 284733 1048576 61165463 73088368640 284733 1048576 61165463 73088368640 (ep274 rfl rfl) rfl)) rfl)

noncomputable def ep276 := @ep161 264548686311 1099511627776 32209002585029 153277418470113280 Bool.false 74640762819 1099511627776 32108011469209 153277418470113280 Bool.false 206376688608365657456640 750794019435 1099511627776 727489420375173 153277418470113280 Bool.false 36478278367869136797696 265414407243 1099511627776 727652336028423 153277418470113280 (ep162 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep261 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep262 ep275) rfl rfl

theorem EMRow37.d7 : Enclosure.Complex.IsNear qz38 Bool.false 750794019435 1099511627776 727489420375173 153277418470113280 Bool.false 265414407243 1099511627776 727652336028423 153277418470113280 := ep160 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep276 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow37.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow37.d9 : @Eq Nat (Nat.pow 24 1) 24 := @Eq.refl Nat 24

noncomputable def ep277 := nat_lit 705795700984307885721396746867

noncomputable def ep278 := nat_lit 461224745984066651317107425280

noncomputable def ep279 := nat_lit 906603586957353337253107953110740718417

noncomputable def ep280 := nat_lit 134449923955461868063531619660888801280000

noncomputable abbrev qz581 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz551 := qz581

noncomputable abbrev qz352 := qz551

noncomputable abbrev qz62 := qz352

noncomputable abbrev qz552 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz353 := qz552

noncomputable abbrev qz63 := qz353

noncomputable abbrev qz582 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz583 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz553 := (@HAdd.hAdd Complex Complex Complex qz579 (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz580) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz354 := qz553

noncomputable abbrev qz64 := (Complex.Stirling.logGammaStirling 1 qz354)

noncomputable abbrev qz554 := (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz580) (2 : Complex))))

noncomputable abbrev qz355 := qz554

noncomputable abbrev qz65 := qz355

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz356 := (@instHSub Real Real.instSub)

noncomputable def ep281 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66))) (zetaApproximant qz5 1 24))

noncomputable def ep282 := @Enclosure.Real.IsNear.of_eq ep281 (@HSub.hSub Real Real Real qz356 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24))))

noncomputable def ep283 := nat_lit 705789350333700611825529946087

noncomputable def ep284 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24))) ep283

noncomputable def ep285 := nat_lit 903091082367136804825273703932740985331

noncomputable def ep286 := nat_lit 23061237299203332565855371264

noncomputable def ep287 := nat_lit 585417431702755404639041529666622181

noncomputable def ep288 := nat_lit 22408320659243644677255269943481466880000

noncomputable def ep289 := nat_lit 16276522145156683278748933889256693748530801511068113829888

noncomputable def ep290 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 24)) 1048575 1048576 50537351

noncomputable def ep291 := nat_lit 50482036358894257336780627

noncomputable def ep292 := nat_lit 32989364575200079773696000

noncomputable def ep293 := nat_lit 5689506823211708778725592719

noncomputable def ep294 := nat_lit 919776473721153424170418176000

noncomputable def ep295 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.true 1048575 1048576 50537351

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28824183) qz16)

noncomputable def ep296 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz357 Bool.false 28824183 262144 355

noncomputable def ep297 := nat_lit 1232448534798857948579363

noncomputable def ep298 := nat_lit 3654418432000000000000000000

noncomputable def ep299 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) Bool.false 495195695534484542817 4503599627370496000 ep297 ep298

noncomputable def ep300 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66 158571680769265117869 900719925474099200 427551945798857948579363 ep298 2165781249 32768000

noncomputable def ep301 := nat_lit 3245314510254797899805491200

noncomputable def ep302 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 408880462804607367577 4503599627370496000 791815207853595174545283 ep298 Bool.false 158571680769265117869 900719925474099200

noncomputable def ep303 := @Enclosure.Complex.IsNear.subLitP qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 372346927765824234577 4503599627370496000 778708007813396571793283 ep298 Bool.false 161377979465228263469 900719925474099200 401337545795203530147363

noncomputable def ep304 := nat_lit 1841433899925905690448484905036808192

noncomputable def ep305 := nat_lit 44633960151498476958576817748312064

noncomputable abbrev qz584 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz555 := qz584

noncomputable abbrev qz358 := (@HSub.hSub Complex Complex Complex qz552 qz553 qz555)

noncomputable abbrev qz359 := (Complex.log qz553)

noncomputable abbrev qz67 := (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 qz358 qz359) qz354)

noncomputable abbrev qz360 := qz555

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz352 qz360 ↑(Real.log qz271))

noncomputable abbrev qz556 := qz583

noncomputable abbrev qz361 := qz556

noncomputable abbrev qz69 := qz361

noncomputable abbrev qz70 := (@instHMul Nat instMulNat)

noncomputable abbrev qz557 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz362 := qz557

noncomputable abbrev qz71 := qz362

noncomputable abbrev qz72 := qz354

noncomputable abbrev qz363 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz73 := qz363

noncomputable abbrev qz364 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz74 := qz364

noncomputable abbrev qz365 := (@instHSub Int Int.instSub)

noncomputable abbrev qz366 := (@instHMul Int Int.instMul)

noncomputable def ep306 := @Enclosure.Complex.IsNear.of_eq qz64 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 372346927765824234577

noncomputable def ep307 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 372347180682748650577 4503599627370496000

noncomputable def ep308 := nat_lit 12793743020162315471939579150336

noncomputable def ep309 := nat_lit 3465565720488574803871132549120000

noncomputable def ep310 := @ep307 23764272727681676731 111524000000000000000000 Bool.false 806896387511644397793 4503599627370496000 1530950004439129177 13940500000000000000000 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000 Bool.true ep308 372346927765824234577 4503599627370496000 778708007813396571793283 ep298 Bool.false ep309

noncomputable def ep311 := @Enclosure.Complex.IsNear.addLitP qz67 qz68 Bool.true 376485708089959146577 4503599627370496000 2930650000536625607 13940500000000000000000

noncomputable def ep312 := nat_lit 48804289666449231128428544

noncomputable def ep313 := @ep311 Bool.false 806896387511644397793 4503599627370496000 1530950004439129177 13940500000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep312 372347180682748650577 4503599627370496000 23764272727681676731 111524000000000000000000 Bool.false 806896387511644397793 806896387511644397793 4503599627370496000

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz352 qz358 qz359)

noncomputable def ep314 := @Enclosure.Complex.IsNear.subLitP qz75 qz72 Bool.true 366352608928375530577 4503599627370496000 2930650000536625607 13940500000000000000000 Bool.false 1066925222796762095841

noncomputable def ep315 := nat_lit 1505942832359836586308000

noncomputable def ep316 := nat_lit 3227585550046577591172000

noncomputable def ep317 := @ep314 4503599627370496000 1530950004439129177 13940500000000000000000 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 Bool.true ep315 376485708089959146577 4503599627370496000 2930650000536625607 13940500000000000000000 Bool.false ep316 806896387511644397793 4503599627370496000 1530950004439129177 13940500000000000000000

noncomputable abbrev qz76 := qz358

noncomputable abbrev qz77 := qz359

noncomputable def ep318 := @Enclosure.Complex.IsNear.mul qz76 qz77 Bool.true 366352608928375530577 4503599627370496000 2930650000536625607 13940500000000000000000 Bool.false 1066925222796762095841 4503599627370496000 1530950004439129177

noncomputable abbrev qz78 := (Complex.re qz358)

noncomputable abbrev qz79 := (Complex.re qz359)

noncomputable abbrev qz80 := (Complex.im qz358)

noncomputable abbrev qz81 := (Complex.im qz359)

noncomputable def ep319 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz78 qz79) (@HMul.hMul Real Real Real qz0 qz80 qz81) 255774911805634123 36028797018963968 100000000306691 31864000000000000000 24895279556504987247 281474976710656000

noncomputable def ep320 := nat_lit 824952736528020542710015857677828096

noncomputable def ep321 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz79 7000 4000 0 1 36539273115090589 9007199254740992 100000000306691 55762000000000000000

noncomputable def ep322 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable abbrev qz367 := (Enclosure.sfrac Bool.false 230952 4000)

noncomputable abbrev qz82 := qz367

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz82) Bool.false 7000 4000 0 1 Bool.false 230952 4000 0

noncomputable abbrev qz368 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz83 := qz368

noncomputable abbrev qz369 := (Complex.log (Complex.mk qz83 qz82))

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq qz77 qz369 Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000

noncomputable def ep325 := nat_lit 2877393316316620227867606925209761048760752183259889660789518634065530307852027140002283520

noncomputable def ep326 := nat_lit 57046800954069501173890297079055609033886471464218043285667834347954960254033644102877184

noncomputable def ep327 := nat_lit 3474217539500180090565393951674276488063740703129816472597617740632030035819395809280

noncomputable def ep328 := BSN.log_dyadic_bound 20651826304 86187826304 5 4 ep325 1048576 278810 ep326 ep327 512470 106839652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20651826304) (BSN.artanhQ 86187826304) 0 4 ep326 ep325 ep327 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz84 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz370 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz371 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 53419826304 16000000))

noncomputable def ep329 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz558 1 2 0 1 36539273115090589 4503599627370496 100000000306691 27881000000000000000 36539273115090589 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 53419826304 16000000 36539273115090589 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53419826304) qz371)) Bool.false 306513638767433835610112 37778931862957161709568 1000000003066910 278810000000000000000 36539273115090589 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 53419826304 16000000 11 106839652608 65536000000 512470 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep328 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep330 := BSN.arctan_dyadic_bound_f 9000 230952 1 0 1048576 278810 0 1 1 0 1 1 40841 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz86 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz370 BSN.pi_near_15 rfl)

noncomputable abbrev qz372 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 230952)))

noncomputable def ep331 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz372 884279719003555 562949953421312 1 2000000000000000 40841 1048576 1 278810 904243051586191884288 862353374086563 562949953421312 200000000027881 55762000000000000000 qz86 (ep330 rfl) rfl rfl

noncomputable abbrev qz373 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230952) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep332 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (ep324 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 115476 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz369 Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz369) (@HMul.hMul Real Real Real qz0 qz84 qz558) Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 9000 230952 4000 53419826304 16000000 rfl rfl rfl) (ep329 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz369) qz373 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 9000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz356 qz85 qz372) Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 230952 9000 rfl rfl) ep331))))

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz81 230952 4000 0 1 862353374086563 562949953421312 200000000027881 55762000000000000000

noncomputable def ep334 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable def ep335 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (ep324 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz13 Bool.false 115476 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz369 Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz369) (@HMul.hMul Real Real Real qz0 qz84 qz558) Bool.false 36539273115090589 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 9000 230952 4000 53419826304 16000000 rfl rfl rfl) (ep329 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz369) qz373 Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 9000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz373 (@HSub.hSub Real Real Real qz356 qz85 qz372) Bool.false 862353374086563 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 230952 9000 rfl rfl) ep331))))

noncomputable abbrev qz374 := (Enclosure.Real.IsNear.const Bool.false 230952 4000)

noncomputable abbrev qz87 := (@ep323 1 (BSN.w_sub_half_mk qz284 Bool.false 115476 1000 2 qz286 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz367 Bool.false 7000 4000 0 1 Bool.false 230952 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz374))

noncomputable def ep336 := @ep319 5773800000804896589 27881000000000000000000 ep320 366352608928375530577 4503599627370496000 2930650000536625607 13940500000000000000000 (@ep321 255774911805634123 36028797018963968 100000000306691 31864000000000000000 (ep322 qz87) ep332 rfl) (@ep333 24895279556504987247 281474976710656000 5773800000804896589 27881000000000000000000 (ep334 qz87) ep335 rfl) rfl

noncomputable def ep337 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz78 qz81) (@HMul.hMul Real Real Real qz0 qz80 qz79) 6036473618605941 2251799813685248 200000000027881 31864000000000000000 1054852275559550213841 4503599627370496000

noncomputable def ep338 := nat_lit 2402502017909840599491287510383853568

noncomputable def ep339 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz81 7000 4000 0 1 862353374086563 562949953421312 200000000027881 55762000000000000000

noncomputable def ep340 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz79 230952 4000 0 1 36539273115090589 9007199254740992 100000000306691 55762000000000000000

noncomputable def ep341 := @ep337 2886900008853862479 27881000000000000000000 ep338 1066925222796762095841 4503599627370496000 1530950004439129177 13940500000000000000000 (@ep339 6036473618605941 2251799813685248 200000000027881 31864000000000000000 (ep322 qz87) ep335 rfl) (@ep340 1054852275559550213841 4503599627370496000 2886900008853862479 27881000000000000000000 (ep334 qz87) ep332 rfl) rfl

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk qz83 qz82) Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 115476 1000 2 qz14 rfl)

noncomputable abbrev qz375 := (ep342 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 230952 4000) Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 230952 4000)))

noncomputable abbrev qz88 := qz375

noncomputable def ep343 := ep317 (@ep318 13940500000000000000000 (ep336 rfl) (ep341 rfl)) qz88 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz89 := qz360

noncomputable def ep344 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz90 := (@Enclosure.Complex.IsNear.of_eq qz360 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz370 qz295))

noncomputable def ep346 := ep345 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow37.d4)

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep348 := ep347 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz19)

noncomputable def ep349 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep351 := ep350 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz19)

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep353 := ep352 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow37.d4)

noncomputable def ep354 := @ep313 1530950004439129177 13940500000000000000000 (ep343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep344 131072 3 1048576 (ep346 rfl) (ep348 rfl) rfl rfl) (@ep349 1 0 1 (ep351 rfl) (ep353 rfl) rfl rfl))

noncomputable abbrev qz91 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz376 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz92 := (@HMul.hMul Complex Complex Complex qz352 (@HMul.hMul Complex Complex Complex qz352 (2 : Complex) qz376) (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 (2 : Complex) qz376) (1 : Complex)))

noncomputable abbrev qz377 := (@HPow.hPow Complex Int Complex qz557 qz553 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz93 := qz377

noncomputable def ep355 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93)) Bool.false 1929603 34359738368 3 34359738368

noncomputable def ep356 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93) Bool.false 0 1 0 1 Bool.false

noncomputable def ep357 := @ep356 0 1 0 1 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000 Bool.false 1929603 1929603 34359738368 3 34359738368 Bool.true 6189523223 6189523223 4294967296000 9623

noncomputable def ep358 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep359 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93 Bool.false 1929603 34359738368 3 34359738368 Bool.true 6189523223 4294967296000 9623 4294967296000

noncomputable abbrev qz94 := (Complex.re qz377)

noncomputable abbrev qz95 := (Complex.im qz377)

noncomputable def ep360 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) 1929603 34359738368 3 34359738368 0 1 0

noncomputable def ep361 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 1 12 0 1 5788809 8589934592 9 8589934592 1929603

noncomputable def ep362 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz378 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz19)

noncomputable def ep363 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep362 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep364 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869 1073741824000

noncomputable abbrev qz559 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz379 := (@HPow.hPow Complex Nat Complex qz559 qz553 1)

noncomputable abbrev qz96 := (@Inv.inv Complex Complex.instInv qz379)

noncomputable def ep365 := @Enclosure.Complex.IsNear.of_eq qz93 qz96 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869

noncomputable def ep366 := @Enclosure.Complex.IsNear.of_parts qz96 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869

noncomputable abbrev qz97 := (Complex.re qz379)

noncomputable abbrev qz98 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz100 := qz379

noncomputable def ep367 := @Enclosure.Real.IsNear.mulLit_ff qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 9000 4000 0 1 643201 2147483648 1 2147483648

noncomputable def ep368 := @Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable def ep369 := @Enclosure.Complex.IsNear.of_eq qz100 qz72 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0

noncomputable def ep370 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) Bool.false 643201 2147483648 1 2147483648 643201 2147483648 1

noncomputable abbrev qz101 := (Complex.im qz379)

noncomputable abbrev qz380 := (@instHAdd Real Real.instAdd)

noncomputable def ep371 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101)) Bool.false 417342393 125000 0 1

noncomputable def ep372 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101) 81 16 0 1 833419161 250000

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz97 9000 4000 0 1 9000 4000 0 1

noncomputable def ep374 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 230952 4000 0 1 230952 4000 0 1

noncomputable def ep375 := @Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 230952 4000 0 1

noncomputable abbrev qz102 := (ep368 (@ep369 1 (BSN.pow_one_c qz354) qz375))

noncomputable abbrev qz103 := (ep375 (@ep369 1 (BSN.pow_one_c qz354) qz375))

noncomputable def ep376 := @ep372 0 1 13354956576 417342393 125000 0 1 (@ep373 81 16 0 1 qz102 qz102 rfl) (@ep374 833419161 250000 0 1 qz103 qz103 rfl)

noncomputable def ep377 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) 417342393 125000 0 1 321600 321601 1073741824 (ep371 (Enclosure.Complex.normSq_eq_mul_add_mul qz100) (ep376 rfl rfl)) rfl

noncomputable def ep378 := @Enclosure.Real.IsNear.of_eq (Complex.re qz96) (@HMul.hMul Real Real Real qz0 qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.false 5788809 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz100) (@ep367 5788809 8589934592 9 8589934592 qz102 (@ep370 2147483648 (ep377 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep379 := @Enclosure.Real.IsNear.of_eq (Complex.im qz96) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.true 18568569669 1073741824000 28869 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz100)

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 230952 4000 0 1 643201 2147483648 1

noncomputable def ep381 := @ep380 2147483648 18568569669 1073741824000 28869 1073741824000 (@Enclosure.Real.IsNear.neg qz101 Bool.false 230952 4000 0 1 qz103) (@ep370 2147483648 (ep377 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 0 1 0 1 18568569669 1073741824000 28869 1073741824000 0

noncomputable def ep383 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep362 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz378)

noncomputable def ep384 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 5788809 8589934592 9 8589934592 Bool.true 18568569669 1073741824000 28869 1073741824000

noncomputable abbrev qz104 := (@ep365 1073741824000 (BSN.zpow_one_sub_two_mul qz354 1 1 rfl rfl) (@ep366 1073741824000 ep378 (ep379 ep381)))

noncomputable def ep385 := @ep360 1 1929603 1929603 34359738368 3 34359738368 (@ep361 34359738368 3 34359738368 ep363 (ep364 qz104) rfl) (@ep382 1 0 1 ep383 (ep384 qz104) rfl) rfl

noncomputable def ep386 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) 6189523223 4294967296000 9623 4294967296000 0 1 0

noncomputable def ep387 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 1 12 0 1 18568569669 1073741824000 28869 1073741824000 6189523223

noncomputable def ep388 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 0 1 0 1 5788809 8589934592 9 8589934592 0

noncomputable def ep389 := @ep386 1 6189523223 6189523223 4294967296000 9623 4294967296000 (@ep387 4294967296000 9623 4294967296000 ep363 (ep384 qz104) rfl) (@ep388 1 0 1 ep383 (ep364 qz104) rfl) rfl

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep390 := @ep357 4294967296000 (@ep358 0 1 0 1 (BSN.stirling_sum_base qz72) qz105) (ep359 (ep385 rfl) (ep389 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep391 := @ep310 161377979465228263469 900719925474099200 401337545795203530147363 ep298 (ep354 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep355 Bool.true 6189523223 4294967296000 9623 4294967296000 (BSN.stirling_sum_succ qz72 0 1 rfl) (ep390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep392 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 36533535038783133 4503599627370496 100000000306691 27881000000000000000 Bool.false 876968342488483 281474976710656

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz355 qz376))

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz106) Bool.false 36533535038783133 4503599627370496 100000000306691 27881000000000000000 Bool.false 876968342488483 281474976710656 200000000027881 27881000000000000000

noncomputable def ep394 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz106 Bool.false 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000 Bool.false

noncomputable def ep395 := nat_lit 658129659148762707641681546575872

noncomputable def ep396 := nat_lit 987378575111713388403613499392

noncomputable abbrev qz107 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz355 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz107) Bool.false 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000

noncomputable def ep398 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz107 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz381 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82))

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq qz107 qz381 Bool.false 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000

noncomputable def ep400 := nat_lit 2856096106768604957078870079492742171339905744544836605270915945259209653458276816802283520

noncomputable def ep401 := nat_lit 56279184211775573460989305999952864000701117189693451786252261384209210162009262662877184

noncomputable def ep402 := nat_lit 3368000048152100483750829786709861210874366636340753473866988072815279796894595809280

noncomputable def ep403 := BSN.log_dyadic_bound 20571826304 86107826304 5 4 ep400 1048576 278810 ep401 ep402 510898 106679652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20571826304) (BSN.artanhQ 86107826304) 0 4 ep401 ep400 ep402 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep404 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 53339826304 16000000)) 1 2 0 1 36532521426501277 4503599627370496 100000000306691 27881000000000000000 36532521426501277 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 53339826304 16000000 36532521426501277 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53339826304) qz371)) Bool.false 306457001498520024252416 37778931862957161709568 1000000003066910 278810000000000000000 36532521426501277 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 53339826304 16000000 11 106679652608 65536000000 510898 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep403 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep405 := BSN.arctan_dyadic_bound_f 1000 230952 1 0 1048576 278810 0 1 1 0 1 1 4540 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 230952)

noncomputable def ep406 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383)) 884279719003555 562949953421312 1 2000000000000000 4540 1048576 1 278810 924678697845338931200 881842325063075 562949953421312 200000000027881 55762000000000000000 qz86 (ep405 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz273 qz355 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz384 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82)

noncomputable def ep407 := @ep398 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000 Bool.false 36532521426501277 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 881842325063075 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz105) (ep399 (@congrArg Complex Complex qz108 qz384 Complex.log (BSN.w_shift_mk qz13 Bool.false 115476 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz381 Bool.false 36532521426501277 9007199254740992 100000000306691 55762000000000000000 Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz381) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 53339826304 16000000))) Bool.false 36532521426501277 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 1000 230952 4000 53339826304 16000000 rfl rfl rfl) (ep404 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz381) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 1000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz382)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz383))) Bool.false 881842325063075 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 230952 1000 rfl rfl) ep406)))) rfl rfl

noncomputable abbrev qz385 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82))

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq qz106 qz385 Bool.false 36534548651064989 9007199254740992 100000000306691 55762000000000000000 Bool.false 872094359913891 562949953421312 200000000027881 55762000000000000000

noncomputable def ep409 := nat_lit 2862470738684229514019076214551777185877222692528436893684577506036236247513361913762283520

noncomputable def ep410 := nat_lit 56508586127491905123437073998101514114754028530960273756642159585948036392048577094877184

noncomputable def ep411 := nat_lit 3399562760698186239566054423961175926244469674157895310410389757888942308572035809280

noncomputable def ep412 := BSN.log_dyadic_bound 20595826304 86131826304 5 4 ep409 1048576 278810 ep410 ep411 511370 106727652608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 20595826304) (BSN.artanhQ 86131826304) 0 4 ep410 ep409 ep411 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep413 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 53363826304 16000000)) 1 2 0 1 36534548651064989 4503599627370496 100000000306691 27881000000000000000 36534548651064989 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 53363826304 16000000 36534548651064989 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53363826304) qz371)) Bool.false 306474007090712975245312 37778931862957161709568 1000000003066910 278810000000000000000 36534548651064989 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 53363826304 16000000 11 106727652608 65536000000 511370 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep412 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep414 := BSN.arctan_dyadic_bound_f 5000 230952 1 0 1048576 278810 0 1 1 0 1 1 22697 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 230952) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 230952) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep415 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383)) 884279719003555 562949953421312 1 2000000000000000 22697 1048576 1 278810 914457215541068169216 872094359913891 562949953421312 200000000027881 55762000000000000000 qz86 (ep414 rfl) rfl rfl

noncomputable abbrev qz109 := (@HAdd.hAdd Complex Complex Complex qz273 qz355 qz376)

noncomputable abbrev qz387 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82)

noncomputable def ep416 := @ep394 36534548651064989 9007199254740992 100000000306691 55762000000000000000 Bool.false 872094359913891 562949953421312 200000000027881 55762000000000000000 Bool.false ep395 36533535038783133 4503599627370496 100000000306691 27881000000000000000 Bool.false ep396 876968342488483 281474976710656 200000000027881 27881000000000000000 (ep397 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep408 (@congrArg Complex Complex qz109 qz387 Complex.log (BSN.w_shift_mk qz13 Bool.false 115476 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz385 Bool.false 36534548651064989 9007199254740992 100000000306691 55762000000000000000 Bool.false 872094359913891 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz385) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 53363826304 16000000))) Bool.false 36534548651064989 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 5000 230952 4000 53363826304 16000000 rfl rfl rfl) (ep413 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz385) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) Bool.false 872094359913891 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 5000 230952 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz383 qz386)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz383))) Bool.false 872094359913891 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 230952 5000 rfl rfl) ep415)))) rfl rfl

noncomputable def ep417 := @ep303 ep298 Bool.false 36533535038783133 4503599627370496 100000000306691 27881000000000000000 Bool.false 876968342488483 281474976710656 200000000027881 27881000000000000000 Bool.true ep304 408880462804607367577 4503599627370496000 791815207853595174545283 ep298 Bool.false ep305 158571680769265117869 900719925474099200 427551945798857948579363 ep298 (@ep306 4503599627370496000 778708007813396571793283 ep298 Bool.false 161377979465228263469 900719925474099200 401337545795203530147363 ep298 (BSN.logGammaStirling_unfold 1 qz72) (ep391 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep392 200000000027881 27881000000000000000 (BSN.log_sum_c_eq qz13 2) (ep393 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep416 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz110 := (@HDiv.hDiv Real Real Real qz270 qz284 (2 : Real))

noncomputable def ep418 := @Enclosure.Real.IsNear.mulLit_ff qz110 (Real.log Real.pi) 115476 2000 0 1 75021 65536 1 262144 2165781249 32768000 28869 131072000 (@Enclosure.Real.IsNear.of_eq qz110 (Enclosure.sfrac Bool.false 115476 2000) Bool.false 115476 2000 0 1 (BSN.t_half_eq qz13 Bool.false 115476 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 115476 2000)) EMRow37.d5 rfl

noncomputable def ep419 := @ep300 28869 131072000 ep301 495195695534484542817 4503599627370496000 ep297 ep298 (@ep302 427551945798857948579363 ep298 (ep417 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep418 rfl rfl

noncomputable def ep420 := nat_lit 8339501083047080909305861699183199203744187071212877939439587670172554571612160

noncomputable def ep421 := nat_lit 16746792847428112866369059834787208516685049801295806823738024940567569432576

noncomputable def ep422 := nat_lit 21814436600513185436874564067652056719826809391593534725579534714833866860855296

noncomputable def ep423 := BSN.sin_dyadic_bound_f 3372806732 2147483648 3 2 1048576 279083 ep420 ep64 ep421 ep422 ep66 ep421 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372806732) qz292 0 2 ep420 ep64 ep421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372806732) qz293 0 2 ep422 ep66 ep421 rfl rfl rfl rfl) rfl rfl

noncomputable def ep424 := @ep296 1048576 Bool.true 1048575 1048576 1 139405 (@ep299 28824183 262144 355 1048576 ep419 rfl) (Enclosure.sfrac_false_div 28824183 262144) (BSN.cos_reduce1 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335043538710163357696) qz291) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 17 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 28824183 262144 226375608064910080 72057594037927936 17 59335043538710163357696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 59335043538710163357696 37778931862957161709568 3372806732 2147483648 279083 278810 (ep423 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep425 := nat_lit 5688689402019237257321860711

noncomputable abbrev qz560 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz388 := (@HPow.hPow Complex Complex Complex qz532 qz560 qz533)

noncomputable abbrev qz111 := qz388

noncomputable abbrev qz389 := qz560

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz272 (1 : Complex))) qz360)

noncomputable abbrev qz113 := (@instHSub Nat instSubNat)

noncomputable abbrev qz390 := qz559

noncomputable abbrev qz114 := qz390

noncomputable abbrev qz115 := qz389

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 24) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep291 ep292 ep293

noncomputable def ep427 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 1753042911965 1099511627776 185977685970215 30655483694022656

noncomputable def ep428 := nat_lit 2115653631670940784859373

noncomputable def ep429 := nat_lit 109496998546700506361952719

noncomputable def ep430 := nat_lit 109418213209995410882044711

noncomputable def ep431 := nat_lit 55505585970415041019822297828191895552

noncomputable def ep432 := nat_lit 31739155393819837047178382251393024

noncomputable def ep433 := @ep427 Bool.false 169839202491 1099511627776 185953067772121 30655483694022656 Bool.true ep428 ep292 ep429 ep294 Bool.true 39077358034171881529931 439858194336001063649280 ep430 ep294 Bool.false ep431 ep291 ep292 ep293 ep294 Bool.false ep432 28866593669426799394549 439858194336001063649280

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 24) Bool.false 1753042911965 1099511627776 185977685970215 30655483694022656 Bool.false 169839202491 1099511627776 185953067772121

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 23) qz275)

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz116) Bool.false 1753042911965 1099511627776 185977685970215 30655483694022656 Bool.false 169839202491 1099511627776 185953067772121 30655483694022656

noncomputable def ep436 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz116 Bool.false 957126712327 549755813888 225759680088479 38319354617528320 Bool.false 3413535741 549755813888 451457240333123 76638709235056640 Bool.true

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 22) qz275)

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz117) Bool.false 957126712327 549755813888 225759680088479 38319354617528320 Bool.false 3413535741 549755813888 451457240333123 76638709235056640

noncomputable def ep438 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz117 Bool.false 1829408848457 1099511627776 875637756074203 153277418470113280 Bool.true 211696095549 1099511627776 875430157493923 153277418470113280 Bool.false

noncomputable def ep439 := nat_lit 2104743898917102109589504

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 21) qz275)

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz118) Bool.false 1829408848457 1099511627776 875637756074203 153277418470113280 Bool.true 211696095549 1099511627776 875430157493923 153277418470113280

noncomputable def ep441 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz118 Bool.false 1599441953279 1099511627776 847397682333973 153277418470113280 Bool.true 280128923627 1099511627776 847386909673193 153277418470113280 Bool.false

noncomputable abbrev qz119 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 20) qz275)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz119) Bool.false 1599441953279 1099511627776 847397682333973 153277418470113280 Bool.true 280128923627 1099511627776 847386909673193 153277418470113280

noncomputable def ep443 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz119 Bool.false 1369333607741 1099511627776 818610624059293 153277418470113280 Bool.true 96773395233 549755813888 409342592899689 76638709235056640 Bool.false

noncomputable abbrev qz120 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz275)

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz120) Bool.false 1369333607741 1099511627776 818610624059293 153277418470113280 Bool.true 96773395233 549755813888 409342592899689 76638709235056640

noncomputable def ep445 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz120 Bool.false 1179698542451 1099511627776 789072802145183 153277418470113280 Bool.true 13608299989 549755813888 394580434581429 76638709235056640 Bool.false

noncomputable abbrev qz121 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz121) Bool.false 1179698542451 1099511627776 789072802145183 153277418470113280 Bool.true 13608299989 549755813888 394580434581429 76638709235056640

noncomputable def ep447 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz121 Bool.false 247949571859 274877906944 379366242190053 76638709235056640 Bool.false 151264730427 1099511627776 758825864122331 153277418470113280 Bool.false

noncomputable abbrev qz122 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz38 qz122) Bool.false 247949571859 274877906944 379366242190053 76638709235056640 Bool.false 151264730427 1099511627776 758825864122331 153277418470113280

noncomputable def ep449 := @Enclosure.Complex.IsNear.addLitP qz38 qz122 Bool.false 750794019435 1099511627776 727489420375173 153277418470113280 Bool.false 265414407243 1099511627776 727652336028423 153277418470113280 Bool.false

noncomputable abbrev qz391 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz391))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz267 qz284 qz561)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 241004268001 1099511627776 31243064004933 153277418470113280 Bool.true 7134354801 68719476736 7793382023477 38319354617528320 (BSN.cpow_neg_s_mk qz13 115476 1000 17 qz14 rfl)

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep451 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz391) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz391) (Real.sqrt qz392) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz392) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep452 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 139405 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 115476 1000 0 1 3189913004350711 1125899906842624 50000000027881 6970250000000000000 92089598522600675859 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz392) Bool.false 53517859495200818200576 18889465931478580854784 1000000000557620 139405000000000000000 3189913004350711 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep454 := nat_lit 814220747365819228429870698201760000

noncomputable def ep455 := BSN.cos_dyadic_bound_f 949916740 2147483648 2 1 1048576 279083 ep454 ep109 ep454 ep454 ep110 ep454 947653 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 949916740) qz287 0 1 ep454 ep109 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 949916740) qz288 0 1 ep454 ep110 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 343060487) qz22)

noncomputable def ep456 := @Enclosure.Real.IsNear.cos_image qz124 qz393 Bool.false 343060487 1048576 435 524288 Bool.false 947653 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 92089598522600675859 281474976710656000 1443450000804896589 1742562500000000000000 343060487 1048576 435 524288 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 343060487 1048576) (BSN.cos_reduce0 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66844448127308764545024) qz24) 226375608064910080 72057594037927936 Bool.false 947653 1048576 52 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 343060487 1048576 226375608064910080 72057594037927936 52 66844448127308764545024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947653 1048576 66844448127308764545024 151115727451828646838272 949916740 2147483648 279083 278810 (ep455 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep457 := BSN.sin_dyadic_bound_f 949916740 2147483648 2 1 1048576 279083 ep454 ep113 ep454 ep454 ep114 ep454 448848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 949916740) qz292 0 1 ep454 ep113 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 949916740) qz293 0 1 ep454 ep114 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image qz124 qz393 Bool.false 343060487 1048576 435 524288 Bool.false 448848 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 92089598522600675859 281474976710656000 1443450000804896589 1742562500000000000000 343060487 1048576 435 524288 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 343060487 1048576) (BSN.sin_reduce0 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66844448127308764545024) qz24) 226375608064910080 72057594037927936 Bool.false 448848 1048576 52 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 343060487 1048576 226375608064910080 72057594037927936 52 66844448127308764545024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448848 1048576 66844448127308764545024 151115727451828646838272 949916740 2147483648 279083 278810 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz394 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep451 rfl rfl) rfl)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 241004268001 1099511627776 31243064004933 153277418470113280 Bool.true 7134354801 68719476736 7793382023477 38319354617528320 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 254317 1048576 1 1048576 947653 1048576 61165463 73088368640 241004268001 1099511627776 31243064004933 153277418470113280 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 947653 1048576 61165463 73088368640 947653 1048576 61165463 73088368640 (ep456 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 254317 1048576 1 1048576 28053 65536 61165463 73088368640 7134354801 68719476736 7793382023477 38319354617528320 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 28053 65536 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 448848 1048576 61165463 73088368640 28053 65536 61165463 73088368640 (ep458 rfl rfl) rfl)) rfl)

noncomputable def ep460 := @ep449 241004268001 1099511627776 31243064004933 153277418470113280 Bool.true 7134354801 68719476736 7793382023477 38319354617528320 Bool.false 1090493749444205489422336 247949571859 274877906944 379366242190053 76638709235056640 Bool.false 10394833123555537846272 151264730427 1099511627776 758825864122331 153277418470113280 EMRow37.d7 (ep450 ep459) rfl rfl

noncomputable abbrev qz395 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz395))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz284 qz562)

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 187900255015 1099511627776 30340317765077 153277418470113280 Bool.true 178481330405 1099511627776 30335005040527 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 18 qz14 rfl)

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep462 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz395) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz395) (Real.sqrt qz396) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz396) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep463 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 139405 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 115476 1000 0 1 3254268794313975 1125899906842624 50000000027881 6970250000000000000 3757899432922005771 11258999068426240 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz396) Bool.false 54597570484265130393600 18889465931478580854784 1000000000557620 139405000000000000000 3254268794313975 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep465 := nat_lit 253159454593132909116510077311194996069733332368060708554750126755147551932416

noncomputable def ep466 := nat_lit 50183230950324118439366957856092827010073738022683938782514705429273051136

noncomputable def ep467 := nat_lit 759377997317498079112651498017872802555179849628136757786685350854584109694976

noncomputable def ep468 := BSN.cos_dyadic_bound_f 1631435196 2147483648 3 2 1048576 279083 ep465 ep57 ep466 ep467 ep60 ep466 760265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1631435196) qz287 0 2 ep465 ep57 ep466 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1631435196) qz288 0 2 ep467 ep60 ep466 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349981657) qz22)

noncomputable def ep469 := @Enclosure.Real.IsNear.cos_image qz126 qz397 Bool.false 349981657 1048576 435 524288 Bool.false 760265 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 3757899432922005771 11258999068426240 1443450000804896589 1742562500000000000000 349981657 1048576 435 524288 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 349981657 1048576) (BSN.cos_reduce0 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114802045973195541970944) qz24) 226375608064910080 72057594037927936 Bool.false 760265 1048576 53 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 349981657 1048576 226375608064910080 72057594037927936 53 114802045973195541970944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 760265 1048576 114802045973195541970944 151115727451828646838272 1631435196 2147483648 279083 278810 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep470 := nat_lit 7084012348261691055376635521332429056

noncomputable def ep471 := BSN.sin_dyadic_bound_f 1631435196 2147483648 2 1 1048576 279083 ep470 ep113 ep470 ep470 ep114 ep470 722155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1631435196) qz292 0 1 ep470 ep113 ep470 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1631435196) qz293 0 1 ep470 ep114 ep470 rfl rfl rfl rfl) rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.sin_image qz126 qz397 Bool.false 349981657 1048576 435 524288 Bool.false 722155 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 3757899432922005771 11258999068426240 1443450000804896589 1742562500000000000000 349981657 1048576 435 524288 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 349981657 1048576) (BSN.sin_reduce0 qz397 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114802045973195541970944) qz24) 226375608064910080 72057594037927936 Bool.false 722155 1048576 53 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 349981657 1048576 226375608064910080 72057594037927936 53 114802045973195541970944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 722155 1048576 114802045973195541970944 151115727451828646838272 1631435196 2147483648 279083 278810 (ep471 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz398 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep462 rfl rfl) rfl)

noncomputable def ep473 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 187900255015 1099511627776 30340317765077 153277418470113280 Bool.true 178481330405 1099511627776 30335005040527 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz126) 247151 1048576 1 1048576 760265 1048576 61165463 73088368640 187900255015 1099511627776 30340317765077 153277418470113280 qz398 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 760265 1048576 61165463 73088368640 760265 1048576 61165463 73088368640 (ep469 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 247151 1048576 1 1048576 722155 1048576 61165463 73088368640 178481330405 1099511627776 30335005040527 153277418470113280 qz398 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 722155 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 722155 1048576 61165463 73088368640 722155 1048576 61165463 73088368640 (ep472 rfl rfl) rfl)) rfl)

noncomputable def ep474 := @ep447 187900255015 1099511627776 30340317765077 153277418470113280 Bool.true 178481330405 1099511627776 30335005040527 153277418470113280 Bool.false 324273066173818411679744 1179698542451 1099511627776 789072802145183 153277418470113280 Bool.true 29924968144339025788928 13608299989 549755813888 394580434581429 76638709235056640 (ep448 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep460 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep461 ep473) rfl rfl

noncomputable abbrev qz399 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz399))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz284 qz563)

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq qz120 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 94817532645 549755813888 2953782191411 15327741847011328 Bool.true 20791273811 137438953472 738107915913 3831935461752832 (BSN.cpow_neg_s_mk qz13 115476 1000 19 qz14 rfl)

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep476 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz399) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz399) (Real.sqrt qz400) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz400) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep477 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 139405 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep478 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 115476 1000 0 1 3315143513283831 1125899906842624 50000000027881 6970250000000000000 95704878084990917139 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 55618878793361701994496 18889465931478580854784 1000000000557620 139405000000000000000 3315143513283831 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep477 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep479 := nat_lit 204268312858222935540796074379849608751787612959295107992071703666284041973281

noncomputable def ep480 := nat_lit 32674245455444236559789979649047895710266277083323319306930563248947834401

noncomputable def ep481 := nat_lit 612739590083757918149268643180250730463942306323718677337601249872354230251041

noncomputable def ep482 := BSN.cos_dyadic_bound_f 1546235699 2147483648 3 2 1048576 279083 ep479 ep57 ep480 ep481 ep60 ep480 788310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1546235699) qz287 0 2 ep479 ep57 ep480 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1546235699) qz288 0 2 ep481 ep60 ep480 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 356528453) qz22)

noncomputable def ep483 := @Enclosure.Real.IsNear.cos_image qz128 qz401 Bool.false 356528453 1048576 435 524288 Bool.false 788310 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 95704878084990917139 281474976710656000 1443450000804896589 1742562500000000000000 356528453 1048576 435 524288 (ep478 rfl) rfl) (Enclosure.sfrac_false_div 356528453 1048576) (BSN.cos_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108806664398371853172736) qz24) 226375608064910080 72057594037927936 Bool.false 788310 1048576 54 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 356528453 1048576 226375608064910080 72057594037927936 54 108806664398371853172736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 788310 1048576 108806664398371853172736 151115727451828646838272 1546235699 2147483648 279083 278810 (ep482 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep484 := nat_lit 5716139033949772338216664940469997201

noncomputable def ep485 := BSN.sin_dyadic_bound_f 1546235699 2147483648 2 1 1048576 279083 ep484 ep113 ep484 ep484 ep114 ep484 691432 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1546235699) qz292 0 1 ep484 ep113 ep484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1546235699) qz293 0 1 ep484 ep114 ep484 rfl rfl rfl rfl) rfl rfl

noncomputable def ep486 := @Enclosure.Real.IsNear.sin_image qz128 qz401 Bool.false 356528453 1048576 435 524288 Bool.false 691432 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 95704878084990917139 281474976710656000 1443450000804896589 1742562500000000000000 356528453 1048576 435 524288 (ep478 rfl) rfl) (Enclosure.sfrac_false_div 356528453 1048576) (BSN.sin_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 108806664398371853172736) qz24) 226375608064910080 72057594037927936 Bool.false 691432 1048576 54 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 356528453 1048576 226375608064910080 72057594037927936 54 108806664398371853172736 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 691432 1048576 108806664398371853172736 151115727451828646838272 1546235699 2147483648 279083 278810 (ep485 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep476 rfl rfl) rfl)

noncomputable def ep487 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 94817532645 549755813888 2953782191411 15327741847011328 Bool.true 20791273811 137438953472 738107915913 3831935461752832 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 240559 1048576 1 1048576 394155 524288 61165463 73088368640 94817532645 549755813888 2953782191411 15327741847011328 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 788310 1048576 61165463 73088368640 394155 524288 61165463 73088368640 (ep483 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 240559 1048576 1 1048576 86429 131072 61165463 73088368640 20791273811 137438953472 738107915913 3831935461752832 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.false 86429 131072 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.false 691432 1048576 61165463 73088368640 86429 131072 61165463 73088368640 (ep486 rfl rfl) rfl)) rfl)

noncomputable def ep488 := @ep445 94817532645 549755813888 2953782191411 15327741847011328 Bool.true 20791273811 137438953472 738107915913 3831935461752832 Bool.false 752799112007844792107008 1369333607741 1099511627776 818610624059293 153277418470113280 Bool.true 13300434164755753598976 96773395233 549755813888 409342592899689 76638709235056640 (ep446 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep475 ep487) rfl rfl

noncomputable abbrev qz403 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz403))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz284 qz564)

noncomputable def ep489 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 115054172769 549755813888 719676456867 3831935461752832 Bool.true 86582133161 1099511627776 5740344774763 30655483694022656 (BSN.cpow_neg_s_mk qz13 115476 1000 20 qz14 rfl)

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep490 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz403) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz403) (Real.sqrt qz404) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz404) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep491 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 139405 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 115476 1000 0 1 3372893643545847 1125899906842624 50000000027881 6970250000000000000 97372066595525057043 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 56587765202795681021952 18889465931478580854784 1000000000557620 139405000000000000000 3372893643545847 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep491 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep493 := nat_lit 356742749545551736027735863360405681

noncomputable def ep494 := BSN.cos_dyadic_bound_f 772838571 2147483648 2 1 1048576 279083 ep493 ep109 ep493 ep493 ep110 ep493 981402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 772838571) qz287 0 1 ep493 ep109 ep493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 772838571) qz288 0 1 ep493 ep110 ep493 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 362739215) qz22)

noncomputable def ep495 := @Enclosure.Real.IsNear.cos_image qz130 qz405 Bool.false 362739215 1048576 869 1048576 Bool.false 981402 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 97372066595525057043 281474976710656000 1443450000804896589 1742562500000000000000 362739215 1048576 869 1048576 (ep492 rfl) rfl) (Enclosure.sfrac_false_div 362739215 1048576) (BSN.cos_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54383679713666012282880) qz24) 226375608064910080 72057594037927936 Bool.false 981402 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 362739215 1048576 226375608064910080 72057594037927936 55 54383679713666012282880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 981402 1048576 54383679713666012282880 151115727451828646838272 772838571 2147483648 279083 278810 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := BSN.sin_dyadic_bound_f 772838571 2147483648 2 1 1048576 279083 ep493 ep113 ep493 ep493 ep114 ep493 369269 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 772838571) qz292 0 1 ep493 ep113 ep493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 772838571) qz293 0 1 ep493 ep114 ep493 rfl rfl rfl rfl) rfl rfl

noncomputable def ep497 := @Enclosure.Real.IsNear.sin_image qz130 qz405 Bool.false 362739215 1048576 869 1048576 Bool.false 369269 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 97372066595525057043 281474976710656000 1443450000804896589 1742562500000000000000 362739215 1048576 869 1048576 (ep492 rfl) rfl) (Enclosure.sfrac_false_div 362739215 1048576) (BSN.sin_reduce0 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54383679713666012282880) qz24) 226375608064910080 72057594037927936 Bool.false 369269 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 362739215 1048576 226375608064910080 72057594037927936 55 54383679713666012282880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369269 1048576 54383679713666012282880 151115727451828646838272 772838571 2147483648 279083 278810 (ep496 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz406 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep490 rfl rfl) rfl)

noncomputable def ep498 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 115054172769 549755813888 719676456867 3831935461752832 Bool.true 86582133161 1099511627776 5740344774763 30655483694022656 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 234469 1048576 1 1048576 490701 524288 122191521 146176737280 115054172769 549755813888 719676456867 3831935461752832 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 981402 1048576 122191521 146176737280 490701 524288 122191521 146176737280 (ep495 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 234469 1048576 1 1048576 369269 1048576 122191521 146176737280 86582133161 1099511627776 5740344774763 30655483694022656 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.false 369269 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.false 369269 1048576 122191521 146176737280 369269 1048576 122191521 146176737280 (ep497 rfl rfl) rfl)) rfl)

noncomputable def ep499 := @ep443 115054172769 549755813888 719676456867 3831935461752832 Bool.true 86582133161 1099511627776 5740344774763 30655483694022656 Bool.false 879302512791509115338752 1599441953279 1099511627776 847397682333973 153277418470113280 Bool.true 154002504402130777931776 280128923627 1099511627776 847386909673193 153277418470113280 (ep444 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep488 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep489 ep498) rfl rfl

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz407))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz267 qz284 qz565)

noncomputable def ep500 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.false 114983447589 549755813888 2824007374023 15327741847011328 Bool.false 34216414039 549755813888 2804324782073 15327741847011328 (BSN.cpow_neg_s_mk qz13 115476 1000 21 qz14 rfl)

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep501 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz407) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz407) (Real.sqrt qz408) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz408) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep502 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 139405 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 115476 1000 0 1 3427826275261687 1125899906842624 50000000027881 6970250000000000000 98957916740529642003 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz408) Bool.false 57509381830540779323392 18889465931478580854784 1000000000557620 139405000000000000000 3427826275261687 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep502 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep504 := nat_lit 3692906307518741427904094448236883144123743430141012462181939902051152543416320

noncomputable def ep505 := nat_lit 3291240510280662754439087202471560572767761077015947913078142629649643012096

noncomputable def ep506 := nat_lit 9666568796961011238146393604197359041301513561006530628141049417305014382166016

noncomputable def ep507 := BSN.sin_dyadic_bound_f 2752136388 2147483648 3 2 1048576 279083 ep504 ep64 ep505 ep506 ep66 ep505 1005021 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2752136388) qz292 0 2 ep504 ep64 ep505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2752136388) qz293 0 2 ep506 ep66 ep505 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 368646967) qz22)

noncomputable def ep508 := @Enclosure.Real.IsNear.cos_image qz132 qz409 Bool.false 368646967 1048576 869 1048576 Bool.false 1005021 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 98957916740529642003 281474976710656000 1443450000804896589 1742562500000000000000 368646967 1048576 869 1048576 (ep503 rfl) rfl) (Enclosure.sfrac_false_div 368646967 1048576) (BSN.cos_reduce3 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193664381492366235664384) qz24) 226375608064910080 72057594037927936 Bool.false 1005021 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 368646967 1048576 226375608064910080 72057594037927936 55 193664381492366235664384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1005021 1048576 193664381492366235664384 151115727451828646838272 2752136388 2147483648 279083 278810 (ep507 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep509 := nat_lit 2053077388848314421170914287777144662545532021668125122506890231197151254347776

noncomputable def ep510 := nat_lit 6152649685524381938003864688926490866491060542850343471694514408332154477019136

noncomputable def ep511 := BSN.cos_dyadic_bound_f 2752136388 2147483648 3 2 1048576 279083 ep509 ep57 ep505 ep510 ep60 ep505 299071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2752136388) qz287 0 2 ep509 ep57 ep505 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2752136388) qz288 0 2 ep510 ep60 ep505 rfl rfl rfl rfl) rfl rfl

noncomputable def ep512 := @Enclosure.Real.IsNear.sin_image qz132 qz409 Bool.false 368646967 1048576 869 1048576 Bool.true 299071 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 98957916740529642003 281474976710656000 1443450000804896589 1742562500000000000000 368646967 1048576 869 1048576 (ep503 rfl) rfl) (Enclosure.sfrac_false_div 368646967 1048576) (BSN.sin_reduce3 qz409 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 193664381492366235664384) qz24) 226375608064910080 72057594037927936 Bool.false 299071 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 368646967 1048576 226375608064910080 72057594037927936 55 193664381492366235664384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 299071 1048576 193664381492366235664384 151115727451828646838272 2752136388 2147483648 279083 278810 (ep511 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz410 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep501 rfl rfl) rfl)

noncomputable def ep513 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.false 114983447589 549755813888 2824007374023 15327741847011328 Bool.false 34216414039 549755813888 2804324782073 15327741847011328 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz132) 114409 524288 1 524288 1005021 1048576 122191521 146176737280 114983447589 549755813888 2824007374023 15327741847011328 qz410 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 1005021 1048576 122191521 146176737280 1005021 1048576 122191521 146176737280 (ep508 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 114409 524288 1 524288 299071 1048576 122191521 146176737280 34216414039 549755813888 2804324782073 15327741847011328 qz410 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 299071 1048576 122191521 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 299071 1048576 122191521 146176737280 299071 1048576 122191521 146176737280 (ep512 rfl rfl) rfl)) rfl)

noncomputable def ep514 := @ep441 114983447589 549755813888 2824007374023 15327741847011328 Bool.false 34216414039 549755813888 2804324782073 15327741847011328 Bool.false 1005728150417386887970816 1829408848457 1099511627776 875637756074203 153277418470113280 Bool.true 116381159305452309184512 211696095549 1099511627776 875430157493923 153277418470113280 (ep442 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep499 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep500 ep513) rfl rfl

noncomputable abbrev qz411 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz411))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz267 qz284 qz566)

noncomputable def ep515 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)))) Bool.false 84844576197 1099511627776 27400964279713 153277418470113280 Bool.false 218523167031 1099511627776 27484323172323 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 22 qz14 rfl)

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep516 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz411) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz411) (Real.sqrt qz412) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz412) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep517 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 139405 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 115476 1000 0 1 3480203401436407 1125899906842624 50000000027881 6970250000000000000 100469991996067633683 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 58388124189833310502912 18889465931478580854784 1000000000557620 139405000000000000000 3480203401436407 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep517 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep519 := nat_lit 400092690419413223279949078661939456

noncomputable def ep520 := BSN.sin_dyadic_bound_f 795316796 2147483648 2 1 1048576 279083 ep519 ep113 ep519 ep519 ep114 ep519 379521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 795316796) qz292 0 1 ep519 ep113 ep519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 795316796) qz293 0 1 ep519 ep114 ep519 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187139943) qz33)

noncomputable def ep521 := @Enclosure.Real.IsNear.cos_image qz134 qz413 Bool.false 187139943 524288 435 524288 Bool.false 379521 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 100469991996067633683 281474976710656000 1443450000804896589 1742562500000000000000 187139943 524288 435 524288 (ep518 rfl) rfl) (Enclosure.sfrac_false_div 187139943 524288) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27982722092171805065216) qz309) 226375608064910080 72057594037927936 Bool.false 379521 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 187139943 524288 226375608064910080 72057594037927936 56 27982722092171805065216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379521 1048576 27982722092171805065216 75557863725914323419136 795316796 2147483648 279083 278810 (ep520 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep522 := BSN.cos_dyadic_bound_f 795316796 2147483648 2 1 1048576 279083 ep519 ep109 ep519 ep519 ep110 ep519 977483 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 795316796) qz287 0 1 ep519 ep109 ep519 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 795316796) qz288 0 1 ep519 ep110 ep519 rfl rfl rfl rfl) rfl rfl

noncomputable def ep523 := @Enclosure.Real.IsNear.sin_image qz134 qz413 Bool.false 187139943 524288 435 524288 Bool.true 977483 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 100469991996067633683 281474976710656000 1443450000804896589 1742562500000000000000 187139943 524288 435 524288 (ep518 rfl) rfl) (Enclosure.sfrac_false_div 187139943 524288) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27982722092171805065216) qz309) 226375608064910080 72057594037927936 Bool.false 977483 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 187139943 524288 226375608064910080 72057594037927936 56 27982722092171805065216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977483 1048576 27982722092171805065216 75557863725914323419136 795316796 2147483648 279083 278810 (ep522 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep516 rfl rfl) rfl)

noncomputable def ep524 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134))) Bool.false 84844576197 1099511627776 27400964279713 153277418470113280 Bool.false 218523167031 1099511627776 27484323172323 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz133 (Real.cos qz134) 223557 1048576 1 1048576 379521 1048576 61165463 73088368640 84844576197 1099511627776 27400964279713 153277418470113280 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 379521 1048576 61165463 73088368640 379521 1048576 61165463 73088368640 (ep521 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)) 223557 1048576 1 1048576 977483 1048576 61165463 73088368640 218523167031 1099511627776 27484323172323 153277418470113280 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz134) Bool.true 977483 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz134) Bool.true 977483 1048576 61165463 73088368640 977483 1048576 61165463 73088368640 (ep523 rfl rfl) rfl)) rfl)

noncomputable def ep525 := @ep438 84844576197 1099511627776 27400964279713 153277418470113280 Bool.false 218523167031 1099511627776 27484323172323 153277418470113280 Bool.false ep439 957126712327 549755813888 225759680088479 38319354617528320 Bool.false 7506444478116928684032 3413535741 549755813888 451457240333123 76638709235056640 (ep440 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep514 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep515 ep524) rfl rfl

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz415))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz136 := (@HMul.hMul Real Real Real qz267 qz284 qz567)

noncomputable def ep526 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)))) Bool.true 161210512689 1099511627776 26849709497159 153277418470113280 Bool.false 163012131009 1099511627776 26850858194359 153277418470113280 (BSN.cpow_neg_s_mk qz13 115476 1000 23 qz14 rfl)

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep527 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz415) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz415) (Real.sqrt qz416) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz416) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep528 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 139405 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 115476 1000 0 1 3530250507853047 1125899906842624 50000000027881 6970250000000000000 101914801911209613843 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz416) Bool.false 59227775304360265777152 18889465931478580854784 1000000000557620 139405000000000000000 3530250507853047 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep528 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep530 := nat_lit 297478912027657555435710933531157629158872237220778727909933514566589231190625

noncomputable def ep531 := nat_lit 69287126479598172329268995542575191595351048189207424175833824497250390625

noncomputable def ep532 := nat_lit 892298161830013469962474262602387737093426009565957768881448876050773192790625

noncomputable def ep533 := BSN.cos_dyadic_bound_f 1698562645 2147483648 3 2 1048576 279083 ep530 ep57 ep531 ep532 ep60 ep531 737323 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1698562645) qz287 0 2 ep530 ep57 ep531 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1698562645) qz288 0 2 ep532 ep60 ep531 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189831111) qz33)

noncomputable def ep534 := @Enclosure.Real.IsNear.cos_image qz136 qz417 Bool.false 189831111 524288 435 524288 Bool.true 737323 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 101914801911209613843 281474976710656000 1443450000804896589 1742562500000000000000 189831111 524288 435 524288 (ep529 rfl) rfl) (Enclosure.sfrac_false_div 189831111 524288) (BSN.cos_reduce2 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59762860152489972334592) qz309) 226375608064910080 72057594037927936 Bool.false 737323 1048576 57 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 189831111 524288 226375608064910080 72057594037927936 57 59762860152489972334592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 737323 1048576 59762860152489972334592 75557863725914323419136 1698562645 2147483648 279083 278810 (ep533 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep535 := nat_lit 8323888903607386105084593394285800625

noncomputable def ep536 := BSN.sin_dyadic_bound_f 1698562645 2147483648 2 1 1048576 279083 ep535 ep113 ep535 ep535 ep114 ep535 745563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1698562645) qz292 0 1 ep535 ep113 ep535 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1698562645) qz293 0 1 ep535 ep114 ep535 rfl rfl rfl rfl) rfl rfl

noncomputable def ep537 := @Enclosure.Real.IsNear.sin_image qz136 qz417 Bool.false 189831111 524288 435 524288 Bool.true 745563 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz136 Bool.false 101914801911209613843 281474976710656000 1443450000804896589 1742562500000000000000 189831111 524288 435 524288 (ep529 rfl) rfl) (Enclosure.sfrac_false_div 189831111 524288) (BSN.sin_reduce2 qz417 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59762860152489972334592) qz309) 226375608064910080 72057594037927936 Bool.false 745563 1048576 57 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 189831111 524288 226375608064910080 72057594037927936 57 59762860152489972334592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 745563 1048576 59762860152489972334592 75557863725914323419136 1698562645 2147483648 279083 278810 (ep536 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz418 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep527 rfl rfl) rfl)

noncomputable def ep538 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz136)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136))) Bool.true 161210512689 1099511627776 26849709497159 153277418470113280 Bool.false 163012131009 1099511627776 26850858194359 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz136) 218643 1048576 1 1048576 737323 1048576 61165463 73088368640 161210512689 1099511627776 26849709497159 153277418470113280 qz418 (@Enclosure.Real.IsNear.recentre' (Real.cos qz136) Bool.true 737323 1048576 61165463 73088368640 737323 1048576 61165463 73088368640 (ep534 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz136)) 218643 1048576 1 1048576 745563 1048576 61165463 73088368640 163012131009 1099511627776 26850858194359 153277418470113280 qz418 (@Enclosure.Real.IsNear.neg (Real.sin qz136) Bool.true 745563 1048576 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz136) Bool.true 745563 1048576 61165463 73088368640 745563 1048576 61165463 73088368640 (ep537 rfl rfl) rfl)) rfl)

noncomputable def ep539 := @ep436 161210512689 1099511627776 26849709497159 153277418470113280 Bool.false 163012131009 1099511627776 26850858194359 153277418470113280 Bool.false 963745532847908108369920 1753042911965 1099511627776 185977685970215 30655483694022656 Bool.false 93370088995528541995008 169839202491 1099511627776 185953067772121 30655483694022656 (ep437 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep525 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep526 ep538) rfl rfl

noncomputable def ep540 := @Enclosure.Complex.IsNear.mul qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true ep428 ep292 ep429 ep294 Bool.true

noncomputable abbrev qz137 := (Complex.re qz388)

noncomputable abbrev qz138 := (Complex.im qz388)

noncomputable def ep541 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 22605123207768071248075 263914916601600638189568 632481256320454067375941

noncomputable def ep542 := nat_lit 7358211789769227393363345408

noncomputable def ep543 := nat_lit 1832742476400004431872000

noncomputable def ep544 := nat_lit 5072806917773957989993349

noncomputable def ep545 := nat_lit 153296078953525570695069696000

noncomputable def ep546 := nat_lit 31019586208906102882136150388215802210233090048

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 188038612475 1099511627776 5261236435733 30655483694022656 120215326577

noncomputable abbrev qz419 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz139 := (@Inv.inv Real Real.instInv (Real.sqrt qz419))

noncomputable abbrev qz420 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz537 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz140 := (Real.cos qz420)

noncomputable abbrev qz141 := (Real.sin qz420)

noncomputable abbrev qz421 := (@Neg.neg Real Real.instNeg qz141)

noncomputable def ep548 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz421)) Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (BSN.cpow_neg_s_mk qz13 115476 1000 24 qz14 rfl)

noncomputable abbrev qz422 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep549 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz419) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz419) (Real.sqrt qz422) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz422) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep550 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 139405 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz423 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz142 := qz423

noncomputable abbrev qz424 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15))

noncomputable def ep551 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 115476 1000 0 1 3578169457974519 1125899906842624 50000000027881 6970250000000000000 103298174082266389011 281474976710656000 1443450000804896589 1742562500000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false 60031721881041427759104 18889465931478580854784 1000000000557620 139405000000000000000 3578169457974519 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep550 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep552 := nat_lit 1331885300635997379892938939761889451221406516873168562842263137071236720265345

noncomputable def ep553 := nat_lit 428599438042109413486201489191816797291608122172360622964643156034110523521

noncomputable def ep554 := nat_lit 3487577102575544008288243373155780859336640178660495747387794031981564755085441

noncomputable def ep555 := BSN.sin_dyadic_bound_f 2133076591 2147483648 3 2 1048576 279083 ep552 ep64 ep553 ep554 ep66 ep553 878525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2133076591) qz292 0 2 ep552 ep64 ep553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2133076591) qz293 0 2 ep554 ep66 ep553 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz143 := qz420

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384815685) qz22)

noncomputable def ep556 := @Enclosure.Real.IsNear.cos_image qz143 qz425 Bool.false 384815685 1048576 435 524288 Bool.true 878525 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 103298174082266389011 281474976710656000 1443450000804896589 1742562500000000000000 384815685 1048576 435 524288 (ep551 rfl) rfl) (Enclosure.sfrac_false_div 384815685 1048576) (BSN.cos_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150101920985130918215680) qz24) 226375608064910080 72057594037927936 Bool.false 878525 1048576 58 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 384815685 1048576 226375608064910080 72057594037927936 58 150101920985130918215680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 878525 1048576 150101920985130918215680 151115727451828646838272 2133076591 2147483648 279083 278810 (ep555 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep557 := nat_lit 740126766770239481902071056085134947032911001872725806300352695331146671491201

noncomputable def ep558 := nat_lit 2219523101434634226879240765277021207504149789373832697655128799681371793426561

noncomputable def ep559 := BSN.cos_dyadic_bound_f 2133076591 2147483648 3 2 1048576 279083 ep557 ep57 ep553 ep558 ep60 ep553 572454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2133076591) qz287 0 2 ep557 ep57 ep553 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2133076591) qz288 0 2 ep558 ep60 ep553 rfl rfl rfl rfl) rfl rfl

noncomputable def ep560 := @Enclosure.Real.IsNear.sin_image qz143 qz425 Bool.false 384815685 1048576 435 524288 Bool.false 572454 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 103298174082266389011 281474976710656000 1443450000804896589 1742562500000000000000 384815685 1048576 435 524288 (ep551 rfl) rfl) (Enclosure.sfrac_false_div 384815685 1048576) (BSN.sin_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 150101920985130918215680) qz24) 226375608064910080 72057594037927936 Bool.false 572454 1048576 58 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 384815685 1048576 226375608064910080 72057594037927936 58 150101920985130918215680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 572454 1048576 150101920985130918215680 151115727451828646838272 2133076591 2147483648 279083 278810 (ep559 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz426 := (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep549 rfl rfl) rfl)

noncomputable def ep561 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 qz140) (@HMul.hMul Real Real Real qz0 qz139 qz421) Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (@Enclosure.Real.IsNear.mulLit_ft qz139 qz140 214039 1048576 1 1048576 878525 1048576 61165463 73088368640 188038612475 1099511627776 5261236435733 30655483694022656 qz426 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 878525 1048576 61165463 73088368640 878525 1048576 61165463 73088368640 (ep556 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz139 qz421 214039 1048576 1 1048576 286227 524288 61165463 73088368640 61263740853 549755813888 2626351435091 15327741847011328 qz426 (@Enclosure.Real.IsNear.neg qz141 Bool.false 286227 524288 61165463 73088368640 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 572454 1048576 61165463 73088368640 286227 524288 61165463 73088368640 (ep560 rfl rfl) rfl)) rfl)

noncomputable def ep562 := @ep547 240029218368 0 1 22605123207768071248075 263914916601600638189568 632481256320454067375941 ep542 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (ep548 ep561))

noncomputable def ep563 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 120215326577 240029218368 0 1 Bool.false

noncomputable def ep564 := @Enclosure.Complex.IsNear.addLitP qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 415967393 833434786 0 1 Bool.true 86607000

noncomputable def ep565 := @ep564 416717393 0 1 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1 Bool.false 240430653154 120215326577 240029218368 0 1 Bool.false 1931503472839 1931503472839 10001217432000 0 1

noncomputable abbrev qz144 := (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz272 (1 : Complex)))

noncomputable def ep566 := @Enclosure.Complex.IsNear.addLitP qz144 qz89 Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1

noncomputable def ep567 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (Enclosure.sfrac Bool.true 48000000 53339826304) (Enclosure.sfrac Bool.true 11085696000 53339826304)) Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1

noncomputable def ep568 := @ep566 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 53243826304 415967393 833434786 0 1 Bool.true 11085696000 86607000 416717393 0 1 (ep567 (BSN.N_div_s_sub_one_mk qz13 115476 1000 24 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 53339826304) (Enclosure.sfrac Bool.true 11085696000 53339826304) Bool.true 48000000 53339826304 0 1 Bool.true 11085696000 53339826304 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 53339826304) (Enclosure.Real.IsNear.const Bool.true 11085696000 53339826304))) qz90 rfl

noncomputable abbrev qz145 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz427 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz559 qz560 1))

noncomputable abbrev qz146 := qz427

noncomputable def ep569 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146)) Bool.false 1 576 0 1

noncomputable def ep570 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146) Bool.false 0 1 0 1 Bool.false

noncomputable def ep571 := @ep570 0 1 0 1 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1 Bool.false 1 1 576 0 1 Bool.false 9623 9623 24000 0

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep573 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz146 Bool.false 1 576 0 1 Bool.false 9623 24000 0 1

noncomputable abbrev qz147 := (Complex.re qz427)

noncomputable abbrev qz148 := (Complex.im qz427)

noncomputable def ep574 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) 1 576 0 1 0 1 0

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 1 24 0 1 1

noncomputable def ep576 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow37.d8 rfl) qz378

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep580 := ep579 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz84 qz13) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 115476 1000 qz14) (@Enclosure.Complex.IsNear.mk qz84 qz13 Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 qz370 qz18))

noncomputable def ep581 := @ep577 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep582 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 115476 1000 0 1 0 1 0

noncomputable def ep583 := @ep582 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep584 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 9623 1000 0 1 0 1 0 1 9623

noncomputable def ep585 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 115476 1000 0 1 9623 1000 0

noncomputable def ep586 := @ep585 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep588 := @ep587 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep589 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 (@ep576 1 24 0 1 (ep581 rfl) (ep583 rfl) rfl rfl) (@ep584 9623 1000 0 1 (ep586 rfl) (ep588 rfl) rfl rfl)

noncomputable def ep590 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 ep589

noncomputable abbrev qz149 := (@Enclosure.Complex.IsNear.re_isNear qz427 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz283) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow37.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz283 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz295)))

noncomputable def ep591 := @ep575 576 0 1 ep590 qz149

noncomputable def ep592 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 9623 1000 0 1 0 1 0 1 0

noncomputable def ep593 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 9623 1000 0 1 ep589

noncomputable abbrev qz150 := (@Enclosure.Complex.IsNear.im_isNear qz427 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (Enclosure.sfrac Bool.false 1 24) qz283) Bool.false 1 24 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 24 1 24 EMRow37.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 24) qz283 Bool.false 1 24 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 24) qz295)))

noncomputable def ep594 := @ep592 1 0 1 ep593 qz150

noncomputable def ep595 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 0 1 0 1 9623 24000 0

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 1 24 0 1 0 1 0 1 0

noncomputable def ep597 := @ep596 1 0 1 ep590 qz150

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 9623 1000 0 1 1 24 0 1 9623

noncomputable def ep599 := @ep598 24000 0 1 ep593 qz149

noncomputable def ep600 := @ep571 1 (@ep572 0 1 0 1 (BSN.bern_sum_base qz5 24) qz105) (ep573 (@ep574 1 1 1 576 0 1 (ep591 rfl) (ep594 rfl) rfl rfl) (@ep595 1 9623 9623 24000 0 1 (ep597 rfl) (ep599 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep601 := ep565 (ep568 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep569 Bool.false 9623 24000 0 1 (BSN.bern_sum_succ qz5 24 0 1 1 rfl rfl) (ep600 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 61263740853 549755813888 2626351435091 15327741847011328 1931503472839

noncomputable def ep603 := @ep602 10001217432000 0 1 39443709405559340063889 ep543 ep544 ep545 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (ep548 ep561))

noncomputable def ep604 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 120215326577 240029218368 0 1 Bool.false

noncomputable def ep605 := nat_lit 10162096447045371734555987

noncomputable def ep606 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 14527889320931576362661 439858194336001063649280 ep605

noncomputable def ep607 := nat_lit 306592157907051141390139392000

noncomputable def ep608 := nat_lit 3679105894884613696681672704

noncomputable def ep609 := nat_lit 572949871477742265314096538260266718546886656

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 188038612475 1099511627776 5261236435733 30655483694022656 1931503472839

noncomputable def ep611 := @ep610 10001217432000 0 1 14527889320931576362661 439858194336001063649280 ep605 ep607 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (ep548 ep561))

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_tf qz138 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 61263740853 549755813888 2626351435091 15327741847011328 120215326577

noncomputable def ep613 := @ep612 240029218368 0 1 818315623774676838909 14661939811200035454976 315727695475437182713507 ep608 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 188038612475 1099511627776 5261236435733 30655483694022656 Bool.true 61263740853 549755813888 2626351435091 15327741847011328 (ep548 ep561))

noncomputable abbrev qz428 := (ep601 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep614 := @ep540 39077358034171881529931 439858194336001063649280 ep430 ep294 (@ep541 ep542 39443709405559340063889 ep543 ep544 ep545 ep546 ep428 ep292 ep429 ep294 (ep562 (@ep563 1931503472839 10001217432000 0 1 qz428) rfl) (ep603 (@ep604 1931503472839 10001217432000 0 1 qz428) rfl) rfl rfl) (@ep606 ep607 818315623774676838909 14661939811200035454976 315727695475437182713507 ep608 ep609 39077358034171881529931 439858194336001063649280 ep430 ep294 (ep611 (@ep604 1931503472839 10001217432000 0 1 qz428) rfl) (ep613 (@ep563 1931503472839 10001217432000 0 1 qz428) rfl) rfl rfl)

noncomputable def ep615 := @ep433 ep425 ep294 (@ep434 30655483694022656 (BSN.head_sum_c_eq qz5 24) (ep435 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep539 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep614 rfl rfl rfl

noncomputable def ep616 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 24) Bool.false ep291 ep292 ep293 ep294 Bool.false 28866593669426799394549 439858194336001063649280 ep425 ep294 (@ep426 ep294 Bool.false 28866593669426799394549 439858194336001063649280 ep425 ep294 (BSN.zetaApproximant_eq_folded' qz5 1 24 rfl) (ep615 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 24)) 55 262144 50537351

noncomputable def ep618 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 220 1048576 50537351

noncomputable def ep619 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz357 Bool.false 28824183 262144 355

noncomputable def ep620 := nat_lit 4640499176291679666443864970583904983643075061696619213832543383402782570643456

noncomputable def ep621 := nat_lit 13888003943180182773598856792082140533895855085487266027850154100327212573065216

noncomputable def ep622 := BSN.cos_dyadic_bound_f 3372806732 2147483648 3 2 1048576 279083 ep620 ep57 ep421 ep621 ep60 ep421 220 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372806732) qz287 0 2 ep620 ep57 ep421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372806732) qz288 0 2 ep621 ep60 ep421 rfl rfl rfl rfl) rfl rfl

noncomputable def ep623 := @ep619 1048576 Bool.false 220 1048576 1 139405 (@ep299 28824183 262144 355 1048576 ep419 rfl) (Enclosure.sfrac_false_div 28824183 262144) (BSN.sin_reduce1 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335043538710163357696) qz291) 226375608064910080 72057594037927936 Bool.false 220 1048576 17 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 28824183 262144 226375608064910080 72057594037927936 17 59335043538710163357696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 220 1048576 59335043538710163357696 37778931862957161709568 3372806732 2147483648 279083 278810 (ep622 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep624 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 24) Bool.false ep291 ep292 ep293 ep294 Bool.false 28866593669426799394549 439858194336001063649280 ep425 ep294 (@ep426 ep294 Bool.false 28866593669426799394549 439858194336001063649280 ep425 ep294 (BSN.zetaApproximant_eq_folded' qz5 1 24 rfl) (ep615 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow37.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 24 qz13) Bool.true ep277 ep278 ep279 ep280 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 24 qz13) ep281 Bool.true ep277 ep278 ep279 ep280 (@Eq.refl Real ep281) (@ep282 Bool.true ep277 ep278 ep279 ep280 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) (zetaApproximant qz5 1 24)) (@ep284 ep278 ep285 ep280 317532530363694793340039 ep286 ep287 ep288 ep289 ep277 ep278 ep279 ep280 (@ep290 146176737280 ep291 ep292 ep293 ep294 ep283 ep278 ep285 ep280 (@ep295 146176737280 1048575 1048576 50537351 146176737280 (ep424 rfl rfl) rfl) ep616 rfl) (@ep617 146176737280 28866593669426799394549 439858194336001063649280 ep425 ep294 317532530363694793340039 ep286 ep287 ep288 (@ep618 146176737280 55 262144 50537351 146176737280 (ep623 rfl rfl) rfl) ep624 rfl) rfl rfl))

noncomputable abbrev qz585 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 117628 1000)))

noncomputable abbrev qz568 := qz585

noncomputable abbrev qz429 := qz568

noncomputable abbrev qz151 := (BSN.headSumC qz429 9)

noncomputable abbrev qz152 := qz429

noncomputable abbrev qz569 := (@Neg.neg Complex Complex.instNeg qz585)

noncomputable abbrev qz430 := qz569

noncomputable abbrev qz153 := qz430

noncomputable abbrev qz431 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz153)

noncomputable def ep625 := @Enclosure.Complex.IsNear.of_eq qz151 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 8) qz431) Bool.false 1694563523977 1099511627776 441115854405507 153277418470113280 Bool.false 35777219993 137438953472 55073670808689 19159677308764160

noncomputable def ep626 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 8) qz431 Bool.false 335866536975 274877906944 98701357459321 38319354617528320 Bool.false 29836901403 274877906944 98587054281241 38319354617528320 Bool.false

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz153)

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 7) qz432) Bool.false 335866536975 274877906944 98701357459321 38319354617528320 Bool.false 29836901403 274877906944 98587054281241 38319354617528320

noncomputable def ep628 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 7) qz432 Bool.false 859469452175 549755813888 172653217848799 76638709235056640 Bool.false 297460420187 1099511627776 344918643190153 153277418470113280 Bool.true

noncomputable abbrev qz433 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz153)

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 6) qz433) Bool.false 859469452175 549755813888 172653217848799 76638709235056640 Bool.false 297460420187 1099511627776 344918643190153 153277418470113280

noncomputable def ep630 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 6) qz433 Bool.false 2151035425765 1099511627776 291843475701193 153277418470113280 Bool.false 87944062291 549755813888 145778403093349 76638709235056640 Bool.true

noncomputable def ep631 := nat_lit 1889993312769362467225600

noncomputable abbrev qz434 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz153)

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 5) qz434) Bool.false 2151035425765 1099511627776 291843475701193 153277418470113280 Bool.false 87944062291 549755813888 145778403093349 76638709235056640

noncomputable def ep633 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 5) qz434 Bool.false 907641314973 549755813888 23333208692663 15327741847011328 Bool.false 267564752897 549755813888 23303843475509 15327741847011328 Bool.false

noncomputable abbrev qz435 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz153)

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 4) qz435) Bool.false 907641314973 549755813888 23333208692663 15327741847011328 Bool.false 267564752897 549755813888 23303843475509 15327741847011328

noncomputable def ep635 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 4) qz435 Bool.false 1289420147511 1099511627776 167959300954317 153277418470113280 Bool.false 93705616025 274877906944 20970355992899 19159677308764160 Bool.false

noncomputable def ep636 := nat_lit 1995924359325424702980096

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz153)) Bool.false 1289420147511 1099511627776 167959300954317 153277418470113280 Bool.false 93705616025 274877906944 20970355992899 19159677308764160

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz153) Bool.false 1868476832641 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 549755813888 46189182924483 76638709235056640 Bool.true

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz153)) Bool.false 1868476832641 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 549755813888 46189182924483 76638709235056640

noncomputable def ep640 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz153) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz152)

noncomputable abbrev qz586 := (Enclosure.sfrac Bool.false 117628 1000)

noncomputable abbrev qz570 := qz586

noncomputable abbrev qz436 := qz570

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log qz285))

noncomputable abbrev qz155 := qz436

noncomputable abbrev qz437 := (@Eq.refl Real qz570)

noncomputable abbrev qz156 := qz437

noncomputable def ep642 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz153) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 768965204865 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 549755813888 46189182924483 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 2 qz156 rfl)

noncomputable def ep643 := nat_lit 5611840512509130786006779313723074877066502190125173888789155748986191099709985

noncomputable def ep644 := nat_lit 7593326366135418614004590674756041876214807393779914577198041336155397933601

noncomputable def ep645 := nat_lit 14685383575788266142737938389134638705469824619309335561322801561371963188300321

noncomputable def ep646 := BSN.sin_dyadic_bound_f 3055301043 2147483648 3 2 1048576 279083 ep643 ep64 ep644 ep645 ep66 ep644 1037103 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3055301043) qz292 0 2 ep643 ep64 ep644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3055301043) qz293 0 2 ep645 ep66 ep644 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz157 := (Enclosure.Real.IsNear.const Bool.false 117628 1000)

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10686739) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep647 := @Enclosure.Real.IsNear.cos_image qz154 qz438 Bool.false 10686739 131072 443 524288 Bool.false 1037103 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 667921191 8192000 4201 4978750 10686739 131072 443 524288 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz17 117628 1000 0 1 363408 524288 1 139405 667921191 8192000 4201 4978750 qz157 qz290 rfl) rfl) (Enclosure.sfrac_false_div 10686739 131072) (BSN.cos_reduce3 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26874712188105311387648) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 1037103 1048576 12 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 10686739 131072 226375608064910080 72057594037927936 12 26874712188105311387648 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1037103 1048576 26874712188105311387648 18889465931478580854784 3055301043 2147483648 279083 278810 (ep646 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep648 := nat_lit 3121063985334466178276657214590488728093041131133443233583841212252841898920481

noncomputable def ep649 := nat_lit 9348005303271127697601962462421954100526693778612769871597127554086214900894241

noncomputable def ep650 := BSN.cos_dyadic_bound_f 3055301043 2147483648 3 2 1048576 279083 ep648 ep57 ep644 ep649 ep60 ep644 154686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3055301043) qz287 0 2 ep648 ep57 ep644 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3055301043) qz288 0 2 ep649 ep60 ep644 rfl rfl rfl rfl) rfl rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.sin_image qz154 qz438 Bool.false 10686739 131072 443 524288 Bool.true 154686 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 667921191 8192000 4201 4978750 10686739 131072 443 524288 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz17 117628 1000 0 1 363408 524288 1 139405 667921191 8192000 4201 4978750 qz157 qz290 rfl) rfl) (Enclosure.sfrac_false_div 10686739 131072) (BSN.sin_reduce3 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26874712188105311387648) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 154686 1048576 12 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 10686739 131072 226375608064910080 72057594037927936 12 26874712188105311387648 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 154686 1048576 26874712188105311387648 18889465931478580854784 3055301043 2147483648 279083 278810 (ep650 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep652 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 768965204865 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 549755813888 46189182924483 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz154) 741455 1048576 1 1048576 1037103 1048576 62280703 73088368640 768965204865 1099511627776 92501379190851 153277418470113280 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 1037103 1048576 62280703 73088368640 1037103 1048576 62280703 73088368640 (ep647 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 741455 1048576 1 1048576 77343 524288 62280703 73088368640 57346354065 549755813888 46189182924483 76638709235056640 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 77343 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 154686 1048576 62280703 73088368640 77343 524288 62280703 73088368640 (ep651 rfl rfl) rfl)) rfl)

noncomputable def ep653 := @ep640 768965204865 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 549755813888 46189182924483 76638709235056640 Bool.false 1868476832641 1868476832641 1099511627776 92501379190851 153277418470113280 Bool.false 57346354065 57346354065 549755813888 46189182924483 76638709235056640 (ep641 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz19)) (ep642 ep652) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz153) (Complex.mk (@HMul.hMul Real Real Real qz0 qz20 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz20 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 289528342565 549755813888 37728960881733 76638709235056640 Bool.false 130064877985 549755813888 37692241047113 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 3 qz156 rfl)

noncomputable def ep655 := nat_lit 675846673515707463003856959759689281

noncomputable def ep656 := BSN.cos_dyadic_bound_f 906696721 2147483648 2 1 1048576 279083 ep655 ep109 ep655 ep655 ep110 ep655 956494 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 906696721) qz287 0 1 ep655 ep109 ep655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 906696721) qz288 0 1 ep655 ep110 ep655 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33876217) qz16)

noncomputable def ep657 := @Enclosure.Real.IsNear.cos_image qz158 qz439 Bool.false 33876217 262144 885 1048576 Bool.true 956494 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 16938108523 131072000 4201 4978750 33876217 262144 885 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz23 117628 1000 0 1 575989 524288 1 139405 16938108523 131072000 4201 4978750 qz157 qz298 rfl) rfl) (Enclosure.sfrac_false_div 33876217 262144) (BSN.cos_reduce2 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15950777406947363651584) qz291) 226375608064910080 72057594037927936 Bool.false 956494 1048576 20 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 33876217 262144 226375608064910080 72057594037927936 20 15950777406947363651584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956494 1048576 15950777406947363651584 37778931862957161709568 906696721 2147483648 279083 278810 (ep656 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep658 := BSN.sin_dyadic_bound_f 906696721 2147483648 2 1 1048576 279083 ep655 ep113 ep655 ep655 ep114 ep655 429686 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 906696721) qz292 0 1 ep655 ep113 ep655 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 906696721) qz293 0 1 ep655 ep114 ep655 rfl rfl rfl rfl) rfl rfl

noncomputable def ep659 := @Enclosure.Real.IsNear.sin_image qz158 qz439 Bool.false 33876217 262144 885 1048576 Bool.true 429686 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 16938108523 131072000 4201 4978750 33876217 262144 885 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz23 117628 1000 0 1 575989 524288 1 139405 16938108523 131072000 4201 4978750 qz157 qz298 rfl) rfl) (Enclosure.sfrac_false_div 33876217 262144) (BSN.sin_reduce2 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15950777406947363651584) qz291) 226375608064910080 72057594037927936 Bool.false 429686 1048576 20 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 33876217 262144 226375608064910080 72057594037927936 20 15950777406947363651584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429686 1048576 15950777406947363651584 37778931862957161709568 906696721 2147483648 279083 278810 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz20 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz20 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 289528342565 549755813888 37728960881733 76638709235056640 Bool.false 130064877985 549755813888 37692241047113 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ft qz20 (Real.cos qz158) 605395 1048576 1 1048576 478247 524288 124422001 146176737280 289528342565 549755813888 37728960881733 76638709235056640 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 956494 1048576 124422001 146176737280 478247 524288 124422001 146176737280 (ep657 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz20 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 605395 1048576 1 1048576 214843 524288 124422001 146176737280 130064877985 549755813888 37692241047113 76638709235056640 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 214843 524288 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 429686 1048576 124422001 146176737280 214843 524288 124422001 146176737280 (ep659 rfl rfl) rfl)) rfl)

noncomputable def ep661 := @ep638 289528342565 549755813888 37728960881733 76638709235056640 Bool.false 130064877985 549755813888 37692241047113 76638709235056640 Bool.false 708866222638494822432768 1289420147511 1099511627776 167959300954317 153277418470113280 Bool.false 103030414407400580710400 93705616025 274877906944 20970355992899 19159677308764160 (ep639 (BSN.head_sum_c_succ qz152 2 3 rfl rfl) (ep653 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep654 ep660) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq qz435 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 525862482435 1099511627776 65372785972313 153277418470113280 Bool.false 80153520847 549755813888 32637793405949 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 4 qz156 rfl)

noncomputable def ep663 := nat_lit 3616628146058619022994476357313694712486707796861503173855332535927719103365120

noncomputable def ep664 := nat_lit 3156797563425149658432307262779978477792889737672012446890682571560226717696

noncomputable def ep665 := nat_lit 9467010329336551960776642914538985234215427170300086958992809822313881094127616

noncomputable def ep666 := BSN.sin_dyadic_bound_f 2737825988 2147483648 3 2 1048576 279083 ep663 ep64 ep664 ep665 ep66 ep664 1003005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2737825988) qz292 0 2 ep663 ep64 ep664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2737825988) qz293 0 2 ep665 ep66 ep664 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42747015) qz16)

noncomputable def ep667 := @Enclosure.Real.IsNear.cos_image qz159 qz440 Bool.false 42747015 262144 885 1048576 Bool.false 1003005 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 21373507519 131072000 4201 4978750 42747015 262144 885 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz27 117628 1000 0 1 726817 524288 1 139405 21373507519 131072000 4201 4978750 qz157 qz301 rfl) rfl) (Enclosure.sfrac_false_div 42747015 262144) (BSN.cos_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48164344147949933035520) qz291) 226375608064910080 72057594037927936 Bool.false 1003005 1048576 25 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 42747015 262144 226375608064910080 72057594037927936 25 48164344147949933035520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1003005 1048576 48164344147949933035520 37778931862957161709568 2737825988 2147483648 279083 278810 (ep666 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep668 := nat_lit 2010640880060755079289567890624399275149412282584244879896025045547204047077376

noncomputable def ep669 := nat_lit 6025609045055414938551839057347637868492651068277390614794293771498491687796736

noncomputable def ep670 := BSN.cos_dyadic_bound_f 2737825988 2147483648 3 2 1048576 279083 ep668 ep57 ep664 ep669 ep60 ep664 305762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2737825988) qz287 0 2 ep668 ep57 ep664 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2737825988) qz288 0 2 ep669 ep60 ep664 rfl rfl rfl rfl) rfl rfl

noncomputable def ep671 := @Enclosure.Real.IsNear.sin_image qz159 qz440 Bool.false 42747015 262144 885 1048576 Bool.true 305762 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 21373507519 131072000 4201 4978750 42747015 262144 885 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz27 117628 1000 0 1 726817 524288 1 139405 21373507519 131072000 4201 4978750 qz157 qz301 rfl) rfl) (Enclosure.sfrac_false_div 42747015 262144) (BSN.sin_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48164344147949933035520) qz291) 226375608064910080 72057594037927936 Bool.false 305762 1048576 25 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 42747015 262144 226375608064910080 72057594037927936 25 48164344147949933035520 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 305762 1048576 48164344147949933035520 37778931862957161709568 2737825988 2147483648 279083 278810 (ep670 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep672 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 525862482435 1099511627776 65372785972313 153277418470113280 Bool.false 80153520847 549755813888 32637793405949 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz159) 524287 1048576 1 1048576 1003005 1048576 124422001 146176737280 525862482435 1099511627776 65372785972313 153277418470113280 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 1003005 1048576 124422001 146176737280 1003005 1048576 124422001 146176737280 (ep667 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 524287 1048576 1 1048576 152881 524288 124422001 146176737280 80153520847 549755813888 32637793405949 76638709235056640 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 152881 524288 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 305762 1048576 124422001 146176737280 152881 524288 124422001 146176737280 (ep671 rfl rfl) rfl)) rfl)

noncomputable def ep673 := @ep635 525862482435 1099511627776 65372785972313 153277418470113280 Bool.false 80153520847 549755813888 32637793405949 76638709235056640 Bool.false ep636 907641314973 549755813888 23333208692663 15327741847011328 Bool.false 73547639248315920416768 267564752897 549755813888 23303843475509 15327741847011328 (ep637 (BSN.head_sum_c_succ qz152 3 4 rfl rfl) (ep661 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep662 ep672) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz436 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep674 := @Enclosure.Complex.IsNear.of_eq qz434 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 335752795819 1099511627776 58511388774563 153277418470113280 Bool.true 89810345303 274877906944 7314796428951 19159677308764160 (BSN.cpow_neg_s_mk qz155 117628 1000 5 qz156 rfl)

noncomputable def ep675 := nat_lit 342283555474465007473602640371042073577069883846997855404508898752859478163456

noncomputable def ep676 := nat_lit 91723747248727315263647205404381176335939029494140721149547579350320152576

noncomputable def ep677 := nat_lit 1026667218928897567790280626702317458378537773482005284771227601099877794185216

noncomputable def ep678 := BSN.cos_dyadic_bound_f 1759179776 2147483648 3 2 1048576 279083 ep675 ep57 ep676 ep677 ep60 ep676 715987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1759179776) qz287 0 2 ep675 ep57 ep676 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1759179776) qz288 0 2 ep677 ep60 ep676 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99255447) qz33)

noncomputable def ep679 := @Enclosure.Real.IsNear.cos_image qz160 qz441 Bool.false 99255447 524288 443 524288 Bool.false 715987 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 775433183 4096000 4201 4978750 99255447 524288 443 524288 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz30 117628 1000 0 1 843808 524288 1 139405 775433183 4096000 4201 4978750 qz157 qz304 rfl) rfl) (Enclosure.sfrac_false_div 99255447 524288) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61895635821875360169984) qz309) 226375608064910080 72057594037927936 Bool.false 715987 1048576 30 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 99255447 524288 226375608064910080 72057594037927936 30 61895635821875360169984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 715987 1048576 61895635821875360169984 75557863725914323419136 1759179776 2147483648 279083 278810 (ep678 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep680 := nat_lit 9577251549830322550294630977268350976

noncomputable def ep681 := BSN.sin_dyadic_bound_f 1759179776 2147483648 2 1 1048576 279083 ep680 ep113 ep680 ep680 ep114 ep680 766076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1759179776) qz292 0 1 ep680 ep113 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1759179776) qz293 0 1 ep680 ep114 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable def ep682 := @Enclosure.Real.IsNear.sin_image qz160 qz441 Bool.false 99255447 524288 443 524288 Bool.false 766076 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 775433183 4096000 4201 4978750 99255447 524288 443 524288 (@Enclosure.Real.IsNear.mulLit_ff qz155 qz30 117628 1000 0 1 843808 524288 1 139405 775433183 4096000 4201 4978750 qz157 qz304 rfl) rfl) (Enclosure.sfrac_false_div 99255447 524288) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61895635821875360169984) qz309) 226375608064910080 72057594037927936 Bool.false 766076 1048576 30 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 99255447 524288 226375608064910080 72057594037927936 30 61895635821875360169984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 766076 1048576 61895635821875360169984 75557863725914323419136 1759179776 2147483648 279083 278810 (ep681 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep683 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 335752795819 1099511627776 58511388774563 153277418470113280 Bool.true 89810345303 274877906944 7314796428951 19159677308764160 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz160) 468937 1048576 1 1048576 715987 1048576 62280703 73088368640 335752795819 1099511627776 58511388774563 153277418470113280 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 715987 1048576 62280703 73088368640 715987 1048576 62280703 73088368640 (ep679 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 468937 1048576 1 1048576 191519 262144 62280703 73088368640 89810345303 274877906944 7314796428951 19159677308764160 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 191519 262144 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 766076 1048576 62280703 73088368640 191519 262144 62280703 73088368640 (ep682 rfl rfl) rfl)) rfl)

noncomputable def ep684 := @ep633 335752795819 1099511627776 58511388774563 153277418470113280 Bool.true 89810345303 274877906944 7314796428951 19159677308764160 Bool.false 1182544231193358180024320 2151035425765 1099511627776 291843475701193 153277418470113280 Bool.false 24173879770702837448704 87944062291 549755813888 145778403093349 76638709235056640 (ep634 (BSN.head_sum_c_succ qz152 4 5 rfl rfl) (ep673 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep674 ep683) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz436 qz540)

noncomputable def ep685 := @Enclosure.Complex.IsNear.of_eq qz433 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 432096521415 1099511627776 10692591999281 30655483694022656 Bool.false 121572295605 1099511627776 10672367400691 30655483694022656 (BSN.cpow_neg_s_mk qz155 117628 1000 6 qz156 rfl)

noncomputable def ep686 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz540 117628 1000 0 1 4034681531866359 2251799813685248 100000000027881 13940500000000000000 118647879807594019113 562949953421312000 420100000117128081 497875000000000000000 qz157 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000278810 139405000000000000000 4034681531866359 2251799813685248 100000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep687 := nat_lit 120336162045468456990026525818045456

noncomputable def ep688 := BSN.cos_dyadic_bound_f 588977954 2147483648 2 1 1048576 279083 ep687 ep109 ep687 ep687 ep110 ep687 1009385 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 588977954) qz287 0 1 ep687 ep109 ep687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 588977954) qz288 0 1 ep687 ep110 ep687 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220998897) qz22)

noncomputable def ep689 := @Enclosure.Real.IsNear.cos_image qz161 qz442 Bool.false 220998897 1048576 443 524288 Bool.true 1009385 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 118647879807594019113 562949953421312000 420100000117128081 497875000000000000000 220998897 1048576 443 524288 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 220998897 1048576) (BSN.cos_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41445639007365668798464) qz24) 226375608064910080 72057594037927936 Bool.false 1009385 1048576 33 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 220998897 1048576 226375608064910080 72057594037927936 33 41445639007365668798464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009385 1048576 41445639007365668798464 151115727451828646838272 588977954 2147483648 279083 278810 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep690 := BSN.sin_dyadic_bound_f 588977954 2147483648 2 1 1048576 279083 ep687 ep113 ep687 ep687 ep114 ep687 283995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 588977954) qz292 0 1 ep687 ep113 ep687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 588977954) qz293 0 1 ep687 ep114 ep687 rfl rfl rfl rfl) rfl rfl

noncomputable def ep691 := @Enclosure.Real.IsNear.sin_image qz161 qz442 Bool.false 220998897 1048576 443 524288 Bool.true 283995 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 118647879807594019113 562949953421312000 420100000117128081 497875000000000000000 220998897 1048576 443 524288 (ep686 rfl) rfl) (Enclosure.sfrac_false_div 220998897 1048576) (BSN.sin_reduce2 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41445639007365668798464) qz24) 226375608064910080 72057594037927936 Bool.false 283995 1048576 33 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 220998897 1048576 226375608064910080 72057594037927936 33 41445639007365668798464 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283995 1048576 41445639007365668798464 151115727451828646838272 588977954 2147483648 279083 278810 (ep690 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep692 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 432096521415 1099511627776 10692591999281 30655483694022656 Bool.false 121572295605 1099511627776 10672367400691 30655483694022656 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz161) 428079 1048576 1 1048576 1009385 1048576 62280703 73088368640 432096521415 1099511627776 10692591999281 30655483694022656 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 1009385 1048576 62280703 73088368640 1009385 1048576 62280703 73088368640 (ep689 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 428079 1048576 1 1048576 283995 1048576 62280703 73088368640 121572295605 1099511627776 10672367400691 30655483694022656 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 283995 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 283995 1048576 62280703 73088368640 283995 1048576 62280703 73088368640 (ep691 rfl rfl) rfl)) rfl)

noncomputable def ep693 := @ep630 432096521415 1099511627776 10692591999281 30655483694022656 Bool.false 121572295605 1099511627776 10672367400691 30655483694022656 Bool.false ep631 859469452175 549755813888 172653217848799 76638709235056640 Bool.false 163530595399370650157056 297460420187 1099511627776 344918643190153 153277418470113280 (ep632 (BSN.head_sum_c_succ qz152 5 6 rfl rfl) (ep684 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep685 ep692) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz436 qz541)

noncomputable def ep694 := @Enclosure.Complex.IsNear.of_eq qz432 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 187736378225 549755813888 3535642438549 10948387033579520 Bool.true 178112814575 1099511627776 7061367704973 21896774067159040 (BSN.cpow_neg_s_mk qz155 117628 1000 7 qz156 rfl)

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz541 117628 1000 0 1 4381796493761783 2251799813685248 100000000027881 13940500000000000000 128855489492052752681 562949953421312000 420100000117128081 497875000000000000000 qz157 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 100000000027881 13940500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000278810 139405000000000000000 4381796493761783 2251799813685248 100000000027881 13940500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep696 := nat_lit 2214508057874179634664890225019771927401944656537363358482266940924982695525985

noncomputable def ep697 := nat_lit 1184369911567356000331204168774066225386322678583318047273899256791580245601

noncomputable def ep698 := nat_lit 5797984505051742371550366734969006559783039101832531042996065198863958786932321

noncomputable def ep699 := BSN.sin_dyadic_bound_f 2422065707 2147483648 3 2 1048576 279083 ep696 ep64 ep697 ep698 ep66 ep697 947386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2422065707) qz292 0 2 ep696 ep64 ep697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2422065707) qz293 0 2 ep698 ep66 ep697 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60003013) qz16)

noncomputable def ep700 := @Enclosure.Real.IsNear.cos_image qz162 qz443 Bool.false 60003013 262144 443 524288 Bool.true 947386 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 128855489492052752681 562949953421312000 420100000117128081 497875000000000000000 60003013 262144 443 524288 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 60003013 262144) (BSN.cos_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42609430530695612071936) qz291) 226375608064910080 72057594037927936 Bool.false 947386 1048576 36 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 60003013 262144 226375608064910080 72057594037927936 36 42609430530695612071936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 947386 1048576 42609430530695612071936 37778931862957161709568 2422065707 2147483648 279083 278810 (ep699 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep701 := nat_lit 1230808641001907510813975104641550655767918730377905562733381144628008866512481

noncomputable def ep702 := nat_lit 3690057183182587820441262905587103834852983545776550052105595635370443439046241

noncomputable def ep703 := BSN.cos_dyadic_bound_f 2422065707 2147483648 3 2 1048576 279083 ep701 ep57 ep697 ep702 ep60 ep697 449411 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2422065707) qz287 0 2 ep701 ep57 ep697 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2422065707) qz288 0 2 ep702 ep60 ep697 rfl rfl rfl rfl) rfl rfl

noncomputable def ep704 := @Enclosure.Real.IsNear.sin_image qz162 qz443 Bool.false 60003013 262144 443 524288 Bool.false 449411 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 128855489492052752681 562949953421312000 420100000117128081 497875000000000000000 60003013 262144 443 524288 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 60003013 262144) (BSN.sin_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42609430530695612071936) qz291) 226375608064910080 72057594037927936 Bool.false 449411 1048576 36 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 60003013 262144 226375608064910080 72057594037927936 36 42609430530695612071936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 449411 1048576 42609430530695612071936 37778931862957161709568 2422065707 2147483648 279083 278810 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 187736378225 549755813888 3535642438549 10948387033579520 Bool.true 178112814575 1099511627776 7061367704973 21896774067159040 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz162) 396325 1048576 1 1048576 473693 524288 62280703 73088368640 187736378225 549755813888 3535642438549 10948387033579520 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 947386 1048576 62280703 73088368640 473693 524288 62280703 73088368640 (ep700 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 396325 1048576 1 1048576 449411 1048576 62280703 73088368640 178112814575 1099511627776 7061367704973 21896774067159040 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 449411 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 449411 1048576 62280703 73088368640 449411 1048576 62280703 73088368640 (ep704 rfl rfl) rfl)) rfl)

noncomputable def ep706 := @ep628 187736378225 549755813888 3535642438549 10948387033579520 Bool.true 178112814575 1099511627776 7061367704973 21896774067159040 Bool.false 369289162784870341017600 335866536975 274877906944 98701357459321 38319354617528320 Bool.false 131224080117618192678912 29836901403 274877906944 98587054281241 38319354617528320 (ep629 (BSN.head_sum_c_succ qz152 6 7 rfl rfl) (ep693 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep694 ep705) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz436 qz542)

noncomputable def ep707 := @Enclosure.Complex.IsNear.of_eq qz431 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 351097376077 1099511627776 46310424568223 153277418470113280 Bool.false 41717538583 274877906944 11560287336137 38319354617528320 (BSN.cpow_neg_s_mk qz155 117628 1000 8 qz156 rfl)

noncomputable def ep708 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz542 117628 1000 0 1 9364972152248037 4503599627370496 200000000083643 27881000000000000000 275395736081158024059 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 39279540158062550581248 18889465931478580854784 1000000000418215 139405000000000000000 9364972152248037 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep147 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep709 := nat_lit 2208666345090588449981795366010295327288599840675200494698363338050662160977505

noncomputable def ep710 := nat_lit 1178132910629295728606107635148579408621436524467397838737056625625139039841

noncomputable def ep711 := nat_lit 5782694879096236604486958927189104347665707733109720746756805888929293529828961

noncomputable def ep712 := BSN.sin_dyadic_bound_f 2420467669 2147483648 3 2 1048576 279083 ep709 ep64 ep710 ep711 ep66 ep710 947051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2420467669) qz292 0 2 ep709 ep64 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2420467669) qz293 0 2 ep711 ep66 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256482265) qz22)

noncomputable def ep713 := @Enclosure.Real.IsNear.cos_image qz163 qz444 Bool.false 256482265 1048576 443 524288 Bool.false 947051 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 275395736081158024059 1125899906842624000 840200000351384243 995750000000000000000 256482265 1048576 443 524288 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 256482265 1048576) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170325270244477296967680) qz24) 226375608064910080 72057594037927936 Bool.false 947051 1048576 38 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 256482265 1048576 226375608064910080 72057594037927936 38 170325270244477296967680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 947051 1048576 170325270244477296967680 151115727451828646838272 2420467669 2147483648 279083 278810 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep714 := nat_lit 1227560473010606603647044584510230106008609438830430229427418324083979040116321

noncomputable def ep715 := nat_lit 3680325153210561219483921538260393159208585443442355892604780859000686842269281

noncomputable def ep716 := BSN.cos_dyadic_bound_f 2420467669 2147483648 3 2 1048576 279083 ep714 ep57 ep710 ep715 ep60 ep710 450116 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2420467669) qz287 0 2 ep714 ep57 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2420467669) qz288 0 2 ep715 ep60 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable def ep717 := @Enclosure.Real.IsNear.sin_image qz163 qz444 Bool.false 256482265 1048576 443 524288 Bool.true 450116 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 275395736081158024059 1125899906842624000 840200000351384243 995750000000000000000 256482265 1048576 443 524288 (ep708 rfl) rfl) (Enclosure.sfrac_false_div 256482265 1048576) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170325270244477296967680) qz24) 226375608064910080 72057594037927936 Bool.false 450116 1048576 38 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 256482265 1048576 226375608064910080 72057594037927936 38 170325270244477296967680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 450116 1048576 170325270244477296967680 151115727451828646838272 2420467669 2147483648 279083 278810 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 351097376077 1099511627776 46310424568223 153277418470113280 Bool.false 41717538583 274877906944 11560287336137 38319354617528320 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz163) 370727 1048576 1 1048576 947051 1048576 62280703 73088368640 351097376077 1099511627776 46310424568223 153277418470113280 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 947051 1048576 62280703 73088368640 947051 1048576 62280703 73088368640 (ep713 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 370727 1048576 1 1048576 112529 262144 62280703 73088368640 41717538583 274877906944 11560287336137 38319354617528320 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 112529 262144 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 450116 1048576 62280703 73088368640 112529 262144 62280703 73088368640 (ep717 rfl rfl) rfl)) rfl)

noncomputable def ep719 := @ep626 351097376077 1099511627776 46310424568223 153277418470113280 Bool.false 41717538583 274877906944 11560287336137 38319354617528320 Bool.false 465798074654446518796288 1694563523977 1099511627776 441115854405507 153277418470113280 Bool.false 19668734695901740662784 35777219993 137438953472 55073670808689 19159677308764160 (ep627 (BSN.head_sum_c_succ qz152 7 8 rfl rfl) (ep706 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep707 ep718) rfl rfl

theorem EMRow37.d11 : Enclosure.Complex.IsNear qz151 Bool.false 1694563523977 1099511627776 441115854405507 153277418470113280 Bool.false 35777219993 137438953472 55073670808689 19159677308764160 := ep625 (BSN.head_sum_c_succ qz152 8 9 rfl rfl) (ep719 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz164 := (BSN.headSumC qz429 17)

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz430)

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq qz164 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 16) qz165) Bool.false 2347483159709 1099511627776 741380487919793 153277418470113280 Bool.false 268061722897 1099511627776 740578244486753 153277418470113280

noncomputable def ep721 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 16) qz165 Bool.false 132457331273 68719476736 354303063202797 76638709235056640 Bool.false 114772555075 1099511627776 707843701640919 153277418470113280 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz430)

noncomputable def ep722 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 15) qz166) Bool.false 132457331273 68719476736 354303063202797 76638709235056640 Bool.false 114772555075 1099511627776 707843701640919 153277418470113280

noncomputable def ep723 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 15) qz166 Bool.false 2211134507921 1099511627776 674872588174987 153277418470113280 Bool.true 38465452301 274877906944 337009559978241 76638709235056640 Bool.true

noncomputable def ep724 := nat_lit 2330214014701457603821568

noncomputable abbrev qz445 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz153)

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 14) qz445) Bool.false 2211134507921 1099511627776 674872588174987 153277418470113280 Bool.true 38465452301 274877906944 337009559978241 76638709235056640

noncomputable def ep726 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 14) qz445 Bool.false 2455176277667 1099511627776 639882671985833 153277418470113280 Bool.false 4914904277 549755813888 159767293352827 38319354617528320 Bool.true

noncomputable def ep727 := nat_lit 1215584051017951737806848

noncomputable abbrev qz446 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz153)

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 13) qz446) Bool.false 2455176277667 1099511627776 639882671985833 153277418470113280 Bool.false 4914904277 549755813888 159767293352827 38319354617528320

noncomputable def ep729 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 13) qz446 Bool.false 2152302735839 1099511627776 603512044261709 153277418470113280 Bool.false 2834687581 68719476736 301413349097197 76638709235056640 Bool.false

noncomputable abbrev qz447 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz153)

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 12) qz447) Bool.false 2152302735839 1099511627776 603512044261709 153277418470113280 Bool.false 2834687581 68719476736 301413349097197 76638709235056640

noncomputable def ep731 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 12) qz447 Bool.false 2467172392997 1099511627776 80808934965093 21896774067159040 Bool.false 2675585585 549755813888 10091139039911 2737096758394880 Bool.true

noncomputable abbrev qz448 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz153)

noncomputable def ep732 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 11) qz448) Bool.false 2467172392997 1099511627776 80808934965093 21896774067159040 Bool.false 2675585585 549755813888 10091139039911 2737096758394880

noncomputable def ep733 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 11) qz448 Bool.false 1105096988207 549755813888 65771018590601 19159677308764160 Bool.true 204086085009 1099511627776 525630352812833 153277418470113280 Bool.false

noncomputable def ep734 := nat_lit 1356342366914070326542336

noncomputable abbrev qz449 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz153)

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 10) qz449) Bool.false 1105096988207 549755813888 65771018590601 19159677308764160 Bool.true 204086085009 1099511627776 525630352812833 153277418470113280

noncomputable def ep736 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 10) qz449 Bool.false 1937965044427 1099511627776 484750382974153 153277418470113280 Bool.false 12210082869 1099511627776 484236102036983 153277418470113280 Bool.false

noncomputable def ep737 := nat_lit 2430133976707667291275264

noncomputable abbrev qz450 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz153)

noncomputable def ep738 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 10) (@HAdd.hAdd Complex Complex Complex qz4 qz151 qz450) Bool.false 1937965044427 1099511627776 484750382974153 153277418470113280 Bool.false 12210082869 1099511627776 484236102036983 153277418470113280

noncomputable def ep739 := @Enclosure.Complex.IsNear.addLitP qz151 qz450 Bool.false 1694563523977 1099511627776 441115854405507 153277418470113280 Bool.false 35777219993 137438953472 55073670808689 19159677308764160 Bool.false

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz436 qz543)

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq qz450 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 121700760225 549755813888 21817264284323 76638709235056640 Bool.true 274007677075 1099511627776 43646735567471 153277418470113280 (BSN.cpow_neg_s_mk qz155 117628 1000 9 qz156 rfl)

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz543 117628 1000 0 1 9895417793173221 4503599627370496 200000000083643 27881000000000000000 290994551043844909947 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 41504390431577613533184 18889465931478580854784 1000000000418215 139405000000000000000 9895417793173221 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep742 := nat_lit 386582462836165732691705015311557286401824990395722713311828816832886971597056

noncomputable def ep743 := nat_lit 116994084187912106383938982345914121070775863816300702697171243640391762176

noncomputable def ep744 := nat_lit 1159513400340121373862347167969980030963333419459535538530092108011380131266816

noncomputable def ep745 := BSN.cos_dyadic_bound_f 1813512226 2147483648 3 2 1048576 279083 ep742 ep57 ep743 ep744 ep60 ep743 696378 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1813512226) qz287 0 2 ep742 ep57 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1813512226) qz288 0 2 ep744 ep60 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135504897) qz33)

noncomputable def ep746 := @Enclosure.Real.IsNear.cos_image qz167 qz451 Bool.false 135504897 524288 443 524288 Bool.false 696378 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 290994551043844909947 1125899906842624000 840200000351384243 995750000000000000000 135504897 524288 443 524288 (ep741 rfl) rfl) (Enclosure.sfrac_false_div 135504897 524288) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63807288968243654426624) qz309) 226375608064910080 72057594037927936 Bool.false 696378 1048576 41 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 135504897 524288 226375608064910080 72057594037927936 41 63807288968243654426624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 696378 1048576 63807288968243654426624 75557863725914323419136 1813512226 2147483648 279083 278810 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := nat_lit 10816380364424695396176001941049205776

noncomputable def ep748 := BSN.sin_dyadic_bound_f 1813512226 2147483648 2 1 1048576 279083 ep747 ep113 ep747 ep747 ep114 ep747 783943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1813512226) qz292 0 1 ep747 ep113 ep747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1813512226) qz293 0 1 ep747 ep114 ep747 rfl rfl rfl rfl) rfl rfl

noncomputable def ep749 := @Enclosure.Real.IsNear.sin_image qz167 qz451 Bool.false 135504897 524288 443 524288 Bool.false 783943 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 290994551043844909947 1125899906842624000 840200000351384243 995750000000000000000 135504897 524288 443 524288 (ep741 rfl) rfl) (Enclosure.sfrac_false_div 135504897 524288) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63807288968243654426624) qz309) 226375608064910080 72057594037927936 Bool.false 783943 1048576 41 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 135504897 524288 226375608064910080 72057594037927936 41 63807288968243654426624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 783943 1048576 63807288968243654426624 75557863725914323419136 1813512226 2147483648 279083 278810 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 121700760225 549755813888 21817264284323 76638709235056640 Bool.true 274007677075 1099511627776 43646735567471 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz167) 349525 1048576 1 1048576 348189 524288 62280703 73088368640 121700760225 549755813888 21817264284323 76638709235056640 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 696378 1048576 62280703 73088368640 348189 524288 62280703 73088368640 (ep746 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 349525 1048576 1 1048576 783943 1048576 62280703 73088368640 274007677075 1099511627776 43646735567471 153277418470113280 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 783943 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 783943 1048576 62280703 73088368640 783943 1048576 62280703 73088368640 (ep749 rfl rfl) rfl)) rfl)

noncomputable def ep751 := @ep739 121700760225 549755813888 21817264284323 76638709235056640 Bool.true 274007677075 1099511627776 43646735567471 153277418470113280 Bool.false 1065407550285459463602176 1937965044427 1099511627776 484750382974153 153277418470113280 Bool.false 1678141011321755271168 12210082869 1099511627776 484236102036983 153277418470113280 EMRow37.d11 (ep740 ep750) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz436 qz544)

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq qz449 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 272228931987 1099511627776 1183364735733 4379354813431808 Bool.true 108148083939 549755813888 591346439655 2189677406715904 (BSN.cpow_neg_s_mk qz155 117628 1000 10 qz156 rfl)

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz544 117628 1000 0 1 10369917190100709 4503599627370496 200000000083643 27881000000000000000 304948154809291549563 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000418215 139405000000000000000 10369917190100709 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep192 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep754 := nat_lit 154429290230438993291612295108829161543288906857485002293932726978485779690625

noncomputable def ep755 := nat_lit 18676556665953308282315475092970669315863191476677898358684517749062890625

noncomputable def ep756 := nat_lit 463250517577985073258272254376301543291234994189501651085080811899959213290625

noncomputable def ep757 := BSN.cos_dyadic_bound_f 1441823505 2147483648 3 2 1048576 279083 ep754 ep57 ep755 ep756 ep60 ep755 820983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1441823505) qz287 0 2 ep754 ep57 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1441823505) qz288 0 2 ep756 ep60 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71001275) qz16)

noncomputable def ep758 := @Enclosure.Real.IsNear.cos_image qz168 qz452 Bool.false 71001275 262144 443 524288 Bool.false 820983 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 304948154809291549563 1125899906842624000 840200000351384243 995750000000000000000 71001275 262144 443 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 71001275 262144) (BSN.cos_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25364827352904090255360) qz291) 226375608064910080 72057594037927936 Bool.false 820983 1048576 43 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 71001275 262144 226375608064910080 72057594037927936 43 25364827352904090255360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 820983 1048576 25364827352904090255360 37778931862957161709568 1441823505 2147483648 279083 278810 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := nat_lit 4321638192393401676296634113749250625

noncomputable def ep760 := BSN.sin_dyadic_bound_f 1441823505 2147483648 2 1 1048576 279083 ep759 ep113 ep759 ep759 ep114 ep759 652302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1441823505) qz292 0 1 ep759 ep113 ep759 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1441823505) qz293 0 1 ep759 ep114 ep759 rfl rfl rfl rfl) rfl rfl

noncomputable def ep761 := @Enclosure.Real.IsNear.sin_image qz168 qz452 Bool.false 71001275 262144 443 524288 Bool.false 652302 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 304948154809291549563 1125899906842624000 840200000351384243 995750000000000000000 71001275 262144 443 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 71001275 262144) (BSN.sin_reduce0 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25364827352904090255360) qz291) 226375608064910080 72057594037927936 Bool.false 652302 1048576 43 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 71001275 262144 226375608064910080 72057594037927936 43 25364827352904090255360 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 652302 1048576 25364827352904090255360 37778931862957161709568 1441823505 2147483648 279083 278810 (ep760 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep762 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 272228931987 1099511627776 1183364735733 4379354813431808 Bool.true 108148083939 549755813888 591346439655 2189677406715904 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz168) 331589 1048576 1 1048576 820983 1048576 62280703 73088368640 272228931987 1099511627776 1183364735733 4379354813431808 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 820983 1048576 62280703 73088368640 820983 1048576 62280703 73088368640 (ep758 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 331589 1048576 1 1048576 326151 524288 62280703 73088368640 108148083939 549755813888 591346439655 2189677406715904 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 326151 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 652302 1048576 62280703 73088368640 326151 524288 62280703 73088368640 (ep761 rfl rfl) rfl)) rfl)

noncomputable def ep763 := @ep736 272228931987 1099511627776 1183364735733 4379354813431808 Bool.true 108148083939 549755813888 591346439655 2189677406715904 Bool.false ep737 1105096988207 549755813888 65771018590601 19159677308764160 Bool.true 112197511767338350804992 204086085009 1099511627776 525630352812833 153277418470113280 (ep738 (BSN.head_sum_c_succ qz152 9 10 rfl rfl) (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep752 ep762) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz436 qz545)

noncomputable def ep764 := @Enclosure.Complex.IsNear.of_eq qz448 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 256978416583 1099511627776 39494396030843 153277418470113280 Bool.false 209437256179 1099511627776 39473433422183 153277418470113280 (BSN.cpow_neg_s_mk qz155 117628 1000 11 qz156 rfl)

noncomputable def ep765 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz545 117628 1000 0 1 10799156221662949 4503599627370496 200000000083643 27881000000000000000 317570787010442341243 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 45294944137145793642496 18889465931478580854784 1000000000418215 139405000000000000000 10799156221662949 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep766 := nat_lit 846754842054485324231889591575480476895676895906260693897219826705912056152320

noncomputable def ep767 := nat_lit 173274685140527284573163396358494496063121566233611472674544128001147044096

noncomputable def ep768 := nat_lit 2217410713033424519289449522913106543637908721028209303536959808022529718518016

noncomputable def ep769 := BSN.sin_dyadic_bound_f 1904767138 2147483648 3 2 1048576 279083 ep766 ep64 ep767 ep768 ep66 ep767 812819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1904767138) qz292 0 2 ep766 ep64 ep767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1904767138) qz293 0 2 ep768 ep66 ep767 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147880421) qz33)

noncomputable def ep770 := @Enclosure.Real.IsNear.cos_image qz169 qz453 Bool.false 147880421 524288 443 524288 Bool.false 812819 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 317570787010442341243 1125899906842624000 840200000351384243 995750000000000000000 147880421 524288 443 524288 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 147880421 524288) (BSN.cos_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67018035748478178557952) qz309) 226375608064910080 72057594037927936 Bool.false 812819 1048576 44 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 147880421 524288 226375608064910080 72057594037927936 44 67018035748478178557952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 812819 1048576 67018035748478178557952 75557863725914323419136 1904767138 2147483648 279083 278810 (ep769 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep771 := nat_lit 470496367668109858921971179051426262495848551755137546152977478893507207659776

noncomputable def ep772 := nat_lit 1411142553634048522196767210361561798495419412132945415513583348424519328891136

noncomputable def ep773 := BSN.cos_dyadic_bound_f 1904767138 2147483648 3 2 1048576 279083 ep771 ep57 ep767 ep772 ep60 ep767 662447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1904767138) qz287 0 2 ep771 ep57 ep767 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1904767138) qz288 0 2 ep772 ep60 ep767 rfl rfl rfl rfl) rfl rfl

noncomputable def ep774 := @Enclosure.Real.IsNear.sin_image qz169 qz453 Bool.false 147880421 524288 443 524288 Bool.true 662447 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 317570787010442341243 1125899906842624000 840200000351384243 995750000000000000000 147880421 524288 443 524288 (ep765 rfl) rfl) (Enclosure.sfrac_false_div 147880421 524288) (BSN.sin_reduce3 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67018035748478178557952) qz309) 226375608064910080 72057594037927936 Bool.false 662447 1048576 44 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 147880421 524288 226375608064910080 72057594037927936 44 67018035748478178557952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 662447 1048576 67018035748478178557952 75557863725914323419136 1904767138 2147483648 279083 278810 (ep773 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep775 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 256978416583 1099511627776 39494396030843 153277418470113280 Bool.false 209437256179 1099511627776 39473433422183 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz169) 316157 1048576 1 1048576 812819 1048576 62280703 73088368640 256978416583 1099511627776 39494396030843 153277418470113280 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 812819 1048576 62280703 73088368640 812819 1048576 62280703 73088368640 (ep770 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 316157 1048576 1 1048576 662447 1048576 62280703 73088368640 209437256179 1099511627776 39473433422183 153277418470113280 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 662447 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 662447 1048576 62280703 73088368640 662447 1048576 62280703 73088368640 (ep774 rfl rfl) rfl)) rfl)

noncomputable def ep776 := @ep733 256978416583 1099511627776 39494396030843 153277418470113280 Bool.false 209437256179 1099511627776 39473433422183 153277418470113280 Bool.false ep734 2467172392997 1099511627776 80808934965093 21896774067159040 Bool.false 5883674923634702417920 2675585585 549755813888 10091139039911 2737096758394880 (ep735 (BSN.head_sum_c_succ qz152 10 11 rfl rfl) (ep763 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep764 ep775) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz436 qz546)

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_eq qz447 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 157434828579 549755813888 18924749753029 76638709235056640 Bool.false 20001915063 549755813888 18861455979689 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 12 qz156 rfl)

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz546 117628 1000 0 1 11191020447815397 4503599627370496 200000000083643 27881000000000000000 329094338308907379579 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 46938541828353910898688 18889465931478580854784 1000000000418215 139405000000000000000 11191020447815397 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep779 := nat_lit 5424061235544103658381323694015121

noncomputable def ep780 := BSN.cos_dyadic_bound_f 271382067 2147483648 2 1 1048576 279083 ep779 ep109 ep779 ep779 ep110 ep779 1040214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 271382067) qz287 0 1 ep779 ep109 ep779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 271382067) qz288 0 1 ep779 ep110 ep779 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153246493) qz33)

noncomputable def ep781 := @Enclosure.Real.IsNear.cos_image qz170 qz454 Bool.false 153246493 524288 443 524288 Bool.true 1040214 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 329094338308907379579 1125899906842624000 840200000351384243 995750000000000000000 153246493 524288 443 524288 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 153246493 524288) (BSN.cos_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9548407649113217171456) qz309) 226375608064910080 72057594037927936 Bool.false 1040214 1048576 46 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 153246493 524288 226375608064910080 72057594037927936 46 9548407649113217171456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1040214 1048576 9548407649113217171456 75557863725914323419136 271382067 2147483648 279083 278810 (ep780 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep782 := BSN.sin_dyadic_bound_f 271382067 2147483648 1 0 1048576 279083 0 1 1 0 1 1 132158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 271382067) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 271382067) qz293 0 0 rfl) rfl rfl

noncomputable def ep783 := @Enclosure.Real.IsNear.sin_image qz170 qz454 Bool.false 153246493 524288 443 524288 Bool.true 132158 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 329094338308907379579 1125899906842624000 840200000351384243 995750000000000000000 153246493 524288 443 524288 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 153246493 524288) (BSN.sin_reduce2 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9548407649113217171456) qz309) 226375608064910080 72057594037927936 Bool.false 132158 1048576 46 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 153246493 524288 226375608064910080 72057594037927936 46 9548407649113217171456 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 132158 1048576 9548407649113217171456 75557863725914323419136 271382067 2147483648 279083 278810 (ep782 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep784 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 157434828579 549755813888 18924749753029 76638709235056640 Bool.false 20001915063 549755813888 18861455979689 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz170) 302697 1048576 1 1048576 520107 524288 62280703 73088368640 157434828579 549755813888 18924749753029 76638709235056640 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 1040214 1048576 62280703 73088368640 520107 524288 62280703 73088368640 (ep781 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 302697 1048576 1 1048576 66079 524288 62280703 73088368640 20001915063 549755813888 18861455979689 76638709235056640 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.true 66079 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.true 132158 1048576 62280703 73088368640 66079 524288 62280703 73088368640 (ep783 rfl rfl) rfl)) rfl)

noncomputable def ep785 := @ep731 157434828579 549755813888 18924749753029 76638709235056640 Bool.false 20001915063 549755813888 18861455979689 76638709235056640 Bool.false 1183240942274538511532032 2152302735839 1099511627776 603512044261709 153277418470113280 Bool.false 12467087825686887399424 2834687581 68719476736 301413349097197 76638709235056640 (ep732 (BSN.head_sum_c_succ qz152 11 12 rfl rfl) (ep776 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep777 ep784) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz436 qz547)

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq qz446 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 75718385457 274877906944 9092656931031 38319354617528320 Bool.true 17762596371 549755813888 18121237608457 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 13 qz156 rfl)

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz547 117628 1000 0 1 11551497052968677 4503599627370496 200000000083643 27881000000000000000 339694873836649884539 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 48450490295254733815808 18889465931478580854784 1000000000418215 139405000000000000000 11551497052968677 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep788 := nat_lit 3952855454123718048263098785327376

noncomputable def ep789 := BSN.cos_dyadic_bound_f 250742374 2147483648 2 1 1048576 279083 ep788 ep109 ep788 ep788 ep110 ep788 1041436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 250742374) qz287 0 1 ep788 ep109 ep788 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 250742374) qz288 0 1 ep788 ep110 ep788 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4943211) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep790 := @Enclosure.Real.IsNear.cos_image qz171 qz455 Bool.false 4943211 16384 443 524288 Bool.false 1041436 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 339694873836649884539 1125899906842624000 840200000351384243 995750000000000000000 4943211 16384 443 524288 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 4943211 16384) (BSN.cos_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275694156826124746752) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 1041436 1048576 48 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 4943211 16384 226375608064910080 72057594037927936 48 275694156826124746752 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1041436 1048576 275694156826124746752 2361183241434822606848 250742374 2147483648 279083 278810 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := BSN.sin_dyadic_bound_f 250742374 2147483648 1 0 1048576 279083 0 1 1 0 1 1 122154 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 250742374) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 250742374) qz293 0 0 rfl) rfl rfl

noncomputable def ep792 := @Enclosure.Real.IsNear.sin_image qz171 qz455 Bool.false 4943211 16384 443 524288 Bool.false 122154 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 339694873836649884539 1125899906842624000 840200000351384243 995750000000000000000 4943211 16384 443 524288 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 4943211 16384) (BSN.sin_reduce0 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275694156826124746752) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 122154 1048576 48 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 4943211 16384 226375608064910080 72057594037927936 48 275694156826124746752 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122154 1048576 275694156826124746752 2361183241434822606848 250742374 2147483648 279083 278810 (ep791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep793 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 75718385457 274877906944 9092656931031 38319354617528320 Bool.true 17762596371 549755813888 18121237608457 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz171) 290823 1048576 1 1048576 260359 262144 62280703 73088368640 75718385457 274877906944 9092656931031 38319354617528320 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 1041436 1048576 62280703 73088368640 260359 262144 62280703 73088368640 (ep790 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 290823 1048576 1 1048576 61077 524288 62280703 73088368640 17762596371 549755813888 18121237608457 76638709235056640 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 61077 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 122154 1048576 62280703 73088368640 61077 524288 62280703 73088368640 (ep792 rfl rfl) rfl)) rfl)

noncomputable def ep794 := @ep729 75718385457 274877906944 9092656931031 38319354617528320 Bool.true 17762596371 549755813888 18121237608457 76638709235056640 Bool.false 674873716383665931419648 2455176277667 1099511627776 639882671985833 153277418470113280 Bool.false 337749650122968399872 4914904277 549755813888 159767293352827 38319354617528320 (ep730 (BSN.head_sum_c_succ qz152 12 13 rfl rfl) (ep785 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep786 ep793) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz436 qz548)

noncomputable def ep795 := @Enclosure.Complex.IsNear.of_eq qz445 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 122020884873 549755813888 17494958094577 76638709235056640 Bool.true 81845808879 549755813888 17474973272587 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 14 qz156 rfl)

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz548 117628 1000 0 1 11885250371606245 4503599627370496 200000000083643 27881000000000000000 69901911535564969343 225179981368524800 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 49850353174629559828480 18889465931478580854784 1000000000418215 139405000000000000000 11885250371606245 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep797 := nat_lit 1261840572538153685312162804802064048626574365258430855401688546290455715840000

noncomputable def ep798 := nat_lit 384717210962403766547790714588780321258527374300688478298047352857600000000

noncomputable def ep799 := nat_lit 3304197671639320522100301399038928768739942864689879697087177925522757427200000

noncomputable def ep800 := BSN.sin_dyadic_bound_f 2104469820 2147483648 3 2 1048576 279083 ep797 ep64 ep798 ep799 ep66 ep798 870822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2104469820) qz292 0 2 ep797 ep64 ep798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2104469820) qz293 0 2 ep799 ep66 ep798 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 325506141) qz22)

noncomputable def ep801 := @Enclosure.Real.IsNear.cos_image qz172 qz456 Bool.false 325506141 1048576 885 1048576 Bool.true 870822 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 69901911535564969343 225179981368524800 840200000351384243 995750000000000000000 325506141 1048576 885 1048576 (ep796 rfl) rfl) (Enclosure.sfrac_false_div 325506141 1048576) (BSN.cos_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148088898413643213832192) qz24) 226375608064910080 72057594037927936 Bool.false 870822 1048576 49 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 325506141 1048576 226375608064910080 72057594037927936 49 148088898413643213832192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870822 1048576 148088898413643213832192 151115727451828646838272 2104469820 2147483648 279083 278810 (ep800 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep802 := nat_lit 701193525726068671291889465207630596046433992865484114546848324540412108800000

noncomputable def ep803 := nat_lit 2102811142756281206342572814193714227496784923847850966683948878915521126400000

noncomputable def ep804 := BSN.cos_dyadic_bound_f 2104469820 2147483648 3 2 1048576 279083 ep802 ep57 ep798 ep803 ep60 ep798 584106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2104469820) qz287 0 2 ep802 ep57 ep798 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2104469820) qz288 0 2 ep803 ep60 ep798 rfl rfl rfl rfl) rfl rfl

noncomputable def ep805 := @Enclosure.Real.IsNear.sin_image qz172 qz456 Bool.false 325506141 1048576 885 1048576 Bool.false 584106 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 69901911535564969343 225179981368524800 840200000351384243 995750000000000000000 325506141 1048576 885 1048576 (ep796 rfl) rfl) (Enclosure.sfrac_false_div 325506141 1048576) (BSN.sin_reduce1 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148088898413643213832192) qz24) 226375608064910080 72057594037927936 Bool.false 584106 1048576 49 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 325506141 1048576 226375608064910080 72057594037927936 49 148088898413643213832192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584106 1048576 148088898413643213832192 151115727451828646838272 2104469820 2147483648 279083 278810 (ep804 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep806 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 122020884873 549755813888 17494958094577 76638709235056640 Bool.true 81845808879 549755813888 17474973272587 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz172) 280243 1048576 1 1048576 435411 524288 124422001 146176737280 122020884873 549755813888 17494958094577 76638709235056640 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 870822 1048576 124422001 146176737280 435411 524288 124422001 146176737280 (ep801 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz56 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 280243 1048576 1 1048576 292053 524288 124422001 146176737280 81845808879 549755813888 17474973272587 76638709235056640 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 292053 524288 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 584106 1048576 124422001 146176737280 292053 524288 124422001 146176737280 (ep805 rfl rfl) rfl)) rfl)

noncomputable def ep807 := @ep726 122020884873 549755813888 17494958094577 76638709235056640 Bool.true 81845808879 549755813888 17474973272587 76638709235056640 Bool.false ep727 2211134507921 1099511627776 674872588174987 153277418470113280 Bool.true 42293212072612594712576 38465452301 274877906944 337009559978241 76638709235056640 (ep728 (BSN.head_sum_c_succ qz152 13 14 rfl rfl) (ep794 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep795 ep806) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz436 qz549)

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.true 91817207553 1099511627776 33733538230607 153277418470113280 Bool.false 268634364279 1099511627776 33824581684437 153277418470113280 (BSN.cpow_neg_s_mk qz155 117628 1000 15 qz156 rfl)

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz549 117628 1000 0 1 12195965485668069 4503599627370496 200000000083643 27881000000000000000 358646757037040905083 1125899906842624000 840200000351384243 995750000000000000000 qz157 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 200000000083643 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 51153586820399524478976 18889465931478580854784 1000000000418215 139405000000000000000 12195965485668069 4503599627370496 200000000083643 27881000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep253 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep810 := nat_lit 1807511990962888835261858729359813451208765450952007701004312322221565299571841

noncomputable def ep811 := nat_lit 2551982428467859978270984612688831401420219232909258190724108472798400658561

noncomputable def ep812 := nat_lit 5417432008031730785829034218854062690823455914390204586631488749719099097398401

noncomputable def ep813 := BSN.cos_dyadic_bound_f 2665997329 2147483648 3 2 1048576 279083 ep810 ep57 ep811 ep812 ep60 ep811 339133 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2665997329) qz287 0 2 ep810 ep57 ep811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2665997329) qz288 0 2 ep812 ep60 ep811 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 334015821) qz22)

noncomputable def ep814 := @Enclosure.Real.IsNear.cos_image qz173 qz457 Bool.false 334015821 1048576 885 1048576 Bool.true 339133 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 358646757037040905083 1125899906842624000 840200000351384243 995750000000000000000 334015821 1048576 885 1048576 (ep809 rfl) rfl) (Enclosure.sfrac_false_div 334015821 1048576) (BSN.cos_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187602884067636650442752) qz24) 226375608064910080 72057594037927936 Bool.false 339133 1048576 50 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 334015821 1048576 226375608064910080 72057594037927936 50 187602884067636650442752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 339133 1048576 187602884067636650442752 151115727451828646838272 2665997329 2147483648 279083 278810 (ep813 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep815 := nat_lit 3251479997790425615488728925157513147054641636327286455255182893220578818702465

noncomputable def ep816 := nat_lit 8511649165519309600600898924134847753350333454480087631454782830431270924106881

noncomputable def ep817 := BSN.sin_dyadic_bound_f 2665997329 2147483648 3 2 1048576 279083 ep815 ep64 ep811 ep816 ep66 ep811 992219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2665997329) qz292 0 2 ep815 ep64 ep811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2665997329) qz293 0 2 ep816 ep66 ep811 rfl rfl rfl rfl) rfl rfl

noncomputable def ep818 := @Enclosure.Real.IsNear.sin_image qz173 qz457 Bool.false 334015821 1048576 885 1048576 Bool.true 992219 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 358646757037040905083 1125899906842624000 840200000351384243 995750000000000000000 334015821 1048576 885 1048576 (ep809 rfl) rfl) (Enclosure.sfrac_false_div 334015821 1048576) (BSN.sin_reduce2 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187602884067636650442752) qz24) 226375608064910080 72057594037927936 Bool.false 992219 1048576 50 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 334015821 1048576 226375608064910080 72057594037927936 50 187602884067636650442752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 992219 1048576 187602884067636650442752 151115727451828646838272 2665997329 2147483648 279083 278810 (ep817 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep819 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.true 91817207553 1099511627776 33733538230607 153277418470113280 Bool.false 268634364279 1099511627776 33824581684437 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ft qz58 (Real.cos qz173) 270741 1048576 1 1048576 339133 1048576 124422001 146176737280 91817207553 1099511627776 33733538230607 153277418470113280 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.true 339133 1048576 124422001 146176737280 339133 1048576 124422001 146176737280 (ep814 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 270741 1048576 1 1048576 992219 1048576 124422001 146176737280 268634364279 1099511627776 33824581684437 153277418470113280 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 992219 1048576 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 992219 1048576 124422001 146176737280 992219 1048576 124422001 146176737280 (ep818 rfl rfl) rfl)) rfl)

noncomputable def ep820 := @ep723 91817207553 1099511627776 33733538230607 153277418470113280 Bool.false 268634364279 1099511627776 33824581684437 153277418470113280 Bool.false ep724 132457331273 68719476736 354303063202797 76638709235056640 Bool.false 31548439713630964940800 114772555075 1099511627776 707843701640919 153277418470113280 (ep725 (BSN.head_sum_c_succ qz152 14 15 rfl rfl) (ep807 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep808 ep819) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz436 qz550)

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 228165859341 1099511627776 32774361514199 153277418470113280 Bool.false 76644583911 549755813888 16367271422917 76638709235056640 (BSN.cpow_neg_s_mk qz155 117628 1000 16 qz156 rfl)

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz550 117628 1000 0 1 3121657384082679 1125899906842624 50000000027881 6970250000000000000 91798578693719341353 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 52372720210750067441664 18889465931478580854784 1000000000557620 139405000000000000000 3121657384082679 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep264 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep823 := nat_lit 1258011036497526700433422916025260975479154280894506368677952782522170021781760

noncomputable def ep824 := nat_lit 382386319878410965347708978587979298014994495468557365330182007094126059776

noncomputable def ep825 := nat_lit 3294171708213719169096020870291302969296236935064377110803151278594197662474496

noncomputable def ep826 := BSN.sin_dyadic_bound_f 2102871782 2147483648 3 2 1048576 279083 ep823 ep64 ep824 ep825 ep66 ep824 870387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2102871782) qz292 0 2 ep823 ep64 ep824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2102871782) qz293 0 2 ep825 ep66 ep824 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170988177) qz33)

noncomputable def ep827 := @Enclosure.Real.IsNear.cos_image qz174 qz458 Bool.false 170988177 524288 443 524288 Bool.false 870387 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 91798578693719341353 281474976710656000 210050000117128081 248937500000000000000 170988177 524288 443 524288 (ep822 rfl) rfl) (Enclosure.sfrac_false_div 170988177 524288) (BSN.cos_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73988223267669031256064) qz309) 226375608064910080 72057594037927936 Bool.false 870387 1048576 51 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 170988177 524288 226375608064910080 72057594037927936 51 73988223267669031256064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 870387 1048576 73988223267669031256064 75557863725914323419136 2102871782 2147483648 279083 278810 (ep826 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep828 := nat_lit 699064969751905238447611712893406310509759042494934008094564960071025179238656

noncomputable def ep829 := nat_lit 2096430136615958893412139720723042972933247138493864909553034516198887285596416

noncomputable def ep830 := BSN.cos_dyadic_bound_f 2102871782 2147483648 3 2 1048576 279083 ep828 ep57 ep824 ep829 ep60 ep824 584754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2102871782) qz287 0 2 ep828 ep57 ep824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2102871782) qz288 0 2 ep829 ep60 ep824 rfl rfl rfl rfl) rfl rfl

noncomputable def ep831 := @Enclosure.Real.IsNear.sin_image qz174 qz458 Bool.false 170988177 524288 443 524288 Bool.true 584754 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 91798578693719341353 281474976710656000 210050000117128081 248937500000000000000 170988177 524288 443 524288 (ep822 rfl) rfl) (Enclosure.sfrac_false_div 170988177 524288) (BSN.sin_reduce3 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73988223267669031256064) qz309) 226375608064910080 72057594037927936 Bool.false 584754 1048576 51 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 170988177 524288 226375608064910080 72057594037927936 51 73988223267669031256064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 584754 1048576 73988223267669031256064 75557863725914323419136 2102871782 2147483648 279083 278810 (ep830 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep832 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 228165859341 1099511627776 32774361514199 153277418470113280 Bool.false 76644583911 549755813888 16367271422917 76638709235056640 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz174) 262143 1048576 1 1048576 870387 1048576 62280703 73088368640 228165859341 1099511627776 32774361514199 153277418470113280 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 870387 1048576 62280703 73088368640 870387 1048576 62280703 73088368640 (ep827 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 262143 1048576 1 1048576 292377 524288 62280703 73088368640 76644583911 549755813888 16367271422917 76638709235056640 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 292377 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 584754 1048576 62280703 73088368640 292377 524288 62280703 73088368640 (ep831 rfl rfl) rfl)) rfl)

noncomputable def ep833 := @ep721 228165859341 1099511627776 32774361514199 153277418470113280 Bool.false 76644583911 549755813888 16367271422917 76638709235056640 Bool.false 161317814381774398029824 2347483159709 1099511627776 741380487919793 153277418470113280 Bool.false 147368490643459760193536 268061722897 1099511627776 740578244486753 153277418470113280 (ep722 (BSN.head_sum_c_succ qz152 15 16 rfl rfl) (ep820 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep821 ep832) rfl rfl

theorem EMRow37.d12 : Enclosure.Complex.IsNear qz164 Bool.false 2347483159709 1099511627776 741380487919793 153277418470113280 Bool.false 268061722897 1099511627776 740578244486753 153277418470113280 := ep720 (BSN.head_sum_c_succ qz152 16 17 rfl rfl) (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep834 := nat_lit 11141233668273411513963161202811

noncomputable def ep835 := nat_lit 3589314642377761097196660326400

noncomputable def ep836 := nat_lit 518267917914065716944998333881809515599

noncomputable def ep837 := nat_lit 69753857878300250293134013834733813760000

noncomputable abbrev qz571 := (@HAdd.hAdd Complex Complex Complex qz579 (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz586) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz459 := qz571

noncomputable abbrev qz175 := (Complex.Stirling.logGammaStirling 1 qz459)

noncomputable abbrev qz572 := (@HAdd.hAdd Complex Complex Complex qz579 qz582 (@HMul.hMul Complex Complex Complex qz581 Complex.I (@HDiv.hDiv Complex Complex Complex qz583 (↑qz586) (2 : Complex))))

noncomputable abbrev qz460 := qz572

noncomputable abbrev qz176 := qz460

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz436 (2 : Real)) (Real.log Real.pi))

noncomputable def ep838 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177))) (zetaApproximant qz152 1 24))

noncomputable def ep839 := @Enclosure.Real.IsNear.of_eq ep838 (@HSub.hSub Real Real Real qz356 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24))))

noncomputable def ep840 := nat_lit 371379578742686661698092942807

noncomputable def ep841 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24))) ep840

noncomputable def ep842 := nat_lit 119643821412592036573222010880

noncomputable def ep843 := nat_lit 28667465525636113902072596963269967067

noncomputable def ep844 := nat_lit 3875214326572236127396334101929656320000

noncomputable def ep845 := nat_lit 153694007188336979627081399

noncomputable def ep846 := nat_lit 2253538452615666707691588542950108393

noncomputable def ep847 := nat_lit 1332979771322861715367023287766810896166707876112920928583680

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz152 1 24)) 1048575 1048576 51373781

noncomputable def ep849 := nat_lit 26563162773956559738079747

noncomputable def ep850 := nat_lit 8557592969841387503616000

noncomputable def ep851 := nat_lit 3008444658104781359264987087

noncomputable def ep852 := nat_lit 477188499184295449976635392000

noncomputable def ep853 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.false 1048575 1048576 51373781

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118591747) qz22)

noncomputable def ep854 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz461 Bool.false 118591747 1048576 361

noncomputable def ep855 := nat_lit 3763501017024454878861067

noncomputable def ep856 := nat_lit 10963255296000000000000000000

noncomputable def ep857 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) Bool.false 101869535062122567031 900719925474099200 ep855 ep856

noncomputable def ep858 := nat_lit 1303811316024454878861067

noncomputable def ep859 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177 812557598180345408339 4503599627370496000 ep858 ep856 2206142547 32768000

noncomputable def ep860 := nat_lit 16690304624578161382359040000

noncomputable def ep861 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 416513275324499133049 4503599627370496000 805918555055561251661699 ep298 Bool.false 812557598180345408339 4503599627370496000

noncomputable def ep862 := nat_lit 522059776000000000000000000

noncomputable def ep863 := @Enclosure.Complex.IsNear.subLitP qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 379813467069302304049 4503599627370496000 113258765002194664129957 ep862 Bool.false 826591230553874544339 4503599627370496000 175024016573355946223581

noncomputable def ep864 := nat_lit 1566179328000000000000000000

noncomputable def ep865 := nat_lit 1875809031546279102015925403521122304

noncomputable def ep866 := nat_lit 228714631023879299976381771372560384

noncomputable abbrev qz462 := (@HSub.hSub Complex Complex Complex qz552 qz571 qz555)

noncomputable abbrev qz463 := (Complex.log qz571)

noncomputable abbrev qz178 := (@HSub.hSub Complex Complex Complex qz353 (@HMul.hMul Complex Complex Complex qz352 qz462 qz463) qz459)

noncomputable abbrev qz179 := qz459

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq qz175 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 379813467069302304049

noncomputable def ep868 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 379813710830585376049 4503599627370496000

noncomputable def ep869 := nat_lit 13050291357144210891423227052032

noncomputable def ep870 := nat_lit 3550182302389287134022906937344000

noncomputable def ep871 := @ep868 3456381818248810949 15932000000000000000000 Bool.false 826597602365475698387 4503599627370496000 1738671880046461 15558593750000000000 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000 Bool.true ep869 379813467069302304049 4503599627370496000 113258765002194664129957 ep862 Bool.false ep870

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP qz178 qz68 Bool.true 383952238237795872049 4503599627370496000 106587500019433057 497875000000000000000

noncomputable def ep873 := nat_lit 49782942705986486409494528

noncomputable def ep874 := @ep872 Bool.false 826597602365475698387 4503599627370496000 1738671880046461 15558593750000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep873 379813710830585376049 4503599627370496000 3456381818248810949 15932000000000000000000 Bool.false 826597602365475698387 826597602365475698387 4503599627370496000

noncomputable abbrev qz180 := (@HMul.hMul Complex Complex Complex qz352 qz462 qz463)

noncomputable def ep875 := @Enclosure.Complex.IsNear.subLitP qz180 qz179 Bool.true 373819139076212256049 4503599627370496000 106587500019433057 497875000000000000000 Bool.false 1091472310849644050131

noncomputable def ep876 := nat_lit 1535808952951183488196000

noncomputable def ep877 := nat_lit 3306390409461902793548000

noncomputable def ep878 := @ep875 4503599627370496000 1738671880046461 15558593750000000000 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 Bool.true ep876 383952238237795872049 4503599627370496000 106587500019433057 497875000000000000000 Bool.false ep877 826597602365475698387 4503599627370496000 1738671880046461 15558593750000000000

noncomputable abbrev qz181 := qz462

noncomputable abbrev qz182 := qz463

noncomputable def ep879 := @Enclosure.Complex.IsNear.mul qz181 qz182 Bool.true 373819139076212256049 4503599627370496000 106587500019433057 497875000000000000000 Bool.false 1091472310849644050131 4503599627370496000 1738671880046461

noncomputable abbrev qz183 := (Complex.re qz462)

noncomputable abbrev qz184 := (Complex.re qz463)

noncomputable abbrev qz185 := (Complex.im qz462)

noncomputable abbrev qz186 := (Complex.im qz463)

noncomputable def ep880 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz183 qz184) (@HMul.hMul Real Real Real qz0 qz185 qz186) 256937336114361931 36028797018963968 100000000306691 31864000000000000000 25371019130656718589 281474976710656000

noncomputable def ep881 := nat_lit 841765867723794568333142614870065152

noncomputable def ep882 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz184 7000 4000 0 1 36705333730623133 9007199254740992 100000000306691 55762000000000000000

noncomputable def ep883 := @Enclosure.Complex.IsNear.re_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable abbrev qz464 := (Enclosure.sfrac Bool.false 235256 4000)

noncomputable abbrev qz187 := qz464

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq qz181 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz187) Bool.false 7000 4000 0 1 Bool.false 235256 4000 0

noncomputable abbrev qz465 := (Complex.log (Complex.mk qz83 qz187))

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq qz182 qz465 Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000

noncomputable def ep886 := nat_lit 3459069744877859312544299509956199251601190753377157706484904115121392246381543698643025920

noncomputable def ep887 := nat_lit 79268541920322697702960323428826131945514254282386758290362393410129489196050729626763264

noncomputable def ep888 := nat_lit 7294927767333368300395402106415150053400352765210863431456816887969193315854587002880

noncomputable def ep889 := BSN.log_dyadic_bound 22658385536 88194385536 5 4 ep886 1048576 278810 ep887 ep888 551134 110852771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22658385536) (BSN.artanhQ 88194385536) 0 4 ep887 ep886 ep888 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz573 := (Real.log (Enclosure.sfrac Bool.false 55426385536 16000000))

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz573 1 2 0 1 36705333730623133 4503599627370496 100000000306691 27881000000000000000 36705333730623133 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 55426385536 16000000 36705333730623133 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55426385536) qz371)) Bool.false 307906656175375058468864 37778931862957161709568 1000000003066910 278810000000000000000 36705333730623133 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 55426385536 16000000 11 110852771072 65536000000 551134 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep889 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep891 := BSN.arctan_dyadic_bound_f 9000 235256 1 0 1048576 278810 0 1 1 0 1 1 40094 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz466 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 235256)))

noncomputable def ep892 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz466 884279719003555 562949953421312 1 2000000000000000 40094 1048576 1 278810 904663575201397604352 862754416657827 562949953421312 200000000027881 55762000000000000000 qz86 (ep891 rfl) rfl rfl

noncomputable abbrev qz467 := (Complex.mk qz83 qz187)

noncomputable abbrev qz468 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235256) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep893 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (ep885 (@congrArg Complex Complex qz179 qz467 Complex.log (BSN.w_shift_mk qz155 Bool.false 117628 1000 2 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz465 Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz465) (@HMul.hMul Real Real Real qz0 qz84 qz573) Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 9000 235256 4000 55426385536 16000000 rfl rfl rfl) (ep890 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz465) qz468 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 9000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz468 (@HSub.hSub Real Real Real qz356 qz85 qz466) Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 235256 9000 rfl rfl) ep892))))

noncomputable def ep894 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz186 235256 4000 0 1 862754416657827 562949953421312 200000000027881 55762000000000000000

noncomputable def ep895 := @Enclosure.Complex.IsNear.im_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable def ep896 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (ep885 (@congrArg Complex Complex qz179 qz467 Complex.log (BSN.w_shift_mk qz155 Bool.false 117628 1000 2 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz465 Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz465) (@HMul.hMul Real Real Real qz0 qz84 qz573) Bool.false 36705333730623133 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 9000 235256 4000 55426385536 16000000 rfl rfl rfl) (ep890 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz465) qz468 Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 9000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz468 (@HSub.hSub Real Real Real qz356 qz85 qz466) Bool.false 862754416657827 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 235256 9000 rfl rfl) ep892))))

noncomputable abbrev qz469 := (Enclosure.Real.IsNear.const Bool.false 235256 4000)

noncomputable abbrev qz188 := (@ep884 1 (BSN.w_sub_half_mk qz436 Bool.false 117628 1000 2 qz437 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz464 Bool.false 7000 4000 0 1 Bool.false 235256 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz469))

noncomputable def ep897 := @ep880 840200000117128081 3983000000000000000000 ep881 373819139076212256049 4503599627370496000 106587500019433057 497875000000000000000 (@ep882 256937336114361931 36028797018963968 100000000306691 31864000000000000000 (ep883 qz188) ep893 rfl) (@ep894 25371019130656718589 281474976710656000 840200000117128081 3983000000000000000000 (ep895 qz188) ep896 rfl) rfl

noncomputable def ep898 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz183 qz186) (@HMul.hMul Real Real Real qz0 qz185 qz184) 6039280916604789 2251799813685248 200000000027881 31864000000000000000 1079393749016434472131 4503599627370496000

noncomputable def ep899 := nat_lit 2457777146213835561266645311567167488

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz186 7000 4000 0 1 862754416657827 562949953421312 200000000027881 55762000000000000000

noncomputable def ep901 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz184 235256 4000 0 1 36705333730623133 9007199254740992 100000000306691 55762000000000000000

noncomputable def ep902 := @ep898 420100001288408891 3983000000000000000000 ep899 1091472310849644050131 4503599627370496000 1738671880046461 15558593750000000000 (@ep900 6039280916604789 2251799813685248 200000000027881 31864000000000000000 (ep883 qz188) ep896 rfl) (@ep901 1079393749016434472131 4503599627370496000 420100001288408891 3983000000000000000000 (ep895 qz188) ep893 rfl) rfl

noncomputable def ep903 := @Enclosure.Complex.IsNear.of_eq qz179 qz467 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 (BSN.w_shift_mk qz155 Bool.false 117628 1000 2 qz156 rfl)

noncomputable abbrev qz470 := (ep903 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 235256 4000) Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 235256 4000)))

noncomputable abbrev qz189 := qz470

noncomputable def ep904 := ep878 (@ep879 15558593750000000000 (ep897 rfl) (ep902 rfl)) qz189 rfl rfl rfl rfl rfl rfl

noncomputable def ep905 := @ep874 1738671880046461 15558593750000000000 (ep904 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep344 131072 3 1048576 (ep346 rfl) (ep348 rfl) rfl rfl) (@ep349 1 0 1 (ep351 rfl) (ep353 rfl) rfl rfl))

noncomputable abbrev qz471 := (@HPow.hPow Complex Int Complex qz557 qz571 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz190 := qz471

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190)) Bool.false 1859751 34359738368 3 34359738368

noncomputable def ep907 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep908 := @ep907 0 1 0 1 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000 Bool.false 1859751 1859751 34359738368 3 34359738368 Bool.true 6076633073 6076633073 4294967296000 29407

noncomputable def ep909 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz179 (@HSub.hSub Int Int Int qz365 qz73 (@HMul.hMul Int Int Int qz366 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep910 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz190 Bool.false 1859751 34359738368 3 34359738368 Bool.true 6076633073 4294967296000 29407 12884901888000

noncomputable abbrev qz191 := (Complex.re qz471)

noncomputable abbrev qz192 := (Complex.im qz471)

noncomputable def ep911 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) 1859751 34359738368 3 34359738368 0 1 0

noncomputable def ep912 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191 1 12 0 1 5579253 8589934592 9 8589934592 1859751

noncomputable def ep913 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407 1073741824000

noncomputable abbrev qz472 := (@HPow.hPow Complex Nat Complex qz559 qz571 1)

noncomputable abbrev qz193 := (@Inv.inv Complex Complex.instInv qz472)

noncomputable def ep914 := @Enclosure.Complex.IsNear.of_eq qz190 qz193 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_parts qz193 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407

noncomputable abbrev qz194 := (Complex.re qz472)

noncomputable abbrev qz195 := qz472

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) 9000 4000 0 1 619917 2147483648 1 2147483648

noncomputable def ep917 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable def ep918 := @Enclosure.Complex.IsNear.of_eq qz195 qz179 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0

noncomputable def ep919 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) Bool.false 619917 2147483648 1 2147483648 619917 2147483648 1

noncomputable abbrev qz196 := (Complex.im qz472)

noncomputable def ep920 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196)) Bool.false 433018637 125000 0 1

noncomputable def ep921 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196) 81 16 0 1 864771649 250000

noncomputable def ep922 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 9000 4000 0 1 9000 4000 0 1

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 235256 4000 0 1 235256 4000 0 1

noncomputable def ep924 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 235256 4000 0 1

noncomputable abbrev qz197 := (ep917 (@ep918 1 (BSN.pow_one_c qz459) qz470))

noncomputable abbrev qz198 := (ep924 (@ep918 1 (BSN.pow_one_c qz459) qz470))

noncomputable def ep925 := @ep921 0 1 13856596384 433018637 125000 0 1 (@ep922 81 16 0 1 qz197 qz197 rfl) (@ep923 864771649 250000 0 1 qz198 qz198 rfl)

noncomputable def ep926 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195) 433018637 125000 0 1 309958 309959 1073741824 (ep920 (Enclosure.Complex.normSq_eq_mul_add_mul qz195) (ep925 rfl rfl)) rfl

noncomputable def ep927 := @Enclosure.Real.IsNear.of_eq (Complex.re qz193) (@HMul.hMul Real Real Real qz0 qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195))) Bool.false 5579253 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz195) (@ep916 5579253 8589934592 9 8589934592 qz197 (@ep919 2147483648 (ep926 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep928 := @Enclosure.Real.IsNear.of_eq (Complex.im qz193) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195))) Bool.true 18229899219 1073741824000 29407 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz195)

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz195)) 235256 4000 0 1 619917 2147483648 1

noncomputable def ep930 := @ep929 2147483648 18229899219 1073741824000 29407 1073741824000 (@Enclosure.Real.IsNear.neg qz196 Bool.false 235256 4000 0 1 qz198) (@ep919 2147483648 (ep926 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 0 1 0 1 18229899219 1073741824000 29407 1073741824000 0

noncomputable def ep932 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 5579253 8589934592 9 8589934592 Bool.true 18229899219 1073741824000 29407 1073741824000

noncomputable abbrev qz199 := (@ep914 1073741824000 (BSN.zpow_one_sub_two_mul qz459 1 1 rfl rfl) (@ep915 1073741824000 ep927 (ep928 ep930)))

noncomputable def ep933 := @ep911 1 1859751 1859751 34359738368 3 34359738368 (@ep912 34359738368 3 34359738368 ep363 (ep913 qz199) rfl) (@ep931 1 0 1 ep383 (ep932 qz199) rfl) rfl

noncomputable def ep934 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191) 6076633073 4294967296000 29407 12884901888000 0 1 0

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz192 1 12 0 1 18229899219 1073741824000 29407 1073741824000 6076633073

noncomputable def ep936 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz191 0 1 0 1 5579253 8589934592 9 8589934592 0

noncomputable def ep937 := @ep934 1 6076633073 6076633073 4294967296000 29407 12884901888000 (@ep935 4294967296000 29407 12884901888000 ep363 (ep932 qz199) rfl) (@ep936 1 0 1 ep383 (ep913 qz199) rfl) rfl

noncomputable def ep938 := @ep908 12884901888000 (@ep909 0 1 0 1 (BSN.stirling_sum_base qz179) qz105) (ep910 (ep933 rfl) (ep937 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep939 := @ep871 826591230553874544339 4503599627370496000 175024016573355946223581 ep864 (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep906 Bool.true 6076633073 4294967296000 29407 12884901888000 (BSN.stirling_sum_succ qz179 0 1 rfl) (ep938 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz155 2) Bool.false 36699808255196829 4503599627370496 100000000306691 27881000000000000000 Bool.false 877102023345571 281474976710656

noncomputable abbrev qz200 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz460 qz376))

noncomputable def ep941 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz155 1) qz200) Bool.false 36699808255196829 4503599627370496 100000000306691 27881000000000000000 Bool.false 877102023345571 281474976710656 200000000027881 27881000000000000000

noncomputable def ep942 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz155 1) qz200 Bool.false 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000 Bool.false

noncomputable def ep943 := nat_lit 661124971130692368221200749428736

noncomputable def ep944 := nat_lit 987529086376255409735864418304

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz460 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep945 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz155 0) qz201) Bool.false 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000

noncomputable def ep946 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz155 0) qz201 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz473 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187))

noncomputable def ep947 := @Enclosure.Complex.IsNear.of_eq qz201 qz473 Bool.false 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000

noncomputable def ep948 := nat_lit 3434047868927634366734288422094270501264396036086285904230386109039076766754157637843025920

noncomputable def ep949 := nat_lit 78265180379036896710466750235418681157781778557439018633817879515419908247627418266763264

noncomputable def ep950 := nat_lit 7091406406465432244377964502050732669527078537342508802235242906230393117403387002880

noncomputable def ep951 := BSN.log_dyadic_bound 22578385536 88114385536 5 4 ep948 1048576 278810 ep949 ep950 549620 110692771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22578385536) (BSN.artanhQ 88114385536) 0 4 ep949 ep948 ep950 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 55346385536 16000000)) 1 2 0 1 36698831150136989 4503599627370496 100000000306691 27881000000000000000 36698831150136989 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 55346385536 16000000 36698831150136989 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55346385536) qz371)) Bool.false 307852108576688347021312 37778931862957161709568 1000000003066910 278810000000000000000 36698831150136989 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 55346385536 16000000 11 110692771072 65536000000 549620 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep951 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := BSN.arctan_dyadic_bound_f 1000 235256 1 0 1048576 278810 0 1 1 0 1 1 4457 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz474 := (@Nat.cast Real Real.instNatCast 235256)

noncomputable def ep954 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz474)) 884279719003555 562949953421312 1 2000000000000000 4457 1048576 1 278810 924725422691472900096 881886885348771 562949953421312 200000000027881 55762000000000000000 qz86 (ep953 rfl) rfl rfl

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz273 qz460 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz475 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187)

noncomputable def ep955 := @ep946 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000 Bool.false 36698831150136989 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 881886885348771 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz155 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz155) qz105) (ep947 (@congrArg Complex Complex qz202 qz475 Complex.log (BSN.w_shift_mk qz155 Bool.false 117628 1000 0 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz473 Bool.false 36698831150136989 9007199254740992 100000000306691 55762000000000000000 Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz473) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 55346385536 16000000))) Bool.false 36698831150136989 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 1000 235256 4000 55346385536 16000000 rfl rfl rfl) (ep952 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz473) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz474 qz382)) Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 1000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz474 qz382)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz382 qz474))) Bool.false 881886885348771 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 235256 1000 rfl rfl) ep954)))) rfl rfl

noncomputable abbrev qz476 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187))

noncomputable def ep956 := @Enclosure.Complex.IsNear.of_eq qz200 qz476 Bool.false 36700785360256669 9007199254740992 100000000306691 55762000000000000000 Bool.false 872317161342371 562949953421312 200000000027881 55762000000000000000

noncomputable def ep957 := nat_lit 3441537747903049393054523366380760521800662044986296192938283755434779992929733456083025920

noncomputable def ep958 := nat_lit 78565093187082140254608459747981724708543953489730588535979805404222694174266411674763264

noncomputable def ep959 := nat_lit 7151934484702835858936466975333836827311408436692508443855543599021176216938747002880

noncomputable def ep960 := BSN.log_dyadic_bound 22602385536 88138385536 5 4 ep957 1048576 278810 ep958 ep959 550075 110740771072 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 22602385536) (BSN.artanhQ 88138385536) 0 4 ep958 ep957 ep959 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 55370385536 16000000)) 1 2 0 1 36700785360256669 4503599627370496 100000000306691 27881000000000000000 36700785360256669 9007199254740992 100000000306691 55762000000000000000 qz370 (BSN.isNear_log_sfrac 55370385536 16000000 36700785360256669 4503599627370496 100000000306691 27881000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55370385536) qz371)) Bool.false 307868501679331975626752 37778931862957161709568 1000000003066910 278810000000000000000 36700785360256669 4503599627370496 100000000306691 27881000000000000000 (BSN.log_rat_reduce_isNear 55370385536 16000000 11 110740771072 65536000000 550075 1048576 24973259072661432 36028797018963968 278810 1000000000000000 rfl rfl rfl rfl (ep960 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep962 := BSN.arctan_dyadic_bound_f 5000 235256 1 0 1048576 278810 0 1 1 0 1 1 22282 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 235256) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 235256) 0 0 rfl) rfl rfl rfl

noncomputable def ep963 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz474)) 884279719003555 562949953421312 1 2000000000000000 22282 1048576 1 278810 914690839771738013696 872317161342371 562949953421312 200000000027881 55762000000000000000 qz86 (ep962 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz460 qz376)

noncomputable abbrev qz477 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187)

noncomputable def ep964 := @ep942 36700785360256669 9007199254740992 100000000306691 55762000000000000000 Bool.false 872317161342371 562949953421312 200000000027881 55762000000000000000 Bool.false ep943 36699808255196829 4503599627370496 100000000306691 27881000000000000000 Bool.false ep944 877102023345571 281474976710656 200000000027881 27881000000000000000 (ep945 (BSN.log_sum_c_succ qz155 0 1 rfl) (ep955 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep956 (@congrArg Complex Complex qz203 qz477 Complex.log (BSN.w_shift_mk qz155 Bool.false 117628 1000 1 qz156 rfl)) (@Enclosure.Complex.IsNear.of_parts qz476 Bool.false 36700785360256669 9007199254740992 100000000306691 55762000000000000000 Bool.false 872317161342371 562949953421312 200000000027881 55762000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz476) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 55370385536 16000000))) Bool.false 36700785360256669 9007199254740992 100000000306691 55762000000000000000 (Enclosure.clog_re_eq 5000 235256 4000 55370385536 16000000 rfl rfl rfl) (ep961 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz476) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz474 qz386)) Bool.false 872317161342371 562949953421312 200000000027881 55762000000000000000 (Enclosure.clog_im_eq 5000 235256 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz474 qz386)) (@HSub.hSub Real Real Real qz356 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz386 qz474))) Bool.false 872317161342371 562949953421312 200000000027881 55762000000000000000 (BSN.arctan_recip 235256 5000 rfl rfl) ep963)))) rfl rfl

noncomputable def ep965 := @ep863 ep864 Bool.false 36699808255196829 4503599627370496 100000000306691 27881000000000000000 Bool.false 877102023345571 281474976710656 200000000027881 27881000000000000000 Bool.true ep865 416513275324499133049 4503599627370496000 805918555055561251661699 ep298 Bool.false ep866 812557598180345408339 4503599627370496000 ep858 ep856 (@ep867 4503599627370496000 113258765002194664129957 ep862 Bool.false 826591230553874544339 4503599627370496000 175024016573355946223581 ep864 (BSN.logGammaStirling_unfold 1 qz179) (ep939 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep940 200000000027881 27881000000000000000 (BSN.log_sum_c_eq qz155 2) (ep941 (BSN.log_sum_c_succ qz155 1 2 rfl) (ep964 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz204 := (@HDiv.hDiv Real Real Real qz270 qz436 (2 : Real))

noncomputable def ep966 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 117628 2000 0 1 75021 65536 1 262144 2206142547 32768000 29407 131072000 (@Enclosure.Real.IsNear.of_eq qz204 (Enclosure.sfrac Bool.false 117628 2000) Bool.false 117628 2000 0 1 (BSN.t_half_eq qz155 Bool.false 117628 1000 qz156) (Enclosure.Real.IsNear.const Bool.false 117628 2000)) EMRow37.d5 rfl

noncomputable def ep967 := @ep859 29407 131072000 ep860 101869535062122567031 900719925474099200 ep855 ep856 (@ep861 ep858 ep856 (ep965 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep966 rfl rfl

noncomputable def ep968 := BSN.cos_dyadic_bound_f 1219174 2147483648 1 0 1048576 279083 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1219174) qz287 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1219174) qz288 0 0 rfl) rfl rfl

noncomputable def ep969 := @ep854 1048576 Bool.false 1048575 1048576 1 139405 (@ep857 118591747 1048576 361 1048576 ep967 rfl) (Enclosure.sfrac_false_div 118591747 1048576) (BSN.cos_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85791785793433370624) qz24) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 18 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 118591747 1048576 226375608064910080 72057594037927936 18 85791785793433370624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 85791785793433370624 151115727451828646838272 1219174 2147483648 279083 278810 (ep968 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep970 := nat_lit 1291546278893588064093121

noncomputable def ep971 := nat_lit 17115185939682775007232000

noncomputable def ep972 := nat_lit 3004688720184523884833447377

noncomputable abbrev qz478 := (@HPow.hPow Complex Complex Complex qz532 qz560 qz569)

noncomputable abbrev qz205 := qz478

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz429 (1 : Complex))) qz360)

noncomputable def ep973 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz152 1 24) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz62 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep849 ep850 ep851

noncomputable def ep974 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (@HMul.hMul Complex Complex Complex qz62 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 3524334641735 1099511627776 189496906533591 30655483694022656

noncomputable def ep975 := nat_lit 58703419917676253488175087

noncomputable def ep976 := nat_lit 58571437081622796112583377

noncomputable def ep977 := nat_lit 29206506340471824537529046836468252672

noncomputable def ep978 := nat_lit 710035075727162342320116043977064448

noncomputable def ep979 := @ep974 Bool.false 65627308659 549755813888 23658012108219 3831935461752832 Bool.true 867034953451435785430253 ep850 ep975 ep852 Bool.true 751585529892647336282879 ep971 ep976 ep852 Bool.false ep977 ep849 ep850 ep851 ep852 Bool.false ep978 ep970 ep971

noncomputable def ep980 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 24, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz153) (BSN.headSumC qz152 24) Bool.false 3524334641735 1099511627776 189496906533591 30655483694022656 Bool.false 65627308659 549755813888 23658012108219

noncomputable abbrev qz479 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz153)

noncomputable def ep981 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 23) qz479) Bool.false 3524334641735 1099511627776 189496906533591 30655483694022656 Bool.false 65627308659 549755813888 23658012108219 3831935461752832

noncomputable def ep982 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 23) qz479 Bool.false 898865403677 274877906944 115025572329317 19159677308764160 Bool.true 43348298115 549755813888 229736729088179 38319354617528320 Bool.true

noncomputable abbrev qz480 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz153)

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 22) qz480) Bool.false 898865403677 274877906944 115025572329317 19159677308764160 Bool.true 43348298115 549755813888 229736729088179 38319354617528320

noncomputable def ep984 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 22) qz480 Bool.false 429694518973 137438953472 111532426702441 19159677308764160 Bool.true 259950364989 1099511627776 890992180487433 153277418470113280 Bool.false

noncomputable abbrev qz481 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz153)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 21) qz481) Bool.false 429694518973 137438953472 111532426702441 19159677308764160 Bool.true 259950364989 1099511627776 890992180487433 153277418470113280

noncomputable def ep986 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 21) qz481 Bool.false 1598837057515 549755813888 431732490699339 76638709235056640 Bool.true 264894664333 1099511627776 862484015040033 153277418470113280 Bool.false

noncomputable abbrev qz482 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz153)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 20) qz482) Bool.false 1598837057515 549755813888 431732490699339 76638709235056640 Bool.true 264894664333 1099511627776 862484015040033 153277418470113280

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 20) qz482 Bool.false 1492371718685 549755813888 417066234638579 76638709235056640 Bool.true 141984607719 1099511627776 833205025237783 153277418470113280 Bool.false

noncomputable abbrev qz483 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz153)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 19) qz483) Bool.false 1492371718685 549755813888 417066234638579 76638709235056640 Bool.true 141984607719 1099511627776 833205025237783 153277418470113280

noncomputable def ep990 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 19) qz483 Bool.false 2804229647683 1099511627776 804063368913633 153277418470113280 Bool.false 17101243897 549755813888 200784608053147 38319354617528320 Bool.false

noncomputable def ep991 := nat_lit 3281760115316422208389120

noncomputable abbrev qz484 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz153)

noncomputable def ep992 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz152 18) qz484) Bool.false 2804229647683 1099511627776 804063368913633 153277418470113280 Bool.false 17101243897 549755813888 200784608053147 38319354617528320

noncomputable def ep993 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz152 18) qz484 Bool.false 325680978555 137438953472 48325006253551 9579838654382080 Bool.false 100239380183 549755813888 96536687255097 19159677308764160 Bool.false

noncomputable abbrev qz485 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz153)

noncomputable def ep994 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz152 18) (@HAdd.hAdd Complex Complex Complex qz4 qz164 qz485) Bool.false 325680978555 137438953472 48325006253551 9579838654382080 Bool.false 100239380183 549755813888 96536687255097 19159677308764160

noncomputable def ep995 := @Enclosure.Complex.IsNear.addLitP qz164 qz485 Bool.false 2347483159709 1099511627776 741380487919793 153277418470113280 Bool.false 268061722897 1099511627776 740578244486753 153277418470113280 Bool.false

noncomputable def ep996 := nat_lit 2864720182933508786749440

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz267 qz436 qz561)

noncomputable def ep997 := @Enclosure.Complex.IsNear.of_eq qz485 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207)))) Bool.false 257964668731 1099511627776 31819612137023 153277418470113280 Bool.true 67582962531 1099511627776 31715253554023 153277418470113280 (BSN.cpow_neg_s_mk qz155 117628 1000 17 qz156 rfl)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz561 117628 1000 0 1 3189913004350711 1125899906842624 50000000027881 6970250000000000000 93805771718941358377 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz392) Bool.false 53517859495200818200576 18889465931478580854784 1000000000557620 139405000000000000000 3189913004350711 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep999 := nat_lit 91667905777236539018894861684982016

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 550242748 2147483648 2 1 1048576 279083 ep999 ep109 ep999 ep999 ep110 ep999 1014343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 550242748) qz287 0 1 ep999 ep109 ep999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 550242748) qz288 0 1 ep999 ep110 ep999 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 349453731) qz22)

noncomputable def ep1001 := @Enclosure.Real.IsNear.cos_image qz207 qz486 Bool.false 349453731 1048576 443 524288 Bool.false 1014343 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 93805771718941358377 281474976710656000 210050000117128081 248937500000000000000 349453731 1048576 443 524288 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 349453731 1048576) (BSN.cos_reduce0 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38719891193061254889472) qz24) 226375608064910080 72057594037927936 Bool.false 1014343 1048576 53 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 349453731 1048576 226375608064910080 72057594037927936 53 38719891193061254889472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1014343 1048576 38719891193061254889472 151115727451828646838272 550242748 2147483648 279083 278810 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := BSN.sin_dyadic_bound_f 550242748 2147483648 2 1 1048576 279083 ep999 ep113 ep999 ep999 ep114 ep999 265743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 550242748) qz292 0 1 ep999 ep113 ep999 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 550242748) qz293 0 1 ep999 ep114 ep999 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1003 := @Enclosure.Real.IsNear.sin_image qz207 qz486 Bool.false 349453731 1048576 443 524288 Bool.false 265743 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 93805771718941358377 281474976710656000 210050000117128081 248937500000000000000 349453731 1048576 443 524288 (ep998 rfl) rfl) (Enclosure.sfrac_false_div 349453731 1048576) (BSN.sin_reduce0 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38719891193061254889472) qz24) 226375608064910080 72057594037927936 Bool.false 265743 1048576 53 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 349453731 1048576 226375608064910080 72057594037927936 53 38719891193061254889472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 265743 1048576 38719891193061254889472 151115727451828646838272 550242748 2147483648 279083 278810 (ep1002 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207))) Bool.false 257964668731 1099511627776 31819612137023 153277418470113280 Bool.true 67582962531 1099511627776 31715253554023 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz207) 254317 1048576 1 1048576 1014343 1048576 62280703 73088368640 257964668731 1099511627776 31819612137023 153277418470113280 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz207) Bool.false 1014343 1048576 62280703 73088368640 1014343 1048576 62280703 73088368640 (ep1001 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz123 (@Neg.neg Real Real.instNeg (Real.sin qz207)) 254317 1048576 1 1048576 265743 1048576 62280703 73088368640 67582962531 1099511627776 31715253554023 153277418470113280 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz207) Bool.false 265743 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz207) Bool.false 265743 1048576 62280703 73088368640 265743 1048576 62280703 73088368640 (ep1003 rfl rfl) rfl)) rfl)

noncomputable def ep1005 := @ep995 257964668731 1099511627776 31819612137023 153277418470113280 Bool.true 67582962531 1099511627776 31715253554023 153277418470113280 Bool.false ep996 325680978555 137438953472 48325006253551 9579838654382080 Bool.false 220428728144535293526016 100239380183 549755813888 96536687255097 19159677308764160 EMRow37.d12 (ep997 ep1004) rfl rfl

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz267 qz436 qz562)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.of_eq qz484 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 198781819243 1099511627776 30863268856817 153277418470113280 Bool.true 41569068143 274877906944 7711233542953 38319354617528320 (BSN.cpow_neg_s_mk qz155 117628 1000 18 qz156 rfl)

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz562 117628 1000 0 1 3254268794313975 1125899906842624 50000000027881 6970250000000000000 3827931297375642513 11258999068426240 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz396) Bool.false 54597570484265130393600 18889465931478580854784 1000000000557620 139405000000000000000 3254268794313975 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1008 := nat_lit 178944695974050158508175327567072831035176508149395406497830186832921656176161

noncomputable def ep1009 := nat_lit 25076010669082282704048592895810595727599092314690169756732910064579522081

noncomputable def ep1010 := nat_lit 536783935900812310959117885515426871914074326263556839153977094678635809484321

noncomputable def ep1011 := BSN.cos_dyadic_bound_f 1495916339 2147483648 3 2 1048576 279083 ep1008 ep57 ep1009 ep1010 ep60 ep1009 804293 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1495916339) qz287 0 2 ep1008 ep57 ep1009 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1495916339) qz288 0 2 ep1010 ep60 ep1009 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz487 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 356503883) qz22)

noncomputable def ep1012 := @Enclosure.Real.IsNear.cos_image qz208 qz487 Bool.false 356503883 1048576 885 1048576 Bool.false 804293 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 3827931297375642513 11258999068426240 210050000117128081 248937500000000000000 356503883 1048576 885 1048576 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 356503883 1048576) (BSN.cos_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105265754227348074397696) qz24) 226375608064910080 72057594037927936 Bool.false 804293 1048576 54 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 356503883 1048576 226375608064910080 72057594037927936 54 105265754227348074397696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 804293 1048576 105265754227348074397696 151115727451828646838272 1495916339 2147483648 279083 278810 (ep1011 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1013 := nat_lit 5007595298052976914913401049197252241

noncomputable def ep1014 := BSN.sin_dyadic_bound_f 1495916339 2147483648 2 1 1048576 279083 ep1013 ep113 ep1013 ep1013 ep114 ep1013 672772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1495916339) qz292 0 1 ep1013 ep113 ep1013 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1495916339) qz293 0 1 ep1013 ep114 ep1013 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1015 := @Enclosure.Real.IsNear.sin_image qz208 qz487 Bool.false 356503883 1048576 885 1048576 Bool.false 672772 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 3827931297375642513 11258999068426240 210050000117128081 248937500000000000000 356503883 1048576 885 1048576 (ep1007 rfl) rfl) (Enclosure.sfrac_false_div 356503883 1048576) (BSN.sin_reduce0 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105265754227348074397696) qz24) 226375608064910080 72057594037927936 Bool.false 672772 1048576 54 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 356503883 1048576 226375608064910080 72057594037927936 54 105265754227348074397696 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 672772 1048576 105265754227348074397696 151115727451828646838272 1495916339 2147483648 279083 278810 (ep1014 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 198781819243 1099511627776 30863268856817 153277418470113280 Bool.true 41569068143 274877906944 7711233542953 38319354617528320 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz208) 247151 1048576 1 1048576 804293 1048576 124422001 146176737280 198781819243 1099511627776 30863268856817 153277418470113280 qz398 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 804293 1048576 124422001 146176737280 804293 1048576 124422001 146176737280 (ep1012 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 247151 1048576 1 1048576 168193 262144 124422001 146176737280 41569068143 274877906944 7711233542953 38319354617528320 qz398 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.false 168193 262144 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.false 672772 1048576 124422001 146176737280 168193 262144 124422001 146176737280 (ep1015 rfl rfl) rfl)) rfl)

noncomputable def ep1017 := @ep993 198781819243 1099511627776 30863268856817 153277418470113280 Bool.true 41569068143 274877906944 7711233542953 38319354617528320 Bool.false 385410388072706789605376 2804229647683 1099511627776 804063368913633 153277418470113280 Bool.false 4700754128546213920768 17101243897 549755813888 200784608053147 38319354617528320 (ep994 (BSN.head_sum_c_succ qz152 17 18 rfl rfl) (ep1005 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1006 ep1016) rfl rfl

noncomputable abbrev qz209 := (@HMul.hMul Real Real Real qz267 qz436 qz563)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.of_eq qz483 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209)))) Bool.false 180513789687 1099511627776 6013820072705 30655483694022656 Bool.true 176187095513 1099511627776 6013318605039 30655483694022656 (BSN.cpow_neg_s_mk qz155 117628 1000 19 qz156 rfl)

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz563 117628 1000 0 1 3315143513283831 1125899906842624 50000000027881 6970250000000000000 97488425295137618217 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 55618878793361701994496 18889465931478580854784 1000000000557620 139405000000000000000 3315143513283831 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep477 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1020 := nat_lit 271746274083503513882471644858630505439021585630309278754322214989894464551521

noncomputable def ep1021 := nat_lit 57820903589652561971814675868956886534147844632866096727124859019560467041

noncomputable def ep1022 := nat_lit 815123180443331236523471305224153602543996461201662104069512395251644272720481

noncomputable def ep1023 := BSN.cos_dyadic_bound_f 1660583083 2147483648 3 2 1048576 279083 ep1020 ep57 ep1021 ep1022 ep60 ep1021 750393 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1660583083) qz287 0 2 ep1020 ep57 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1660583083) qz288 0 2 ep1022 ep60 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz488 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90793171) qz16)

noncomputable def ep1024 := @Enclosure.Real.IsNear.cos_image qz209 qz488 Bool.false 90793171 262144 443 524288 Bool.false 750393 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 97488425295137618217 281474976710656000 210050000117128081 248937500000000000000 90793171 262144 443 524288 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 90793171 262144) (BSN.cos_reduce0 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29213286543429795315712) qz291) 226375608064910080 72057594037927936 Bool.false 750393 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 90793171 262144 226375608064910080 72057594037927936 55 29213286543429795315712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 750393 1048576 29213286543429795315712 37778931862957161709568 1660583083 2147483648 279083 278810 (ep1023 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1025 := nat_lit 7604005759443673775669600295060742321

noncomputable def ep1026 := BSN.sin_dyadic_bound_f 1660583083 2147483648 2 1 1048576 279083 ep1025 ep113 ep1025 ep1025 ep114 ep1025 732407 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1660583083) qz292 0 1 ep1025 ep113 ep1025 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1660583083) qz293 0 1 ep1025 ep114 ep1025 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1027 := @Enclosure.Real.IsNear.sin_image qz209 qz488 Bool.false 90793171 262144 443 524288 Bool.false 732407 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz209 Bool.false 97488425295137618217 281474976710656000 210050000117128081 248937500000000000000 90793171 262144 443 524288 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 90793171 262144) (BSN.sin_reduce0 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29213286543429795315712) qz291) 226375608064910080 72057594037927936 Bool.false 732407 1048576 55 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 90793171 262144 226375608064910080 72057594037927936 55 29213286543429795315712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 732407 1048576 29213286543429795315712 37778931862957161709568 1660583083 2147483648 279083 278810 (ep1026 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1028 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz209)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209))) Bool.false 180513789687 1099511627776 6013820072705 30655483694022656 Bool.true 176187095513 1099511627776 6013318605039 30655483694022656 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz209) 240559 1048576 1 1048576 750393 1048576 62280703 73088368640 180513789687 1099511627776 6013820072705 30655483694022656 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz209) Bool.false 750393 1048576 62280703 73088368640 750393 1048576 62280703 73088368640 (ep1024 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz127 (@Neg.neg Real Real.instNeg (Real.sin qz209)) 240559 1048576 1 1048576 732407 1048576 62280703 73088368640 176187095513 1099511627776 6013318605039 30655483694022656 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz209) Bool.false 732407 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz209) Bool.false 732407 1048576 62280703 73088368640 732407 1048576 62280703 73088368640 (ep1027 rfl rfl) rfl)) rfl)

noncomputable def ep1029 := @ep990 180513789687 1099511627776 6013820072705 30655483694022656 Bool.true 176187095513 1099511627776 6013318605039 30655483694022656 Bool.false ep991 1492371718685 549755813888 417066234638579 76638709235056640 Bool.true 78056863576127252201472 141984607719 1099511627776 833205025237783 153277418470113280 (ep992 (BSN.head_sum_c_succ qz152 18 19 rfl rfl) (ep1017 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1018 ep1028) rfl rfl

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz267 qz436 qz564)

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq qz482 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 53232669415 274877906944 366656401519 1915967730876416 Bool.true 61455028307 549755813888 2927898980225 15327741847011328 (BSN.cpow_neg_s_mk qz155 117628 1000 20 qz156 rfl)

noncomputable def ep1031 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz564 117628 1000 0 1 3372893643545847 1125899906842624 50000000027881 6970250000000000000 99186683375752722729 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 56587765202795681021952 18889465931478580854784 1000000000557620 139405000000000000000 3372893643545847 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep491 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1032 := nat_lit 1597412211925920084298729158874997776

noncomputable def ep1033 := BSN.cos_dyadic_bound_f 1124227618 2147483648 2 1 1048576 279083 ep1032 ep109 ep1032 ep1032 ep110 ep1032 908140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1124227618) qz287 0 1 ep1032 ep109 ep1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1124227618) qz288 0 1 ep1032 ep110 ep1032 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 369499189) qz22)

noncomputable def ep1034 := @Enclosure.Real.IsNear.cos_image qz210 qz489 Bool.false 369499189 1048576 443 524288 Bool.false 908140 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 99186683375752722729 281474976710656000 210050000117128081 248937500000000000000 369499189 1048576 443 524288 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 369499189 1048576) (BSN.cos_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79110485702477126565888) qz24) 226375608064910080 72057594037927936 Bool.false 908140 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 369499189 1048576 226375608064910080 72057594037927936 56 79110485702477126565888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 908140 1048576 79110485702477126565888 151115727451828646838272 1124227618 2147483648 279083 278810 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := BSN.sin_dyadic_bound_f 1124227618 2147483648 2 1 1048576 279083 ep1032 ep113 ep1032 ep1032 ep114 ep1032 524206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1124227618) qz292 0 1 ep1032 ep113 ep1032 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1124227618) qz293 0 1 ep1032 ep114 ep1032 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1036 := @Enclosure.Real.IsNear.sin_image qz210 qz489 Bool.false 369499189 1048576 443 524288 Bool.false 524206 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 99186683375752722729 281474976710656000 210050000117128081 248937500000000000000 369499189 1048576 443 524288 (ep1031 rfl) rfl) (Enclosure.sfrac_false_div 369499189 1048576) (BSN.sin_reduce0 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79110485702477126565888) qz24) 226375608064910080 72057594037927936 Bool.false 524206 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 369499189 1048576 226375608064910080 72057594037927936 56 79110485702477126565888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524206 1048576 79110485702477126565888 151115727451828646838272 1124227618 2147483648 279083 278810 (ep1035 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1037 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 53232669415 274877906944 366656401519 1915967730876416 Bool.true 61455028307 549755813888 2927898980225 15327741847011328 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz210) 234469 1048576 1 1048576 227035 262144 62280703 73088368640 53232669415 274877906944 366656401519 1915967730876416 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 908140 1048576 62280703 73088368640 227035 262144 62280703 73088368640 (ep1034 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 234469 1048576 1 1048576 262103 524288 62280703 73088368640 61455028307 549755813888 2927898980225 15327741847011328 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 262103 524288 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 524206 1048576 62280703 73088368640 262103 524288 62280703 73088368640 (ep1036 rfl rfl) rfl)) rfl)

noncomputable def ep1038 := @ep988 53232669415 274877906944 366656401519 1915967730876416 Bool.true 61455028307 549755813888 2927898980225 15327741847011328 Bool.false 439484983914226945884160 1598837057515 549755813888 431732490699339 76638709235056640 Bool.true 145627381784976979656704 264894664333 1099511627776 862484015040033 153277418470113280 (ep989 (BSN.head_sum_c_succ qz152 19 20 rfl rfl) (ep1029 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1030 ep1037) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz436 qz565)

noncomputable def ep1039 := @Enclosure.Complex.IsNear.of_eq qz481 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 119941018377 549755813888 2879443222085 15327741847011328 Bool.false 309018709 68719476736 712704136185 3831935461752832 (BSN.cpow_neg_s_mk qz155 117628 1000 21 qz156 rfl)

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz565 117628 1000 0 1 3427826275261687 1125899906842624 50000000027881 6970250000000000000 100802087276620429609 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz408) Bool.false 57509381830540779323392 18889465931478580854784 1000000000557620 139405000000000000000 3427826275261687 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep502 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1041 := nat_lit 7913818001284369362447312289298858253083571839962648794813624305435354379386880

noncomputable def ep1042 := nat_lit 15083860056560414348089130265547078450048289327720068446939187026856698249216

noncomputable def ep1043 := nat_lit 20702244706129393373655578356305171583442609969562057208931114497144350625038336

noncomputable def ep1044 := BSN.sin_dyadic_bound_f 3329002044 2147483648 3 2 1048576 279083 ep1041 ep64 ep1042 ep1043 ep66 ep1042 1048353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3329002044) qz292 0 2 ep1041 ep64 ep1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3329002044) qz293 0 2 ep1043 ep66 ep1042 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz490 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 375517037) qz22)

noncomputable def ep1045 := @Enclosure.Real.IsNear.cos_image qz211 qz490 Bool.false 375517037 1048576 443 524288 Bool.false 1048353 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 100802087276620429609 281474976710656000 210050000117128081 248937500000000000000 375517037 1048576 443 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 375517037 1048576) (BSN.cos_reduce3 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234257693227576778031104) qz24) 226375608064910080 72057594037927936 Bool.false 1048353 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 375517037 1048576 226375608064910080 72057594037927936 56 234257693227576778031104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048353 1048576 234257693227576778031104 151115727451828646838272 3329002044 2147483648 279083 278810 (ep1044 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1046 := nat_lit 4403269494072009829958768663061831064357561373013791583095097586142688743325696

noncomputable def ep1047 := nat_lit 13179640762102908661180127728654399036172587540385934612391414384374352833478656

noncomputable def ep1048 := BSN.cos_dyadic_bound_f 3329002044 2147483648 3 2 1048576 279083 ep1046 ep57 ep1042 ep1047 ep60 ep1042 21608 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3329002044) qz287 0 2 ep1046 ep57 ep1042 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3329002044) qz288 0 2 ep1047 ep60 ep1042 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1049 := @Enclosure.Real.IsNear.sin_image qz211 qz490 Bool.false 375517037 1048576 443 524288 Bool.true 21608 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 100802087276620429609 281474976710656000 210050000117128081 248937500000000000000 375517037 1048576 443 524288 (ep1040 rfl) rfl) (Enclosure.sfrac_false_div 375517037 1048576) (BSN.sin_reduce3 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234257693227576778031104) qz24) 226375608064910080 72057594037927936 Bool.false 21608 1048576 56 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 375517037 1048576 226375608064910080 72057594037927936 56 234257693227576778031104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21608 1048576 234257693227576778031104 151115727451828646838272 3329002044 2147483648 279083 278810 (ep1048 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 119941018377 549755813888 2879443222085 15327741847011328 Bool.false 309018709 68719476736 712704136185 3831935461752832 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz211) 114409 524288 1 524288 1048353 1048576 62280703 73088368640 119941018377 549755813888 2879443222085 15327741847011328 qz410 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 1048353 1048576 62280703 73088368640 1048353 1048576 62280703 73088368640 (ep1045 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 114409 524288 1 524288 2701 131072 62280703 73088368640 309018709 68719476736 712704136185 3831935461752832 qz410 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 2701 131072 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 21608 1048576 62280703 73088368640 2701 131072 62280703 73088368640 (ep1049 rfl rfl) rfl)) rfl)

noncomputable def ep1051 := @ep986 119941018377 549755813888 2879443222085 15327741847011328 Bool.false 309018709 68719476736 712704136185 3831935461752832 Bool.false 944908240004857091588096 429694518973 137438953472 111532426702441 19159677308764160 Bool.true 17863653059376294395904 259950364989 1099511627776 890992180487433 153277418470113280 (ep987 (BSN.head_sum_c_succ qz152 20 21 rfl rfl) (ep1038 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1039 ep1050) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz436 qz566)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq qz480 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 39476365731 274877906944 873286406719 4789919327191040 Bool.false 173253768759 1099511627776 27954735865283 153277418470113280 (BSN.cpow_neg_s_mk qz155 117628 1000 22 qz156 rfl)

noncomputable def ep1053 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz566 117628 1000 0 1 3480203401436407 1125899906842624 50000000027881 6970250000000000000 102342341426040420649 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 58388124189833310502912 18889465931478580854784 1000000000557620 139405000000000000000 3480203401436407 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep517 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1054 := nat_lit 6345928190718815998808025979026810001

noncomputable def ep1055 := BSN.sin_dyadic_bound_f 1587171251 2147483648 2 1 1048576 279083 ep1054 ep113 ep1054 ep1054 ep114 ep1054 706332 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1587171251) qz292 0 1 ep1054 ep113 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1587171251) qz293 0 1 ep1054 ep114 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 381254931) qz22)

noncomputable def ep1056 := @Enclosure.Real.IsNear.cos_image qz212 qz491 Bool.false 381254931 1048576 443 524288 Bool.false 706332 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 102342341426040420649 281474976710656000 210050000117128081 248937500000000000000 381254931 1048576 443 524288 (ep1053 rfl) rfl) (Enclosure.sfrac_false_div 381254931 1048576) (BSN.cos_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111687247787817122660352) qz24) 226375608064910080 72057594037927936 Bool.false 706332 1048576 57 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 381254931 1048576 226375608064910080 72057594037927936 57 111687247787817122660352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 706332 1048576 111687247787817122660352 151115727451828646838272 1587171251 2147483648 279083 278810 (ep1055 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1057 := nat_lit 226778054634653026915788523511384288497917804836635704053432152254249028622881

noncomputable def ep1058 := nat_lit 40270804601759785521034413357259544707940729362032626791610750734153620001

noncomputable def ep1059 := nat_lit 680253622294755561176323501707438346404337533051183046906713235261278778628641

noncomputable def ep1060 := BSN.cos_dyadic_bound_f 1587171251 2147483648 3 2 1048576 279083 ep1057 ep57 ep1058 ep1059 ep60 ep1058 774987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1587171251) qz287 0 2 ep1057 ep57 ep1058 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1587171251) qz288 0 2 ep1059 ep60 ep1058 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1061 := @Enclosure.Real.IsNear.sin_image qz212 qz491 Bool.false 381254931 1048576 443 524288 Bool.true 774987 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 102342341426040420649 281474976710656000 210050000117128081 248937500000000000000 381254931 1048576 443 524288 (ep1053 rfl) rfl) (Enclosure.sfrac_false_div 381254931 1048576) (BSN.sin_reduce3 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111687247787817122660352) qz24) 226375608064910080 72057594037927936 Bool.false 774987 1048576 57 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q3 381254931 1048576 226375608064910080 72057594037927936 57 111687247787817122660352 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 774987 1048576 111687247787817122660352 151115727451828646838272 1587171251 2147483648 279083 278810 (ep1060 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 39476365731 274877906944 873286406719 4789919327191040 Bool.false 173253768759 1099511627776 27954735865283 153277418470113280 (@Enclosure.Real.IsNear.mulLit_ff qz133 (Real.cos qz212) 223557 1048576 1 1048576 176583 262144 62280703 73088368640 39476365731 274877906944 873286406719 4789919327191040 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 706332 1048576 62280703 73088368640 176583 262144 62280703 73088368640 (ep1056 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 223557 1048576 1 1048576 774987 1048576 62280703 73088368640 173253768759 1099511627776 27954735865283 153277418470113280 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 774987 1048576 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 774987 1048576 62280703 73088368640 774987 1048576 62280703 73088368640 (ep1061 rfl rfl) rfl)) rfl)

noncomputable def ep1063 := @ep984 39476365731 274877906944 873286406719 4789919327191040 Bool.false 173253768759 1099511627776 27954735865283 153277418470113280 Bool.false 123539120393553700716544 898865403677 274877906944 115025572329317 19159677308764160 Bool.true 95323915643485924884480 43348298115 549755813888 229736729088179 38319354617528320 (ep985 (BSN.head_sum_c_succ qz152 21 22 rfl rfl) (ep1051 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1052 ep1062) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz436 qz567)

noncomputable def ep1064 := @Enclosure.Complex.IsNear.of_eq qz479 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 71126972973 1099511627776 27279954033419 153277418470113280 Bool.false 54487803387 274877906944 6843391994011 38319354617528320 (BSN.cpow_neg_s_mk qz155 117628 1000 23 qz156 rfl)

noncomputable def ep1065 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz567 117628 1000 0 1 3530250507853047 1125899906842624 50000000027881 6970250000000000000 103814076684434553129 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz416) Bool.false 59227775304360265777152 18889465931478580854784 1000000000557620 139405000000000000000 3530250507853047 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep528 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1066 := nat_lit 1889939234348551494449251180981700019574654796900778578295799205124371837306401

noncomputable def ep1067 := nat_lit 2789684872023212454529055894750282457004662366954991198079071921842688050721

noncomputable def ep1068 := nat_lit 5664238333301608058438695431155599493809955065968425752491239471529430135817761

noncomputable def ep1069 := BSN.cos_dyadic_bound_f 2695841741 2147483648 3 2 1048576 279083 ep1066 ep57 ep1067 ep1068 ep60 ep1067 325311 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2695841741) qz287 0 2 ep1066 ep57 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2695841741) qz288 0 2 ep1068 ep60 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96684393) qz16)

noncomputable def ep1070 := @Enclosure.Real.IsNear.cos_image qz213 qz492 Bool.false 96684393 262144 443 524288 Bool.true 325311 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 103814076684434553129 281474976710656000 210050000117128081 248937500000000000000 96684393 262144 443 524288 (ep1065 rfl) rfl) (Enclosure.sfrac_false_div 96684393 262144) (BSN.cos_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47425749462100545110016) qz291) 226375608064910080 72057594037927936 Bool.false 325311 1048576 58 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 96684393 262144 226375608064910080 72057594037927936 58 47425749462100545110016 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 325311 1048576 47425749462100545110016 37778931862957161709568 2695841741 2147483648 279083 278810 (ep1069 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1071 := nat_lit 3399658873929774120045028881051259809268774904527837447973975311686395156710945

noncomputable def ep1072 := nat_lit 8899351846689942256143933359876084757440212439454980473230188271305194391684641

noncomputable def ep1073 := BSN.sin_dyadic_bound_f 2695841741 2147483648 3 2 1048576 279083 ep1071 ep64 ep1067 ep1072 ep66 ep1067 996836 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2695841741) qz292 0 2 ep1071 ep64 ep1067 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2695841741) qz293 0 2 ep1072 ep66 ep1067 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1074 := @Enclosure.Real.IsNear.sin_image qz213 qz492 Bool.false 96684393 262144 443 524288 Bool.true 996836 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 103814076684434553129 281474976710656000 210050000117128081 248937500000000000000 96684393 262144 443 524288 (ep1065 rfl) rfl) (Enclosure.sfrac_false_div 96684393 262144) (BSN.sin_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47425749462100545110016) qz291) 226375608064910080 72057594037927936 Bool.false 996836 1048576 58 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q2 96684393 262144 226375608064910080 72057594037927936 58 47425749462100545110016 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996836 1048576 47425749462100545110016 37778931862957161709568 2695841741 2147483648 279083 278810 (ep1073 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1075 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 71126972973 1099511627776 27279954033419 153277418470113280 Bool.false 54487803387 274877906944 6843391994011 38319354617528320 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz213) 218643 1048576 1 1048576 325311 1048576 62280703 73088368640 71126972973 1099511627776 27279954033419 153277418470113280 qz418 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 325311 1048576 62280703 73088368640 325311 1048576 62280703 73088368640 (ep1070 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 218643 1048576 1 1048576 249209 262144 62280703 73088368640 54487803387 274877906944 6843391994011 38319354617528320 qz418 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 249209 262144 62280703 73088368640 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 996836 1048576 62280703 73088368640 249209 262144 62280703 73088368640 (ep1074 rfl rfl) rfl)) rfl)

noncomputable def ep1076 := @ep982 71126972973 1099511627776 27279954033419 153277418470113280 Bool.false 54487803387 274877906944 6843391994011 38319354617528320 Bool.false 968761729690348908707840 3524334641735 1099511627776 189496906533591 30655483694022656 Bool.false 18039497242553767428096 65627308659 549755813888 23658012108219 3831935461752832 (ep983 (BSN.head_sum_c_succ qz152 22 23 rfl rfl) (ep1063 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1064 ep1075) rfl rfl

noncomputable def ep1077 := @Enclosure.Complex.IsNear.mul qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true 867034953451435785430253 ep850 ep975 ep852 Bool.true

noncomputable abbrev qz214 := (Complex.re qz478)

noncomputable abbrev qz215 := (Complex.im qz478)

noncomputable def ep1078 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 2153151630238222905907 21064844233455723085824 222691375364822964573611

noncomputable def ep1079 := nat_lit 2545005328982909066542055424

noncomputable def ep1080 := nat_lit 3803374653262838890496000

noncomputable def ep1081 := nat_lit 4842510581934842180178007

noncomputable def ep1082 := nat_lit 136339571195512985707610112000

noncomputable def ep1083 := nat_lit 8117313884184901508797531931662491127415570432

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 224384146987 1099511627776 5355485591181 30655483694022656 124745761093

noncomputable abbrev qz493 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz570 (Real.log (Enclosure.sfrac Bool.false 24 1)))

noncomputable abbrev qz216 := (Real.cos qz493)

noncomputable abbrev qz217 := (Real.sin qz493)

noncomputable abbrev qz494 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1085 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (@HMul.hMul Real Real Real qz0 qz139 qz216) (@HMul.hMul Real Real Real qz0 qz139 qz494)) Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (BSN.cpow_neg_s_mk qz155 117628 1000 24 qz156 rfl)

noncomputable def ep1086 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz142 117628 1000 0 1 3578169457974519 1125899906842624 50000000027881 6970250000000000000 105223229250656680233 281474976710656000 210050000117128081 248937500000000000000 qz157 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 50000000027881 6970250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false 60031721881041427759104 18889465931478580854784 1000000000557620 139405000000000000000 3578169457974519 1125899906842624 50000000027881 6970250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 139405 1000000000000000 rfl rfl rfl rfl (ep550 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1087 := nat_lit 7895195413444471549324195897393064085201240996571885394010716372136106978766785

noncomputable def ep1088 := nat_lit 15013088115918029551985777101937539547801571258815252237345280657083884171201

noncomputable def ep1089 := nat_lit 20653585844928796295622059901673935635306809589935903718786650520245001512873921

noncomputable def ep1090 := BSN.sin_dyadic_bound_f 3327045607 2147483648 3 2 1048576 279083 ep1087 ep64 ep1088 ep1089 ep66 ep1088 1048333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3327045607) qz292 0 2 ep1087 ep64 ep1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3327045607) qz293 0 2 ep1089 ep66 ep1088 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz493

noncomputable abbrev qz495 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 391987075) qz22)

noncomputable def ep1091 := @Enclosure.Real.IsNear.cos_image qz218 qz495 Bool.false 391987075 1048576 885 1048576 Bool.true 1048333 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 105223229250656680233 281474976710656000 210050000117128081 248937500000000000000 391987075 1048576 885 1048576 (ep1086 rfl) rfl) (Enclosure.sfrac_false_div 391987075 1048576) (BSN.cos_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234120021191358351933440) qz24) 226375608064910080 72057594037927936 Bool.false 1048333 1048576 59 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 391987075 1048576 226375608064910080 72057594037927936 59 234120021191358351933440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048333 1048576 234120021191358351933440 151115727451828646838272 3327045607 2147483648 279083 278810 (ep1090 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1092 := nat_lit 4392892157742892207203213621708118953799712363099409775444773664812096714502081

noncomputable def ep1093 := nat_lit 13148650296996840562505669310920481782303533946780598821859630433122122375163841

noncomputable def ep1094 := BSN.cos_dyadic_bound_f 3327045607 2147483648 3 2 1048576 279083 ep1092 ep57 ep1088 ep1093 ep60 ep1088 22563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3327045607) qz287 0 2 ep1092 ep57 ep1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3327045607) qz288 0 2 ep1093 ep60 ep1088 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1095 := @Enclosure.Real.IsNear.sin_image qz218 qz495 Bool.false 391987075 1048576 885 1048576 Bool.false 22563 1048576 1 139405 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 105223229250656680233 281474976710656000 210050000117128081 248937500000000000000 391987075 1048576 885 1048576 (ep1086 rfl) rfl) (Enclosure.sfrac_false_div 391987075 1048576) (BSN.sin_reduce1 qz495 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234120021191358351933440) qz24) 226375608064910080 72057594037927936 Bool.false 22563 1048576 59 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q1 391987075 1048576 226375608064910080 72057594037927936 59 234120021191358351933440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 22563 1048576 234120021191358351933440 151115727451828646838272 3327045607 2147483648 279083 278810 (ep1094 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1096 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz139 qz216) (@HMul.hMul Real Real Real qz0 qz139 qz494) Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (@Enclosure.Real.IsNear.mulLit_ft qz139 qz216 214039 1048576 1 1048576 1048333 1048576 124422001 146176737280 224384146987 1099511627776 5355485591181 30655483694022656 qz426 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 1048333 1048576 124422001 146176737280 1048333 1048576 124422001 146176737280 (ep1091 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz139 qz494 214039 1048576 1 1048576 22563 1048576 124422001 146176737280 4829361957 1099511627776 5326886097811 30655483694022656 qz426 (@Enclosure.Real.IsNear.neg qz217 Bool.false 22563 1048576 124422001 146176737280 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 22563 1048576 124422001 146176737280 22563 1048576 124422001 146176737280 (ep1095 rfl rfl) rfl)) rfl)

noncomputable def ep1097 := @ep1084 249058734912 0 1 2153151630238222905907 21064844233455723085824 222691375364822964573611 ep1079 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (ep1085 ep1096))

noncomputable def ep1098 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 124745761093 249058734912 0 1 Bool.false

noncomputable def ep1099 := @Enclosure.Complex.IsNear.addLitP qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 431643637 864787274 0 1 Bool.true 88221000

noncomputable def ep1100 := @ep1099 432393637 0 1 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1 Bool.false 249491522186 124745761093 249058734912 0 1 Bool.false 6363487683259 6363487683259 31132341864000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz361 qz389 (@HSub.hSub Complex Complex Complex qz353 qz429 (1 : Complex)))

noncomputable def ep1101 := @Enclosure.Complex.IsNear.addLitP qz219 qz89 Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1

noncomputable def ep1102 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 48000000 55346385536) (Enclosure.sfrac Bool.true 11292288000 55346385536)) Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1

noncomputable def ep1103 := @ep1101 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 55250385536 431643637 864787274 0 1 Bool.true 11292288000 88221000 432393637 0 1 (ep1102 (BSN.N_div_s_sub_one_mk qz155 117628 1000 24 qz156 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 48000000 55346385536) (Enclosure.sfrac Bool.true 11292288000 55346385536) Bool.true 48000000 55346385536 0 1 Bool.true 11292288000 55346385536 0 1 (Enclosure.Real.IsNear.const Bool.true 48000000 55346385536) (Enclosure.Real.IsNear.const Bool.true 11292288000 55346385536))) qz90 rfl

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146)) Bool.false 1 576 0 1

noncomputable def ep1105 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1106 := @ep1105 0 1 0 1 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1 Bool.false 1 1 576 0 1 Bool.false 29407 29407 72000 0

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1108 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz146 Bool.false 1 576 0 1 Bool.false 29407 72000 0 1

noncomputable def ep1109 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) 1 576 0 1 0 1 0

noncomputable def ep1110 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 1 24 0 1 1

noncomputable def ep1111 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1112 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1113 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz152 Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 (BSN.ascPochhammer_one_eval qz152)

noncomputable def ep1114 := ep1113 (@Enclosure.Complex.IsNear.of_eq qz152 (Complex.mk qz84 qz155) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_crit_mk qz155 Bool.false 117628 1000 qz156) (@Enclosure.Complex.IsNear.mk qz84 qz155 Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 qz370 qz157))

noncomputable def ep1115 := @ep1112 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 117628 1000 0 1 0 1 0

noncomputable def ep1117 := @ep1116 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1118 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) 29407 3000 0 1 0 1 0 1 29407

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 117628 1000 0 1 29407 3000 0

noncomputable def ep1120 := @ep1119 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1122 := @ep1121 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep578) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1123 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 (@ep1111 1 24 0 1 (ep1115 rfl) (ep1117 rfl) rfl rfl) (@ep1118 29407 3000 0 1 (ep1120 rfl) (ep1122 rfl) rfl rfl)

noncomputable def ep1124 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 ep1123

noncomputable def ep1125 := @ep1110 576 0 1 ep1124 qz149

noncomputable def ep1126 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 29407 3000 0 1 0 1 0 1 0

noncomputable def ep1127 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 29407 3000 0 1 ep1123

noncomputable def ep1128 := @ep1126 1 0 1 ep1127 qz150

noncomputable def ep1129 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 0 1 0 1 29407 72000 0

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz148 1 24 0 1 0 1 0 1 0

noncomputable def ep1131 := @ep1130 1 0 1 ep1124 qz150

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz145) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 29407 3000 0 1 1 24 0 1 29407

noncomputable def ep1133 := @ep1132 72000 0 1 ep1127 qz149

noncomputable def ep1134 := @ep1106 1 (@ep1107 0 1 0 1 (BSN.bern_sum_base qz152 24) qz105) (ep1108 (@ep1109 1 1 1 576 0 1 (ep1125 rfl) (ep1128 rfl) rfl rfl) (@ep1129 1 29407 29407 72000 0 1 (ep1131 rfl) (ep1133 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1135 := ep1100 (ep1103 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1104 Bool.false 29407 72000 0 1 (BSN.bern_sum_succ qz152 24 0 1 1 rfl rfl) (ep1134 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 4829361957 1099511627776 5326886097811 30655483694022656 6363487683259

noncomputable def ep1137 := @ep1136 31132341864000 0 1 3414620592374342264207 ep1080 ep1081 ep1082 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (ep1085 ep1096))

noncomputable def ep1138 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 124745761093 249058734912 0 1 Bool.false

noncomputable def ep1139 := nat_lit 2633105529181965385728000

noncomputable def ep1140 := nat_lit 1622836504635777985320899

noncomputable def ep1141 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 109835827359257811937741 ep1139 ep1140

noncomputable def ep1142 := nat_lit 45446523731837661902536704000

noncomputable def ep1143 := nat_lit 7635015986948727199626166272

noncomputable def ep1144 := nat_lit 3518229358957310272832124177628047656813068288

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 224384146987 1099511627776 5355485591181 30655483694022656 6363487683259

noncomputable def ep1146 := @ep1145 31132341864000 0 1 109835827359257811937741 ep1139 ep1140 ep1142 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (ep1085 ep1096))

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 4829361957 1099511627776 5326886097811 30655483694022656 124745761093

noncomputable def ep1148 := @ep1147 249058734912 0 1 66938048102171659889 30426997226102711123968 664506460527154036267423 ep1143 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 224384146987 1099511627776 5355485591181 30655483694022656 Bool.true 4829361957 1099511627776 5326886097811 30655483694022656 (ep1085 ep1096))

noncomputable abbrev qz496 := (ep1135 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1149 := @ep1077 751585529892647336282879 ep971 ep976 ep852 (@ep1078 ep1079 3414620592374342264207 ep1080 ep1081 ep1082 ep1083 867034953451435785430253 ep850 ep975 ep852 (ep1097 (@ep1098 6363487683259 31132341864000 0 1 qz496) rfl) (ep1137 (@ep1138 6363487683259 31132341864000 0 1 qz496) rfl) rfl rfl) (@ep1141 ep1142 66938048102171659889 30426997226102711123968 664506460527154036267423 ep1143 ep1144 751585529892647336282879 ep971 ep976 ep852 (ep1146 (@ep1138 6363487683259 31132341864000 0 1 qz496) rfl) (ep1148 (@ep1098 6363487683259 31132341864000 0 1 qz496) rfl) rfl rfl)

noncomputable def ep1150 := @ep979 ep972 ep852 (@ep980 3831935461752832 (BSN.head_sum_c_eq qz152 24) (ep981 (BSN.head_sum_c_succ qz152 23 24 rfl rfl) (ep1076 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1149 rfl rfl rfl

noncomputable def ep1151 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz152 1 24) Bool.false ep849 ep850 ep851 ep852 Bool.false ep970 ep971 ep972 ep852 (@ep973 ep852 Bool.false ep970 ep971 ep972 ep852 (BSN.zetaApproximant_eq_folded' qz152 1 24 rfl) (ep1150 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1152 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz152 1 24)) 595 1048576 51373781

noncomputable def ep1153 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.false 595 1048576 51373781

noncomputable def ep1154 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz461 Bool.false 118591747 1048576 361

noncomputable def ep1155 := BSN.sin_dyadic_bound_f 1219174 2147483648 1 0 1048576 279083 0 1 1 0 1 1 595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1219174) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1219174) qz293 0 0 rfl) rfl rfl

noncomputable def ep1156 := @ep1154 1048576 Bool.false 595 1048576 1 139405 (@ep857 118591747 1048576 361 1048576 ep967 rfl) (Enclosure.sfrac_false_div 118591747 1048576) (BSN.sin_reduce0 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85791785793433370624) qz24) 226375608064910080 72057594037927936 Bool.false 595 1048576 18 1000000000000000 278810 139405 (BSN.sin_reduce_arg_pos_rat_q0 118591747 1048576 226375608064910080 72057594037927936 18 85791785793433370624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 595 1048576 85791785793433370624 151115727451828646838272 1219174 2147483648 279083 278810 (ep1155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1157 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz152 1 24) Bool.false ep849 ep850 ep851 ep852 Bool.false ep970 ep971 ep972 ep852 (@ep973 ep852 Bool.false ep970 ep971 ep972 ep852 (BSN.zetaApproximant_eq_folded' qz152 1 24 rfl) (ep1150 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow37.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 24 qz155) Bool.false ep834 ep835 ep836 ep837 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 24 qz155) ep838 Bool.false ep834 ep835 ep836 ep837 (@Eq.refl Real ep838) (@ep839 Bool.false ep834 ep835 ep836 ep837 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz356 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) (zetaApproximant qz152 1 24)) (@ep841 ep842 ep843 ep844 ep845 ep835 ep846 ep837 ep847 ep834 ep835 ep836 ep837 (@ep848 146176737280 ep849 ep850 ep851 ep852 ep840 ep842 ep843 ep844 (@ep853 146176737280 1048575 1048576 51373781 146176737280 (ep969 rfl rfl) rfl) ep1151 rfl) (@ep1152 146176737280 ep970 ep971 ep972 ep852 ep845 ep835 ep846 ep837 (@ep1153 146176737280 595 1048576 51373781 146176737280 (ep1156 rfl rfl) rfl) ep1157 rfl) rfl rfl))

theorem EMRow37.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow37.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow37.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow37.d17 : @Eq Nat (Nat.pow 24 (Nat.succ (Nat.mul 2 3))) 4586471424 := @Eq.refl Nat 4586471424

noncomputable abbrev qz574 := (@HAdd.hAdd Complex Complex Complex qz579 qz578 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz497 := qz574

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz497) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz272) qz296))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz498 := (@HPow.hPow Complex Complex Complex qz532 qz560 (@HSub.hSub Complex Complex Complex qz552 qz533 qz534))

noncomputable abbrev qz223 := qz498

noncomputable def ep1158 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 21329093903 927712935936 90927889 927712935936 1051905527295550267 1008806316530991104 280402509125

noncomputable def ep1159 := nat_lit 997383289709890174654112333824

noncomputable def ep1160 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24)) 26561 1769472 1 1769472 803023 524288 3393 524288 21329093903 927712935936

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz575 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz499 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz575 qz224 2))

noncomputable def ep1161 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz499 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1162 := nat_lit 781950621441006189802102638025

noncomputable def ep1163 := nat_lit 19807040628566084398385987584

noncomputable def ep1164 := nat_lit 26986075409044041160201671

noncomputable def ep1165 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz500 := (@HPow.hPow Real Nat Real qz575 qz224 1)

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff qz500 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1162 ep1163 ep1164 ep1165

noncomputable def ep1167 := ep1166 (@Enclosure.Real.IsNear.of_eq qz500 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz501 := (@HPow.hPow Real Nat Real qz575 qz224 2)

noncomputable def ep1168 := @Enclosure.Real.IsNear.inv_image qz501 ep1162 ep1163 ep1164 ep1165 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz501 (@HMul.hMul Real Real Real qz0 qz500 qz224) Bool.false ep1162 ep1163 ep1164 ep1165 (BSN.pow_succ_r qz224 1 2 rfl) ep1167) rfl rfl rfl

noncomputable def ep1169 := ep1161 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz499 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1168 rfl rfl rfl) rfl)

noncomputable def ep1170 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))))) Bool.false 803023 524288 3393 524288

noncomputable def ep1171 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))))) Bool.false 1606046 1048576 6786 1048576

noncomputable def ep1172 := nat_lit 3063374890419918341882119448815989907667389

noncomputable def ep1173 := nat_lit 1305798837961469417023015536040083456000000

noncomputable def ep1174 := nat_lit 8383669715053497283849452340876559512149278233450419934919

noncomputable def ep1175 := nat_lit 422994380805459817735371311452732787148755801355583488000000

noncomputable def ep1176 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24)))) ep1172 ep1173 ep1174 ep1175 799630 806416

noncomputable def ep1177 := nat_lit 2548435994940721766942335421952458911739468722513129

noncomputable def ep1178 := nat_lit 1088298175075465939822121710354242242573500416000000

noncomputable def ep1179 := nat_lit 5349404829185190818444400582545835349488085820398229698489

noncomputable def ep1180 := nat_lit 281996253870306545156914207635155191432503867570388992000000

noncomputable def ep1181 := nat_lit 833280230075791370962424550743749392970913401

noncomputable def ep1182 := nat_lit 193475231124527278190599415174087509790844518400

noncomputable def ep1183 := nat_lit 719124942551422112365702934115612975834299005706150774371

noncomputable def ep1184 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24))) ep1177 ep1178 ep1179 ep1180 ep1181 ep1182 ep1183

noncomputable def ep1185 := nat_lit 845988761610919635470742622905465574297511602711166976000000

noncomputable def ep1186 := nat_lit 493966100480938721395213790715790956851441655530250339164293757466654184355872746886793216498073600

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 24)) (Complex.re (zetaApproximant qz5 1 24)) ep291 ep292 ep293 ep294 ep291 ep292 ep293 ep294 ep1177

noncomputable def ep1188 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 24)) (Complex.im (zetaApproximant qz5 1 24)) 28866593669426799394549 439858194336001063649280 ep425 ep294 28866593669426799394549 439858194336001063649280 ep425 ep294 ep1181

noncomputable def ep1189 := @ep1158 1008806316530991104 ep1159 29027674164095956793 27237770546336759808 2677225327556167 27237770546336759808 (@ep1160 90927889 927712935936 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow37.d14 EMRow37.d15 rfl) (ep1169 rfl)) (ep1170 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 24)) (@ep1171 803023 524288 3393 524288 (@ep1176 524288 (@ep1184 ep1185 ep1186 ep1172 ep1173 ep1174 ep1175 (@ep1187 ep1178 ep1179 ep1180 ep616 ep616 rfl) (@ep1188 ep1182 ep1183 ep1185 ep624 ep624 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz497)

noncomputable abbrev qz576 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1190 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 1051905527295550267 1008806316530991104 280402509125 1008806316530991104 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1191 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 121140967 3670016 1 3670016 8683317901 274877906944 2243 274877906944

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz576 121140967 1048576 1 1048576 2 7 0 1 121140967 3670016

noncomputable abbrev qz502 := (Complex.re qz574)

noncomputable abbrev qz503 := (Complex.im qz574)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz267 qz502 qz502) (@HMul.hMul Real Real Real qz267 qz503 qz503))

noncomputable abbrev qz227 := qz497

noncomputable def ep1193 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 121140967 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1194 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 121140967 1048576 1 1048576 121140967

noncomputable def ep1195 := @Enclosure.Real.IsNear.sqrt_image qz226 417092393 31250 0 1 60570483 60570484 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz502 qz502)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz503 qz503)

noncomputable def ep1196 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 833419161 62500 0 1

noncomputable abbrev qz230 := qz502

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz504 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1198 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz504 qz13) Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 115476 1000 3 qz14)

noncomputable abbrev qz505 := (ep1198 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1199 := @ep1197 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz505)

noncomputable def ep1200 := ep1199 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz505)

noncomputable abbrev qz231 := qz503

noncomputable def ep1201 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 115476 1000 0 1 115476 1000 0 1 833419161 62500

noncomputable def ep1202 := @ep1201 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz505)

noncomputable def ep1203 := ep1202 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 115476 1000 0 1 qz505)

noncomputable def ep1204 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 8683317901 274877906944

noncomputable def ep1205 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 8683317901 274877906944

noncomputable def ep1206 := nat_lit 200287394371375538312799869382547958013695845402429423958009

noncomputable def ep1207 := nat_lit 200706706786775608273821464453835253553823744000000000000000000

noncomputable def ep1208 := nat_lit 10303352790399404631359778777675503399774780262110118638998254261091

noncomputable def ep1209 := nat_lit 19993031704394961815897392959103029209189152254874091520000000000000000000000

noncomputable def ep1210 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1206 ep1207 ep1208 ep1209

noncomputable def ep1211 := nat_lit 20572762689990636258215668685054352226394636303060659005289

noncomputable def ep1212 := nat_lit 78401057338584221981961509552279395919462400000000000000000000

noncomputable def ep1213 := nat_lit 94968154097980048573439410457957078531552576758049792560829041207801

noncomputable def ep1214 := nat_lit 639777014540638778108716574691296934694052872155970928640000000000000000000000

noncomputable def ep1215 := nat_lit 3690528047124987737294193938720220407853139411664853422611729

noncomputable def ep1216 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1211 ep1212 ep1213 ep1214 ep1215

noncomputable def ep1217 := nat_lit 5017667669669390206845536611345881338845593600000000000000000000

noncomputable def ep1218 := nat_lit 234739135194800899630073510427659030261240391629474003887115095147111

noncomputable def ep1219 := nat_lit 392568587257646108592349746208933163657195395120013496144399267116698254875888473826385997690086359040000000000000000000000

noncomputable def ep1220 := nat_lit 143432083893355730112806101267

noncomputable def ep1221 := nat_lit 8854437155380584775680000000000

noncomputable def ep1222 := nat_lit 3664783088958288353468067056669

noncomputable def ep1223 := nat_lit 799860621946498112583578419200000000000

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1220 ep1221 ep1222 ep1223 ep1220 ep1221 ep1222

noncomputable def ep1225 := nat_lit 1921074711489635880708454821527

noncomputable def ep1226 := nat_lit 70835497243044678205440000000000

noncomputable def ep1227 := nat_lit 5410629869128197950982187822109

noncomputable def ep1228 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1220 ep1221 ep1222 ep1223 Bool.true ep1225 ep1226 ep1227

noncomputable def ep1229 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1220 ep1221 ep1222 ep1223 Bool.true ep1225 ep1226 ep1227 ep1223

noncomputable def ep1230 := nat_lit 389534181486183917978796473

noncomputable def ep1231 := nat_lit 377789318629571617095680000000

noncomputable def ep1232 := nat_lit 3290796095629138180822083673

noncomputable def ep1233 := nat_lit 12797769951143969801337254707200000000

noncomputable def ep1234 := nat_lit 2440988660351010651046946297647

noncomputable def ep1235 := nat_lit 141670994486089356410880000000000

noncomputable def ep1236 := nat_lit 6918216665962934434333373654213

noncomputable abbrev qz232 := (Complex.re qz498)

noncomputable abbrev qz233 := (Complex.im qz498)

noncomputable def ep1237 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1230 ep1231 ep1232 ep1233 ep1234 ep1235 ep1236

noncomputable def ep1238 := nat_lit 1599721243892996225167156838400000000000

noncomputable def ep1239 := nat_lit 866993747899046640173636550626401147925187624131624960000000

noncomputable def ep1240 := nat_lit 853184663409597986755816980480

noncomputable def ep1241 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 1250089679 15000000 0 1 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 ep1230

noncomputable def ep1242 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1250089679 15000000 0 1 0 1 0 1 1250089679

noncomputable def ep1243 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3750269037 62500 0 1 1250089679 15000000 0

noncomputable def ep1244 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow37.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz19)

noncomputable abbrev qz506 := (@HAdd.hAdd Complex Complex Complex qz531 qz530 qz535)

noncomputable abbrev qz234 := qz506

noncomputable def ep1245 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1

noncomputable abbrev qz235 := (Complex.re qz506)

noncomputable abbrev qz236 := (Complex.im qz506)

noncomputable def ep1246 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 416686143 12500 0 1 833419161 31250 0 1

noncomputable def ep1247 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 416686143 31250 0 1 5 2 0 1 416686143 12500

noncomputable abbrev qz507 := (@HAdd.hAdd Complex Complex Complex qz531 qz530 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz507

noncomputable def ep1248 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1

noncomputable abbrev qz238 := (Complex.re qz507)

noncomputable abbrev qz239 := (Complex.im qz507)

noncomputable def ep1249 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 833419161 62500 0 1

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1251 := @ep1250 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable abbrev qz508 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1252 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz508 qz13) Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 115476 1000 1 qz14)

noncomputable abbrev qz509 := (ep1252 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1253 := ep1251 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz509)

noncomputable def ep1254 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 115476 1000 0 1 115476 1000 0 1 833419161 62500

noncomputable def ep1255 := @ep1254 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep1256 := ep1255 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz509)

noncomputable def ep1257 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 (@ep1249 3333489144 416686143 31250 0 1 (ep1253 rfl) (ep1256 rfl) rfl rfl)

noncomputable def ep1258 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 28869 500 0 1 86607 500 0 1

noncomputable def ep1259 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 115476 1000 0 1 28869 500

noncomputable def ep1260 := @ep1259 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep1261 := ep1260 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz509)

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 115476 1000 0 1 3 2 0 1 86607 500

noncomputable def ep1263 := @ep1262 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 115476 1000 0 1 ep580)

noncomputable def ep1264 := ep1263 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 115476 1000 0 1 qz509)

noncomputable abbrev qz240 := (ep1248 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1257 (@ep1258 57738000 28869 125 0 1 (ep1261 rfl) (ep1264 rfl) rfl rfl)))

noncomputable def ep1265 := @ep1247 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz240)

noncomputable abbrev qz510 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1266 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz510 qz13) Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 115476 1000 2 qz14)

noncomputable abbrev qz511 := (ep1266 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1267 := ep1265 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz511)

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 28869 125 0 1 115476 1000 0 1 833419161 31250

noncomputable def ep1269 := @ep1268 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz240)

noncomputable def ep1270 := ep1269 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz511)

noncomputable def ep1271 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 (@ep1246 23439181481250 3750269037 62500 0 1 (ep1267 rfl) (ep1270 rfl) rfl rfl)

noncomputable def ep1272 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 12029312262267 7812500 0 1 28869 50 0 1

noncomputable def ep1273 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 416686143 31250 0 1 115476 1000 0 1 12029312262267 7812500

noncomputable def ep1274 := @ep1273 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz240)

noncomputable def ep1275 := ep1274 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz511)

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 28869 125 0 1 5 2 0 1 28869 50

noncomputable def ep1277 := @ep1276 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 416686143 31250 0 1 Bool.false 28869 125 0 1 qz240)

noncomputable def ep1278 := ep1277 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 115476 1000 0 1 qz511)

noncomputable abbrev qz241 := (ep1245 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1271 (@ep1272 601240074050850 12024801481017 7812500 0 1 (ep1275 rfl) (ep1278 rfl) rfl rfl)))

noncomputable def ep1279 := @ep1243 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz241)

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12024801481017 7812500 0 1 0 1 0

noncomputable def ep1281 := @ep1280 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz241)

noncomputable def ep1282 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 4008267160339 1875000000 0 1 0 1 0 1 4008267160339

noncomputable def ep1283 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12024801481017 7812500 0 1 4008267160339 1875000000 0

noncomputable def ep1284 := @ep1283 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz241)

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3750269037 62500 0 1 0 1 0

noncomputable def ep1286 := @ep1285 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3750269037 62500 0 1 Bool.true 12024801481017 7812500 0 1 qz241)

noncomputable def ep1287 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 (@ep1242 1250089679 15000000 0 1 (ep1279 rfl) (ep1281 rfl) rfl rfl) (@ep1282 4008267160339 1875000000 0 1 (ep1284 rfl) (ep1286 rfl) rfl rfl)

noncomputable def ep1288 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 ep1287

noncomputable def ep1289 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 Bool.true 608988513665981173 75557863725914323419136 1725986913850778567 ep1240

noncomputable abbrev qz512 := (@Nat.cast Real Real.instNatCast 4586471424)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz512))

noncomputable def ep1290 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz140) (@HMul.hMul Real Real Real qz0 qz242 qz421)) Bool.true 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 Bool.true 608988513665981173 75557863725914323419136 1725986913850778567

noncomputable def ep1291 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz512) 18615691844177917 274877906944 1 274877906944 2029413 2029414 137438953472 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz512) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz512 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_natCast_div_one 4586471424) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz512 qz15)) Bool.false 18615691844177917 274877906944 1 274877906944 18615691844177917 274877906944 1 274877906944 (BSN.sqrt_enclosure 4586471424 1 9307845922088958 9307845922088959 137438953472 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1292 := nat_lit 15736960334339222256381591552

noncomputable def ep1293 := nat_lit 4951760157141521099596496896

noncomputable def ep1294 := nat_lit 46251233280000000000000000

noncomputable def ep1295 := nat_lit 54412538019840000000000000000

noncomputable def ep1296 := nat_lit 743426006773320438031319040

noncomputable def ep1297 := BSN.log_dyadic_bound 8 40 8 7 ep1295 137438953472 46251233280 ep1296 594330015278039040 55726700127 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base7 (BSN.artanhP 8) (BSN.artanhQ 40) 0 7 ep1296 ep1295 594330015278039040 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1298 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz142 115476 1000 0 1 3578170511523063 1125899906842624 12209289611 564590250000000000000 103298204497159305747 281474976710656000 117489993926653 47049187500000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578170511523063 1125899906842624 12209289611 564590250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false ep1292 ep1293 1000185004933120 ep1294 3578170511523063 1125899906842624 12209289611 564590250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 55726700127 137438953472 24973259072661432 36028797018963968 46251233280 1000000000000000 rfl rfl rfl rfl (ep1297 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1299 := nat_lit 39352627107768698558107090944

noncomputable def ep1300 := nat_lit 39614081257132168796771975168

noncomputable def ep1301 := nat_lit 51212141532959616176419733979111293923945231804588577784902548764655340930020615635610574790681694633476156982765298455336850793780126485756556904363931572505761969262583444015053861841

noncomputable def ep1302 := nat_lit 6308378847008246063796460162423931949098252867933419242910272974037146636290687601591899635669002301462775740831203986644333398331477415382602044345464892932073894033779958631686261964800

noncomputable def ep1303 := nat_lit 935679592969318072487872981708380218537234051986805272688106858472932698211603137401030145989131821359617066765652280125258451909219630606427234710147165315350399028530202866641

noncomputable def ep1304 := nat_lit 256009743372379379948975915855196364047599415843944369983351961688385157175791497340785786234458483911689531175350493220011362644305158874536708099640814806214232283251159795431757902801

noncomputable def ep1305 := nat_lit 220793259645288612232876105684837618218438850377669673501859554091300132270174066055716487248415080551197150929092139532551668941601709538391071552091271252622586291182298552109019168768000

noncomputable def ep1306 := BSN.sin_dyadic_bound_f 559234466490021 562949953421312 4 3 274877906944 92592801001 ep1301 ep1302 ep1303 ep1304 ep1305 ep1303 230316534543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 559234466490021) (BSN.sinEvenQ 562949953421312) 0 3 ep1301 ep1302 ep1303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 559234466490021) (BSN.sinOddQ 562949953421312) 0 3 ep1304 ep1305 ep1303 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz513 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100877152829257) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1307 := @Enclosure.Real.IsNear.cos_image qz143 qz513 Bool.false 100877152829257 274877906944 687 274877906944 Bool.true 230316534543 274877906944 1 46251233280 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 103298204497159305747 281474976710656000 117489993926653 47049187500000000000000 100877152829257 274877906944 687 274877906944 (ep1298 rfl) rfl) (Enclosure.sfrac_false_div 100877152829257 274877906944) (BSN.cos_reduce1 qz513 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1299) (@Nat.cast Real Real.instNatCast ep1300)) 226375608064910080 72057594037927936 Bool.false 230316534543 274877906944 58 1000000000000000 92502466560 46251233280 (BSN.sin_reduce_arg_pos_rat_q1 100877152829257 274877906944 226375608064910080 72057594037927936 58 ep1299 ep1300 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230316534543 274877906944 ep1299 ep1300 559234466490021 562949953421312 92592801001 92502466560 (ep1306 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1308 := nat_lit 19702051084377372208378486228643825466626169878349461646103651316707906018947405527618666888118962963570173534131862229419662319569307063915218494422515823479522212269219047298129261521

noncomputable def ep1309 := nat_lit 485259911308326620292035397109533226853711759071801480223867151849011279714668277045530741205307869343290441602400306664948722948575185798661695718881914840928761079521535279360481689600

noncomputable def ep1310 := nat_lit 119479607575109743835690632693535515062845045904924816313607323782603369516495797003715395487307821421873994444607664772787218142341385624522256055619987684627437683389290425797804618705

noncomputable def ep1311 := nat_lit 44158651929057722446575221136967523643687770075533934700371910818260026454034813211143297449683016110239430185818427906510333788320341907678214310418254250524517258236459710421803833753600

noncomputable def ep1312 := BSN.cos_dyadic_bound_f 559234466490021 562949953421312 4 3 274877906944 92592801001 ep1308 ep1309 ep1303 ep1310 ep1311 ep1303 150040519999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 559234466490021) (BSN.cosEvenQ 562949953421312) 0 3 ep1308 ep1309 ep1303 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 559234466490021) (BSN.cosOddQ 562949953421312) 0 3 ep1310 ep1311 ep1303 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1313 := @Enclosure.Real.IsNear.sin_image qz143 qz513 Bool.false 100877152829257 274877906944 687 274877906944 Bool.false 150040519999 274877906944 1 46251233280 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 103298204497159305747 281474976710656000 117489993926653 47049187500000000000000 100877152829257 274877906944 687 274877906944 (ep1298 rfl) rfl) (Enclosure.sfrac_false_div 100877152829257 274877906944) (BSN.sin_reduce1 qz513 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1299) (@Nat.cast Real Real.instNatCast ep1300)) 226375608064910080 72057594037927936 Bool.false 150040519999 274877906944 58 1000000000000000 92502466560 46251233280 (BSN.sin_reduce_arg_pos_rat_q1 100877152829257 274877906944 226375608064910080 72057594037927936 58 ep1299 ep1300 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 150040519999 274877906944 ep1299 ep1300 559234466490021 562949953421312 92592801001 92502466560 (ep1312 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz514 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 4058827 274877906944 1 274877906944 4058827 274877906944 1 274877906944 (ep1291 rfl rfl) rfl)

noncomputable def ep1314 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz140) (@HMul.hMul Real Real Real qz0 qz242 qz421) Bool.true 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 Bool.true 608988513665981173 75557863725914323419136 1725986913850778567 ep1240 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz140 4058827 274877906944 1 274877906944 230316534543 274877906944 7824578899 3103867724019793920 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 qz514 (@Enclosure.Real.IsNear.recentre' qz140 Bool.true 230316534543 274877906944 32049475170304 12713442197585075896320 230316534543 274877906944 7824578899 3103867724019793920 (ep1307 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz421 4058827 274877906944 1 274877906944 150040519999 274877906944 7824578899 3103867724019793920 608988513665981173 75557863725914323419136 1725986913850778567 ep1240 qz514 (@Enclosure.Real.IsNear.neg qz141 Bool.false 150040519999 274877906944 7824578899 3103867724019793920 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 150040519999 274877906944 32049475170304 12713442197585075896320 150040519999 274877906944 7824578899 3103867724019793920 (ep1313 rfl rfl) rfl)) rfl)

noncomputable def ep1315 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 4008267160339 1875000000 0 1 608988513665981173 75557863725914323419136 1725986913850778567 ep1240 ep1234

noncomputable def ep1316 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1250089679 15000000 0 1 Bool.false 4008267160339 1875000000 0 1 ep1287

noncomputable def ep1317 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 Bool.true 608988513665981173 75557863725914323419136 1725986913850778567 ep1240

noncomputable def ep1318 := nat_lit 761290255563393517775613467

noncomputable def ep1319 := nat_lit 1133367955888714851287040000000

noncomputable def ep1320 := nat_lit 2157638427093920432721109993

noncomputable def ep1321 := nat_lit 1248996047011282523898319319893

noncomputable def ep1322 := nat_lit 47223664828696452136960000000000

noncomputable def ep1323 := nat_lit 10551554934869655847874236895093

noncomputable def ep1324 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1318 ep1319 ep1320 ep1233 ep1321 ep1322 ep1323

noncomputable def ep1325 := nat_lit 1451523012580340832230646944825332834424769512965406720000000

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 1250089679 15000000 0 1 608988513665981173 75557863725914323419136 1725986913850778567 ep1240 ep1318

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 4008267160339 1875000000 0 1 934814968949561061 75557863725914323419136 2632448016258790487 ep1240 ep1321

noncomputable abbrev qz515 := (@ep1290 ep1240 (BSN.cpow_neg_s_sub_mk qz13 115476 1000 24 3 4586471424 qz14 rfl EMRow37.d17) ep1314)

noncomputable def ep1328 := ep1229 (@ep1237 ep1238 ep1239 ep1220 ep1221 ep1222 ep1223 (@ep1241 ep1231 ep1232 ep1233 ep1288 (ep1289 qz515) rfl) (@ep1315 ep1235 ep1236 ep1238 ep1316 (ep1317 qz515) rfl) rfl rfl) (@ep1324 ep1238 ep1325 ep1225 ep1226 ep1227 ep1223 (@ep1326 ep1319 ep1320 ep1233 ep1288 (ep1317 qz515) rfl) (@ep1327 ep1322 ep1323 ep1238 ep1316 (ep1289 qz515) rfl) rfl rfl)

noncomputable def ep1329 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1225 ep1226 ep1227 ep1223 ep1225 ep1226 ep1227

noncomputable def ep1330 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1220 ep1221 ep1222 ep1223 Bool.true ep1225 ep1226 ep1227

noncomputable def ep1331 := @ep1191 1051905527295550267 1008806316530991104 280402509125 1008806316530991104 (@ep1192 1 3670016 (ep1193 (@ep1194 1048576 1 1048576 (ep1195 (@ep1196 3336739144 417092393 31250 0 1 (ep1200 rfl) (ep1203 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1204 2243 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1205 2243 274877906944 8683317901 274877906944 2243 274877906944 (@ep1210 4341657829 4341660072 137438953472 (@ep1216 ep1217 ep1218 ep1214 ep1219 ep1206 ep1207 ep1208 ep1209 (@ep1224 ep1223 ep1211 ep1212 ep1213 ep1214 (@ep1228 ep1223 ep1328) (@ep1228 ep1223 ep1328) rfl) (@ep1329 ep1223 ep1215 ep1217 ep1218 ep1214 (@ep1330 ep1223 ep1328) (@ep1330 ep1223 ep1328) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow37.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 29027674164095956793 27237770546336759808 2677225327556167 27237770546336759808 := ep1189 (ep1190 ep1331) rfl rfl

noncomputable abbrev qz577 := (@HAdd.hAdd Complex Complex Complex qz579 qz585 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz516 := qz577

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz516) (@HAdd.hAdd Real Real Real qz380 (Complex.re qz429) qz296))

noncomputable abbrev qz517 := (@HPow.hPow Complex Complex Complex qz532 qz560 (@HSub.hSub Complex Complex Complex qz552 qz569 qz534))

noncomputable abbrev qz244 := qz517

noncomputable def ep1332 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 28825617421 618475290624 61141943 618475290624 1132505367249202145 1008806316530991104 291632333011

noncomputable def ep1333 := nat_lit 729506051074900725514857611264

noncomputable def ep1334 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24)) 26561 1769472 1 1769472 3255783 1048576 6783 1048576 28825617421 618475290624

noncomputable def ep1335 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))))) Bool.false 3255783 1048576 6783 1048576

noncomputable def ep1336 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))))) Bool.false 3255783 1048576 6783 1048576

noncomputable def ep1337 := nat_lit 6531258363576173736059470379369910090641921

noncomputable def ep1338 := nat_lit 677460454280262579645735353714737152000000

noncomputable def ep1339 := nat_lit 1143347673472913505859023516985475832470297765796247764761

noncomputable def ep1340 := nat_lit 28463607969220042415965658554950466763709838113374208000000

noncomputable def ep1341 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24)))) ep1337 ep1338 ep1339 ep1340 1624500 1631283

noncomputable def ep1342 := nat_lit 705601616555711553579336138563832056182858931584009

noncomputable def ep1343 := nat_lit 73232397437478738532005420283049164413075456000000

noncomputable def ep1344 := nat_lit 1784271588954700265200403815935133857173212512209847093361

noncomputable def ep1345 := nat_lit 45541772750752067865545053687920746821935740981398732800000

noncomputable def ep1346 := nat_lit 1668091790523873961287891374196967724224159520641

noncomputable def ep1347 := nat_lit 292929589749914954128021681132196657652301824000000

noncomputable def ep1348 := nat_lit 225423443009806720870169056208137373896319565320746651283

noncomputable def ep1349 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24))) ep1342 ep1343 ep1344 ep1345 ep1346 ep1347 ep1348

noncomputable def ep1350 := nat_lit 227708863753760339327725268439603734109678704906993664000000

noncomputable def ep1351 := nat_lit 206813750425507224772765763369076281811293307794747193510695183762284470886517315799182802419712000000

noncomputable def ep1352 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz152 1 24)) (Complex.re (zetaApproximant qz152 1 24)) ep849 ep850 ep851 ep852 ep849 ep850 ep851 ep852 ep1342

noncomputable def ep1353 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz152 1 24)) (Complex.im (zetaApproximant qz152 1 24)) ep970 ep971 ep972 ep852 ep970 ep971 ep972 ep852 ep1346

noncomputable def ep1354 := @ep1332 1008806316530991104 ep1333 10615710213822614249 9079256848778919936 900192327321451 9079256848778919936 (@ep1334 61141943 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz499) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow37.d14 EMRow37.d15 rfl) (ep1169 rfl)) (ep1335 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz152 1 24)) (@ep1336 3255783 1048576 6783 1048576 (@ep1341 524288 (@ep1349 ep1350 ep1351 ep1337 ep1338 ep1339 ep1340 (@ep1352 ep1343 ep1344 ep1345 ep1151 ep1151 rfl) (@ep1353 ep1347 ep1348 ep1350 ep1157 ep1157 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz516)

noncomputable def ep1355 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 1132505367249202145 1008806316530991104 291632333011 1008806316530991104 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz155 3)

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz576) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 123396485 3670016 1 3670016 9177776557 274877906944 2289 274877906944

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz576 123396485 1048576 1 1048576 2 7 0 1 123396485 3670016

noncomputable abbrev qz518 := (Complex.re qz577)

noncomputable abbrev qz519 := (Complex.im qz577)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz267 qz518 qz518) (@HMul.hMul Real Real Real qz267 qz519 qz519))

noncomputable abbrev qz247 := qz516

noncomputable def ep1358 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 123396485 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1359 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 123396485 1048576 1 1048576 123396485

noncomputable def ep1360 := @Enclosure.Real.IsNear.sqrt_image qz246 432768637 31250 0 1 61698242 61698243 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz518 qz518)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz519 qz519)

noncomputable def ep1361 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 864771649 62500 0 1

noncomputable abbrev qz250 := qz518

noncomputable def ep1362 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1363 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz504 qz155) Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 117628 1000 3 qz156)

noncomputable abbrev qz520 := (ep1363 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz155 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz157))

noncomputable def ep1364 := @ep1362 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz520)

noncomputable def ep1365 := ep1364 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz520)

noncomputable abbrev qz251 := qz519

noncomputable def ep1366 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 117628 1000 0 1 117628 1000 0 1 864771649 62500

noncomputable def ep1367 := @ep1366 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz520)

noncomputable def ep1368 := ep1367 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 117628 1000 0 1 qz520)

noncomputable def ep1369 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 9177776557 274877906944

noncomputable def ep1370 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 9177776557 274877906944

noncomputable def ep1371 := nat_lit 2517153482446952535968724485330366622263094611454678474977021

noncomputable def ep1372 := nat_lit 2257950451351225593080491475105646602480517120000000000000000000

noncomputable def ep1373 := nat_lit 100002604518535821231986156140376405036113352254036330315280795910391

noncomputable def ep1374 := nat_lit 179937285339554656343076536631927262882702370293866823680000000000000000000000

noncomputable def ep1375 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1371 ep1372 ep1373 ep1374

noncomputable def ep1376 := nat_lit 3569847585043725371780044448088143736806550920703785551969

noncomputable def ep1377 := nat_lit 11289752256756127965402457375528233012402585600000000000000000000

noncomputable def ep1378 := nat_lit 117288383622980482130092446472054754611776758060535273362799663383

noncomputable def ep1379 := nat_lit 87376371976734159406054460987526006719296295183004781870369

noncomputable def ep1380 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1376 ep1377 ep1378 ep1374 ep1379

noncomputable def ep1381 := nat_lit 3121416129216026273433001990434510946296924234249243595059937382719

noncomputable def ep1382 := nat_lit 5623040166861083010721141769747726965084449071683338240000000000000000000000

noncomputable def ep1383 := nat_lit 986737472536702393561324751025066635028769903951065835552794292664217594058817912198534793065033367552000000000000000000000

noncomputable def ep1384 := nat_lit 59748201521415900872944298063

noncomputable def ep1385 := nat_lit 106253245864567017308160000000000

noncomputable def ep1386 := nat_lit 173846747801381291597325414263

noncomputable def ep1387 := nat_lit 299947733229936792218841907200000000000

noncomputable def ep1388 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1384 ep1385 ep1386 ep1387 ep1384 ep1385 ep1386

noncomputable def ep1389 := nat_lit 295594945790238706182166356463

noncomputable def ep1390 := nat_lit 1246895274428997934587768130939

noncomputable def ep1391 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1384 ep1385 ep1386 ep1387 Bool.true ep1389 ep1221 ep1390

noncomputable def ep1392 := nat_lit 149973866614968396109420953600000000000

noncomputable def ep1393 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1384 ep1385 ep1386 ep1387 Bool.true ep1389 ep1221 ep1390 ep1392

noncomputable def ep1394 := nat_lit 241139971669564298570336691

noncomputable def ep1395 := nat_lit 188894659314785808547840000000

noncomputable def ep1396 := nat_lit 2033594120553313751450632721

noncomputable def ep1397 := nat_lit 6398884975571984900668627353600000000

noncomputable def ep1398 := nat_lit 151786065085428034145740181249

noncomputable def ep1399 := nat_lit 212506491729134034616320000000000

noncomputable def ep1400 := nat_lit 89739455314793953712088006247

noncomputable abbrev qz252 := (Complex.re qz517)

noncomputable abbrev qz253 := (Complex.im qz517)

noncomputable def ep1401 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1394 ep1395 ep1396 ep1397 ep1398 ep1399 ep1400

noncomputable def ep1402 := nat_lit 342797409405642048250105036800000000000

noncomputable def ep1403 := nat_lit 22572232342118047435541607780869817711976188309667840000000

noncomputable def ep1404 := nat_lit 426592331704798993377908490240

noncomputable def ep1405 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 1297118411 15000000 0 1 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 ep1394

noncomputable def ep1406 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) 1297118411 15000000 0 1 0 1 0 1 1297118411

noncomputable def ep1407 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3891355233 62500 0 1 1297118411 15000000 0

noncomputable abbrev qz521 := (@HAdd.hAdd Complex Complex Complex qz531 qz568 qz535)

noncomputable abbrev qz254 := qz521

noncomputable def ep1408 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1

noncomputable abbrev qz255 := (Complex.re qz521)

noncomputable abbrev qz256 := (Complex.im qz521)

noncomputable def ep1409 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 432362387 12500 0 1 864771649 31250 0 1

noncomputable def ep1410 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 432362387 31250 0 1 5 2 0 1 432362387 12500

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz531 qz568 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz522

noncomputable def ep1411 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1

noncomputable abbrev qz258 := (Complex.re qz522)

noncomputable abbrev qz259 := (Complex.im qz522)

noncomputable def ep1412 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 864771649 62500 0 1

noncomputable def ep1413 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1414 := @ep1413 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1415 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz508 qz155) Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 117628 1000 1 qz156)

noncomputable abbrev qz523 := (ep1415 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz155 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz157))

noncomputable def ep1416 := ep1414 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz523)

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 117628 1000 0 1 117628 1000 0 1 864771649 62500

noncomputable def ep1418 := @ep1417 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1419 := ep1418 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz523)

noncomputable def ep1420 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 (@ep1412 3458899096 432362387 31250 0 1 (ep1416 rfl) (ep1419 rfl) rfl rfl)

noncomputable def ep1421 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 29407 500 0 1 88221 500 0 1

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 117628 1000 0 1 29407 500

noncomputable def ep1423 := @ep1422 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1424 := ep1423 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz523)

noncomputable def ep1425 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 117628 1000 0 1 3 2 0 1 88221 500

noncomputable def ep1426 := @ep1425 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 117628 1000 0 1 ep1114)

noncomputable def ep1427 := ep1426 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 117628 1000 0 1 qz523)

noncomputable abbrev qz260 := (ep1411 (BSN.ascPochhammer_succ_eval_c 1 2 qz429 rfl) (ep1420 (@ep1421 58814000 29407 125 0 1 (ep1424 rfl) (ep1427 rfl) rfl rfl)))

noncomputable def ep1428 := @ep1410 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz260)

noncomputable def ep1429 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz510 qz155) Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 (BSN.s_add_nat_mk qz155 Bool.false 117628 1000 2 qz156)

noncomputable abbrev qz524 := (ep1429 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz155 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz157))

noncomputable def ep1430 := ep1428 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz524)

noncomputable def ep1431 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 29407 125 0 1 117628 1000 0 1 864771649 31250

noncomputable def ep1432 := @ep1431 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz260)

noncomputable def ep1433 := ep1432 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz524)

noncomputable def ep1434 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 (@ep1409 24320970206250 3891355233 62500 0 1 (ep1430 rfl) (ep1433 rfl) rfl rfl)

noncomputable def ep1435 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 12714480714509 7812500 0 1 29407 50 0 1

noncomputable def ep1436 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 432362387 31250 0 1 117628 1000 0 1 12714480714509 7812500

noncomputable def ep1437 := @ep1436 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz260)

noncomputable def ep1438 := ep1437 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz524)

noncomputable def ep1439 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 29407 125 0 1 5 2 0 1 29407 50

noncomputable def ep1440 := @ep1439 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 432362387 31250 0 1 Bool.false 29407 125 0 1 qz260)

noncomputable def ep1441 := ep1440 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 117628 1000 0 1 qz524)

noncomputable abbrev qz261 := (ep1408 (BSN.ascPochhammer_succ_eval_c 2 3 qz429 rfl) (ep1434 (@ep1435 635494293537950 12709885870759 7812500 0 1 (ep1438 rfl) (ep1441 rfl) rfl rfl)))

noncomputable def ep1442 := @ep1407 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz261)

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 12709885870759 7812500 0 1 0 1 0

noncomputable def ep1444 := @ep1443 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz261)

noncomputable def ep1445 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) 12709885870759 5625000000 0 1 0 1 0 1 12709885870759

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 12709885870759 7812500 0 1 12709885870759 5625000000 0

noncomputable def ep1447 := @ep1446 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz261)

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3891355233 62500 0 1 0 1 0

noncomputable def ep1449 := @ep1448 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1244) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3891355233 62500 0 1 Bool.true 12709885870759 7812500 0 1 qz261)

noncomputable def ep1450 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 (@ep1406 1297118411 15000000 0 1 (ep1442 rfl) (ep1444 rfl) rfl rfl) (@ep1445 12709885870759 5625000000 0 1 (ep1447 rfl) (ep1449 rfl) rfl rfl)

noncomputable def ep1451 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 ep1450

noncomputable def ep1452 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 Bool.true 11942362553753111 37778931862957161709568 49424219351077831 ep1404

noncomputable def ep1453 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz494)) Bool.true 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 Bool.true 11942362553753111 37778931862957161709568 49424219351077831

noncomputable def ep1454 := @Enclosure.Real.IsNear.mulLit_ff qz155 qz142 117628 1000 0 1 3578170511523063 1125899906842624 12209289611 564590250000000000000 105223260232358713641 281474976710656000 51291225655811 20163937500000000000000 qz157 (BSN.isNear_log_sfrac 24 1 3578170511523063 1125899906842624 12209289611 564590250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz424 Bool.false ep1292 ep1293 1000185004933120 ep1294 3578170511523063 1125899906842624 12209289611 564590250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 55726700127 137438953472 24973259072661432 36028797018963968 46251233280 1000000000000000 rfl rfl rfl rfl (ep1297 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1455 := nat_lit 30688761455712430461143744512

noncomputable def ep1456 := nat_lit 1741285869682633512345182075706254993504400427456840532084312608046288426999777428599552199310742430802860716119524867468472493299548813963712183081814688529576852484473815281646844942146091754158889423457963946623840040482000864796316989731914149761

noncomputable def ep1457 := nat_lit 36189711061676687398051995244972293437204064634277911010709893574360646025770957327274520038916625905157259536660301123060201295733050346820418006399790474322883113512225043577386983430344807139857606659932443931695135483567632475872701705235726336000

noncomputable def ep1458 := nat_lit 112220682267176207162479702674185970392635988796576051853473831547636965018422086764180332157431577013049662003975243500844121361078008509948253084976744464331251180313997395542042065556796697973994002058737527701519306865632610839005523841

noncomputable def ep1459 := nat_lit 14162362620981476507973062010740267839751392300091410357073445043591661736142765335465980456383235157893684661228133785805343020392090474260391269629940393164584824782043325376852546309846473174526418180899875142721197660755134684030031631300396347265

noncomputable def ep1460 := nat_lit 2062813530515571181688963728963420725920631684153840927610463933738556823468944567654647642218247676593963793589637164014431473856783869768763826364788057036404337470196827483911058055529654006971883579616149304106622722563355051124743997198436401152000

noncomputable def ep1461 := BSN.sin_dyadic_bound_f 872227060873241 562949953421312 5 4 274877906944 92592801001 ep1456 ep1457 ep1458 ep1459 ep1460 ep1458 274814910018 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 872227060873241) (BSN.sinEvenQ 562949953421312) 0 4 ep1456 ep1457 ep1458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 872227060873241) (BSN.sinOddQ 562949953421312) 0 4 ep1459 ep1460 ep1458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz525 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 51378545035331) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1462 := @Enclosure.Real.IsNear.cos_image qz218 qz525 Bool.false 51378545035331 137438953472 701 274877906944 Bool.true 274814910018 274877906944 1 46251233280 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 105223260232358713641 281474976710656000 51291225655811 20163937500000000000000 51378545035331 137438953472 701 274877906944 (ep1454 rfl) rfl) (Enclosure.sfrac_false_div 51378545035331 137438953472) (BSN.cos_reduce1 qz525 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1455) (@Nat.cast Real Real.instNatCast ep1163)) 226375608064910080 72057594037927936 Bool.false 274814910018 274877906944 59 1000000000000000 92502466560 46251233280 (BSN.sin_reduce_arg_pos_rat_q1 51378545035331 137438953472 226375608064910080 72057594037927936 59 ep1455 ep1163 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 274814910018 274877906944 ep1455 ep1163 872227060873241 562949953421312 92592801001 92502466560 (ep1461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1463 := nat_lit 512922738257017867965419424027255701233911518352068244766656073549458139275172437753122324805555001943714548818253521694737441335017681695686849419543827048907136639003745491525143360476611420166114429552888677166051377485548409046746124874548277121

noncomputable def ep1464 := nat_lit 2128806533039805141061882073233664319835533213781053588865287857315332119162997489839677649348036817950427031568253007238835370337238255695318706258811204371934300794836767269258057848843812184697506274113673172452655028445154851521923629719748608000

noncomputable def ep1465 := nat_lit 5219881211360771271680885856542541879218200891770193862360805877393228554023567321865502736332297813475731674160151170911950205411656920678758484141118158252437586728336977404423510709501871891491435108140281505422007454545349105514372564969582522241

noncomputable def ep1466 := nat_lit 325707399555090186582467957204750640934836581708501199096389042169245814231938615945470680350249633146415335829942710107541811661597453121383762057598114268905948021610025392196482850873103264258718459939391995385256219352108692282854315347121537024000

noncomputable def ep1467 := BSN.cos_dyadic_bound_f 872227060873241 562949953421312 5 4 274877906944 92592801001 ep1463 ep1464 ep1458 ep1465 ep1466 ep1458 5884637386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 872227060873241) (BSN.cosEvenQ 562949953421312) 0 4 ep1463 ep1464 ep1458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 872227060873241) (BSN.cosOddQ 562949953421312) 0 4 ep1465 ep1466 ep1458 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1468 := @Enclosure.Real.IsNear.sin_image qz218 qz525 Bool.false 51378545035331 137438953472 701 274877906944 Bool.false 5884637386 274877906944 1 46251233280 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 105223260232358713641 281474976710656000 51291225655811 20163937500000000000000 51378545035331 137438953472 701 274877906944 (ep1454 rfl) rfl) (Enclosure.sfrac_false_div 51378545035331 137438953472) (BSN.sin_reduce1 qz525 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1455) (@Nat.cast Real Real.instNatCast ep1163)) 226375608064910080 72057594037927936 Bool.false 5884637386 274877906944 59 1000000000000000 92502466560 46251233280 (BSN.sin_reduce_arg_pos_rat_q1 51378545035331 137438953472 226375608064910080 72057594037927936 59 ep1455 ep1163 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5884637386 274877906944 ep1455 ep1163 872227060873241 562949953421312 92592801001 92502466560 (ep1467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1469 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz494) Bool.true 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 Bool.true 11942362553753111 37778931862957161709568 49424219351077831 ep1404 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 4058827 274877906944 1 274877906944 137407455009 137438953472 7982664169 3103867724019793920 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 qz514 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 274814910018 274877906944 32696992436224 12713442197585075896320 137407455009 137438953472 7982664169 3103867724019793920 (ep1462 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz494 4058827 274877906944 1 274877906944 2942318693 137438953472 7982664169 3103867724019793920 11942362553753111 37778931862957161709568 49424219351077831 ep1404 qz514 (@Enclosure.Real.IsNear.neg qz217 Bool.false 2942318693 137438953472 7982664169 3103867724019793920 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 5884637386 274877906944 32696992436224 12713442197585075896320 2942318693 137438953472 7982664169 3103867724019793920 (ep1468 rfl rfl) rfl)) rfl)

noncomputable def ep1470 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 12709885870759 5625000000 0 1 11942362553753111 37778931862957161709568 49424219351077831 ep1404 ep1398

noncomputable def ep1471 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1297118411 15000000 0 1 Bool.false 12709885870759 5625000000 0 1 ep1450

noncomputable def ep1472 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 Bool.true 11942362553753111 37778931862957161709568 49424219351077831 ep1404

noncomputable def ep1473 := nat_lit 15490658339310137426626621

noncomputable def ep1474 := nat_lit 566683977944357425643520000000

noncomputable def ep1475 := nat_lit 64109064869585527284046541

noncomputable def ep1476 := nat_lit 787607744676498627426334174693

noncomputable def ep1477 := nat_lit 23611832414348226068480000000000

noncomputable def ep1478 := nat_lit 2846611927362553197238967520307

noncomputable def ep1479 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1473 ep1474 ep1475 ep1397 ep1476 ep1477 ep1478

noncomputable def ep1480 := nat_lit 446690452641757759568933844204024284971675950629519360000000

noncomputable def ep1481 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1297118411 15000000 0 1 11942362553753111 37778931862957161709568 49424219351077831 ep1404 ep1473

noncomputable def ep1482 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 12709885870759 5625000000 0 1 557713088391814443 37778931862957161709568 1567778317929768211 ep1404 ep1476

noncomputable abbrev qz526 := (@ep1453 ep1404 (BSN.cpow_neg_s_sub_mk qz155 117628 1000 24 3 4586471424 qz156 rfl EMRow37.d17) ep1469)

noncomputable def ep1483 := ep1393 (@ep1401 ep1402 ep1403 ep1384 ep1385 ep1386 ep1387 (@ep1405 ep1395 ep1396 ep1397 ep1451 (ep1452 qz526) rfl) (@ep1470 ep1399 ep1400 ep1402 ep1471 (ep1472 qz526) rfl) rfl rfl) (@ep1479 ep1402 ep1480 ep1389 ep1221 ep1390 ep1392 (@ep1481 ep1474 ep1475 ep1397 ep1451 (ep1472 qz526) rfl) (@ep1482 ep1477 ep1478 ep1402 ep1471 (ep1452 qz526) rfl) rfl rfl)

noncomputable def ep1484 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1389 ep1221 ep1390 ep1392 ep1389 ep1221 ep1390

noncomputable def ep1485 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1384 ep1385 ep1386 ep1387 Bool.true ep1389 ep1221 ep1390

noncomputable def ep1486 := @ep1356 1132505367249202145 1008806316530991104 291632333011 1008806316530991104 (@ep1357 1 3670016 (ep1358 (@ep1359 1048576 1 1048576 (ep1360 (@ep1361 3462149096 432768637 31250 0 1 (ep1365 rfl) (ep1368 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1369 2289 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1370 2289 274877906944 9177776557 274877906944 2289 274877906944 (@ep1375 4588887134 4588889423 137438953472 (@ep1380 ep1212 ep1381 ep1382 ep1383 ep1371 ep1372 ep1373 ep1374 (@ep1388 ep1387 ep1376 ep1377 ep1378 ep1374 (@ep1391 ep1392 ep1483) (@ep1391 ep1392 ep1483) rfl) (@ep1484 ep1392 ep1379 ep1212 ep1381 ep1382 (@ep1485 ep1392 ep1483) (@ep1485 ep1392 ep1483) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow37.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 10615710213822614249 9079256848778919936 900192327321451 9079256848778919936 := ep1354 (ep1355 ep1486) rfl rfl

noncomputable def EMRow37.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz527 := (EMRow37.d3 qz537 qz570 (@Enclosure.dec_le_dec qz537 qz570 115476 1000 117628 1000 (@Eq.refl Real qz537) (@Eq.refl Real qz570) rfl rfl rfl) 24 24 1 1)

noncomputable abbrev qz262 := qz527

noncomputable def ep1487 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 115476 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 24 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz527)

noncomputable def ep1488 := @Enclosure.Real.IsNear.neg_val qz263 ep277 ep278

noncomputable def ep1489 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 24 qz13) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz527)

noncomputable def ep1490 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1488 ep279 ep280 (@ep1489 ep277 ep278 ep279 ep280 (@Eq.refl Real (hardyZApproximantEM 1 24 qz13)) EMRow37.d10) rfl rfl rfl)

noncomputable def ep1491 := @Enclosure.Real.IsNear.pos_val qz264 ep834 ep835

noncomputable def ep1492 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 24 qz155) Bool.false

noncomputable def ep1493 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 24 qz13)

noncomputable def ep1494 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 24 qz13) Bool.true

noncomputable def ep1495 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 24 qz13) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 29027674164095956793 27237770546336759808 2677225327556167 27237770546336759808 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 24))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1496 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 24 qz155)

noncomputable def ep1497 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 24 qz155) Bool.false

noncomputable def ep1498 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 24 qz155) (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 10615710213822614249 9079256848778919936 900192327321451 9079256848778919936 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz380 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz152 1 24))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz152 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1499 := @List.cons EMRow37.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1487 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 24 rfl) (ep1490 (@ep1491 ep836 ep837 (@ep1492 ep834 ep835 ep836 ep837 (@Eq.refl Real (hardyZApproximantEM 1 24 qz155)) EMRow37.d13) rfl rfl rfl)) (ep1493 (hardyZErrorBoundEM 1 24 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 24 qz13 rfl) (@ep1494 Bool.false ep277 ep278 ep279 ep280 29027674164095956793 27237770546336759808 2677225327556167 27237770546336759808 (@ep1489 ep277 ep278 ep279 ep280 (@Eq.refl Real (hardyZApproximantEM 1 24 qz13)) EMRow37.d10) (ep1495 EMRow37.d18) rfl rfl rfl rfl rfl)) (ep1496 (hardyZErrorBoundEM 1 24 qz155) (BSN.hardyZErrorBoundEM_le_strong 1 24 qz155 rfl) (@ep1497 Bool.false ep834 ep835 ep836 ep837 10615710213822614249 9079256848778919936 900192327321451 9079256848778919936 (@ep1492 ep834 ep835 ep836 ep837 (@Eq.refl Real (hardyZApproximantEM 1 24 qz155)) EMRow37.d13) (ep1498 EMRow37.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow37.d0)

noncomputable abbrev qz528 := (@Enclosure.dec_le_dec qz537 qz570 115476 1000 117628 1000 (@Eq.refl Real qz537) (@Eq.refl Real qz570) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1499 (@List.IsChain.singleton EMRow37.d1 EMRow37.d20 (EMRow37.d2 qz284 qz436 qz528))))

noncomputable abbrev qz529 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1500 := And (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 qz265)) (@Option.some Real qz13))

noncomputable def ep1501 := ep1500 (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 qz265)) (@Option.some Real qz155))

noncomputable def ep1502 := @And.intro (@Eq Nat (@List.length qz529 qz265) 1) ep1501

noncomputable def ep1503 := @And.intro (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 qz265)) (@Option.some Real qz13))

noncomputable def ep1504 := @ep1503 (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 qz265)) (@Option.some Real qz155))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1499 (@List.IsChain.singleton EMRow37.d1 EMRow37.d20 (EMRow37.d2 qz284 qz436 qz528)))

theorem EMRow37.d21 : Zeta.Certificates.BatchSpec 1 115476 1000 117628 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz529 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz529 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz155)))) qz266 (ep1502 (@Eq.refl Nat 1) (ep1504 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz155))))

theorem solution : Zeta.Certificates.BatchSpec 1 115476 1000 117628 1000 := EMRow37.d21
#print axioms solution
#check solution
