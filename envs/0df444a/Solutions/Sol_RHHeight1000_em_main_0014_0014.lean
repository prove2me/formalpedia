-- Prove2me | solution 1 for RHHeight1000.em_main_0014_0014
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:07:30.571175+00:00
-- url     : https://prove2.me/submissions/6288d86d-0711-4830-b49e-4243228ba6d2

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow14.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow14.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow14.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow14.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow14.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz265 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz265

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz266 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000072727 36363500000000000000 4138529546116343 2251799813685248 250000000072727 36363500000000000000 481788 262144

noncomputable abbrev qz267 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 262144 qz267 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 145454 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz268 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz268

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000290908 145454000000000000000 4138529546116343 2251799813685248 250000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 145454 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000290908 145454000000000000000 4138529546116343 2251799813685248 250000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz269)

theorem EMRow14.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 3 262144 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz266) Bool.false 120447 65536 3 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz266) Bool.false 481788 262144 3 262144 120447 65536 3 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 145454 600168 524288 1 145454 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 145454 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 145454 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 145454 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 145454 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 145454 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 145454 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow14.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz489 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 60352 1000)))

noncomputable abbrev qz466 := qz489

noncomputable abbrev qz270 := qz466

noncomputable abbrev qz4 := (BSN.headSumC qz270 9)

noncomputable abbrev qz490 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz467 := qz490

noncomputable abbrev qz271 := qz467

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz6 := qz270

noncomputable abbrev qz468 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz272 := qz468

noncomputable abbrev qz469 := (@Neg.neg Complex Complex.instNeg qz489)

noncomputable abbrev qz273 := qz469

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 8) qz273)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.true 34900714709 137438953472 28601375580389 9995522769158144 Bool.false 15277904063 68719476736 28593905790219 9995522769158144

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.true 165660978053 274877906944 51190254749723 19991045538316288 Bool.false 45124984317 274877906944 51206653233683 19991045538316288 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 7) qz273)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.true 165660978053 274877906944 51190254749723 19991045538316288 Bool.false 45124984317 274877906944 51206653233683 19991045538316288

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.true 128055585543 274877906944 44788981612293 19991045538316288 Bool.true 51724803977 274877906944 44783637050517 19991045538316288 Bool.true

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 6) qz273)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.true 128055585543 274877906944 44788981612293 19991045538316288 Bool.true 51724803977 274877906944 44783637050517 19991045538316288

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.true 77840692617 137438953472 18940193920365 9995522769158144 Bool.false 57039541951 274877906944 37847473709613 19991045538316288 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 5) qz273)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.true 77840692617 137438953472 18940193920365 9995522769158144 Bool.false 57039541951 274877906944 37847473709613 19991045538316288

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.true 9194952661 68719476736 3785721847445 2498880692289536 Bool.false 88248772665 274877906944 30280060837351 19991045538316288 Bool.true

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 4) qz273)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.true 9194952661 68719476736 3785721847445 2498880692289536 Bool.false 88248772665 274877906944 30280060837351 19991045538316288

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 4603730573 68719476736 681897070463 624720173072384 Bool.false 107058498129 137438953472 10897692593067 9995522769158144 Bool.true

noncomputable abbrev qz470 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz274 := qz470

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz272 qz274 qz273)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 4603730573 68719476736 681897070463 624720173072384 Bool.false 107058498129 137438953472 10897692593067 9995522769158144

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 10534986853 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 8589934592 750854765025 1249440346144768 Bool.true

noncomputable abbrev qz471 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz275 := qz471

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz272 qz275 qz273)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 10534986853 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 8589934592 750854765025 1249440346144768

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz276 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz276

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz277 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz277))

noncomputable abbrev qz491 := (Enclosure.sfrac Bool.false 60352 1000)

noncomputable abbrev qz472 := qz491

noncomputable abbrev qz278 := qz472

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz278

noncomputable abbrev qz279 := (@Eq.refl Real qz472)

noncomputable abbrev qz18 := qz279

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.true 6644882331 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 8589934592 750854765025 1249440346144768 (BSN.cpow_neg_s_mk qz17 60352 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz277) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz277) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz277 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz277 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 72727 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 2876418433596667041642133778106226300666251736247425692492628860935906328576

noncomputable def ep57 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep58 := nat_lit 1657242353437222909616904385945804835374662058230691714605782513808900096

noncomputable def ep59 := nat_lit 8625940816083126679107167525546787292328005884625815694048675017780101185536

noncomputable def ep60 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz280 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz281 := (BSN.cosOddQ 1073741824)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 1065180612 1073741824 3 2 524288 145597 ep56 ep57 ep58 ep59 ep60 ep58 286782 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1065180612) qz280 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1065180612) qz281 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz22 := (Enclosure.Real.IsNear.const Bool.false 60352 1000)

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz282 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21932399) qz20)

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 72727 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 72727 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz16 qz282 Bool.false 21932399 524288 109 131072 Bool.true 286782 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 21418359 512000 7544 9090875 21932399 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 60352 1000 0 1 181704 262144 1 72727 21418359 512000 7544 9090875 qz22 qz283 rfl) rfl) (Enclosure.sfrac_false_div 21932399 524288) (BSN.cos_reduce2 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 74955422010188274597888) qz23) 226375608064910080 72057594037927936 Bool.false 286782 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 21932399 524288 226375608064910080 72057594037927936 6 74955422010188274597888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 286782 524288 74955422010188274597888 75557863725914323419136 1065180612 1073741824 145597 145454 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 5176227386591250896628147277082450697330953395598781693115047323673584271360

noncomputable def ep64 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep65 := nat_lit 13554102858214377796934339309067268142323795154664435695382428866503696777216

noncomputable def ep66 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable abbrev qz284 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz285 := (BSN.sinOddQ 1073741824)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 1065180612 1073741824 3 2 524288 145597 ep63 ep64 ep58 ep65 ep66 ep58 438900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1065180612) qz284 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1065180612) qz285 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz16 qz282 Bool.false 21932399 524288 109 131072 Bool.true 438900 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 21418359 512000 7544 9090875 21932399 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 60352 1000 0 1 181704 262144 1 72727 21418359 512000 7544 9090875 qz22 qz283 rfl) rfl) (Enclosure.sfrac_false_div 21932399 524288) (BSN.sin_reduce2 qz282 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 74955422010188274597888) qz23) 226375608064910080 72057594037927936 Bool.false 438900 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 21932399 524288 226375608064910080 72057594037927936 6 74955422010188274597888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 438900 524288 74955422010188274597888 75557863725914323419136 1065180612 1073741824 145597 145454 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz286 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.true 6644882331 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 8589934592 750854765025 1249440346144768 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz16) 46341 65536 1 262144 143391 262144 8058315 9532473344 6644882331 17179869184 2997887517207 4997761384579072 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.true 286782 524288 8058315 9532473344 143391 262144 8058315 9532473344 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 109725 131072 8058315 9532473344 5084766225 8589934592 750854765025 1249440346144768 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.true 109725 131072 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.true 438900 524288 8058315 9532473344 109725 131072 8058315 9532473344 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz287 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz24 := qz287

noncomputable def ep70 := @ep51 6644882331 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 8589934592 750854765025 1249440346144768 Bool.false 10534986853 10534986853 17179869184 2997887517207 4997761384579072 Bool.false 5084766225 5084766225 8589934592 750854765025 1249440346144768 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep53 ep69) rfl rfl

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz288))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 37536216839 68719476736 2457289046497 4997761384579072 Bool.false 25702238529 137438953472 4890854472867 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 3 qz18 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz288) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz288) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 72727 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 15736659599271732797727075839963281

noncomputable def ep75 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep76 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep77 := BSN.cos_dyadic_bound_f 354183347 1073741824 2 1 524288 145597 ep74 ep75 ep74 ep74 ep76 ep74 496022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 354183347) qz280 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 354183347) qz281 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 34762027) qz20)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 72727 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 72727 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz26 qz289 Bool.false 34762027 524288 109 131072 Bool.true 496022 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 135789171 2048000 7544 9090875 34762027 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz27 60352 1000 0 1 287994 262144 1 72727 135789171 2048000 7544 9090875 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 34762027 524288) (BSN.cos_reduce2 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24923437355285677604864) qz23) 226375608064910080 72057594037927936 Bool.false 496022 524288 10 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 34762027 524288 226375608064910080 72057594037927936 10 24923437355285677604864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496022 524288 24923437355285677604864 75557863725914323419136 354183347 1073741824 145597 145454 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep80 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep81 := BSN.sin_dyadic_bound_f 354183347 1073741824 2 1 524288 145597 ep74 ep79 ep74 ep74 ep80 ep74 169821 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 354183347) qz284 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 354183347) qz285 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz26 qz289 Bool.false 34762027 524288 109 131072 Bool.true 169821 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 135789171 2048000 7544 9090875 34762027 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz27 60352 1000 0 1 287994 262144 1 72727 135789171 2048000 7544 9090875 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 34762027 524288) (BSN.sin_reduce2 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24923437355285677604864) qz23) 226375608064910080 72057594037927936 Bool.false 169821 524288 10 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 34762027 524288 226375608064910080 72057594037927936 10 24923437355285677604864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 169821 524288 24923437355285677604864 75557863725914323419136 354183347 1073741824 145597 145454 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz291 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 37536216839 68719476736 2457289046497 4997761384579072 Bool.false 25702238529 137438953472 4890854472867 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz26) 151349 262144 1 262144 248011 262144 8058315 9532473344 37536216839 68719476736 2457289046497 4997761384579072 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 496022 524288 8058315 9532473344 248011 262144 8058315 9532473344 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 151349 262144 1 262144 169821 524288 8058315 9532473344 25702238529 137438953472 4890854472867 9995522769158144 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 169821 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 169821 524288 8058315 9532473344 169821 524288 8058315 9532473344 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 37536216839 68719476736 2457289046497 4997761384579072 Bool.false 25702238529 137438953472 4890854472867 9995522769158144 Bool.false 79091489002521362432 4603730573 68719476736 681897070463 624720173072384 Bool.false 919625496445864378368 107058498129 137438953472 10897692593067 9995522769158144 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz292))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 6899341617 34359738368 1058133565593 2498880692289536 Bool.true 125868223593 274877906944 8484675651217 19991045538316288 (BSN.cpow_neg_s_mk qz17 60352 1000 4 qz18 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz292) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz292) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz292 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz292 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 471225594319403171539306640625

noncomputable def ep88 := nat_lit 73155514365408823868279100600

noncomputable def ep89 := BSN.log_dyadic_bound 3 5 13 12 ep87 262144 72727 ep88 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep88 ep87 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep90 := nat_lit 38769401830828628355083903895603361

noncomputable def ep91 := BSN.sin_dyadic_bound_f 443733559 1073741824 2 1 524288 145597 ep90 ep79 ep90 ep90 ep80 ep90 210552 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 443733559) qz284 0 1 ep90 ep79 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 443733559) qz285 0 1 ep90 ep80 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 43864799) qz20)

noncomputable abbrev qz294 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 72727 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 72727 rfl rfl rfl (ep89 rfl)))

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz29 qz293 Bool.false 43864799 524288 109 131072 Bool.true 210552 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 21418359 256000 7544 9090875 43864799 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz30 60352 1000 0 1 363408 262144 1 72727 21418359 256000 7544 9090875 qz22 qz294 rfl) rfl) (Enclosure.sfrac_false_div 43864799 524288) (BSN.cos_reduce1 qz293 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31224973334429049028608) qz23) 226375608064910080 72057594037927936 Bool.false 210552 524288 13 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 43864799 524288 226375608064910080 72057594037927936 13 31224973334429049028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 210552 524288 31224973334429049028608 75557863725914323419136 443733559 1073741824 145597 145454 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := BSN.cos_dyadic_bound_f 443733559 1073741824 2 1 524288 145597 ep90 ep75 ep90 ep90 ep76 ep90 480151 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 443733559) qz280 0 1 ep90 ep75 ep90 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 443733559) qz281 0 1 ep90 ep76 ep90 rfl rfl rfl rfl) rfl rfl

noncomputable def ep94 := @Enclosure.Real.IsNear.sin_image qz29 qz293 Bool.false 43864799 524288 109 131072 Bool.false 480151 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 21418359 256000 7544 9090875 43864799 524288 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz30 60352 1000 0 1 363408 262144 1 72727 21418359 256000 7544 9090875 qz22 qz294 rfl) rfl) (Enclosure.sfrac_false_div 43864799 524288) (BSN.sin_reduce1 qz293 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31224973334429049028608) qz23) 226375608064910080 72057594037927936 Bool.false 480151 524288 13 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 43864799 524288 226375608064910080 72057594037927936 13 31224973334429049028608 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 480151 524288 31224973334429049028608 75557863725914323419136 443733559 1073741824 145597 145454 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz295 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep95 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 6899341617 34359738368 1058133565593 2498880692289536 Bool.true 125868223593 274877906944 8484675651217 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 262143 524288 1 524288 26319 65536 8058315 9532473344 6899341617 34359738368 1058133565593 2498880692289536 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 210552 524288 8058315 9532473344 26319 65536 8058315 9532473344 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 262143 524288 1 524288 480151 524288 8058315 9532473344 125868223593 274877906944 8484675651217 19991045538316288 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 480151 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 480151 524288 8058315 9532473344 480151 524288 8058315 9532473344 (ep94 rfl rfl) rfl)) rfl)

noncomputable def ep96 := @ep47 6899341617 34359738368 1058133565593 2498880692289536 Bool.true 125868223593 274877906944 8484675651217 19991045538316288 Bool.true 315936167738105397248 9194952661 68719476736 3785721847445 2498880692289536 Bool.false 12128818960266040442880 88248772665 274877906944 30280060837351 19991045538316288 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep95) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep97 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 59450787295 137438953472 3797306530585 9995522769158144 Bool.true 15604615357 137438953472 3783706436131 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 5 qz18 rfl)

noncomputable def ep98 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz296 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz296 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep99 := nat_lit 39510257877627786146545168145625

noncomputable def ep100 := nat_lit 8181717556663416291180905432700

noncomputable def ep101 := nat_lit 6646766139202842132480000

noncomputable def ep102 := BSN.log_dyadic_bound 2 3 16 15 ep99 262144 72727 ep100 ep101 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep100 ep99 ep101 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep103 := nat_lit 15948929931461310016512669997000792307784176790088337701345058103638371442305

noncomputable def ep104 := nat_lit 15712469011473967672282263860779139892595707110658323624168824464544210561

noncomputable def ep105 := nat_lit 41745567727808663619397107279227480293894355686337913836702688365157901246081

noncomputable def ep106 := BSN.sin_dyadic_bound_f 1411011503 1073741824 3 2 524288 145597 ep103 ep64 ep104 ep105 ep66 ep104 507110 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1411011503) qz284 0 2 ep103 ep64 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1411011503) qz285 0 2 ep105 ep66 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz33 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12731375) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 72727 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 72727 rfl rfl rfl (ep102 rfl)))

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep107 := @Enclosure.Real.IsNear.cos_image qz32 qz297 Bool.false 12731375 131072 109 131072 Bool.true 507110 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 24865967 256000 7544 9090875 12731375 131072 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 60352 1000 0 1 421904 262144 1 72727 24865967 256000 7544 9090875 qz22 qz298 rfl) rfl) (Enclosure.sfrac_false_div 12731375 131072) (BSN.cos_reduce1 qz297 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24822776871932018032640) qz299) 226375608064910080 72057594037927936 Bool.false 507110 524288 15 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 12731375 131072 226375608064910080 72057594037927936 15 24822776871932018032640 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 507110 524288 24822776871932018032640 18889465931478580854784 1411011503 1073741824 145597 145454 (ep106 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep108 := nat_lit 8867499948150271772583608782271897566499029642098257977913551757338892672641

noncomputable def ep109 := nat_lit 26571074906427867382406261819094134419711897512073457286492317623087589596801

noncomputable def ep110 := BSN.cos_dyadic_bound_f 1411011503 1073741824 3 2 524288 145597 ep108 ep57 ep104 ep109 ep60 ep104 133106 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1411011503) qz280 0 2 ep108 ep57 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1411011503) qz281 0 2 ep109 ep60 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz32 qz297 Bool.false 12731375 131072 109 131072 Bool.false 133106 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 24865967 256000 7544 9090875 12731375 131072 109 131072 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 60352 1000 0 1 421904 262144 1 72727 24865967 256000 7544 9090875 qz22 qz298 rfl) rfl) (Enclosure.sfrac_false_div 12731375 131072) (BSN.sin_reduce1 qz297 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24822776871932018032640) qz299) 226375608064910080 72057594037927936 Bool.false 133106 524288 15 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 12731375 131072 226375608064910080 72057594037927936 15 24822776871932018032640 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 133106 524288 24822776871932018032640 18889465931478580854784 1411011503 1073741824 145597 145454 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep98 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 59450787295 137438953472 3797306530585 9995522769158144 Bool.true 15604615357 137438953472 3783706436131 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz32) 234469 524288 1 524288 253555 262144 8058315 9532473344 59450787295 137438953472 3797306530585 9995522769158144 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 507110 524288 8058315 9532473344 253555 262144 8058315 9532473344 (ep107 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 234469 524288 1 524288 66553 262144 8058315 9532473344 15604615357 137438953472 3783706436131 9995522769158144 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.false 66553 262144 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.false 133106 524288 8058315 9532473344 66553 262144 8058315 9532473344 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep45 59450787295 137438953472 3797306530585 9995522769158144 Bool.true 15604615357 137438953472 3783706436131 9995522769158144 Bool.true 5349171665408058458112 77840692617 137438953472 18940193920365 9995522769158144 Bool.false 7839454952267681103872 57039541951 274877906944 37847473709613 19991045538316288 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep96 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep97 ep112) rfl rfl

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz301))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 27625799691 274877906944 6908593771563 19991045538316288 Bool.true 13595543241 34359738368 867020417613 2498880692289536 (BSN.cpow_neg_s_mk qz17 60352 1000 6 qz18 rfl)

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz301) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz301) (Real.sqrt qz302) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz302) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 72727 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz36 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz36 60352 1000 0 1 4034681531866359 2251799813685248 500000000072727 36363500000000000000 3804704684549976537 35184372088832000 471500000068581561 568179687500000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz302) Bool.false 16922680887833197019136 9444732965739290427392 1000000000145454 72727000000000000000 4034681531866359 2251799813685248 500000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 9084498357354658436662371106442226756259722972328275119385741125641493578561

noncomputable def ep119 := nat_lit 16489456929140365787019570118962528642080148952687781753244822925002703681

noncomputable def ep120 := nat_lit 27220516158205694578413074179088755211495008619079449794650733731074475328321

noncomputable def ep121 := BSN.cos_dyadic_bound_f 1419550327 1073741824 3 2 524288 145597 ep118 ep57 ep119 ep120 ep60 ep119 129069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1419550327) qz280 0 2 ep118 ep57 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1419550327) qz281 0 2 ep120 ep60 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz303 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 56694517) qz20)

noncomputable def ep122 := @Enclosure.Real.IsNear.cos_image qz35 qz303 Bool.false 56694517 524288 109 131072 Bool.false 129069 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 3804704684549976537 35184372088832000 471500000068581561 568179687500000000000 56694517 524288 109 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 56694517 524288) (BSN.cos_reduce0 qz303 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 99891973847588855087104) qz23) 226375608064910080 72057594037927936 Bool.false 129069 524288 17 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 56694517 524288 226375608064910080 72057594037927936 17 99891973847588855087104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 129069 524288 99891973847588855087104 75557863725914323419136 1419550327 1073741824 145597 145454 (ep121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep123 := nat_lit 16338905477695072893362652335500838138353837231028744989491738167814686278465

noncomputable def ep124 := nat_lit 42765674273220868414199391098500065315982396316294742373449298821445602542401

noncomputable def ep125 := BSN.sin_dyadic_bound_f 1419550327 1073741824 3 2 524288 145597 ep123 ep64 ep119 ep124 ep66 ep119 508152 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1419550327) qz284 0 2 ep123 ep64 ep119 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1419550327) qz285 0 2 ep124 ep66 ep119 rfl rfl rfl rfl) rfl rfl

noncomputable def ep126 := @Enclosure.Real.IsNear.sin_image qz35 qz303 Bool.false 56694517 524288 109 131072 Bool.false 508152 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 3804704684549976537 35184372088832000 471500000068581561 568179687500000000000 56694517 524288 109 131072 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 56694517 524288) (BSN.sin_reduce0 qz303 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 99891973847588855087104) qz23) 226375608064910080 72057594037927936 Bool.false 508152 524288 17 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 56694517 524288 226375608064910080 72057594037927936 17 99891973847588855087104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 508152 524288 99891973847588855087104 75557863725914323419136 1419550327 1073741824 145597 145454 (ep125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep115 rfl rfl) rfl)

noncomputable def ep127 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 27625799691 274877906944 6908593771563 19991045538316288 Bool.true 13595543241 34359738368 867020417613 2498880692289536 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 214039 524288 1 524288 129069 524288 8058315 9532473344 27625799691 274877906944 6908593771563 19991045538316288 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 129069 524288 8058315 9532473344 129069 524288 8058315 9532473344 (ep122 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 214039 524288 1 524288 63519 65536 8058315 9532473344 13595543241 34359738368 867020417613 2498880692289536 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 63519 65536 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 508152 524288 8058315 9532473344 63519 65536 8058315 9532473344 (ep126 rfl rfl) rfl)) rfl)

noncomputable def ep128 := @ep43 27625799691 274877906944 6908593771563 19991045538316288 Bool.true 13595543241 34359738368 867020417613 2498880692289536 Bool.true 17599825663274092855296 128055585543 274877906944 44788981612293 19991045538316288 Bool.true 1777250731785805889536 51724803977 274877906944 44783637050517 19991045538316288 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep127) rfl rfl

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz305))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep129 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 18802696255 137438953472 3200636568715 9995522769158144 Bool.false 48424894147 137438953472 3211508091583 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 7 qz18 rfl)

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep130 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz305) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz305) (Real.sqrt qz306) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz306) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep131 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 72727 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep132 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz39 60352 1000 0 1 4381792198794487 2251799813685248 500000000072727 36363500000000000000 4132030043463201241 35184372088832000 471500000068581561 568179687500000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz306) Bool.false 18378568546572512002048 9444732965739290427392 1000000000145454 72727000000000000000 4381792198794487 2251799813685248 500000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep133 := nat_lit 6171471152142569500075835443185067884771010950694522676777366108374000586881

noncomputable def ep134 := nat_lit 7618806271577056775690424472578036060622378687136044916554434752053891201

noncomputable def ep135 := nat_lit 18499175843884554386676125480610047582191788094709295940498989455617893978241

noncomputable def ep136 := BSN.cos_dyadic_bound_f 1288949393 1073741824 3 2 524288 145597 ep133 ep57 ep134 ep135 ep60 ep134 189770 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1288949393) qz280 0 2 ep133 ep57 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1288949393) qz281 0 2 ep135 ep60 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 61572045) qz20)

noncomputable def ep137 := @Enclosure.Real.IsNear.cos_image qz38 qz307 Bool.false 61572045 524288 109 131072 Bool.true 189770 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 4132030043463201241 35184372088832000 471500000068581561 568179687500000000000 61572045 524288 109 131072 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 61572045 524288) (BSN.cos_reduce2 qz307 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 90701750106028538593280) qz23) 226375608064910080 72057594037927936 Bool.false 189770 524288 18 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 61572045 524288 226375608064910080 72057594037927936 18 90701750106028538593280 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 189770 524288 90701750106028538593280 75557863725914323419136 1288949393 1073741824 145597 145454 (ep136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep138 := nat_lit 11102553028839363454715951458155059763739321808300431982266015447271557943425

noncomputable def ep139 := nat_lit 29065779865377684289476374084117173037123882789579101595117523753255516885121

noncomputable def ep140 := BSN.sin_dyadic_bound_f 1288949393 1073741824 3 2 524288 145597 ep138 ep64 ep134 ep139 ep66 ep134 488738 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1288949393) qz284 0 2 ep138 ep64 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1288949393) qz285 0 2 ep139 ep66 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep141 := @Enclosure.Real.IsNear.sin_image qz38 qz307 Bool.false 61572045 524288 109 131072 Bool.true 488738 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 4132030043463201241 35184372088832000 471500000068581561 568179687500000000000 61572045 524288 109 131072 (ep132 rfl) rfl) (Enclosure.sfrac_false_div 61572045 524288) (BSN.sin_reduce2 qz307 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 90701750106028538593280) qz23) 226375608064910080 72057594037927936 Bool.false 488738 524288 18 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 61572045 524288 226375608064910080 72057594037927936 18 90701750106028538593280 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 488738 524288 90701750106028538593280 75557863725914323419136 1288949393 1073741824 145597 145454 (ep140 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep130 rfl rfl) rfl)

noncomputable def ep142 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 18802696255 137438953472 3200636568715 9995522769158144 Bool.false 48424894147 137438953472 3211508091583 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 198163 524288 1 524288 94885 262144 8058315 9532473344 18802696255 137438953472 3200636568715 9995522769158144 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 189770 524288 8058315 9532473344 94885 262144 8058315 9532473344 (ep137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 198163 524288 1 524288 244369 262144 8058315 9532473344 48424894147 137438953472 3211508091583 9995522769158144 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.true 244369 262144 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.true 488738 524288 8058315 9532473344 244369 262144 8058315 9532473344 (ep141 rfl rfl) rfl)) rfl)

noncomputable def ep143 := @ep41 18802696255 137438953472 3200636568715 9995522769158144 Bool.false 48424894147 137438953472 3211508091583 9995522769158144 Bool.true 22768271454752280150016 165660978053 274877906944 51190254749723 19991045538316288 Bool.false 6201930619968892698624 45124984317 274877906944 51206653233683 19991045538316288 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep128 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep129 ep142) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 95859548635 274877906944 6012496411055 19991045538316288 Bool.false 15986631935 274877906944 5981158346755 19991045538316288 (BSN.cpow_neg_s_mk qz17 60352 1000 8 qz18 rfl)

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep145 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz310) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz310) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep146 := BSN.log_dyadic_bound 0 16 1 0 1 262144 72727 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep147 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz42 60352 1000 0 1 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 8831168739569898891 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 19639770079031275290624 9444732965739290427392 1000000000218181 72727000000000000000 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep148 := nat_lit 20879504851603397099223122431264286588979629950240788462168756143747183597025

noncomputable def ep149 := nat_lit 26912718228462912856875680763800809488075130572331067635734805476410578401

noncomputable def ep150 := nat_lit 54640844496115195305720855265407930231965956801132576624746028786661768484321

noncomputable def ep151 := BSN.sin_dyadic_bound_f 1509192699 1073741824 3 2 524288 145597 ep148 ep64 ep149 ep150 ep66 ep149 517145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1509192699) qz284 0 2 ep148 ep64 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1509192699) qz285 0 2 ep150 ep66 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz43 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 32898667) qz43)

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep152 := @Enclosure.Real.IsNear.cos_image qz41 qz311 Bool.false 32898667 262144 109 131072 Bool.false 517145 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 8831168739569898891 70368744177664000 943000000205744683 1136359375000000000000 32898667 262144 109 131072 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 32898667 262144) (BSN.cos_reduce3 qz311 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53099997505097820012544) qz312) 226375608064910080 72057594037927936 Bool.false 517145 524288 19 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 32898667 262144 226375608064910080 72057594037927936 19 53099997505097820012544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 517145 524288 53099997505097820012544 37778931862957161709568 1509192699 1073741824 145597 145454 (ep151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep153 := nat_lit 11611686125658981905282568319930737353650050030388140731265191104515728922081

noncomputable def ep154 := nat_lit 34781232940520019890133953598264610441973999830019760058524103702594365609441

noncomputable def ep155 := BSN.cos_dyadic_bound_f 1509192699 1073741824 3 2 524288 145597 ep153 ep57 ep149 ep154 ep60 ep149 86245 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1509192699) qz280 0 2 ep153 ep57 ep149 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1509192699) qz281 0 2 ep154 ep60 ep149 rfl rfl rfl rfl) rfl rfl

noncomputable def ep156 := @Enclosure.Real.IsNear.sin_image qz41 qz311 Bool.false 32898667 262144 109 131072 Bool.true 86245 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 8831168739569898891 70368744177664000 943000000205744683 1136359375000000000000 32898667 262144 109 131072 (ep147 rfl) rfl) (Enclosure.sfrac_false_div 32898667 262144) (BSN.sin_reduce3 qz311 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 53099997505097820012544) qz312) 226375608064910080 72057594037927936 Bool.false 86245 524288 19 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 32898667 262144 226375608064910080 72057594037927936 19 53099997505097820012544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 86245 524288 53099997505097820012544 37778931862957161709568 1509192699 1073741824 145597 145454 (ep155 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep145 rfl rfl) rfl)

noncomputable def ep157 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 95859548635 274877906944 6012496411055 19991045538316288 Bool.false 15986631935 274877906944 5981158346755 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 185363 524288 1 524288 517145 524288 8058315 9532473344 95859548635 274877906944 6012496411055 19991045538316288 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 517145 524288 8058315 9532473344 517145 524288 8058315 9532473344 (ep152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 185363 524288 1 524288 86245 524288 8058315 9532473344 15986631935 274877906944 5981158346755 19991045538316288 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 86245 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 86245 524288 8058315 9532473344 86245 524288 8058315 9532473344 (ep156 rfl rfl) rfl)) rfl)

noncomputable def ep158 := @ep39 95859548635 274877906944 6012496411055 19991045538316288 Bool.false 15986631935 274877906944 5981158346755 19991045538316288 Bool.true 19186870820119188078592 34900714709 137438953472 28601375580389 9995522769158144 Bool.false 16798233165314694053888 15277904063 68719476736 28593905790219 9995522769158144 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep143 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep144 ep157) rfl rfl

theorem EMRow14.d6 : Enclosure.Complex.IsNear qz4 Bool.true 34900714709 137438953472 28601375580389 9995522769158144 Bool.false 15277904063 68719476736 28593905790219 9995522769158144 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep158 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow14.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow14.d8 : @Eq Nat (Nat.pow 16 1) 16 := @Eq.refl Nat 16

noncomputable def ep159 := nat_lit 11800042334805941443706501073

noncomputable def ep160 := nat_lit 20998239514507504241889771520

noncomputable def ep161 := nat_lit 13707929098557756331827733107306967759

noncomputable def ep162 := nat_lit 2776605888000850668268524842990436352000

noncomputable abbrev qz492 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz473 := qz492

noncomputable abbrev qz314 := qz473

noncomputable abbrev qz44 := qz314

noncomputable abbrev qz474 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz315 := qz474

noncomputable abbrev qz45 := qz315

noncomputable abbrev qz493 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz494 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz475 := (@HAdd.hAdd Complex Complex Complex qz490 (@HAdd.hAdd Complex Complex Complex qz490 qz493 (@HMul.hMul Complex Complex Complex qz492 Complex.I (@HDiv.hDiv Complex Complex Complex qz494 (↑qz491) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz316 := qz475

noncomputable abbrev qz46 := (Complex.Stirling.logGammaStirling 1 qz316)

noncomputable abbrev qz476 := (@HAdd.hAdd Complex Complex Complex qz490 qz493 (@HMul.hMul Complex Complex Complex qz492 Complex.I (@HDiv.hDiv Complex Complex Complex qz494 (↑qz491) (2 : Complex))))

noncomputable abbrev qz317 := qz476

noncomputable abbrev qz47 := qz317

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz265 (@HDiv.hDiv Real Real Real qz268 qz278 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz318 := (@instHSub Real Real.instSub)

noncomputable def ep163 := Complex.re (@HMul.hMul Complex Complex Complex qz44 (Complex.exp (@HMul.hMul Complex Complex Complex qz44 Complex.I ↑(@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48))) (zetaApproximant qz6 1 16))

noncomputable def ep164 := @Enclosure.Real.IsNear.of_eq ep163 (@HSub.hSub Real Real Real qz318 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.im (zetaApproximant qz6 1 16))))

noncomputable def ep165 := nat_lit 295002687082743982141772228777

noncomputable def ep166 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.im (zetaApproximant qz6 1 16))) ep165

noncomputable def ep167 := nat_lit 524955987862687606047244288000

noncomputable def ep168 := nat_lit 13684564498609222446517231014911402767

noncomputable def ep169 := nat_lit 8202437310354493844488192000

noncomputable def ep170 := nat_lit 365071874195841957976595193680703

noncomputable def ep171 := nat_lit 43384467000013291691695700671725568000

noncomputable def ep172 := nat_lit 2419727687769370201998056213366556074211096469595750400000

noncomputable def ep173 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.re (zetaApproximant qz6 1 16)) 524287 524288 14269691

noncomputable def ep174 := nat_lit 11843137937727005860287557

noncomputable def ep175 := nat_lit 2511022773564416393740288000

noncomputable def ep176 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) Bool.false 524287 524288 14269691

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19765299) qz20)

noncomputable def ep177 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48) qz319 Bool.false 19765299 524288 189

noncomputable def ep178 := nat_lit 223417344000000000000000000

noncomputable def ep179 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48) Bool.false 5305707121014276101 140737488355328000 80373431723902947449573 ep178

noncomputable def ep180 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48 10167252964965679109 140737488355328000 28937260973902947449573 ep178 70744803 2048000

noncomputable def ep181 := nat_lit 10866088183837237454848000

noncomputable def ep182 := nat_lit 1191559168000000000000000000

noncomputable def ep183 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 213169897253452887667 4503599627370496000 269380780582549917014909 ep182 Bool.false 10167252964965679109 140737488355328000

noncomputable def ep184 := @Enclosure.Complex.IsNear.subLitP qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 182477938626869160667 4503599627370496000 261188780571825884502909 ep182 Bool.false 10602400617709568609 140737488355328000 25865260973679530105573

noncomputable def ep185 := nat_lit 960031869837257343611989381278072832

noncomputable def ep186 := nat_lit 2861827291525062691100126036885504

noncomputable abbrev qz495 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz477 := qz495

noncomputable abbrev qz320 := (@HSub.hSub Complex Complex Complex qz474 qz475 qz477)

noncomputable abbrev qz321 := (Complex.log qz475)

noncomputable abbrev qz49 := (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 qz320 qz321) qz316)

noncomputable abbrev qz322 := qz477

noncomputable abbrev qz50 := (@HMul.hMul Complex Complex Complex qz314 qz322 ↑(Real.log qz269))

noncomputable abbrev qz478 := qz494

noncomputable abbrev qz323 := qz478

noncomputable abbrev qz51 := qz323

noncomputable abbrev qz52 := (@instHMul Nat instMulNat)

noncomputable abbrev qz479 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz324 := qz479

noncomputable abbrev qz53 := qz324

noncomputable abbrev qz54 := qz316

noncomputable abbrev qz325 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz55 := qz325

noncomputable abbrev qz326 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz56 := qz326

noncomputable abbrev qz327 := (@instHSub Int Int.instSub)

noncomputable abbrev qz328 := (@instHMul Int Int.instMul)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz46 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz49 qz50) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k)))))) Bool.true 182477938626869160667

noncomputable def ep188 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz49 qz50) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) Bool.true 182478860837926824667 4503599627370496000

noncomputable def ep189 := nat_lit 783736778643898191935734546432

noncomputable def ep190 := nat_lit 355757530563693715640025088000

noncomputable def ep191 := @ep188 31883294467451388327 145454000000000000000000 Bool.false 10602787126610625121 140737488355328000 8419000009939380909 72727000000000000000000 Bool.false 879489 4294967296 3 4294967296 Bool.true 92150903 33554432000 943 100663296000 Bool.true ep189 182477938626869160667 4503599627370496000 261188780571825884502909 ep182 Bool.false ep190

noncomputable def ep192 := @Enclosure.Complex.IsNear.addLitP qz49 qz50 Bool.true 186617388245137320667 4503599627370496000 15525500001670030101 72727000000000000000000

noncomputable def ep193 := nat_lit 23917869247748744762753024

noncomputable def ep194 := @ep192 Bool.false 10602787126610625121 140737488355328000 8419000009939380909 72727000000000000000000 Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 Bool.true ep193 182478860837926824667 4503599627370496000 31883294467451388327 145454000000000000000000 Bool.false 10602787126610625121 10602787126610625121 140737488355328000

noncomputable abbrev qz57 := (@HMul.hMul Complex Complex Complex qz314 qz320 qz321)

noncomputable def ep195 := @Enclosure.Complex.IsNear.subLitP qz57 qz54 Bool.true 176484289083553704667 4503599627370496000 15525500001670030101 72727000000000000000000 Bool.false 14849681575221002849

noncomputable def ep196 := @ep195 140737488355328000 8419000009939380909 72727000000000000000000 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 Bool.true 746469552980549282668000 186617388245137320667 4503599627370496000 15525500001670030101 72727000000000000000000 Bool.false 42411148506442500484000 10602787126610625121 140737488355328000 8419000009939380909 72727000000000000000000

noncomputable abbrev qz58 := qz320

noncomputable abbrev qz59 := qz321

noncomputable def ep197 := @Enclosure.Complex.IsNear.mul qz58 qz59 Bool.true 176484289083553704667 4503599627370496000 15525500001670030101 72727000000000000000000 Bool.false 14849681575221002849 140737488355328000 8419000009939380909

noncomputable abbrev qz60 := (Complex.re qz320)

noncomputable abbrev qz61 := (Complex.re qz321)

noncomputable abbrev qz62 := (Complex.im qz320)

noncomputable abbrev qz63 := (Complex.im qz321)

noncomputable def ep198 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz60 qz61) (@HMul.hMul Real Real Real qz0 qz62 qz63) 214990396404146377 36028797018963968 3500000004581801 581816000000000000000 794367533726843757 17592186044416000

noncomputable def ep199 := nat_lit 24837955579794979979408427267915776

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz61 7000 4000 0 1 30712913772020911 9007199254740992 500000000654543 145454000000000000000

noncomputable def ep201 := @Enclosure.Complex.IsNear.re_isNear qz58 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable abbrev qz329 := (Enclosure.sfrac Bool.false 120704 4000)

noncomputable abbrev qz64 := qz329

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz58 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz64) Bool.false 7000 4000 0 1 Bool.false 120704 4000 0

noncomputable abbrev qz330 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz65 := qz330

noncomputable abbrev qz331 := (Complex.log (Complex.mk qz65 qz64))

noncomputable def ep203 := @Enclosure.Complex.IsNear.of_eq qz59 qz331 Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep204 := nat_lit 402024380110579564924759132422704137228142013674434690135880314637167850547389939809980409698540865475051520

noncomputable def ep205 := nat_lit 11257919936610313141983182938747197752949384756038233943084975757891683260729118530002729295836153699631104

noncomputable def ep206 := nat_lit 119321471907731022667711529269889184285616913437585785661360254394233684552574977301141321180061368320

noncomputable def ep207 := BSN.log_dyadic_bound 6458455616 22842455616 6 5 ep204 524288 145454 ep205 ep206 304775 29300911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 6458455616) (BSN.artanhQ 22842455616) 0 5 ep205 ep204 ep206 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz66 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz332 := (Real.log (Enclosure.sfrac Bool.false 14650455616 16000000))

noncomputable abbrev qz333 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep208 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz332 1 2 0 1 30712913772020911 4503599627370496 500000000654543 72727000000000000000 30712913772020911 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 14650455616 16000000 30712913772020911 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14650455616) qz334)) Bool.false 128819297085642395090944 18889465931478580854784 1000000001309086 145454000000000000000 30712913772020911 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 14650455616 16000000 9 29300911232 16384000000 304775 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep207 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep209 := BSN.arctan_dyadic_bound_f 9000 120704 1 0 524288 145454 0 1 1 0 1 1 39019 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz265 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz68 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz333 BSN.pi_near_15 rfl)

noncomputable abbrev qz335 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 120704)))

noncomputable def ep210 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz335 884279719003555 562949953421312 1 2000000000000000 39019 524288 1 145454 441651501084389670912 842383386772899 562949953421312 1000000000072727 145454000000000000000 qz68 (ep209 rfl) rfl rfl

noncomputable abbrev qz336 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 120704) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep211 := @Enclosure.Complex.IsNear.re_isNear qz59 Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (ep203 (@congrArg Complex Complex qz54 (Complex.mk qz65 qz64) Complex.log (BSN.w_shift_mk qz17 Bool.false 60352 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz331 Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz331) (@HMul.hMul Real Real Real qz0 qz66 qz332) Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 9000 120704 4000 14650455616 16000000 rfl rfl rfl) (ep208 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz331) qz336 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 9000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz336 (@HSub.hSub Real Real Real qz318 qz67 qz335) Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 120704 9000 rfl rfl) ep210))))

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz63 120704 4000 0 1 842383386772899 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep213 := @Enclosure.Complex.IsNear.im_isNear qz58 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable def ep214 := @Enclosure.Complex.IsNear.im_isNear qz59 Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (ep203 (@congrArg Complex Complex qz54 (Complex.mk qz65 qz64) Complex.log (BSN.w_shift_mk qz17 Bool.false 60352 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz331 Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz331) (@HMul.hMul Real Real Real qz0 qz66 qz332) Bool.false 30712913772020911 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 9000 120704 4000 14650455616 16000000 rfl rfl rfl) (ep208 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz331) qz336 Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 9000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz336 (@HSub.hSub Real Real Real qz318 qz67 qz335) Bool.false 842383386772899 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 120704 9000 rfl rfl) ep210))))

noncomputable abbrev qz337 := (Enclosure.Real.IsNear.const Bool.false 120704 4000)

noncomputable abbrev qz69 := (@ep202 1 (BSN.w_sub_half_mk qz278 Bool.false 60352 1000 2 qz279 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz329 Bool.false 7000 4000 0 1 Bool.false 120704 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz337))

noncomputable def ep215 := @ep198 943000000068581561 4545437500000000000000 ep199 176484289083553704667 4503599627370496000 15525500001670030101 72727000000000000000000 (@ep200 214990396404146377 36028797018963968 3500000004581801 581816000000000000000 (ep201 qz69) ep211 rfl) (@ep212 794367533726843757 17592186044416000 943000000068581561 4545437500000000000000 (ep213 qz69) ep214 rfl) rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz60 qz63) (@HMul.hMul Real Real Real qz0 qz62 qz61) 5896683707410293 2251799813685248 7000000000509089 581816000000000000000 28962277687015719073 281474976710656000

noncomputable def ep217 := nat_lit 66877020408735828498215417994543104

noncomputable def ep218 := @Enclosure.Real.IsNear.mulLit_ff qz60 qz63 7000 4000 0 1 842383386772899 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff qz62 qz61 120704 4000 0 1 30712913772020911 9007199254740992 500000000654543 145454000000000000000

noncomputable def ep220 := @ep216 471500000617234049 4545437500000000000000 ep217 14849681575221002849 140737488355328000 8419000009939380909 72727000000000000000000 (@ep218 5896683707410293 2251799813685248 7000000000509089 581816000000000000000 (ep201 qz69) ep214 rfl) (@ep219 28962277687015719073 281474976710656000 471500000617234049 4545437500000000000000 (ep213 qz69) ep211 rfl) rfl

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq qz54 (Complex.mk qz65 qz64) Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 60352 1000 2 qz18 rfl)

noncomputable abbrev qz338 := (ep221 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 120704 4000) Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 120704 4000)))

noncomputable abbrev qz70 := qz338

noncomputable def ep222 := ep196 (@ep197 72727000000000000000000 (ep215 rfl) (ep220 rfl)) qz70 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz71 := qz322

noncomputable def ep223 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz71) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz71) (Complex.im ↑qz3)) 120447 131072 3 524288 0 1 0 1 120447 120447

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz71) (Complex.re ↑qz3) 1 2 0 1 120447 65536 3 262144 120447 131072 3 524288

noncomputable abbrev qz72 := (@Enclosure.Complex.IsNear.of_eq qz322 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz276) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz276 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz333 qz287))

noncomputable def ep225 := ep224 (@Enclosure.Complex.IsNear.re_isNear qz71 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz72) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 3 262144 (Complex.ofReal_re qz3) EMRow14.d4)

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz71) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep227 := ep226 (@Enclosure.Complex.IsNear.im_isNear qz71 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz72) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep228 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz71) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz71) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep229 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz71) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep230 := ep229 (@Enclosure.Complex.IsNear.re_isNear qz71 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz72) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz71) (Complex.re ↑qz3) 0 1 0 1 120447 65536 3 262144 0 1 0 1

noncomputable def ep232 := ep231 (@Enclosure.Complex.IsNear.im_isNear qz71 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz72) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 3 262144 (Complex.ofReal_re qz3) EMRow14.d4)

noncomputable def ep233 := @ep194 8419000009939380909 72727000000000000000000 (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz71 (↑qz3) Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 (@ep223 131072 3 524288 (ep225 rfl) (ep227 rfl) rfl rfl) (@ep228 1 0 1 (ep230 rfl) (ep232 rfl) rfl rfl))

noncomputable abbrev qz73 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz339 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz74 := (@HMul.hMul Complex Complex Complex qz314 (@HMul.hMul Complex Complex Complex qz314 (2 : Complex) qz339) (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 (2 : Complex) qz339) (1 : Complex)))

noncomputable abbrev qz340 := (@HPow.hPow Complex Int Complex qz479 qz475 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz75 := qz340

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz75)) Bool.false 879489 4294967296 3 4294967296

noncomputable def ep235 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz75) Bool.false 0 1 0 1 Bool.false

noncomputable def ep236 := @ep235 0 1 0 1 Bool.false 879489 4294967296 3 4294967296 Bool.true 92150903 33554432000 943 100663296000 Bool.false 879489 879489 4294967296 3 4294967296 Bool.true 92150903 92150903 33554432000 943

noncomputable def ep237 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz54 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep238 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz75 Bool.false 879489 4294967296 3 4294967296 Bool.true 92150903 33554432000 943 100663296000

noncomputable abbrev qz76 := (Complex.re qz340)

noncomputable abbrev qz77 := (Complex.im qz340)

noncomputable def ep239 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz76) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz77) 879489 4294967296 3 4294967296 0 1 0

noncomputable def ep240 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz76 1 12 0 1 2638467 1073741824 9 1073741824 879489

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz341 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz24)

noncomputable def ep242 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep241 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz341)

noncomputable def ep243 := @Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 2638467 1073741824 9 1073741824 Bool.true 276452709 8388608000 943 8388608000

noncomputable abbrev qz480 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz342 := (@HPow.hPow Complex Nat Complex qz480 qz475 1)

noncomputable abbrev qz78 := (@Inv.inv Complex Complex.instInv qz342)

noncomputable def ep244 := @Enclosure.Complex.IsNear.of_eq qz75 qz78 Bool.false 2638467 1073741824 9 1073741824 Bool.true 276452709 8388608000 943

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_parts qz78 Bool.false 2638467 1073741824 9 1073741824 Bool.true 276452709 8388608000 943

noncomputable abbrev qz79 := (Complex.re qz342)

noncomputable abbrev qz80 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz81 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz82 := qz342

noncomputable def ep246 := @Enclosure.Real.IsNear.mulLit_ff qz79 (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82)) 9000 4000 0 1 293163 268435456 1 268435456

noncomputable def ep247 := @Enclosure.Complex.IsNear.re_isNear qz82 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable def ep248 := @Enclosure.Complex.IsNear.of_eq qz82 qz54 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0

noncomputable def ep249 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82)) Bool.false 293163 268435456 1 268435456 293163 268435456 1

noncomputable abbrev qz83 := (Complex.im qz342)

noncomputable abbrev qz343 := (@instHAdd Real Real.instAdd)

noncomputable def ep250 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 qz79 qz79) (@HMul.hMul Real Real Real qz0 qz83 qz83)) Bool.false 228913369 250000 0 1

noncomputable def ep251 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz79 qz79) (@HMul.hMul Real Real Real qz0 qz83 qz83) 81 16 0 1 14227984 15625

noncomputable def ep252 := @Enclosure.Real.IsNear.mulLit_ff qz79 qz79 9000 4000 0 1 9000 4000 0 1

noncomputable def ep253 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz83 120704 4000 0 1 120704 4000 0 1

noncomputable def ep254 := @Enclosure.Complex.IsNear.im_isNear qz82 Bool.false 9000 4000 0 1 Bool.false 120704 4000 0 1

noncomputable abbrev qz84 := (ep247 (@ep248 1 (BSN.pow_one_c qz316) qz338))

noncomputable abbrev qz85 := (ep254 (@ep248 1 (BSN.pow_one_c qz316) qz338))

noncomputable def ep255 := @ep251 0 1 228913369 228913369 250000 0 1 (@ep252 81 16 0 1 qz84 qz84 rfl) (@ep253 14227984 15625 0 1 qz85 qz85 rfl)

noncomputable def ep256 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82) 228913369 250000 0 1 146581 146582 134217728 (ep250 (Enclosure.Complex.normSq_eq_mul_add_mul qz82) (ep255 rfl rfl)) rfl

noncomputable def ep257 := @Enclosure.Real.IsNear.of_eq (Complex.re qz78) (@HMul.hMul Real Real Real qz0 qz79 (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82))) Bool.false 2638467 1073741824 9 1073741824 (Enclosure.Complex.inv_re_eq_mul qz82) (@ep246 2638467 1073741824 9 1073741824 qz84 (@ep249 268435456 (ep256 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep258 := @Enclosure.Real.IsNear.of_eq (Complex.im qz78) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz83) (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82))) Bool.true 276452709 8388608000 943 8388608000 (Enclosure.Complex.inv_im_eq_mul qz82)

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz83) (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz82)) 120704 4000 0 1 293163 268435456 1

noncomputable def ep260 := @ep259 268435456 276452709 8388608000 943 8388608000 (@Enclosure.Real.IsNear.neg qz83 Bool.false 120704 4000 0 1 qz85) (@ep249 268435456 (ep256 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep261 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz77 0 1 0 1 276452709 8388608000 943 8388608000 0

noncomputable def ep262 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep241 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz341)

noncomputable def ep263 := @Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 2638467 1073741824 9 1073741824 Bool.true 276452709 8388608000 943 8388608000

noncomputable abbrev qz86 := (@ep244 8388608000 (BSN.zpow_one_sub_two_mul qz316 1 1 rfl rfl) (@ep245 8388608000 ep257 (ep258 ep260)))

noncomputable def ep264 := @ep239 1 879489 879489 4294967296 3 4294967296 (@ep240 4294967296 3 4294967296 ep242 (ep243 qz86) rfl) (@ep261 1 0 1 ep262 (ep263 qz86) rfl) rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz77) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz76) 92150903 33554432000 943 100663296000 0 1 0

noncomputable def ep266 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz77 1 12 0 1 276452709 8388608000 943 8388608000 92150903

noncomputable def ep267 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz76 0 1 0 1 2638467 1073741824 9 1073741824 0

noncomputable def ep268 := @ep265 1 92150903 92150903 33554432000 943 100663296000 (@ep266 33554432000 943 100663296000 ep242 (ep263 qz86) rfl) (@ep267 1 0 1 ep262 (ep243 qz86) rfl) rfl

noncomputable abbrev qz87 := (@Enclosure.Complex.IsNear.mk qz276 qz276 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz287 qz287)

noncomputable def ep269 := @ep236 100663296000 (@ep237 0 1 0 1 (BSN.stirling_sum_base qz54) qz87) (ep238 (ep264 rfl) (ep268 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep270 := @ep191 10602400617709568609 140737488355328000 25865260973679530105573 ep178 (ep233 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep234 Bool.true 92150903 33554432000 943 100663296000 (BSN.stirling_sum_succ qz54 0 1 rfl) (ep269 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 30691958626583727 4503599627370496 500000000654543 72727000000000000000 Bool.false 870295305487779 281474976710656

noncomputable abbrev qz88 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz317 qz339))

noncomputable def ep272 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz88) Bool.false 30691958626583727 4503599627370496 500000000654543 72727000000000000000 Bool.false 870295305487779 281474976710656 1000000000072727 72727000000000000000

noncomputable def ep273 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz88 Bool.false 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000 Bool.false

noncomputable def ep274 := nat_lit 552897173735812612419138374074368

noncomputable def ep275 := nat_lit 979865403374263371740108292096

noncomputable abbrev qz89 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz317 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep276 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz89) Bool.false 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep277 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz89 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz344 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz64))

noncomputable def ep278 := @Enclosure.Complex.IsNear.of_eq qz89 qz344 Bool.false 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep279 := nat_lit 68105894979878015064403015378539144402432005356431442138364854372822784161597850910720

noncomputable def ep280 := nat_lit 1871592755267475423265824118880388963416370740797488330739904986419950491590589415424

noncomputable def ep281 := nat_lit 287682604574346103404375002279557290027675582567839773770070896710461218178990080

noncomputable def ep282 := BSN.log_dyadic_bound 6378455616 22762455616 5 4 ep279 524288 145454 ep280 ep281 301904 29140911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6378455616) (BSN.artanhQ 22762455616) 0 4 ep280 ep279 ep281 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep283 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log (Enclosure.sfrac Bool.false 14570455616 16000000)) 1 2 0 1 30688252069807279 4503599627370496 500000000654543 72727000000000000000 30688252069807279 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 14570455616 16000000 30688252069807279 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14570455616) qz334)) Bool.false 128715858409400949538816 18889465931478580854784 1000000001309086 145454000000000000000 30688252069807279 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 14570455616 16000000 9 29140911232 16384000000 301904 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep282 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep284 := BSN.arctan_dyadic_bound_f 1000 120704 1 0 524288 145454 0 1 1 0 1 1 4343 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 120704)

noncomputable def ep285 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz346)) 884279719003555 562949953421312 1 2000000000000000 4343 524288 1 145454 461172353669227085824 879616458261923 562949953421312 1000000000072727 145454000000000000000 qz68 (ep284 rfl) rfl rfl

noncomputable abbrev qz90 := (@HAdd.hAdd Complex Complex Complex qz271 qz317 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz347 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz64)

noncomputable def ep286 := @ep277 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000 Bool.false 30688252069807279 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 879616458261923 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz87) (ep278 (@congrArg Complex Complex qz90 qz347 Complex.log (BSN.w_shift_mk qz17 Bool.false 60352 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz344 Bool.false 30688252069807279 9007199254740992 500000000654543 145454000000000000000 Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz344) (@HMul.hMul Real Real Real qz0 qz66 (Real.log (Enclosure.sfrac Bool.false 14570455616 16000000))) Bool.false 30688252069807279 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 1000 120704 4000 14570455616 16000000 rfl rfl rfl) (ep283 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz344) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz345)) Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 1000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz345)) (@HSub.hSub Real Real Real qz318 qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz346))) Bool.false 879616458261923 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 120704 1000 rfl rfl) ep285)))) rfl rfl

noncomputable abbrev qz348 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz64))

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq qz88 qz348 Bool.false 30695665183360175 9007199254740992 500000000654543 145454000000000000000 Bool.false 860974152713635 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep288 := nat_lit 392276473409012625558062422815557042818804989264704953887820473923343489723483654523275618284743182275051520

noncomputable def ep289 := nat_lit 10841480305122574446553025541255073229970821375218859938758008473094015947987657044577948863575689059631104

noncomputable def ep290 := nat_lit 109369839111884161812020329567206507428797497981438518864218454903244857508877457351962903208861368320

noncomputable def ep291 := BSN.log_dyadic_bound 6402455616 22786455616 6 5 ep288 524288 145454 ep289 ep290 302767 29188911232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 6402455616) (BSN.artanhQ 22786455616) 0 5 ep289 ep288 ep290 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log (Enclosure.sfrac Bool.false 14594455616 16000000)) 1 2 0 1 30695665183360175 4503599627370496 500000000654543 72727000000000000000 30695665183360175 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 14594455616 16000000 30695665183360175 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14594455616) qz334)) Bool.false 128746951261228315443200 18889465931478580854784 1000000001309086 145454000000000000000 30695665183360175 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 14594455616 16000000 9 29188911232 16384000000 302767 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep291 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep293 := BSN.arctan_dyadic_bound_f 5000 120704 1 0 524288 145454 0 1 1 0 1 1 21705 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 120704) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 120704) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep294 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz346)) 884279719003555 562949953421312 1 2000000000000000 21705 524288 1 145454 451398416577926266880 860974152713635 562949953421312 1000000000072727 145454000000000000000 qz68 (ep293 rfl) rfl rfl

noncomputable abbrev qz91 := (@HAdd.hAdd Complex Complex Complex qz271 qz317 qz339)

noncomputable abbrev qz350 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz64)

noncomputable def ep295 := @ep273 30695665183360175 9007199254740992 500000000654543 145454000000000000000 Bool.false 860974152713635 562949953421312 1000000000072727 145454000000000000000 Bool.false ep274 30691958626583727 4503599627370496 500000000654543 72727000000000000000 Bool.false ep275 870295305487779 281474976710656 1000000000072727 72727000000000000000 (ep276 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep286 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep287 (@congrArg Complex Complex qz91 qz350 Complex.log (BSN.w_shift_mk qz17 Bool.false 60352 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz348 Bool.false 30695665183360175 9007199254740992 500000000654543 145454000000000000000 Bool.false 860974152713635 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz348) (@HMul.hMul Real Real Real qz0 qz66 (Real.log (Enclosure.sfrac Bool.false 14594455616 16000000))) Bool.false 30695665183360175 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 5000 120704 4000 14594455616 16000000 rfl rfl rfl) (ep292 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz348) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz349)) Bool.false 860974152713635 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 5000 120704 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz346 qz349)) (@HSub.hSub Real Real Real qz318 qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz346))) Bool.false 860974152713635 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 120704 5000 rfl rfl) ep294)))) rfl rfl

noncomputable def ep296 := @ep184 ep178 Bool.false 30691958626583727 4503599627370496 500000000654543 72727000000000000000 Bool.false 870295305487779 281474976710656 1000000000072727 72727000000000000000 Bool.true ep185 213169897253452887667 4503599627370496000 269380780582549917014909 ep182 Bool.false ep186 10167252964965679109 140737488355328000 28937260973902947449573 ep178 (@ep187 4503599627370496000 261188780571825884502909 ep182 Bool.false 10602400617709568609 140737488355328000 25865260973679530105573 ep178 (BSN.logGammaStirling_unfold 1 qz54) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep271 1000000000072727 72727000000000000000 (BSN.log_sum_c_eq qz17 2) (ep272 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep295 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz92 := (@HDiv.hDiv Real Real Real qz268 qz278 (2 : Real))

noncomputable def ep297 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log Real.pi) 60352 2000 0 1 75021 65536 1 131072 70744803 2048000 943 4096000 (@Enclosure.Real.IsNear.of_eq qz92 (Enclosure.sfrac Bool.false 60352 2000) Bool.false 60352 2000 0 1 (BSN.t_half_eq qz17 Bool.false 60352 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 60352 2000)) EMRow14.d5 rfl

noncomputable def ep298 := @ep180 943 4096000 ep181 5305707121014276101 140737488355328000 80373431723902947449573 ep178 (@ep183 28937260973902947449573 ep178 (ep296 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep297 rfl rfl

noncomputable def ep299 := BSN.cos_dyadic_bound_f 219238 1073741824 1 0 524288 145597 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 219238) qz280 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 219238) qz281 0 0 rfl) rfl rfl

noncomputable def ep300 := @ep177 524288 Bool.false 524287 524288 1 72727 (@ep179 19765299 524288 189 524288 ep298 rfl) (Enclosure.sfrac_false_div 19765299 524288) (BSN.cos_reduce0 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15427533272166432768) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 19765299 524288 226375608064910080 72057594037927936 6 15427533272166432768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 15427533272166432768 75557863725914323419136 219238 1073741824 145597 145454 (ep299 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep301 := nat_lit 10724527456655924136838289

noncomputable def ep302 := nat_lit 2275614388542752356827136000

noncomputable abbrev qz93 := qz272

noncomputable abbrev qz94 := qz273

noncomputable abbrev qz481 := (@Nat.cast Complex Complex.instNatCast 16)

noncomputable abbrev qz351 := (@HPow.hPow Complex Complex Complex qz468 qz481 qz469)

noncomputable abbrev qz95 := qz351

noncomputable abbrev qz352 := qz481

noncomputable abbrev qz96 := (@HAdd.hAdd Complex Complex Complex qz271 (@HDiv.hDiv Complex Complex Complex qz323 qz352 (@HSub.hSub Complex Complex Complex qz315 qz270 (1 : Complex))) qz322)

noncomputable abbrev qz97 := (@instHSub Nat instSubNat)

noncomputable abbrev qz353 := qz480

noncomputable abbrev qz98 := qz353

noncomputable abbrev qz99 := qz352

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 16) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz94) (@HMul.hMul Complex Complex Complex qz44 qz95 (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) Bool.false 562674045098856126781271 1001274085736632549376000 ep174

noncomputable def ep304 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz94) (@HMul.hMul Complex Complex Complex qz44 qz95 (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) Bool.false 180246412039 274877906944 91950463647527 19991045538316288

noncomputable def ep305 := nat_lit 154666663808487433698226476180045824

noncomputable def ep306 := nat_lit 65376330205832331388596263059456

noncomputable def ep307 := @ep304 Bool.true 18832468831 274877906944 91876397307095 19991045538316288 Bool.true 93894041540518263474729 1001274085736632549376000 293481476977750501135557 ep175 Bool.false 1309703528937485735349 15644907589634883584000 266082385398036485310789 ep302 Bool.false ep305 562674045098856126781271 1001274085736632549376000 ep174 ep175 Bool.false ep306 237837703774247825599 15644907589634883584000

noncomputable def ep308 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz94) (BSN.headSumC qz6 16) Bool.false 180246412039 274877906944 91950463647527 19991045538316288 Bool.true 18832468831 274877906944 91876397307095

noncomputable abbrev qz100 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 15) qz273)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 16) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 15) qz100) Bool.false 180246412039 274877906944 91950463647527 19991045538316288 Bool.true 18832468831 274877906944 91876397307095 19991045538316288

noncomputable def ep310 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 15) qz100 Bool.false 54731608723 137438953472 43774477531433 9995522769158144 Bool.true 6820969289 137438953472 43755063931507 9995522769158144 Bool.false

noncomputable abbrev qz101 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 14) qz273)

noncomputable def ep311 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 14) qz101) Bool.false 54731608723 137438953472 43774477531433 9995522769158144 Bool.true 6820969289 137438953472 43755063931507 9995522769158144

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 14) qz101 Bool.false 38063131925 68719476736 10376269658781 2498880692289536 Bool.false 46073848355 274877906944 82962544721523 19991045538316288 Bool.true

noncomputable abbrev qz102 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 13) qz273)

noncomputable def ep313 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz102) Bool.false 38063131925 68719476736 10376269658781 2498880692289536 Bool.false 46073848355 274877906944 82962544721523 19991045538316288

noncomputable def ep314 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz102 Bool.false 6309445037 8589934592 1223244482669 312360086536192 Bool.true 11779372105 274877906944 78235931375659 19991045538316288 Bool.true

noncomputable abbrev qz103 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 12) qz273)

noncomputable def ep315 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz103) Bool.false 6309445037 8589934592 1223244482669 312360086536192 Bool.true 11779372105 274877906944 78235931375659 19991045538316288

noncomputable def ep316 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz103 Bool.false 74099840455 137438953472 36691668779657 9995522769158144 Bool.true 70196151031 274877906944 73329356743561 19991045538316288 Bool.false

noncomputable abbrev qz104 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 11) qz273)

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz104) Bool.false 74099840455 137438953472 36691668779657 9995522769158144 Bool.true 70196151031 274877906944 73329356743561 19991045538316288

noncomputable def ep318 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz104 Bool.false 67045241969 274877906944 68250567303981 19991045538316288 Bool.true 53378126221 274877906944 68226185577231 19991045538316288 Bool.false

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 10) qz273)

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz105) Bool.false 67045241969 274877906944 68250567303981 19991045538316288 Bool.true 53378126221 274877906944 68226185577231 19991045538316288

noncomputable def ep320 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz105 Bool.false 2583482789 274877906944 62866087334821 19991045538316288 Bool.false 4935622769 274877906944 62844402470685 19991045538316288 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 9) qz273)

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz106) Bool.false 2583482789 274877906944 62866087334821 19991045538316288 Bool.false 4935622769 274877906944 62844402470685 19991045538316288

noncomputable def ep322 := @Enclosure.Complex.IsNear.addLitP qz4 qz106 Bool.true 34900714709 137438953472 28601375580389 9995522769158144 Bool.false 15277904063 68719476736 28593905790219 9995522769158144 Bool.false

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz107 := (@Inv.inv Real Real.instInv (Real.sqrt qz354))

noncomputable abbrev qz108 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep323 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz108)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108)))) Bool.false 72384912207 274877906944 5663336174043 19991045538316288 Bool.true 56175993483 274877906944 5656590890247 19991045538316288 (BSN.cpow_neg_s_mk qz17 60352 1000 9 qz18 rfl)

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep324 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz354) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz354) (Real.sqrt qz355) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz355) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep325 := BSN.log_dyadic_bound 1 17 2 1 867 262144 72727 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz109 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep326 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz109 60352 1000 0 1 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 9331378978962347403 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 20752195215788806766592 9444732965739290427392 1000000000218181 72727000000000000000 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep327 := nat_lit 252185709835655694452763417518410000

noncomputable def ep328 := BSN.cos_dyadic_bound_f 708647270 1073741824 2 1 524288 145597 ep327 ep75 ep327 ep327 ep76 ep327 414189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 708647270) qz280 0 1 ep327 ep75 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 708647270) qz281 0 1 ep327 ep76 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 69524191) qz20)

noncomputable def ep329 := @Enclosure.Real.IsNear.cos_image qz108 qz356 Bool.false 69524191 524288 109 131072 Bool.false 414189 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 9331378978962347403 70368744177664000 943000000205744683 1136359375000000000000 69524191 524288 109 131072 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 69524191 524288) (BSN.cos_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49866618491337747464192) qz23) 226375608064910080 72057594037927936 Bool.false 414189 524288 21 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 69524191 524288 226375608064910080 72057594037927936 21 49866618491337747464192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 414189 524288 49866618491337747464192 75557863725914323419136 708647270 1073741824 145597 145454 (ep328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep330 := BSN.sin_dyadic_bound_f 708647270 1073741824 2 1 524288 145597 ep327 ep79 ep327 ep327 ep80 ep327 321441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 708647270) qz284 0 1 ep327 ep79 ep327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 708647270) qz285 0 1 ep327 ep80 ep327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.sin_image qz108 qz356 Bool.false 69524191 524288 109 131072 Bool.false 321441 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz108 Bool.false 9331378978962347403 70368744177664000 943000000205744683 1136359375000000000000 69524191 524288 109 131072 (ep326 rfl) rfl) (Enclosure.sfrac_false_div 69524191 524288) (BSN.sin_reduce0 qz356 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 49866618491337747464192) qz23) 226375608064910080 72057594037927936 Bool.false 321441 524288 21 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 69524191 524288 226375608064910080 72057594037927936 21 49866618491337747464192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 321441 524288 49866618491337747464192 75557863725914323419136 708647270 1073741824 145597 145454 (ep330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz357 := (@Enclosure.Real.IsNear.recentre' qz107 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep324 rfl rfl) rfl)

noncomputable def ep332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz108)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108))) Bool.false 72384912207 274877906944 5663336174043 19991045538316288 Bool.true 56175993483 274877906944 5656590890247 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz107 (Real.cos qz108) 174763 524288 1 524288 414189 524288 8058315 9532473344 72384912207 274877906944 5663336174043 19991045538316288 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz108) Bool.false 414189 524288 8058315 9532473344 414189 524288 8058315 9532473344 (ep329 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz107 (@Neg.neg Real Real.instNeg (Real.sin qz108)) 174763 524288 1 524288 321441 524288 8058315 9532473344 56175993483 274877906944 5656590890247 19991045538316288 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz108) Bool.false 321441 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz108) Bool.false 321441 524288 8058315 9532473344 321441 524288 8058315 9532473344 (ep331 rfl rfl) rfl)) rfl)

noncomputable def ep333 := @ep322 72384912207 274877906944 5663336174043 19991045538316288 Bool.true 56175993483 274877906944 5656590890247 19991045538316288 Bool.false 355071170833083793408 2583482789 274877906944 62866087334821 19991045538316288 Bool.false 339173414051967401984 4935622769 274877906944 62844402470685 19991045538316288 EMRow14.d6 (ep323 ep332) rfl rfl

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz110 := (@Inv.inv Real Real.instInv (Real.sqrt qz358))

noncomputable abbrev qz111 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep334 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)))) Bool.false 16115439795 68719476736 673059996145 2498880692289536 Bool.true 29156874495 137438953472 2690891553273 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 10 qz18 rfl)

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep335 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz358) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz358) (Real.sqrt qz359) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz359) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep336 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 72727 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz112 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz112 60352 1000 0 1 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 9778823809956648331 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 21747274560655572598784 9444732965739290427392 1000000000218181 72727000000000000000 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep338 := nat_lit 868156008994851206282035398701239835890174306168629011939333372254943478016

noncomputable def ep339 := nat_lit 151086914789872009495742710266137251687502679005695594677075879375175936

noncomputable def ep340 := nat_lit 2604165853154973874827114710683187233167147913147875644628645965006080082176

noncomputable def ep341 := BSN.cos_dyadic_bound_f 789593122 1073741824 3 2 524288 145597 ep338 ep57 ep339 ep340 ep60 ep339 388804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 789593122) qz280 0 2 ep338 ep57 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 789593122) qz281 0 2 ep340 ep60 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 36428957) qz43)

noncomputable def ep342 := @Enclosure.Real.IsNear.cos_image qz111 qz360 Bool.false 36428957 262144 437 524288 Bool.false 388804 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 9778823809956648331 70368744177664000 943000000205744683 1136359375000000000000 36428957 262144 437 524288 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 36428957 262144) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27781338212300954271744) qz312) 226375608064910080 72057594037927936 Bool.false 388804 524288 22 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 36428957 262144 226375608064910080 72057594037927936 22 27781338212300954271744 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 388804 524288 27781338212300954271744 37778931862957161709568 789593122 1073741824 145597 145454 (ep341 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep343 := nat_lit 388699002815638838237197217996989456

noncomputable def ep344 := BSN.sin_dyadic_bound_f 789593122 1073741824 2 1 524288 145597 ep343 ep79 ep343 ep343 ep80 ep343 351722 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 789593122) qz284 0 1 ep343 ep79 ep343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 789593122) qz285 0 1 ep343 ep80 ep343 rfl rfl rfl rfl) rfl rfl

noncomputable def ep345 := @Enclosure.Real.IsNear.sin_image qz111 qz360 Bool.false 36428957 262144 437 524288 Bool.false 351722 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz111 Bool.false 9778823809956648331 70368744177664000 943000000205744683 1136359375000000000000 36428957 262144 437 524288 (ep337 rfl) rfl) (Enclosure.sfrac_false_div 36428957 262144) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27781338212300954271744) qz312) 226375608064910080 72057594037927936 Bool.false 351722 524288 22 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 36428957 262144 226375608064910080 72057594037927936 22 27781338212300954271744 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 351722 524288 27781338212300954271744 37778931862957161709568 789593122 1073741824 145597 145454 (ep344 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep335 rfl rfl) rfl)

noncomputable def ep346 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz111)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111))) Bool.false 16115439795 68719476736 673059996145 2498880692289536 Bool.true 29156874495 137438953472 2690891553273 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz111) 165795 524288 1 524288 97201 131072 32305987 38129893376 16115439795 68719476736 673059996145 2498880692289536 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz111) Bool.false 388804 524288 32305987 38129893376 97201 131072 32305987 38129893376 (ep342 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz110 (@Neg.neg Real Real.instNeg (Real.sin qz111)) 165795 524288 1 524288 175861 262144 32305987 38129893376 29156874495 137438953472 2690891553273 9995522769158144 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz111) Bool.false 175861 262144 32305987 38129893376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz111) Bool.false 351722 524288 32305987 38129893376 175861 262144 32305987 38129893376 (ep345 rfl rfl) rfl)) rfl)

noncomputable def ep347 := @ep320 16115439795 68719476736 673059996145 2498880692289536 Bool.true 29156874495 137438953472 2690891553273 9995522769158144 Bool.false 4607313945748186333184 67045241969 274877906944 68250567303981 19991045538316288 Bool.true 7336233806110562189312 53378126221 274877906944 68226185577231 19991045538316288 (ep321 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep334 ep346) rfl rfl

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz113 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz114 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep348 := @Enclosure.Complex.IsNear.of_eq qz104 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)))) Bool.false 81154438941 274877906944 5132770255333 19991045538316288 Bool.true 8409012405 137438953472 2551585583165 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 11 qz18 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep349 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep350 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 72727 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz115 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep351 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz115 60352 1000 0 1 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 10183596216719840651 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 22647454054174387339264 9444732965739290427392 1000000000218181 72727000000000000000 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep350 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep352 := nat_lit 2317624114800574694891615555301841

noncomputable def ep353 := BSN.cos_dyadic_bound_f 219412189 1073741824 2 1 524288 145597 ep352 ep75 ep352 ep352 ep76 ep352 513379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 219412189) qz280 0 1 ep352 ep75 ep352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 219412189) qz281 0 1 ep352 ep76 ep352 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9484213) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep354 := @Enclosure.Real.IsNear.cos_image qz114 qz364 Bool.false 9484213 65536 109 131072 Bool.false 513379 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 10183596216719840651 70368744177664000 943000000205744683 1136359375000000000000 9484213 65536 109 131072 (ep351 rfl) rfl) (Enclosure.sfrac_false_div 9484213 65536) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1929970033418123083776) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 513379 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 9484213 65536 226375608064910080 72057594037927936 23 1929970033418123083776 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 513379 524288 1929970033418123083776 9444732965739290427392 219412189 1073741824 145597 145454 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep355 := BSN.sin_dyadic_bound_f 219412189 1073741824 2 1 524288 145597 ep352 ep79 ep352 ep352 ep80 ep352 106390 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 219412189) qz284 0 1 ep352 ep79 ep352 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 219412189) qz285 0 1 ep352 ep80 ep352 rfl rfl rfl rfl) rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.sin_image qz114 qz364 Bool.false 9484213 65536 109 131072 Bool.false 106390 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz114 Bool.false 10183596216719840651 70368744177664000 943000000205744683 1136359375000000000000 9484213 65536 109 131072 (ep351 rfl) rfl) (Enclosure.sfrac_false_div 9484213 65536) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1929970033418123083776) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 106390 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 9484213 65536 226375608064910080 72057594037927936 23 1929970033418123083776 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 106390 524288 1929970033418123083776 9444732965739290427392 219412189 1073741824 145597 145454 (ep355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep349 rfl rfl) rfl)

noncomputable def ep357 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz114)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114))) Bool.false 81154438941 274877906944 5132770255333 19991045538316288 Bool.true 8409012405 137438953472 2551585583165 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz114) 158079 524288 1 524288 513379 524288 8058315 9532473344 81154438941 274877906944 5132770255333 19991045538316288 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz114) Bool.false 513379 524288 8058315 9532473344 513379 524288 8058315 9532473344 (ep354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz114)) 158079 524288 1 524288 53195 262144 8058315 9532473344 8409012405 137438953472 2551585583165 9995522769158144 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz114) Bool.false 53195 262144 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz114) Bool.false 106390 524288 8058315 9532473344 53195 262144 8058315 9532473344 (ep356 rfl rfl) rfl)) rfl)

noncomputable def ep358 := @ep318 81154438941 274877906944 5132770255333 19991045538316288 Bool.true 8409012405 137438953472 2551585583165 9995522769158144 Bool.false 40736818098309473239040 74099840455 137438953472 36691668779657 9995522769158144 Bool.true 9647685535463093829632 70196151031 274877906944 73329356743561 19991045538316288 (ep319 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep347 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep348 ep357) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz116 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz117 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq qz103 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)))) Bool.false 26851280137 137438953472 2452154665751 9995522769158144 Bool.false 29208389463 137438953472 2453287316049 9995522769158144 (BSN.cpow_neg_s_mk qz17 60352 1000 12 qz18 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep360 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep361 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 72727 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz118 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz118 60352 1000 0 1 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 10553132282289919371 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 23469270914176955449344 9444732965739290427392 1000000000218181 72727000000000000000 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep363 := nat_lit 405916734838264780454689979919102736

noncomputable def ep364 := BSN.sin_dyadic_bound_f 798195434 1073741824 2 1 524288 145597 ep363 ep79 ep363 ep363 ep80 ep363 354826 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 798195434) qz284 0 1 ep363 ep79 ep363 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 798195434) qz285 0 1 ep363 ep80 ep363 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39313481) qz43)

noncomputable def ep365 := @Enclosure.Real.IsNear.cos_image qz117 qz368 Bool.false 39313481 262144 109 131072 Bool.false 354826 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 10553132282289919371 70368744177664000 943000000205744683 1136359375000000000000 39313481 262144 109 131072 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 39313481 262144) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28084005177646521516032) qz312) 226375608064910080 72057594037927936 Bool.false 354826 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 39313481 262144 226375608064910080 72057594037927936 23 28084005177646521516032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354826 524288 28084005177646521516032 37778931862957161709568 798195434 1073741824 145597 145454 (ep364 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep366 := nat_lit 906618660075389795340488945137324370691705232282533045343201806712247378176

noncomputable def ep367 := nat_lit 164768395621758160521477425413325125792093571419710209306114927322685696

noncomputable def ep368 := nat_lit 2719526443434925869700423880561146461823531509704759715610993190282096763136

noncomputable def ep369 := BSN.cos_dyadic_bound_f 798195434 1073741824 3 2 524288 145597 ep366 ep57 ep367 ep368 ep60 ep367 385974 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 798195434) qz280 0 2 ep366 ep57 ep367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 798195434) qz281 0 2 ep368 ep60 ep367 rfl rfl rfl rfl) rfl rfl

noncomputable def ep370 := @Enclosure.Real.IsNear.sin_image qz117 qz368 Bool.false 39313481 262144 109 131072 Bool.true 385974 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz117 Bool.false 10553132282289919371 70368744177664000 943000000205744683 1136359375000000000000 39313481 262144 109 131072 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 39313481 262144) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 28084005177646521516032) qz312) 226375608064910080 72057594037927936 Bool.false 385974 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 39313481 262144 226375608064910080 72057594037927936 23 28084005177646521516032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 385974 524288 28084005177646521516032 37778931862957161709568 798195434 1073741824 145597 145454 (ep369 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep360 rfl rfl) rfl)

noncomputable def ep371 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz117)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117))) Bool.false 26851280137 137438953472 2452154665751 9995522769158144 Bool.false 29208389463 137438953472 2453287316049 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz117) 151349 524288 1 524288 177413 262144 8058315 9532473344 26851280137 137438953472 2452154665751 9995522769158144 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz117) Bool.false 354826 524288 8058315 9532473344 177413 262144 8058315 9532473344 (ep365 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz116 (@Neg.neg Real Real.instNeg (Real.sin qz117)) 151349 524288 1 524288 192987 262144 8058315 9532473344 29208389463 137438953472 2453287316049 9995522769158144 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz117) Bool.true 192987 262144 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz117) Bool.true 385974 524288 8058315 9532473344 192987 262144 8058315 9532473344 (ep370 rfl rfl) rfl)) rfl)

noncomputable def ep372 := @ep316 26851280137 137438953472 2452154665751 9995522769158144 Bool.false 29208389463 137438953472 2453287316049 9995522769158144 Bool.false 13874616365990149095424 6309445037 8589934592 1223244482669 312360086536192 Bool.true 1618944574668469698560 11779372105 274877906944 78235931375659 19991045538316288 (ep317 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep359 ep371) rfl rfl

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (Real.sqrt qz370))

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep373 := @Enclosure.Complex.IsNear.of_eq qz102 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)))) Bool.true 12412428371 68719476736 590313797429 2498880692289536 Bool.false 14463305115 68719476736 590826668233 2498880692289536 (BSN.cpow_neg_s_mk qz17 60352 1000 13 qz18 rfl)

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep374 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz370) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz370) (Real.sqrt qz371) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz371) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep375 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 72727 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz121 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz121 60352 1000 0 1 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 2178610724128228431 14073748835532800 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 24225227133228857425920 9444732965739290427392 1000000000218181 72727000000000000000 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep375 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep377 := nat_lit 1636040018067444564310505839847158591281158411008745399132671487691122941761

noncomputable def ep378 := nat_lit 536395959461515798924103836036269209939554823375013636225541548070018881

noncomputable def ep379 := nat_lit 4907047262283410661333669311869403235423596123379486170125563379977228787521

noncomputable def ep380 := BSN.cos_dyadic_bound_f 925093623 1073741824 3 2 524288 145597 ep377 ep57 ep378 ep379 ep60 ep378 341444 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 925093623) qz280 0 2 ep377 ep57 ep378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 925093623) qz281 0 2 ep379 ep60 ep378 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 81159573) qz20)

noncomputable def ep381 := @Enclosure.Real.IsNear.cos_image qz120 qz372 Bool.false 81159573 524288 437 524288 Bool.true 341444 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 2178610724128228431 14073748835532800 943000000205744683 1136359375000000000000 81159573 524288 437 524288 (ep376 rfl) rfl) (Enclosure.sfrac_false_div 81159573 524288) (BSN.cos_reduce2 qz372 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65097676539867730804736) qz23) 226375608064910080 72057594037927936 Bool.false 341444 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 81159573 524288 226375608064910080 72057594037927936 24 65097676539867730804736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 341444 524288 65097676539867730804736 75557863725914323419136 925093623 1073741824 145597 145454 (ep380 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep382 := nat_lit 732390578490408899473583170094644641

noncomputable def ep383 := BSN.sin_dyadic_bound_f 925093623 1073741824 2 1 524288 145597 ep382 ep79 ep382 ep382 ep80 ep382 397860 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 925093623) qz284 0 1 ep382 ep79 ep382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 925093623) qz285 0 1 ep382 ep80 ep382 rfl rfl rfl rfl) rfl rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.sin_image qz120 qz372 Bool.false 81159573 524288 437 524288 Bool.true 397860 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 2178610724128228431 14073748835532800 943000000205744683 1136359375000000000000 81159573 524288 437 524288 (ep376 rfl) rfl) (Enclosure.sfrac_false_div 81159573 524288) (BSN.sin_reduce2 qz372 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65097676539867730804736) qz23) 226375608064910080 72057594037927936 Bool.false 397860 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 81159573 524288 226375608064910080 72057594037927936 24 65097676539867730804736 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 397860 524288 65097676539867730804736 75557863725914323419136 925093623 1073741824 145597 145454 (ep383 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep374 rfl rfl) rfl)

noncomputable def ep385 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120))) Bool.true 12412428371 68719476736 590313797429 2498880692289536 Bool.false 14463305115 68719476736 590826668233 2498880692289536 (@Enclosure.Real.IsNear.mulLit_ft qz119 (Real.cos qz120) 145411 524288 1 524288 85361 131072 32305987 38129893376 12412428371 68719476736 590313797429 2498880692289536 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz120) Bool.true 341444 524288 32305987 38129893376 85361 131072 32305987 38129893376 (ep381 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)) 145411 524288 1 524288 99465 131072 32305987 38129893376 14463305115 68719476736 590826668233 2498880692289536 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz120) Bool.true 99465 131072 32305987 38129893376 (@Enclosure.Real.IsNear.recentre' (Real.sin qz120) Bool.true 397860 524288 32305987 38129893376 99465 131072 32305987 38129893376 (ep384 rfl rfl) rfl)) rfl)

noncomputable def ep386 := @ep314 12412428371 68719476736 590313797429 2498880692289536 Bool.false 14463305115 68719476736 590826668233 2498880692289536 Bool.false 326959813602417049600 38063131925 68719476736 10376269658781 2498880692289536 Bool.false 3166170750169414369280 46073848355 274877906944 82962544721523 19991045538316288 (ep315 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep372 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep373 ep385) rfl rfl

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz122 := (@Inv.inv Real Real.instInv (Real.sqrt qz374))

noncomputable abbrev qz123 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq qz101 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)))) Bool.true 21394655127 137438953472 2269398896309 9995522769158144 Bool.true 59715786933 274877906944 4547583141491 19991045538316288 (BSN.cpow_neg_s_mk qz17 60352 1000 14 qz18 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14) qz19)

noncomputable def ep388 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz374) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz374) (Real.sqrt qz375) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep389 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 72727 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz124 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep390 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz124 60352 1000 0 1 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 11207783000116368779 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 24925158572916270432256 9444732965739290427392 1000000000218181 72727000000000000000 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep389 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep391 := nat_lit 198632816315106775153115062500000000

noncomputable def ep392 := BSN.sin_dyadic_bound_f 667594500 1073741824 2 1 524288 145597 ep391 ep79 ep391 ep391 ep80 ep391 305374 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 667594500) qz284 0 1 ep391 ep79 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 667594500) qz285 0 1 ep391 ep80 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 41752245) qz43)

noncomputable def ep393 := @Enclosure.Real.IsNear.cos_image qz123 qz376 Bool.false 41752245 262144 109 131072 Bool.true 305374 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 11207783000116368779 70368744177664000 943000000205744683 1136359375000000000000 41752245 262144 109 131072 (ep390 rfl) rfl) (Enclosure.sfrac_false_div 41752245 262144) (BSN.cos_reduce1 qz376 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23488893306866363269120) qz312) 226375608064910080 72057594037927936 Bool.false 305374 524288 25 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 41752245 262144 226375608064910080 72057594037927936 25 23488893306866363269120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 305374 524288 23488893306866363269120 37778931862957161709568 667594500 1073741824 145597 145454 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep394 := BSN.cos_dyadic_bound_f 667594500 1073741824 2 1 524288 145597 ep391 ep75 ep391 ep391 ep76 ep391 426173 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 667594500) qz280 0 1 ep391 ep75 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 667594500) qz281 0 1 ep391 ep76 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable def ep395 := @Enclosure.Real.IsNear.sin_image qz123 qz376 Bool.false 41752245 262144 109 131072 Bool.false 426173 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 11207783000116368779 70368744177664000 943000000205744683 1136359375000000000000 41752245 262144 109 131072 (ep390 rfl) rfl) (Enclosure.sfrac_false_div 41752245 262144) (BSN.sin_reduce1 qz376 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23488893306866363269120) qz312) 226375608064910080 72057594037927936 Bool.false 426173 524288 25 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q1 41752245 262144 226375608064910080 72057594037927936 25 23488893306866363269120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 426173 524288 23488893306866363269120 37778931862957161709568 667594500 1073741824 145597 145454 (ep394 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz377 := (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep388 rfl rfl) rfl)

noncomputable def ep396 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz123)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123))) Bool.true 21394655127 137438953472 2269398896309 9995522769158144 Bool.true 59715786933 274877906944 4547583141491 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ft qz122 (Real.cos qz123) 140121 524288 1 524288 152687 262144 8058315 9532473344 21394655127 137438953472 2269398896309 9995522769158144 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz123) Bool.true 305374 524288 8058315 9532473344 152687 262144 8058315 9532473344 (ep393 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz122 (@Neg.neg Real Real.instNeg (Real.sin qz123)) 140121 524288 1 524288 426173 524288 8058315 9532473344 59715786933 274877906944 4547583141491 19991045538316288 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz123) Bool.false 426173 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz123) Bool.false 426173 524288 8058315 9532473344 426173 524288 8058315 9532473344 (ep395 rfl rfl) rfl)) rfl)

noncomputable def ep397 := @ep312 21394655127 137438953472 2269398896309 9995522769158144 Bool.true 59715786933 274877906944 4547583141491 19991045538316288 Bool.false 3761127512364053168128 54731608723 137438953472 43774477531433 9995522769158144 Bool.true 3749867522979247685632 6820969289 137438953472 43755063931507 9995522769158144 (ep313 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep386 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep387 ep396) rfl rfl

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz378))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz265 qz278 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep398 := @Enclosure.Complex.IsNear.of_eq qz100 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 70783194593 274877906944 4401508584661 19991045538316288 Bool.true 5190530253 274877906944 4366269444081 19991045538316288 (BSN.cpow_neg_s_mk qz17 60352 1000 15 qz18 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15) qz19)

noncomputable def ep399 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz378) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz378) (Real.sqrt qz379) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep400 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 72727 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz127 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz127 60352 1000 0 1 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 11500787352676668811 70368744177664000 943000000205744683 1136359375000000000000 qz22 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 25576775395801252757504 9444732965739290427392 1000000000218181 72727000000000000000 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep402 := BSN.cos_dyadic_bound_f 78597905 1073741824 1 0 524288 145597 0 1 1 0 1 1 522883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 78597905) qz280 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 78597905) qz281 0 0 rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85687543) qz20)

noncomputable def ep403 := @Enclosure.Real.IsNear.cos_image qz126 qz380 Bool.false 85687543 524288 109 131072 Bool.false 522883 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 11500787352676668811 70368744177664000 943000000205744683 1136359375000000000000 85687543 524288 109 131072 (ep401 rfl) rfl) (Enclosure.sfrac_false_div 85687543 524288) (BSN.cos_reduce0 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5530835884887387406336) qz23) 226375608064910080 72057594037927936 Bool.false 522883 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 85687543 524288 226375608064910080 72057594037927936 26 5530835884887387406336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522883 524288 5530835884887387406336 75557863725914323419136 78597905 1073741824 145597 145454 (ep402 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep404 := BSN.sin_dyadic_bound_f 78597905 1073741824 1 0 524288 145597 0 1 1 0 1 1 38343 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 78597905) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 78597905) qz285 0 0 rfl) rfl rfl

noncomputable def ep405 := @Enclosure.Real.IsNear.sin_image qz126 qz380 Bool.false 85687543 524288 109 131072 Bool.false 38343 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 11500787352676668811 70368744177664000 943000000205744683 1136359375000000000000 85687543 524288 109 131072 (ep401 rfl) rfl) (Enclosure.sfrac_false_div 85687543 524288) (BSN.sin_reduce0 qz380 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5530835884887387406336) qz23) 226375608064910080 72057594037927936 Bool.false 38343 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 85687543 524288 226375608064910080 72057594037927936 26 5530835884887387406336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 38343 524288 5530835884887387406336 75557863725914323419136 78597905 1073741824 145597 145454 (ep404 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep399 rfl rfl) rfl)

noncomputable def ep406 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 70783194593 274877906944 4401508584661 19991045538316288 Bool.true 5190530253 274877906944 4366269444081 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz126) 135371 524288 1 524288 522883 524288 8058315 9532473344 70783194593 274877906944 4401508584661 19991045538316288 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 522883 524288 8058315 9532473344 522883 524288 8058315 9532473344 (ep403 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 135371 524288 1 524288 38343 524288 8058315 9532473344 5190530253 274877906944 4366269444081 19991045538316288 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 38343 524288 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 38343 524288 8058315 9532473344 38343 524288 8058315 9532473344 (ep405 rfl rfl) rfl)) rfl)

noncomputable def ep407 := @ep310 70783194593 274877906944 4401508584661 19991045538316288 Bool.true 5190530253 274877906944 4366269444081 19991045538316288 Bool.false 24772878237723061649408 180246412039 274877906944 91950463647527 19991045538316288 Bool.true 2588314807426699231232 18832468831 274877906944 91876397307095 19991045538316288 (ep311 (BSN.head_sum_c_succ qz6 14 15 rfl rfl) (ep397 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep398 ep406) rfl rfl

noncomputable def ep408 := @Enclosure.Complex.IsNear.mul qz95 (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.true 93894041540518263474729 1001274085736632549376000 293481476977750501135557 ep175 Bool.false

noncomputable abbrev qz128 := (Complex.re qz351)

noncomputable abbrev qz129 := (Complex.im qz351)

noncomputable def ep409 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) 678597792261701651229 8010192685893060395008 61985151387803660260453

noncomputable def ep410 := nat_lit 582557283466944603347746816

noncomputable def ep411 := nat_lit 284451798567844044603392000

noncomputable def ep412 := nat_lit 2937927206237494433676756716301346481897472

noncomputable def ep413 := @Enclosure.Real.IsNear.mulLit_tf qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 46535578911 274877906944 4250698921527 19991045538316288 43747030217

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz130 := (@Inv.inv Real Real.instInv (Real.sqrt qz382))

noncomputable abbrev qz383 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz472 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable abbrev qz131 := (Real.cos qz383)

noncomputable abbrev qz132 := (@Neg.neg Real Real.instNeg (Real.sin qz383))

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq qz95 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz130 qz132)) Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (BSN.cpow_neg_s_mk qz17 60352 1000 16 qz18 rfl)

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16) qz19)

noncomputable def ep415 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz382) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz382) (Real.sqrt qz384) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz384) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep416 := BSN.log_dyadic_bound 0 32 1 0 1 262144 72727 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz385 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz133 := qz385

noncomputable abbrev qz386 := (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16) qz19))

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz133 60352 1000 0 1 3121657384082679 1125899906842624 250000000072727 18181750000000000000 2943722913189966297 17592186044416000 235750000068581561 284089843750000000000 qz22 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000072727 18181750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 26186360105375033720832 9444732965739290427392 1000000000290908 72727000000000000000 3121657384082679 1125899906842624 250000000072727 18181750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep418 := nat_lit 1387919007326436767185396287334014187487107686755284001529768383665308055681

noncomputable def ep419 := nat_lit 386072686759470970847066749764452373654077515749419590728165831712848001

noncomputable def ep420 := nat_lit 4162984876605791359614494728502513657714014905234353165407848819332498471041

noncomputable def ep421 := BSN.cos_dyadic_bound_f 887837807 1073741824 3 2 524288 145597 ep418 ep57 ep419 ep420 ep60 ep419 355041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 887837807) qz280 0 2 ep418 ep57 ep419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 887837807) qz281 0 2 ep420 ep60 ep419 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz134 := qz383

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 87729779) qz20)

noncomputable def ep422 := @Enclosure.Real.IsNear.cos_image qz134 qz387 Bool.false 87729779 524288 109 131072 Bool.true 355041 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 2943722913189966297 17592186044416000 235750000068581561 284089843750000000000 87729779 524288 109 131072 (ep417 rfl) rfl) (Enclosure.sfrac_false_div 87729779 524288) (BSN.cos_reduce2 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 62476031517899827970048) qz23) 226375608064910080 72057594037927936 Bool.false 355041 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 87729779 524288 226375608064910080 72057594037927936 26 62476031517899827970048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 355041 524288 62476031517899827970048 75557863725914323419136 887837807 1073741824 145597 145454 (ep421 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep423 := nat_lit 621347476666213693932528393968424001

noncomputable def ep424 := BSN.sin_dyadic_bound_f 887837807 1073741824 2 1 524288 145597 ep423 ep79 ep423 ep423 ep80 ep423 385776 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 887837807) qz284 0 1 ep423 ep79 ep423 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 887837807) qz285 0 1 ep423 ep80 ep423 rfl rfl rfl rfl) rfl rfl

noncomputable def ep425 := @Enclosure.Real.IsNear.sin_image qz134 qz387 Bool.false 87729779 524288 109 131072 Bool.true 385776 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 2943722913189966297 17592186044416000 235750000068581561 284089843750000000000 87729779 524288 109 131072 (ep417 rfl) rfl) (Enclosure.sfrac_false_div 87729779 524288) (BSN.sin_reduce2 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 62476031517899827970048) qz23) 226375608064910080 72057594037927936 Bool.false 385776 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 87729779 524288 226375608064910080 72057594037927936 26 62476031517899827970048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 385776 524288 62476031517899827970048 75557863725914323419136 887837807 1073741824 145597 145454 (ep424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz135 := (Real.sin qz383)

noncomputable abbrev qz388 := (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep415 rfl rfl) rfl)

noncomputable def ep426 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 qz131) (@HMul.hMul Real Real Real qz0 qz130 qz132) Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (@Enclosure.Real.IsNear.mulLit_ft qz130 qz131 131071 524288 1 524288 355041 524288 8058315 9532473344 46535578911 274877906944 4250698921527 19991045538316288 qz388 (@Enclosure.Real.IsNear.recentre' qz131 Bool.true 355041 524288 8058315 9532473344 355041 524288 8058315 9532473344 (ep422 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 qz132 131071 524288 1 524288 24111 32768 8058315 9532473344 3160252881 17179869184 265808386617 1249440346144768 qz388 (@Enclosure.Real.IsNear.neg qz135 Bool.true 24111 32768 8058315 9532473344 (@Enclosure.Real.IsNear.recentre' qz135 Bool.true 385776 524288 8058315 9532473344 24111 32768 8058315 9532473344 (ep425 rfl rfl) rfl)) rfl)

noncomputable def ep427 := @ep413 87422733696 0 1 678597792261701651229 8010192685893060395008 61985151387803660260453 ep410 (@Enclosure.Complex.IsNear.re_isNear qz95 Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (ep414 ep426))

noncomputable def ep428 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.false 43747030217 87422733696 0 1 Bool.false

noncomputable def ep429 := @Enclosure.Complex.IsNear.addLitP qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) Bool.false 226663369 455326738 0 1 Bool.true 60352000

noncomputable def ep430 := @ep429 227663369 0 1 Bool.false 1 384 0 1 Bool.false 943 3000 0 1 Bool.false 87494060434 43747030217 87422733696 0 1 Bool.false 33630556967 33630556967 682990107000 0 1

noncomputable abbrev qz136 := (@HDiv.hDiv Complex Complex Complex qz323 qz352 (@HSub.hSub Complex Complex Complex qz315 qz270 (1 : Complex)))

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP qz136 qz71 Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (Enclosure.sfrac Bool.true 32000000 14570455616) (Enclosure.sfrac Bool.true 3862528000 14570455616)) Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1

noncomputable def ep433 := @ep431 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 14506455616 226663369 455326738 0 1 Bool.true 3862528000 60352000 227663369 0 1 (ep432 (BSN.N_div_s_sub_one_mk qz17 60352 1000 16 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 32000000 14570455616) (Enclosure.sfrac Bool.true 3862528000 14570455616) Bool.true 32000000 14570455616 0 1 Bool.true 3862528000 14570455616 0 1 (Enclosure.Real.IsNear.const Bool.true 32000000 14570455616) (Enclosure.Real.IsNear.const Bool.true 3862528000 14570455616))) qz72 rfl

noncomputable abbrev qz137 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz389 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz480 qz481 1))

noncomputable abbrev qz138 := qz389

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz138)) Bool.false 1 384 0 1

noncomputable def ep435 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz138) Bool.false 0 1 0 1 Bool.false

noncomputable def ep436 := @ep435 0 1 0 1 Bool.false 1 384 0 1 Bool.false 943 3000 0 1 Bool.false 1 1 384 0 1 Bool.false 943 943 3000 0

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep438 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz138 Bool.false 1 384 0 1 Bool.false 943 3000 0 1

noncomputable abbrev qz139 := (Complex.re qz389)

noncomputable abbrev qz140 := (Complex.im qz389)

noncomputable def ep439 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 1 384 0 1 0 1 0

noncomputable def ep440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 1 16 0 1 1

noncomputable def ep441 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep443 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow14.d7 rfl) qz341

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep445 := ep444 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz66 qz17) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 60352 1000 qz18) (@Enclosure.Complex.IsNear.mk qz66 qz17 Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 qz333 qz22))

noncomputable def ep446 := @ep442 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 60352 1000 0 1 0 1 0

noncomputable def ep448 := @ep447 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep449 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1886 375 0 1 0 1 0 1 1886

noncomputable def ep450 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 60352 1000 0 1 1886 375 0

noncomputable def ep451 := @ep450 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep453 := @ep452 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep454 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 (@ep441 1 24 0 1 (ep446 rfl) (ep448 rfl) rfl rfl) (@ep449 1886 375 0 1 (ep451 rfl) (ep453 rfl) rfl rfl)

noncomputable def ep455 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 ep454

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.re_isNear qz389 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz389 (Complex.mk (Enclosure.sfrac Bool.false 1 16) qz276) Bool.false 1 16 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 16 1 16 EMRow14.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 16) qz276 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 16) qz287)))

noncomputable def ep456 := @ep440 384 0 1 ep455 qz141

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1886 375 0 1 0 1 0 1 0

noncomputable def ep458 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 1886 375 0 1 ep454

noncomputable abbrev qz142 := (@Enclosure.Complex.IsNear.im_isNear qz389 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz389 (Complex.mk (Enclosure.sfrac Bool.false 1 16) qz276) Bool.false 1 16 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 16 1 16 EMRow14.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 16) qz276 Bool.false 1 16 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 16) qz287)))

noncomputable def ep459 := @ep457 1 0 1 ep458 qz142

noncomputable def ep460 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 0 1 0 1 943 3000 0

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 0 1 0 1 0

noncomputable def ep462 := @ep461 1 0 1 ep455 qz142

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1886 375 0 1 1 16 0 1 943

noncomputable def ep464 := @ep463 3000 0 1 ep458 qz141

noncomputable def ep465 := @ep436 1 (@ep437 0 1 0 1 (BSN.bern_sum_base qz6 16) qz87) (ep438 (@ep439 1 1 1 384 0 1 (ep456 rfl) (ep459 rfl) rfl rfl) (@ep460 1 943 943 3000 0 1 (ep462 rfl) (ep464 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep466 := ep430 (ep433 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep434 Bool.false 943 3000 0 1 (BSN.bern_sum_succ qz6 16 0 1 1 rfl rfl) (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep467 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 3160252881 17179869184 265808386617 1249440346144768 33630556967

noncomputable def ep468 := @ep467 682990107000 0 1 35427021514865457309 3911226897408720896000 2979761362809792970213 ep411 (@Enclosure.Complex.IsNear.im_isNear qz95 Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (ep414 ep426))

noncomputable def ep469 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.false 43747030217 87422733696 0 1 Bool.false

noncomputable def ep470 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) 521672479186236440979 62579630358539534336000 47651124076659745376203

noncomputable def ep471 := nat_lit 4551228777085504713654272000

noncomputable def ep472 := nat_lit 36409830216684037709234176

noncomputable def ep473 := nat_lit 2622744407045844602620172072853535822184448

noncomputable def ep474 := @Enclosure.Real.IsNear.mulLit_tf qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 46535578911 274877906944 4250698921527 19991045538316288 33630556967

noncomputable def ep475 := @ep474 682990107000 0 1 521672479186236440979 62579630358539534336000 47651124076659745376203 ep471 (@Enclosure.Complex.IsNear.re_isNear qz95 Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (ep414 ep426))

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz96 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 3160252881 17179869184 265808386617 1249440346144768 43747030217

noncomputable def ep477 := @ep476 87422733696 0 1 46083892759489435059 500637042868316274688 3876109173755305801963 ep472 (@Enclosure.Complex.IsNear.im_isNear qz95 Bool.true 46535578911 274877906944 4250698921527 19991045538316288 Bool.false 3160252881 17179869184 265808386617 1249440346144768 (ep414 ep426))

noncomputable abbrev qz390 := (ep466 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep478 := @ep408 1309703528937485735349 15644907589634883584000 266082385398036485310789 ep302 (@ep409 ep410 35427021514865457309 3911226897408720896000 2979761362809792970213 ep411 ep412 93894041540518263474729 1001274085736632549376000 293481476977750501135557 ep175 (ep427 (@ep428 33630556967 682990107000 0 1 qz390) rfl) (ep468 (@ep469 33630556967 682990107000 0 1 qz390) rfl) rfl rfl) (@ep470 ep471 46083892759489435059 500637042868316274688 3876109173755305801963 ep472 ep473 1309703528937485735349 15644907589634883584000 266082385398036485310789 ep302 (ep475 (@ep469 33630556967 682990107000 0 1 qz390) rfl) (ep477 (@ep428 33630556967 682990107000 0 1 qz390) rfl) rfl rfl)

noncomputable def ep479 := @ep307 ep301 ep302 (@ep308 19991045538316288 (BSN.head_sum_c_eq qz6 16) (ep309 (BSN.head_sum_c_succ qz6 15 16 rfl rfl) (ep407 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep478 rfl rfl rfl

noncomputable def ep480 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 16) Bool.false 562674045098856126781271 1001274085736632549376000 ep174 ep175 Bool.false 237837703774247825599 15644907589634883584000 ep301 ep302 (@ep303 ep175 Bool.false 237837703774247825599 15644907589634883584000 ep301 ep302 (BSN.zetaApproximant_eq_folded' qz6 1 16 rfl) (ep479 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep481 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) (Complex.im (zetaApproximant qz6 1 16)) 107 524288 14269691

noncomputable def ep482 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48)) Bool.false 107 524288 14269691

noncomputable def ep483 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48) qz319 Bool.false 19765299 524288 189

noncomputable def ep484 := BSN.sin_dyadic_bound_f 219238 1073741824 1 0 524288 145597 0 1 1 0 1 1 107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 219238) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 219238) qz285 0 0 rfl) rfl rfl

noncomputable def ep485 := @ep483 524288 Bool.false 107 524288 1 72727 (@ep179 19765299 524288 189 524288 ep298 rfl) (Enclosure.sfrac_false_div 19765299 524288) (BSN.sin_reduce0 qz319 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15427533272166432768) qz23) 226375608064910080 72057594037927936 Bool.false 107 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 19765299 524288 226375608064910080 72057594037927936 6 15427533272166432768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 107 524288 15427533272166432768 75557863725914323419136 219238 1073741824 145597 145454 (ep484 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep486 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 16) Bool.false 562674045098856126781271 1001274085736632549376000 ep174 ep175 Bool.false 237837703774247825599 15644907589634883584000 ep301 ep302 (@ep303 ep175 Bool.false 237837703774247825599 15644907589634883584000 ep301 ep302 (BSN.zetaApproximant_eq_folded' qz6 1 16 rfl) (ep479 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow14.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 16 qz17) Bool.false ep159 ep160 ep161 ep162 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 16 qz17) ep163 Bool.false ep159 ep160 ep161 ep162 (@Eq.refl Real ep163) (@ep164 Bool.false ep159 ep160 ep161 ep162 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz46 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz47 (@Nat.cast Complex Complex.instNatCast j))))) qz48) (zetaApproximant qz6 1 16)) (@ep166 ep167 ep168 ep162 25448634303844517339093 ep169 ep170 ep171 ep172 ep159 ep160 ep161 ep162 (@ep173 38129893376 562674045098856126781271 1001274085736632549376000 ep174 ep175 ep165 ep167 ep168 ep162 (@ep176 38129893376 524287 524288 14269691 38129893376 (ep300 rfl rfl) rfl) ep480 rfl) (@ep481 38129893376 237837703774247825599 15644907589634883584000 ep301 ep302 25448634303844517339093 ep169 ep170 ep171 (@ep482 38129893376 107 524288 14269691 38129893376 (ep485 rfl rfl) rfl) ep486 rfl) rfl rfl))

noncomputable abbrev qz496 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 63102 1000)))

noncomputable abbrev qz482 := qz496

noncomputable abbrev qz391 := qz482

noncomputable abbrev qz143 := (BSN.headSumC qz391 9)

noncomputable abbrev qz144 := qz391

noncomputable abbrev qz483 := (@Neg.neg Complex Complex.instNeg qz496)

noncomputable abbrev qz392 := qz483

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 8) qz392)

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq qz143 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 8) qz145) Bool.false 444076798561 137438953472 7481532053137 2498880692289536 Bool.false 69066327811 274877906944 59668505768709 19991045538316288

noncomputable def ep488 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 8) qz145 Bool.false 815733199837 274877906944 53579336990631 19991045538316288 Bool.false 1064882597 68719476736 26699286761521 9995522769158144 Bool.false

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 7) qz392)

noncomputable def ep489 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 7) qz146) Bool.false 815733199837 274877906944 53579336990631 19991045538316288 Bool.false 1064882597 68719476736 26699286761521 9995522769158144

noncomputable def ep490 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 7) qz146 Bool.false 915905388989 274877906944 46866864002023 19991045538316288 Bool.true 23300781489 274877906944 46712749525409 19991045538316288 Bool.true

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 6) qz392)

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 6) qz147) Bool.false 915905388989 274877906944 46866864002023 19991045538316288 Bool.true 23300781489 274877906944 46712749525409 19991045538316288

noncomputable def ep492 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 6) qz147 Bool.false 803751521457 274877906944 39618219214747 19991045538316288 Bool.true 27091840257 274877906944 39500924672785 19991045538316288 Bool.false

noncomputable abbrev qz148 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 5) qz392)

noncomputable def ep493 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 5) qz148) Bool.false 803751521457 274877906944 39618219214747 19991045538316288 Bool.true 27091840257 274877906944 39500924672785 19991045538316288

noncomputable def ep494 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 5) qz148 Bool.false 185054891687 68719476736 7924933642025 4997761384579072 Bool.false 78147225703 274877906944 31569503420105 19991045538316288 Bool.false

noncomputable abbrev qz149 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 4) qz392)

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 4) qz149) Bool.false 185054891687 68719476736 7924933642025 4997761384579072 Bool.false 78147225703 274877906944 31569503420105 19991045538316288

noncomputable def ep496 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 4) qz149 Bool.false 154687197995 68719476736 5708744994637 4997761384579072 Bool.false 6925050689 137438953472 5680152665495 4997761384579072 Bool.false

noncomputable abbrev qz150 := (@HPow.hPow Complex Complex Complex qz272 qz274 qz392)

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 3) qz150) Bool.false 154687197995 68719476736 5708744994637 4997761384579072 Bool.false 6925050689 137438953472 5680152665495 4997761384579072

noncomputable def ep498 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 3) qz150 Bool.false 1810610065 1073741824 785193108983 1249440346144768 Bool.false 5855787783 34359738368 6253729048901 9995522769158144 Bool.false

noncomputable abbrev qz151 := (@HPow.hPow Complex Complex Complex qz272 qz275 qz392)

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 2) qz151) Bool.false 1810610065 1073741824 785193108983 1249440346144768 Bool.false 5855787783 34359738368 6253729048901 9995522769158144

noncomputable def ep500 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 2) qz151 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep501 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz144)

noncomputable abbrev qz497 := (Enclosure.sfrac Bool.false 63102 1000)

noncomputable abbrev qz484 := qz497

noncomputable abbrev qz393 := qz484

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz153 := qz393

noncomputable abbrev qz394 := (@Eq.refl Real qz484)

noncomputable abbrev qz154 := qz394

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq qz151 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 736868241 1073741824 785193108983 1249440346144768 Bool.false 5855787783 34359738368 6253729048901 9995522769158144 (BSN.cpow_neg_s_mk qz153 63102 1000 2 qz154 rfl)

noncomputable def ep503 := nat_lit 16603860160245459783152303032850897000930050532962770949148268451431426030625

noncomputable def ep504 := nat_lit 17028028395910085471770962296559478807919087975844060590812255700625390625

noncomputable def ep505 := nat_lit 43458731230859016436539831147081729179603977634370176387765102292138436590625

noncomputable def ep506 := BSN.sin_dyadic_bound_f 1425264755 1073741824 3 2 524288 145597 ep503 ep64 ep504 ep505 ep66 ep504 508832 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1425264755) qz284 0 2 ep503 ep64 ep504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1425264755) qz285 0 2 ep505 ep66 ep504 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz155 := (Enclosure.Real.IsNear.const Bool.false 63102 1000)

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 22931771) qz20)

noncomputable def ep507 := @Enclosure.Real.IsNear.cos_image qz152 qz395 Bool.false 22931771 524288 57 65536 Bool.false 508832 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 716617863 16384000 31551 36363500 22931771 524288 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz21 63102 1000 0 1 181704 262144 1 72727 716617863 16384000 31551 36363500 qz155 qz283 rfl) rfl) (Enclosure.sfrac_false_div 22931771 524288) (BSN.cos_reduce3 qz395 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 100294090946796933087232) qz23) 226375608064910080 72057594037927936 Bool.false 508832 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 22931771 524288 226375608064910080 72057594037927936 6 100294090946796933087232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 508832 524288 100294090946796933087232 75557863725914323419136 1425264755 1073741824 145597 145454 (ep506 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep508 := nat_lit 9231934768312326584183177668160080324431325446301914554233843475551070190625

noncomputable def ep509 := nat_lit 27661748248145159581605991079887122015678138162954055541519905915251959790625

noncomputable def ep510 := BSN.cos_dyadic_bound_f 1425264755 1073741824 3 2 524288 145597 ep508 ep57 ep504 ep509 ep60 ep504 126363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1425264755) qz280 0 2 ep508 ep57 ep504 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1425264755) qz281 0 2 ep509 ep60 ep504 rfl rfl rfl rfl) rfl rfl

noncomputable def ep511 := @Enclosure.Real.IsNear.sin_image qz152 qz395 Bool.false 22931771 524288 57 65536 Bool.true 126363 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 716617863 16384000 31551 36363500 22931771 524288 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz21 63102 1000 0 1 181704 262144 1 72727 716617863 16384000 31551 36363500 qz155 qz283 rfl) rfl) (Enclosure.sfrac_false_div 22931771 524288) (BSN.sin_reduce3 qz395 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 100294090946796933087232) qz23) 226375608064910080 72057594037927936 Bool.false 126363 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 22931771 524288 226375608064910080 72057594037927936 6 100294090946796933087232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 126363 524288 100294090946796933087232 75557863725914323419136 1425264755 1073741824 145597 145454 (ep510 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep512 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 736868241 1073741824 785193108983 1249440346144768 Bool.false 5855787783 34359738368 6253729048901 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz15 (Real.cos qz152) 46341 65536 1 262144 15901 16384 4210975 4766236672 736868241 1073741824 785193108983 1249440346144768 qz286 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 508832 524288 4210975 4766236672 15901 16384 4210975 4766236672 (ep507 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 46341 65536 1 262144 126363 524288 4210975 4766236672 5855787783 34359738368 6253729048901 9995522769158144 qz286 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 126363 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 126363 524288 4210975 4766236672 126363 524288 4210975 4766236672 (ep511 rfl rfl) rfl)) rfl)

noncomputable def ep513 := @ep500 736868241 1073741824 785193108983 1249440346144768 Bool.false 5855787783 34359738368 6253729048901 9995522769158144 Bool.false 1810610065 1810610065 1073741824 785193108983 1249440346144768 Bool.false 5855787783 5855787783 34359738368 6253729048901 9995522769158144 (ep501 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep502 ep512) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep514 := @Enclosure.Complex.IsNear.of_eq qz150 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 38808153835 68719476736 2567972558705 4997761384579072 Bool.true 16498100443 137438953472 5106576282089 9995522769158144 (BSN.cpow_neg_s_mk qz153 63102 1000 3 qz154 rfl)

noncomputable def ep515 := nat_lit 2557806765654616327153457620573761

noncomputable def ep516 := BSN.cos_dyadic_bound_f 224888337 1073741824 2 1 524288 145597 ep515 ep75 ep515 ep515 ep76 ep515 512830 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 224888337) qz280 0 1 ep515 ep75 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 224888337) qz281 0 1 ep515 ep76 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz396 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18172997) qz43)

noncomputable def ep517 := @Enclosure.Real.IsNear.cos_image qz156 qz396 Bool.false 18172997 262144 57 65536 Bool.false 512830 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 4543249347 65536000 31551 36363500 18172997 262144 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz27 63102 1000 0 1 287994 262144 1 72727 4543249347 65536000 31551 36363500 qz155 qz290 rfl) rfl) (Enclosure.sfrac_false_div 18172997 262144) (BSN.cos_reduce0 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7912554931981861781504) qz312) 226375608064910080 72057594037927936 Bool.false 512830 524288 11 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 18172997 262144 226375608064910080 72057594037927936 11 7912554931981861781504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512830 524288 7912554931981861781504 37778931862957161709568 224888337 1073741824 145597 145454 (ep516 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep518 := BSN.sin_dyadic_bound_f 224888337 1073741824 2 1 524288 145597 ep515 ep79 ep515 ep515 ep80 ep515 109007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 224888337) qz284 0 1 ep515 ep79 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 224888337) qz285 0 1 ep515 ep80 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable def ep519 := @Enclosure.Real.IsNear.sin_image qz156 qz396 Bool.false 18172997 262144 57 65536 Bool.false 109007 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 4543249347 65536000 31551 36363500 18172997 262144 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz27 63102 1000 0 1 287994 262144 1 72727 4543249347 65536000 31551 36363500 qz155 qz290 rfl) rfl) (Enclosure.sfrac_false_div 18172997 262144) (BSN.sin_reduce0 qz396 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7912554931981861781504) qz312) 226375608064910080 72057594037927936 Bool.false 109007 524288 11 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 18172997 262144 226375608064910080 72057594037927936 11 7912554931981861781504 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 109007 524288 7912554931981861781504 37778931862957161709568 224888337 1073741824 145597 145454 (ep518 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep520 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 38808153835 68719476736 2567972558705 4997761384579072 Bool.true 16498100443 137438953472 5106576282089 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz156) 151349 262144 1 262144 256415 262144 4210975 4766236672 38808153835 68719476736 2567972558705 4997761384579072 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 512830 524288 4210975 4766236672 256415 262144 4210975 4766236672 (ep517 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 151349 262144 1 262144 109007 524288 4210975 4766236672 16498100443 137438953472 5106576282089 9995522769158144 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 109007 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 109007 524288 4210975 4766236672 109007 524288 4210975 4766236672 (ep519 rfl rfl) rfl)) rfl)

noncomputable def ep521 := @ep498 38808153835 68719476736 2567972558705 4997761384579072 Bool.true 16498100443 137438953472 5106576282089 9995522769158144 Bool.false 166094114124600442880 154687197995 68719476736 5708744994637 4997761384579072 Bool.false 237942929859178135552 6925050689 137438953472 5680152665495 4997761384579072 (ep499 (BSN.head_sum_c_succ qz144 2 3 rfl rfl) (ep513 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep514 ep520) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep522 := @Enclosure.Complex.IsNear.of_eq qz149 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 7591923423 17179869184 554047161847 1249440346144768 Bool.false 64297124325 274877906944 8848892758125 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 4 qz154 rfl)

noncomputable def ep523 := nat_lit 7379805621735208791491064702654796997033104480666855355925172516420327830625

noncomputable def ep524 := nat_lit 3367680273551482452132836338944408883532707883421351299352264110250390625

noncomputable def ep525 := nat_lit 19322609907911225387077906771928082139751458779459081839605071972541405590625

noncomputable def ep526 := BSN.sin_dyadic_bound_f 1163901845 1073741824 3 2 524288 145597 ep523 ep64 ep524 ep525 ep66 ep524 463376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1163901845) qz284 0 2 ep523 ep64 ep524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1163901845) qz285 0 2 ep525 ep66 ep524 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz397 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 45863543) qz20)

noncomputable def ep527 := @Enclosure.Real.IsNear.cos_image qz157 qz397 Bool.false 45863543 524288 57 65536 Bool.false 463376 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 716617863 8192000 31551 36363500 45863543 524288 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz30 63102 1000 0 1 363408 262144 1 72727 716617863 8192000 31551 36363500 qz155 qz294 rfl) rfl) (Enclosure.sfrac_false_div 45863543 524288) (BSN.cos_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 81902311207646366007296) qz23) 226375608064910080 72057594037927936 Bool.false 463376 524288 13 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 45863543 524288 226375608064910080 72057594037927936 13 81902311207646366007296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 463376 524288 81902311207646366007296 75557863725914323419136 1163901845 1073741824 145597 145454 (ep526 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep528 := nat_lit 4101388758863361098584872762069973624522183692763106909424807959838071190625

noncomputable def ep529 := nat_lit 12297430916042980330850352613532032055799485662522478025675719351293712790625

noncomputable def ep530 := BSN.cos_dyadic_bound_f 1163901845 1073741824 3 2 524288 145597 ep528 ep57 ep524 ep529 ep60 ep524 245275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1163901845) qz280 0 2 ep528 ep57 ep524 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1163901845) qz281 0 2 ep529 ep60 ep524 rfl rfl rfl rfl) rfl rfl

noncomputable def ep531 := @Enclosure.Real.IsNear.sin_image qz157 qz397 Bool.false 45863543 524288 57 65536 Bool.true 245275 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 716617863 8192000 31551 36363500 45863543 524288 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz30 63102 1000 0 1 363408 262144 1 72727 716617863 8192000 31551 36363500 qz155 qz294 rfl) rfl) (Enclosure.sfrac_false_div 45863543 524288) (BSN.sin_reduce3 qz397 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 81902311207646366007296) qz23) 226375608064910080 72057594037927936 Bool.false 245275 524288 13 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 45863543 524288 226375608064910080 72057594037927936 13 81902311207646366007296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 245275 524288 81902311207646366007296 75557863725914323419136 1163901845 1073741824 145597 145454 (ep530 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep532 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 7591923423 17179869184 554047161847 1249440346144768 Bool.false 64297124325 274877906944 8848892758125 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz157) 262143 524288 1 524288 28961 32768 4210975 4766236672 7591923423 17179869184 554047161847 1249440346144768 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 463376 524288 4210975 4766236672 28961 32768 4210975 4766236672 (ep527 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 262143 524288 1 524288 245275 524288 4210975 4766236672 64297124325 274877906944 8848892758125 19991045538316288 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 245275 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 245275 524288 4210975 4766236672 245275 524288 4210975 4766236672 (ep531 rfl rfl) rfl)) rfl)

noncomputable def ep533 := @ep496 7591923423 17179869184 554047161847 1249440346144768 Bool.false 64297124325 274877906944 8848892758125 19991045538316288 Bool.false 3179218831041949073408 185054891687 68719476736 7924933642025 4997761384579072 Bool.false 10740472917360499490816 78147225703 274877906944 31569503420105 19991045538316288 (ep497 (BSN.head_sum_c_succ qz144 3 4 rfl rfl) (ep521 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep522 ep532) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep534 := @Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 63531954709 274877906944 7918484646647 19991045538316288 Bool.true 13154883245 34359738368 991427656585 2498880692289536 (BSN.cpow_neg_s_mk qz153 63102 1000 5 qz154 rfl)

noncomputable def ep535 := nat_lit 3312882890090255345374533006423101926841638059865493535488172949839042916321

noncomputable def ep536 := nat_lit 2197951895697963042772670880120737311524433738884458752028008230674051041

noncomputable def ep537 := nat_lit 9934252766479370110038053677509064305901865312118711688960462833055780646881

noncomputable def ep538 := BSN.cos_dyadic_bound_f 1103449019 1073741824 3 2 524288 145597 ep535 ep57 ep536 ep537 ep60 ep536 270961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1103449019) qz280 0 2 ep535 ep57 ep536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1103449019) qz281 0 2 ep537 ep60 ep536 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13311493) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep539 := @Enclosure.Real.IsNear.cos_image qz158 qz398 Bool.false 13311493 131072 57 65536 Bool.false 270961 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 831968319 8192000 31551 36363500 13311493 131072 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz33 63102 1000 0 1 421904 262144 1 72727 831968319 8192000 31551 36363500 qz155 qz298 rfl) rfl) (Enclosure.sfrac_false_div 13311493 131072) (BSN.cos_reduce0 qz398 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19412080447269692768256) qz299) 226375608064910080 72057594037927936 Bool.false 270961 524288 16 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 13311493 131072 226375608064910080 72057594037927936 16 19412080447269692768256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270961 524288 19412080447269692768256 18889465931478580854784 1103449019 1073741824 145597 145454 (ep538 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep540 := nat_lit 5961430840645901251239941274857486878465728960766780796877088903125738008545

noncomputable def ep541 := nat_lit 15609712660527182765463928538439889202239202956907184391936711304384412987361

noncomputable def ep542 := BSN.sin_dyadic_bound_f 1103449019 1073741824 3 2 524288 145597 ep540 ep64 ep536 ep541 ep66 ep536 448840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1103449019) qz284 0 2 ep540 ep64 ep536 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1103449019) qz285 0 2 ep541 ep66 ep536 rfl rfl rfl rfl) rfl rfl

noncomputable def ep543 := @Enclosure.Real.IsNear.sin_image qz158 qz398 Bool.false 13311493 131072 57 65536 Bool.false 448840 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 831968319 8192000 31551 36363500 13311493 131072 57 65536 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz33 63102 1000 0 1 421904 262144 1 72727 831968319 8192000 31551 36363500 qz155 qz298 rfl) rfl) (Enclosure.sfrac_false_div 13311493 131072) (BSN.sin_reduce0 qz398 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19412080447269692768256) qz299) 226375608064910080 72057594037927936 Bool.false 448840 524288 16 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 13311493 131072 226375608064910080 72057594037927936 16 19412080447269692768256 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448840 524288 19412080447269692768256 18889465931478580854784 1103449019 1073741824 145597 145454 (ep542 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep544 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 63531954709 274877906944 7918484646647 19991045538316288 Bool.true 13154883245 34359738368 991427656585 2498880692289536 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz158) 234469 524288 1 524288 270961 524288 4210975 4766236672 63531954709 274877906944 7918484646647 19991045538316288 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 270961 524288 4210975 4766236672 270961 524288 4210975 4766236672 (ep539 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 234469 524288 1 524288 56105 65536 4210975 4766236672 13154883245 34359738368 991427656585 2498880692289536 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 56105 65536 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 448840 524288 4210975 4766236672 56105 65536 4210975 4766236672 (ep543 rfl rfl) rfl)) rfl)

noncomputable def ep545 := @ep494 63531954709 274877906944 7918484646647 19991045538316288 Bool.true 13154883245 34359738368 991427656585 2498880692289536 Bool.false 55233383980288916324352 803751521457 274877906944 39618219214747 19991045538316288 Bool.true 930868543138169880576 27091840257 274877906944 39500924672785 19991045538316288 (ep495 (BSN.head_sum_c_succ qz144 4 5 rfl rfl) (ep533 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep534 ep544) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 28038466883 68719476736 1812161196819 4997761384579072 Bool.false 236941173 17179869184 450739053289 1249440346144768 (BSN.cpow_neg_s_mk qz153 63102 1000 6 qz154 rfl)

noncomputable def ep547 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz36 63102 1000 0 1 4034681531866359 2251799813685248 500000000072727 36363500000000000000 127298237011915492809 1125899906842624000 15775500002294609577 18181750000000000000000 qz155 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz302) Bool.false 16922680887833197019136 9444732965739290427392 1000000000145454 72727000000000000000 4034681531866359 2251799813685248 500000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep548 := nat_lit 29873340476682617294687916450348601908426217341642636849967883881149265674240

noncomputable def ep549 := nat_lit 55030507386249038690218617791893204890247665524162428949264643291160313856

noncomputable def ep550 := nat_lit 78150604236495784947255617703059463618913025388691595436378981694824293400576

noncomputable def ep551 := BSN.sin_dyadic_bound_f 1650347652 1073741824 3 2 524288 145597 ep548 ep64 ep549 ep550 ep66 ep549 523988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1650347652) qz284 0 2 ep548 ep64 ep549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1650347652) qz285 0 2 ep550 ep66 ep549 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 14819465) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep552 := @Enclosure.Real.IsNear.cos_image qz159 qz399 Bool.false 14819465 131072 57 65536 Bool.false 523988 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 127298237011915492809 1125899906842624000 15775500002294609577 18181750000000000000000 14819465 131072 57 65536 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 14819465 131072) (BSN.cos_reduce3 qz399 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29033222938406965739520) qz299) 226375608064910080 72057594037927936 Bool.false 523988 524288 17 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 14819465 131072 226375608064910080 72057594037927936 17 29033222938406965739520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523988 524288 29033222938406965739520 18889465931478580854784 1650347652 1073741824 145597 145454 (ep551 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep553 := nat_lit 16620758268106453625355606302545620262410230818923314885070719775434552180736

noncomputable def ep554 := nat_lit 49752213789546862798686381672053074377450197125721619797313630039721335914496

noncomputable def ep555 := BSN.cos_dyadic_bound_f 1650347652 1073741824 3 2 524288 145597 ep553 ep57 ep549 ep554 ep60 ep549 17712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1650347652) qz280 0 2 ep553 ep57 ep549 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1650347652) qz281 0 2 ep554 ep60 ep549 rfl rfl rfl rfl) rfl rfl

noncomputable def ep556 := @Enclosure.Real.IsNear.sin_image qz159 qz399 Bool.false 14819465 131072 57 65536 Bool.true 17712 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 127298237011915492809 1125899906842624000 15775500002294609577 18181750000000000000000 14819465 131072 57 65536 (ep547 rfl) rfl) (Enclosure.sfrac_false_div 14819465 131072) (BSN.sin_reduce3 qz399 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 29033222938406965739520) qz299) 226375608064910080 72057594037927936 Bool.false 17712 524288 17 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 14819465 131072 226375608064910080 72057594037927936 17 29033222938406965739520 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 17712 524288 29033222938406965739520 18889465931478580854784 1650347652 1073741824 145597 145454 (ep555 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep557 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 28038466883 68719476736 1812161196819 4997761384579072 Bool.false 236941173 17179869184 450739053289 1249440346144768 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz159) 214039 524288 1 524288 130997 131072 4210975 4766236672 28038466883 68719476736 1812161196819 4997761384579072 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 523988 524288 4210975 4766236672 130997 131072 4210975 4766236672 (ep552 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 214039 524288 1 524288 1107 32768 4210975 4766236672 236941173 17179869184 450739053289 1249440346144768 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 1107 32768 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 17712 524288 4210975 4766236672 1107 32768 4210975 4766236672 (ep556 rfl rfl) rfl)) rfl)

noncomputable def ep558 := @ep492 28038466883 68719476736 1812161196819 4997761384579072 Bool.false 236941173 17179869184 450739053289 1249440346144768 Bool.false 62940539071006616059904 915905388989 274877906944 46866864002023 19991045538316288 Bool.true 400304377865988734976 23300781489 274877906944 46712749525409 19991045538316288 (ep493 (BSN.head_sum_c_succ qz144 5 6 rfl rfl) (ep545 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep546 ep557) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep559 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 3130380911 8589934592 104882390447 312360086536192 Bool.false 27560311877 274877906944 6685823997633 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 7 qz154 rfl)

noncomputable def ep560 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz39 63102 1000 0 1 4381792198794487 2251799813685248 500000000072727 36363500000000000000 138249925664164859337 1125899906842624000 15775500002294609577 18181750000000000000000 qz155 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 500000000072727 36363500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz306) Bool.false 18378568546572512002048 9444732965739290427392 1000000000145454 72727000000000000000 4381792198794487 2251799813685248 500000000072727 36363500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep131 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep561 := nat_lit 6906980142854546623802231400960256

noncomputable def ep562 := BSN.cos_dyadic_bound_f 288285004 1073741824 2 1 524288 145597 ep561 ep75 ep561 ep561 ep76 ep561 505504 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 288285004) qz280 0 1 ep561 ep75 ep561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 288285004) qz281 0 1 ep561 ep76 ep561 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 32188819) qz43)

noncomputable def ep563 := @Enclosure.Real.IsNear.cos_image qz160 qz400 Bool.false 32188819 262144 57 65536 Bool.true 505504 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 138249925664164859337 1125899906842624000 15775500002294609577 18181750000000000000000 32188819 262144 57 65536 (ep560 rfl) rfl) (Enclosure.sfrac_false_div 32188819 262144) (BSN.cos_reduce2 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10143126880395468996608) qz312) 226375608064910080 72057594037927936 Bool.false 505504 524288 19 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 32188819 262144 226375608064910080 72057594037927936 19 10143126880395468996608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505504 524288 10143126880395468996608 37778931862957161709568 288285004 1073741824 145597 145454 (ep562 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep564 := BSN.sin_dyadic_bound_f 288285004 1073741824 2 1 524288 145597 ep561 ep79 ep561 ep561 ep80 ep561 139079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 288285004) qz284 0 1 ep561 ep79 ep561 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 288285004) qz285 0 1 ep561 ep80 ep561 rfl rfl rfl rfl) rfl rfl

noncomputable def ep565 := @Enclosure.Real.IsNear.sin_image qz160 qz400 Bool.false 32188819 262144 57 65536 Bool.true 139079 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 138249925664164859337 1125899906842624000 15775500002294609577 18181750000000000000000 32188819 262144 57 65536 (ep560 rfl) rfl) (Enclosure.sfrac_false_div 32188819 262144) (BSN.sin_reduce2 qz400 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10143126880395468996608) qz312) 226375608064910080 72057594037927936 Bool.false 139079 524288 19 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 32188819 262144 226375608064910080 72057594037927936 19 10143126880395468996608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 139079 524288 10143126880395468996608 37778931862957161709568 288285004 1073741824 145597 145454 (ep564 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep566 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 3130380911 8589934592 104882390447 312360086536192 Bool.false 27560311877 274877906944 6685823997633 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz160) 198163 524288 1 524288 15797 16384 4210975 4766236672 3130380911 8589934592 104882390447 312360086536192 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 505504 524288 4210975 4766236672 15797 16384 4210975 4766236672 (ep563 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 198163 524288 1 524288 139079 524288 4210975 4766236672 27560311877 274877906944 6685823997633 19991045538316288 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 139079 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 139079 524288 4210975 4766236672 139079 524288 4210975 4766236672 (ep565 rfl rfl) rfl)) rfl)

noncomputable def ep567 := @ep490 3130380911 8589934592 104882390447 312360086536192 Bool.false 27560311877 274877906944 6685823997633 19991045538316288 Bool.false 7007094831122695061504 815733199837 274877906944 53579336990631 19991045538316288 Bool.false 1170850797617804214272 1064882597 68719476736 26699286761521 9995522769158144 (ep491 (BSN.head_sum_c_succ qz144 6 7 rfl rfl) (ep558 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep559 ep566) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep568 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 72420397285 274877906944 6272919434465 19991045538316288 Bool.false 64806797423 274877906944 6269932245667 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 8 qz154 rfl)

noncomputable def ep569 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz42 63102 1000 0 1 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 295474236375577815387 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 19639770079031275290624 9444732965739290427392 1000000000218181 72727000000000000000 9364972152248037 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep146 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep570 := nat_lit 664384523502772491396309738715051681

noncomputable def ep571 := BSN.sin_dyadic_bound_f 902827703 1073741824 2 1 524288 145597 ep570 ep79 ep570 ep570 ep80 ep570 390695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 902827703) qz284 0 1 ep570 ep79 ep570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 902827703) qz285 0 1 ep570 ep80 ep570 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1074929) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep572 := @Enclosure.Real.IsNear.cos_image qz161 qz401 Bool.false 1074929 8192 57 65536 Bool.false 390695 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 295474236375577815387 2251799813685248000 31551000006883828731 36363500000000000000000 1074929 8192 57 65536 (ep569 rfl) rfl) (Enclosure.sfrac_false_div 1074929 8192) (BSN.cos_reduce3 qz401 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 992669557968976478208) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 390695 524288 20 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 1074929 8192 226375608064910080 72057594037927936 20 992669557968976478208 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390695 524288 992669557968976478208 1180591620717411303424 902827703 1073741824 145597 145454 (ep571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep573 := nat_lit 1484080501253329117386235119597095596686058299259164718920466916053595115841

noncomputable def ep574 := nat_lit 441406795070006053000497877537760838242779080700607275218438062500925761

noncomputable def ep575 := nat_lit 4451358690169847340052704363036211268381689339616092942210963872035783496001

noncomputable def ep576 := BSN.cos_dyadic_bound_f 902827703 1073741824 3 2 524288 145597 ep573 ep57 ep574 ep575 ep60 ep574 349621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 902827703) qz280 0 2 ep573 ep57 ep574 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 902827703) qz281 0 2 ep575 ep60 ep574 rfl rfl rfl rfl) rfl rfl

noncomputable def ep577 := @Enclosure.Real.IsNear.sin_image qz161 qz401 Bool.false 1074929 8192 57 65536 Bool.true 349621 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 295474236375577815387 2251799813685248000 31551000006883828731 36363500000000000000000 1074929 8192 57 65536 (ep569 rfl) rfl) (Enclosure.sfrac_false_div 1074929 8192) (BSN.sin_reduce3 qz401 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 992669557968976478208) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 349621 524288 20 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 1074929 8192 226375608064910080 72057594037927936 20 992669557968976478208 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 349621 524288 992669557968976478208 1180591620717411303424 902827703 1073741824 145597 145454 (ep576 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep578 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 72420397285 274877906944 6272919434465 19991045538316288 Bool.false 64806797423 274877906944 6269932245667 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz161) 185363 524288 1 524288 390695 524288 4210975 4766236672 72420397285 274877906944 6272919434465 19991045538316288 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 390695 524288 4210975 4766236672 390695 524288 4210975 4766236672 (ep572 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 185363 524288 1 524288 349621 524288 4210975 4766236672 64806797423 274877906944 6269932245667 19991045538316288 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 349621 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 349621 524288 4210975 4766236672 349621 524288 4210975 4766236672 (ep577 rfl rfl) rfl)) rfl)

noncomputable def ep579 := @ep488 72420397285 274877906944 6272919434465 19991045538316288 Bool.false 64806797423 274877906944 6269932245667 19991045538316288 Bool.false 244133801821679982215168 444076798561 137438953472 7481532053137 2498880692289536 Bool.false 4746201907248964304896 69066327811 274877906944 59668505768709 19991045538316288 (ep489 (BSN.head_sum_c_succ qz144 7 8 rfl rfl) (ep567 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep568 ep578) rfl rfl

theorem EMRow14.d10 : Enclosure.Complex.IsNear qz143 Bool.false 444076798561 137438953472 7481532053137 2498880692289536 Bool.false 69066327811 274877906944 59668505768709 19991045538316288 := ep487 (BSN.head_sum_c_succ qz144 8 9 rfl rfl) (ep579 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep580 := nat_lit 11538205928535945229331513349541

noncomputable def ep581 := nat_lit 2754637814599961091875694182400

noncomputable def ep582 := nat_lit 19200093728251687445322927475503660037

noncomputable def ep583 := nat_lit 2913975172078110345981161856579844177920

noncomputable abbrev qz485 := (@HAdd.hAdd Complex Complex Complex qz490 (@HAdd.hAdd Complex Complex Complex qz490 qz493 (@HMul.hMul Complex Complex Complex qz492 Complex.I (@HDiv.hDiv Complex Complex Complex qz494 (↑qz497) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz402 := qz485

noncomputable abbrev qz162 := (Complex.Stirling.logGammaStirling 1 qz402)

noncomputable abbrev qz486 := (@HAdd.hAdd Complex Complex Complex qz490 qz493 (@HMul.hMul Complex Complex Complex qz492 Complex.I (@HDiv.hDiv Complex Complex Complex qz494 (↑qz497) (2 : Complex))))

noncomputable abbrev qz403 := qz486

noncomputable abbrev qz163 := qz403

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz265 (@HDiv.hDiv Real Real Real qz268 qz393 (2 : Real)) (Real.log Real.pi))

noncomputable def ep584 := Complex.re (@HMul.hMul Complex Complex Complex qz44 (Complex.exp (@HMul.hMul Complex Complex Complex qz44 Complex.I ↑(@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164))) (zetaApproximant qz144 1 16))

noncomputable def ep585 := @Enclosure.Real.IsNear.of_eq ep584 (@HSub.hSub Real Real Real qz318 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.im (zetaApproximant qz144 1 16))))

noncomputable def ep586 := nat_lit 57690980331202491063591285508423

noncomputable def ep587 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.im (zetaApproximant qz144 1 16))) ep586

noncomputable def ep588 := nat_lit 13773189072999805459378470912000

noncomputable def ep589 := nat_lit 479130363073493134682882089131088372163

noncomputable def ep590 := nat_lit 72849379301952758649529046414496104448000

noncomputable def ep591 := nat_lit 24655738617541533140619641

noncomputable def ep592 := nat_lit 6886594536499902729689235456000

noncomputable def ep593 := nat_lit 435990066399525725095548878251564381

noncomputable def ep594 := nat_lit 36424689650976379324764523207248052224000

noncomputable def ep595 := nat_lit 397294729542332137676506526924369193498204034880149892628480000

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.re (zetaApproximant qz144 1 16)) 524287 524288 7462117

noncomputable def ep597 := nat_lit 110037022339296017379014329

noncomputable def ep598 := nat_lit 26270273347854243201024000

noncomputable def ep599 := nat_lit 9429785309889912068258358527

noncomputable def ep600 := nat_lit 1910558169769395545280872448000

noncomputable def ep601 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) Bool.true 524287 524288 7462117

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21412371) qz20)

noncomputable def ep602 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164) qz404 Bool.false 21412371 524288 99

noncomputable def ep603 := nat_lit 1787139715161322083566599

noncomputable def ep604 := nat_lit 4766236672000000000000000000

noncomputable def ep605 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164) Bool.false 367861740463828707633 9007199254740992000 ep603 ep604

noncomputable def ep606 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164 138635607020660000829 1801439850948198400 639834926661322083566599 ep604 2366987571 65536000

noncomputable def ep607 := nat_lit 4821637404607495636687257600

noncomputable def ep608 := nat_lit 2383118336000000000000000000

noncomputable def ep609 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 44589396740136578783 900719925474099200 561288728872274116557693 ep608 Bool.false 138635607020660000829 1801439850948198400

noncomputable def ep610 := @Enclosure.Complex.IsNear.subLitP qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 38370804231508166183 900719925474099200 544904728850826051533693 ep608 Bool.false 144209393370112717629 1801439850948198400 574298926656555846894599

noncomputable def ep611 := nat_lit 200812790543554305270808555833786368

noncomputable def ep612 := nat_lit 39022454257407931180376908653133824

noncomputable abbrev qz405 := (@HSub.hSub Complex Complex Complex qz474 qz485 qz477)

noncomputable abbrev qz406 := (Complex.log qz485)

noncomputable abbrev qz165 := (@HSub.hSub Complex Complex Complex qz315 (@HMul.hMul Complex Complex Complex qz314 qz405 qz406) qz402)

noncomputable abbrev qz166 := qz402

noncomputable def ep613 := @Enclosure.Complex.IsNear.of_eq qz162 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz165 qz50) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k)))))) Bool.true 38370804231508166183

noncomputable def ep614 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz165 qz50) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) Bool.true 38370973027183199783 900719925474099200

noncomputable def ep615 := nat_lit 329602698591091973025836302336

noncomputable def ep616 := nat_lit 1548436570751583365125594152960000

noncomputable def ep617 := @ep614 2078643404221961747 9090875000000000000000 Bool.false 721070636505421299761 9007199254740992000 17525500020778758443 145454000000000000000000 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000 Bool.true ep615 38370804231508166183 900719925474099200 544904728850826051533693 ep608 Bool.false ep616

noncomputable def ep618 := @Enclosure.Complex.IsNear.addLitP qz165 qz50 Bool.true 39198678508625298983 900719925474099200 32426000003440059827 145454000000000000000000

noncomputable def ep619 := nat_lit 5029360176618956361957376

noncomputable def ep620 := @ep618 Bool.false 721070636505421299761 9007199254740992000 17525500020778758443 145454000000000000000000 Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 Bool.true ep619 38370973027183199783 900719925474099200 2078643404221961747 9090875000000000000000 Bool.false 721070636505421299761 721070636505421299761 9007199254740992000

noncomputable abbrev qz167 := (@HMul.hMul Complex Complex Complex qz314 qz405 qz406)

noncomputable def ep621 := @Enclosure.Complex.IsNear.subLitP qz167 qz166 Bool.true 37172058676308575783 900719925474099200 32426000003440059827 145454000000000000000000 Bool.false 1005256780191754338353

noncomputable def ep622 := nat_lit 2884282546021685199044000

noncomputable def ep623 := @ep621 9007199254740992000 17525500020778758443 145454000000000000000000 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 Bool.true 156794714034501195932000 39198678508625298983 900719925474099200 32426000003440059827 145454000000000000000000 Bool.false ep622 721070636505421299761 9007199254740992000 17525500020778758443 145454000000000000000000

noncomputable abbrev qz168 := qz405

noncomputable abbrev qz169 := qz406

noncomputable def ep624 := @Enclosure.Complex.IsNear.mul qz168 qz169 Bool.true 37172058676308575783 900719925474099200 32426000003440059827 145454000000000000000000 Bool.false 1005256780191754338353 9007199254740992000 17525500020778758443

noncomputable abbrev qz170 := (Complex.re qz405)

noncomputable abbrev qz171 := (Complex.re qz406)

noncomputable abbrev qz172 := (Complex.im qz405)

noncomputable abbrev qz173 := (Complex.im qz406)

noncomputable def ep625 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz170 qz171) (@HMul.hMul Real Real Real qz0 qz172 qz173) 217784977004830921 36028797018963968 3500000004581801 581816000000000000000 5327085387678668601 112589990684262400

noncomputable def ep626 := nat_lit 167408069603217514684557655034298368

noncomputable def ep627 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz171 7000 4000 0 1 31112139572118703 9007199254740992 500000000654543 145454000000000000000

noncomputable def ep628 := @Enclosure.Complex.IsNear.re_isNear qz168 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable abbrev qz407 := (Enclosure.sfrac Bool.false 126204 4000)

noncomputable abbrev qz174 := qz407

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq qz168 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz174) Bool.false 7000 4000 0 1 Bool.false 126204 4000 0

noncomputable abbrev qz408 := (Complex.log (Complex.mk qz65 qz174))

noncomputable def ep630 := @Enclosure.Complex.IsNear.of_eq qz169 qz408 Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep631 := nat_lit 716240444564264294568200230424197544953405785569636439697480328239743435443511845199688504559877035151851520

noncomputable def ep632 := nat_lit 26591681868544723072078338383359816903719699591733841952323826958281563851642914785243180687633861106991104

noncomputable def ep633 := nat_lit 804502015872228639047265110910785499907445531589906569908374174378366432802002414731796560031850168320

noncomputable def ep634 := BSN.log_dyadic_bound 7816449616 24200449616 6 5 ep631 524288 145454 ep632 ep633 351251 32016899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7816449616) (BSN.artanhQ 24200449616) 0 5 ep632 ep631 ep633 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 16008449616 16000000))

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz409 1 2 0 1 31112139572118703 4503599627370496 500000000654543 72727000000000000000 31112139572118703 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 16008449616 16000000 31112139572118703 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16008449616) qz334)) Bool.false 130493771455895764467712 18889465931478580854784 1000000001309086 145454000000000000000 31112139572118703 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 16008449616 16000000 9 32016899232 16384000000 351251 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep634 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep636 := BSN.arctan_dyadic_bound_f 9000 126204 1 0 524288 145454 0 1 1 0 1 1 37325 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz410 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 126204)))

noncomputable def ep637 := @Enclosure.Real.IsNear.subLit_ff_p qz67 qz410 884279719003555 562949953421312 1 2000000000000000 37325 524288 1 145454 442605138305485373440 844202305422755 562949953421312 1000000000072727 145454000000000000000 qz68 (ep636 rfl) rfl rfl

noncomputable abbrev qz411 := (Complex.mk qz65 qz174)

noncomputable abbrev qz412 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 126204) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep638 := @Enclosure.Complex.IsNear.re_isNear qz169 Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (ep630 (@congrArg Complex Complex qz166 qz411 Complex.log (BSN.w_shift_mk qz153 Bool.false 63102 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz408 Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz408) (@HMul.hMul Real Real Real qz0 qz66 qz409) Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 9000 126204 4000 16008449616 16000000 rfl rfl rfl) (ep635 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz408) qz412 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 9000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz412 (@HSub.hSub Real Real Real qz318 qz67 qz410) Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 126204 9000 rfl rfl) ep637))))

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz173 126204 4000 0 1 844202305422755 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep640 := @Enclosure.Complex.IsNear.im_isNear qz168 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable def ep641 := @Enclosure.Complex.IsNear.im_isNear qz169 Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (ep630 (@congrArg Complex Complex qz166 qz411 Complex.log (BSN.w_shift_mk qz153 Bool.false 63102 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz408 Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz408) (@HMul.hMul Real Real Real qz0 qz66 qz409) Bool.false 31112139572118703 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 9000 126204 4000 16008449616 16000000 rfl rfl rfl) (ep635 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz408) qz412 Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 9000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz412 (@HSub.hSub Real Real Real qz318 qz67 qz410) Bool.false 844202305422755 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 126204 9000 rfl rfl) ep637))))

noncomputable abbrev qz413 := (Enclosure.Real.IsNear.const Bool.false 126204 4000)

noncomputable abbrev qz175 := (@ep629 1 (BSN.w_sub_half_mk qz393 Bool.false 63102 1000 2 qz394 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz407 Bool.false 7000 4000 0 1 Bool.false 126204 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz413))

noncomputable def ep642 := @ep625 31551000002294609577 145454000000000000000000 ep626 37172058676308575783 900719925474099200 32426000003440059827 145454000000000000000000 (@ep627 217784977004830921 36028797018963968 3500000004581801 581816000000000000000 (ep628 qz175) ep638 rfl) (@ep639 5327085387678668601 112589990684262400 31551000002294609577 145454000000000000000000 (ep640 qz175) ep641 rfl) rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz170 qz173) (@HMul.hMul Real Real Real qz0 qz172 qz171) 5909416137959285 2251799813685248 7000000000509089 581816000000000000000 981619115639917198353 9007199254740992000

noncomputable def ep644 := nat_lit 2263637030341624721358063404836716544

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_ff qz170 qz173 7000 4000 0 1 844202305422755 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff qz172 qz171 126204 4000 0 1 31112139572118703 9007199254740992 500000000654543 145454000000000000000

noncomputable def ep647 := @ep643 15775500020651486193 145454000000000000000000 ep644 1005256780191754338353 9007199254740992000 17525500020778758443 145454000000000000000000 (@ep645 5909416137959285 2251799813685248 7000000000509089 581816000000000000000 (ep628 qz175) ep641 rfl) (@ep646 981619115639917198353 9007199254740992000 15775500020651486193 145454000000000000000000 (ep640 qz175) ep638 rfl) rfl

noncomputable def ep648 := @Enclosure.Complex.IsNear.of_eq qz166 qz411 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 (BSN.w_shift_mk qz153 Bool.false 63102 1000 2 qz154 rfl)

noncomputable abbrev qz414 := (ep648 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 126204 4000) Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 126204 4000)))

noncomputable abbrev qz176 := qz414

noncomputable def ep649 := ep623 (@ep624 145454000000000000000000 (ep642 rfl) (ep647 rfl)) qz176 rfl rfl rfl rfl rfl rfl

noncomputable def ep650 := @ep620 17525500020778758443 145454000000000000000000 (ep649 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz71 (↑qz3) Bool.false 120447 131072 3 524288 Bool.false 0 1 0 1 (@ep223 131072 3 524288 (ep225 rfl) (ep227 rfl) rfl rfl) (@ep228 1 0 1 (ep230 rfl) (ep232 rfl) rfl rfl))

noncomputable abbrev qz415 := (@HPow.hPow Complex Int Complex qz479 qz485 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz177 := qz415

noncomputable def ep651 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz177)) Bool.false 1609761 8589934592 3 8589934592

noncomputable def ep652 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz177) Bool.false 0 1 0 1 Bool.false

noncomputable def ep653 := @ep652 0 1 0 1 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000 Bool.false 1609761 1609761 8589934592 3 8589934592 Bool.true 5643285479 5643285479 2147483648000 10517

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz45 (@HMul.hMul Complex Complex Complex qz44 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz53 qz166 (@HSub.hSub Int Int Int qz327 qz55 (@HMul.hMul Int Int Int qz328 qz56 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep655 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74) qz177 Bool.false 1609761 8589934592 3 8589934592 Bool.true 5643285479 2147483648000 10517 2147483648000

noncomputable abbrev qz178 := (Complex.re qz415)

noncomputable abbrev qz179 := (Complex.im qz415)

noncomputable def ep656 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz178) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz179) 1609761 8589934592 3 8589934592 0 1 0

noncomputable def ep657 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz178 1 12 0 1 4829283 2147483648 9 2147483648 1609761

noncomputable def ep658 := @Enclosure.Complex.IsNear.re_isNear qz177 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551 536870912000

noncomputable abbrev qz416 := (@HPow.hPow Complex Nat Complex qz480 qz485 1)

noncomputable abbrev qz180 := (@Inv.inv Complex Complex.instInv qz416)

noncomputable def ep659 := @Enclosure.Complex.IsNear.of_eq qz177 qz180 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_parts qz180 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551

noncomputable abbrev qz181 := (Complex.re qz416)

noncomputable abbrev qz182 := qz416

noncomputable def ep661 := @Enclosure.Real.IsNear.mulLit_ff qz181 (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182)) 9000 4000 0 1 536587 536870912 1 536870912

noncomputable def ep662 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable def ep663 := @Enclosure.Complex.IsNear.of_eq qz182 qz166 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0

noncomputable def ep664 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182)) Bool.false 536587 536870912 1 536870912 536587 536870912 1

noncomputable abbrev qz183 := (Complex.im qz416)

noncomputable def ep665 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 qz181 qz181) (@HMul.hMul Real Real Real qz0 qz183 qz183)) Bool.false 1000528101 1000000 0 1

noncomputable def ep666 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz181 qz181) (@HMul.hMul Real Real Real qz0 qz183 qz183) 81 16 0 1 995465601 1000000

noncomputable def ep667 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz181 9000 4000 0 1 9000 4000 0 1

noncomputable def ep668 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz183 126204 4000 0 1 126204 4000 0 1

noncomputable def ep669 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 9000 4000 0 1 Bool.false 126204 4000 0 1

noncomputable abbrev qz184 := (ep662 (@ep663 1 (BSN.pow_one_c qz402) qz414))

noncomputable abbrev qz185 := (ep669 (@ep663 1 (BSN.pow_one_c qz402) qz414))

noncomputable def ep670 := @ep666 0 1 16008449616 1000528101 1000000 0 1 (@ep667 81 16 0 1 qz184 qz184 rfl) (@ep668 995465601 1000000 0 1 qz185 qz185 rfl)

noncomputable def ep671 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182) 1000528101 1000000 0 1 268293 268294 268435456 (ep665 (Enclosure.Complex.normSq_eq_mul_add_mul qz182) (ep670 rfl rfl)) rfl

noncomputable def ep672 := @Enclosure.Real.IsNear.of_eq (Complex.re qz180) (@HMul.hMul Real Real Real qz0 qz181 (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182))) Bool.false 4829283 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz182) (@ep661 4829283 2147483648 9 2147483648 qz184 (@ep664 536870912 (ep671 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep673 := @Enclosure.Real.IsNear.of_eq (Complex.im qz180) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz183) (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182))) Bool.true 16929856437 536870912000 31551 536870912000 (Enclosure.Complex.inv_im_eq_mul qz182)

noncomputable def ep674 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz183) (@Inv.inv Real Real.instInv (@DFunLike.coe qz80 Complex (fun (x : Complex) => Real) qz81 Complex.normSq qz182)) 126204 4000 0 1 536587 536870912 1

noncomputable def ep675 := @ep674 536870912 16929856437 536870912000 31551 536870912000 (@Enclosure.Real.IsNear.neg qz183 Bool.false 126204 4000 0 1 qz185) (@ep664 536870912 (ep671 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep676 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz179 0 1 0 1 16929856437 536870912000 31551 536870912000 0

noncomputable def ep677 := @Enclosure.Complex.IsNear.im_isNear qz177 Bool.false 4829283 2147483648 9 2147483648 Bool.true 16929856437 536870912000 31551 536870912000

noncomputable abbrev qz186 := (@ep659 536870912000 (BSN.zpow_one_sub_two_mul qz402 1 1 rfl rfl) (@ep660 536870912000 ep672 (ep673 ep675)))

noncomputable def ep678 := @ep656 1 1609761 1609761 8589934592 3 8589934592 (@ep657 8589934592 3 8589934592 ep242 (ep658 qz186) rfl) (@ep676 1 0 1 ep262 (ep677 qz186) rfl) rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz179) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz178) 5643285479 2147483648000 10517 2147483648000 0 1 0

noncomputable def ep680 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz179 1 12 0 1 16929856437 536870912000 31551 536870912000 5643285479

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 (@Rat.cast Complex Complex.instRatCast (bernoulli qz73)) qz74)) qz178 0 1 0 1 4829283 2147483648 9 2147483648 0

noncomputable def ep682 := @ep679 1 5643285479 5643285479 2147483648000 10517 2147483648000 (@ep680 2147483648000 10517 2147483648000 ep242 (ep677 qz186) rfl) (@ep681 1 0 1 ep262 (ep658 qz186) rfl) rfl

noncomputable def ep683 := @ep653 2147483648000 (@ep654 0 1 0 1 (BSN.stirling_sum_base qz166) qz87) (ep655 (ep678 rfl) (ep682 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep684 := @ep617 144209393370112717629 1801439850948198400 574298926656555846894599 ep604 (ep650 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep651 Bool.true 5643285479 2147483648000 10517 2147483648000 (BSN.stirling_sum_succ qz166 0 1 rfl) (ep683 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep685 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz153 2) Bool.false 31092962543142063 4503599627370496 500000000654543 72727000000000000000 Bool.false 870904117101987 281474976710656

noncomputable abbrev qz187 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz403 qz339))

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz153 1) qz187) Bool.false 31092962543142063 4503599627370496 500000000654543 72727000000000000000 Bool.false 870904117101987 281474976710656 1000000000072727 72727000000000000000

noncomputable def ep687 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 1) qz187 Bool.false 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000 Bool.false

noncomputable def ep688 := nat_lit 560121018092557538340777851092992

noncomputable def ep689 := nat_lit 980550864313984866482166693888

noncomputable abbrev qz188 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz271 qz403 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz153 0) qz188) Bool.false 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep691 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 0) qz188 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz417 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz174))

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq qz188 qz417 Bool.false 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep693 := nat_lit 692912639692736604420311604543779027072546753571945732499180369596291553449328324211471713394310059151851520

noncomputable def ep694 := nat_lit 25345078892645866746941203327662774387809283655346852707323372041879395861353252468485083912993425906991104

noncomputable def ep695 := nat_lit 725853246623388114637466398311028570111632484724991619182457631729963376392971484758164781215850168320

noncomputable def ep696 := BSN.log_dyadic_bound 7736449616 24120449616 6 5 ep693 524288 145454 ep694 ep695 348624 31856899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7736449616) (BSN.artanhQ 24120449616) 0 5 ep694 ep693 ep695 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep697 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log (Enclosure.sfrac Bool.false 15928449616 16000000)) 1 2 0 1 31089573813945519 4503599627370496 500000000654543 72727000000000000000 31089573813945519 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 15928449616 16000000 31089573813945519 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15928449616) qz334)) Bool.false 130399123806126946123776 18889465931478580854784 1000000001309086 145454000000000000000 31089573813945519 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 15928449616 16000000 9 31856899232 16384000000 348624 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep696 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep698 := BSN.arctan_dyadic_bound_f 1000 126204 1 0 524288 145454 0 1 1 0 1 1 4154 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 126204)

noncomputable def ep699 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz418)) 884279719003555 562949953421312 1 2000000000000000 4154 524288 1 145454 461278751210423713792 879819395466659 562949953421312 1000000000072727 145454000000000000000 qz68 (ep698 rfl) rfl rfl

noncomputable abbrev qz189 := (@HAdd.hAdd Complex Complex Complex qz271 qz403 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz419 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz174)

noncomputable def ep700 := @ep691 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000 Bool.false 31089573813945519 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 879819395466659 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz153) qz87) (ep692 (@congrArg Complex Complex qz189 qz419 Complex.log (BSN.w_shift_mk qz153 Bool.false 63102 1000 0 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz417 Bool.false 31089573813945519 9007199254740992 500000000654543 145454000000000000000 Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz417) (@HMul.hMul Real Real Real qz0 qz66 (Real.log (Enclosure.sfrac Bool.false 15928449616 16000000))) Bool.false 31089573813945519 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 1000 126204 4000 15928449616 16000000 rfl rfl rfl) (ep697 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz417) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz418 qz345)) Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 1000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz418 qz345)) (@HSub.hSub Real Real Real qz318 qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz345 qz418))) Bool.false 879819395466659 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 126204 1000 rfl rfl) ep699)))) rfl rfl

noncomputable abbrev qz420 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz174))

noncomputable def ep701 := @Enclosure.Complex.IsNear.of_eq qz187 qz420 Bool.false 31096351272338607 9007199254740992 500000000654543 145454000000000000000 Bool.false 861988838737315 562949953421312 1000000000072727 145454000000000000000

noncomputable def ep702 := nat_lit 699838116787715779982656807111554726887291619378534140545864362213629056727125551308260991742380151951851520

noncomputable def ep703 := nat_lit 25713600341310037446787508424594765257399462942336782549583601226431131183849729345894892281065556466991104

noncomputable def ep704 := nat_lit 748687608023801390563050488278996258902650841174752335923914027751508431511137228426708714860650168320

noncomputable def ep705 := BSN.log_dyadic_bound 7760449616 24144449616 6 5 ep702 524288 145454 ep703 ep704 349413 31904899232 16384000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7760449616) (BSN.artanhQ 24144449616) 0 5 ep703 ep702 ep704 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep706 := @Enclosure.Real.IsNear.mulLit_ff qz66 (Real.log (Enclosure.sfrac Bool.false 15952449616 16000000)) 1 2 0 1 31096351272338607 4503599627370496 500000000654543 72727000000000000000 31096351272338607 9007199254740992 500000000654543 145454000000000000000 qz333 (BSN.isNear_log_sfrac 15952449616 16000000 31096351272338607 4503599627370496 500000000654543 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 15952449616) qz334)) Bool.false 130427550526974908694528 18889465931478580854784 1000000001309086 145454000000000000000 31096351272338607 4503599627370496 500000000654543 72727000000000000000 (BSN.log_rat_reduce_isNear 15952449616 16000000 9 31904899232 16384000000 349413 524288 24973259072661432 36028797018963968 145454 1000000000000000 rfl rfl rfl rfl (ep705 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep707 := BSN.arctan_dyadic_bound_f 5000 126204 1 0 524288 145454 0 1 1 0 1 1 20760 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 126204) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 126204) 0 0 rfl) rfl rfl rfl

noncomputable def ep708 := @Enclosure.Real.IsNear.subLit_ff_p qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz418)) 884279719003555 562949953421312 1 2000000000000000 20760 524288 1 145454 451930404283909406720 861988838737315 562949953421312 1000000000072727 145454000000000000000 qz68 (ep707 rfl) rfl rfl

noncomputable abbrev qz190 := (@HAdd.hAdd Complex Complex Complex qz271 qz403 qz339)

noncomputable abbrev qz421 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz174)

noncomputable def ep709 := @ep687 31096351272338607 9007199254740992 500000000654543 145454000000000000000 Bool.false 861988838737315 562949953421312 1000000000072727 145454000000000000000 Bool.false ep688 31092962543142063 4503599627370496 500000000654543 72727000000000000000 Bool.false ep689 870904117101987 281474976710656 1000000000072727 72727000000000000000 (ep690 (BSN.log_sum_c_succ qz153 0 1 rfl) (ep700 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep701 (@congrArg Complex Complex qz190 qz421 Complex.log (BSN.w_shift_mk qz153 Bool.false 63102 1000 1 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz420 Bool.false 31096351272338607 9007199254740992 500000000654543 145454000000000000000 Bool.false 861988838737315 562949953421312 1000000000072727 145454000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz420) (@HMul.hMul Real Real Real qz0 qz66 (Real.log (Enclosure.sfrac Bool.false 15952449616 16000000))) Bool.false 31096351272338607 9007199254740992 500000000654543 145454000000000000000 (Enclosure.clog_re_eq 5000 126204 4000 15952449616 16000000 rfl rfl rfl) (ep706 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz420) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz418 qz349)) Bool.false 861988838737315 562949953421312 1000000000072727 145454000000000000000 (Enclosure.clog_im_eq 5000 126204 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz418 qz349)) (@HSub.hSub Real Real Real qz318 qz67 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz349 qz418))) Bool.false 861988838737315 562949953421312 1000000000072727 145454000000000000000 (BSN.arctan_recip 126204 5000 rfl rfl) ep708)))) rfl rfl

noncomputable def ep710 := @ep610 ep604 Bool.false 31092962543142063 4503599627370496 500000000654543 72727000000000000000 Bool.false 870904117101987 281474976710656 1000000000072727 72727000000000000000 Bool.true ep611 44589396740136578783 900719925474099200 561288728872274116557693 ep608 Bool.false ep612 138635607020660000829 1801439850948198400 639834926661322083566599 ep604 (@ep613 900719925474099200 544904728850826051533693 ep608 Bool.false 144209393370112717629 1801439850948198400 574298926656555846894599 ep604 (BSN.logGammaStirling_unfold 1 qz166) (ep684 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep685 1000000000072727 72727000000000000000 (BSN.log_sum_c_eq qz153 2) (ep686 (BSN.log_sum_c_succ qz153 1 2 rfl) (ep709 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz191 := (@HDiv.hDiv Real Real Real qz268 qz393 (2 : Real))

noncomputable def ep711 := @Enclosure.Real.IsNear.mulLit_ff qz191 (Real.log Real.pi) 63102 2000 0 1 75021 65536 1 131072 2366987571 65536000 31551 131072000 (@Enclosure.Real.IsNear.of_eq qz191 (Enclosure.sfrac Bool.false 63102 2000) Bool.false 63102 2000 0 1 (BSN.t_half_eq qz153 Bool.false 63102 1000 qz154) (Enclosure.Real.IsNear.const Bool.false 63102 2000)) EMRow14.d5 rfl

noncomputable def ep712 := @ep606 31551 131072000 ep607 367861740463828707633 9007199254740992000 ep603 ep604 (@ep609 639834926661322083566599 ep604 (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep711 rfl rfl

noncomputable def ep713 := BSN.cos_dyadic_bound_f 163268 1073741824 1 0 524288 145597 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 163268) qz280 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 163268) qz281 0 0 rfl) rfl rfl

noncomputable def ep714 := @ep602 262144 Bool.true 524287 524288 1 72727 (@ep605 21412371 524288 99 262144 ep712 rfl) (Enclosure.sfrac_false_div 21412371 524288) (BSN.cos_reduce2 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11488985477097193472) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 21412371 524288 226375608064910080 72057594037927936 6 11488985477097193472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 11488985477097193472 75557863725914323419136 163268 1073741824 145597 145454 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep715 := nat_lit 13135136673927121600512000

noncomputable def ep716 := nat_lit 1568168743047746349287067259

noncomputable def ep717 := nat_lit 318426361628232590880145408000

noncomputable abbrev qz192 := qz392

noncomputable abbrev qz422 := (@HPow.hPow Complex Complex Complex qz468 qz481 qz483)

noncomputable abbrev qz193 := qz422

noncomputable abbrev qz194 := (@HAdd.hAdd Complex Complex Complex qz271 (@HDiv.hDiv Complex Complex Complex qz323 qz352 (@HSub.hSub Complex Complex Complex qz315 qz391 (1 : Complex))) qz322)

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz144 1 16) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz192) (@HMul.hMul Complex Complex Complex qz44 qz193 (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) Bool.false ep597 ep598 ep599

noncomputable def ep719 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz192) (@HMul.hMul Complex Complex Complex qz44 qz193 (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) Bool.false 1136282412459 274877906944 96112996692515 19991045538316288

noncomputable def ep720 := nat_lit 1441719400895344384550329

noncomputable def ep721 := nat_lit 244199158332913137312918527

noncomputable def ep722 := nat_lit 1497790670862570891157321

noncomputable def ep723 := nat_lit 40768124350341591477883259

noncomputable def ep724 := nat_lit 30246746386975859859578507505304600576

noncomputable def ep725 := nat_lit 42894416616127650333432517375295488

noncomputable def ep726 := @ep719 Bool.true 18937693997 137438953472 47945677561837 9995522769158144 Bool.false ep720 ep598 ep721 ep600 Bool.false ep722 ep715 ep723 ep717 Bool.false ep724 ep597 ep598 ep599 ep600 Bool.true ep725 312097957184070039754679 ep715

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 16, @HPow.hPow Complex Complex Complex qz93 (@Nat.cast Complex Complex.instNatCast n) qz192) (BSN.headSumC qz144 16) Bool.false 1136282412459 274877906944 96112996692515 19991045538316288 Bool.true 18937693997 137438953472 47945677561837

noncomputable abbrev qz195 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 15) qz392)

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 16) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 15) qz195) Bool.false 1136282412459 274877906944 96112996692515 19991045538316288 Bool.true 18937693997 137438953472 47945677561837 9995522769158144

noncomputable def ep729 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 15) qz195 Bool.false 556519402823 137438953472 45770062193417 9995522769158144 Bool.false 455998215 4294967296 11411867899647 2498880692289536 Bool.false

noncomputable abbrev qz196 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 14) qz392)

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 15) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 14) qz196) Bool.false 556519402823 137438953472 45770062193417 9995522769158144 Bool.false 455998215 4294967296 11411867899647 2498880692289536

noncomputable def ep731 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 14) qz196 Bool.false 148309913051 34359738368 21695401163635 4997761384579072 Bool.false 27335549649 274877906944 86573581943719 19991045538316288 Bool.true

noncomputable abbrev qz197 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 13) qz392)

noncomputable def ep732 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 13) qz197) Bool.false 148309913051 34359738368 21695401163635 4997761384579072 Bool.false 27335549649 274877906944 86573581943719 19991045538316288

noncomputable def ep733 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 13) qz197 Bool.false 73863625587 17179869184 20470165736057 4997761384579072 Bool.true 48758899117 274877906944 81636913094657 19991045538316288 Bool.false

noncomputable abbrev qz198 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 12) qz392)

noncomputable def ep734 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 12) qz198) Bool.false 73863625587 17179869184 20470165736057 4997761384579072 Bool.true 48758899117 274877906944 81636913094657 19991045538316288

noncomputable def ep735 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 12) qz198 Bool.false 1105494978927 274877906944 76745339279033 19991045538316288 Bool.true 17616910733 68719476736 19131958241853 4997761384579072 Bool.false

noncomputable abbrev qz199 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 11) qz392)

noncomputable def ep736 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 11) qz199) Bool.false 1105494978927 274877906944 76745339279033 19991045538316288 Bool.true 17616910733 68719476736 19131958241853 4997761384579072

noncomputable def ep737 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 11) qz199 Bool.false 1033380919917 274877906944 71386794524903 19991045538316288 Bool.true 29620819727 274877906944 71183673250247 19991045538316288 Bool.false

noncomputable abbrev qz200 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 10) qz392)

noncomputable def ep738 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz144 10) qz200) Bool.false 1033380919917 274877906944 71386794524903 19991045538316288 Bool.true 29620819727 274877906944 71183673250247 19991045538316288

noncomputable def ep739 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 10) qz200 Bool.false 485923798911 137438953472 16443625016149 4997761384579072 Bool.false 7943806027 68719476736 8196429875987 2498880692289536 Bool.false

noncomputable abbrev qz201 := (@HPow.hPow Complex Complex Complex qz272 (@Nat.cast Complex Complex.instNatCast 9) qz392)

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 10) (@HAdd.hAdd Complex Complex Complex qz5 qz143 qz201) Bool.false 485923798911 137438953472 16443625016149 4997761384579072 Bool.false 7943806027 68719476736 8196429875987 2498880692289536

noncomputable def ep741 := @Enclosure.Complex.IsNear.addLitP qz143 qz201 Bool.false 444076798561 137438953472 7481532053137 2498880692289536 Bool.false 69066327811 274877906944 59668505768709 19991045538316288 Bool.false

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep742 := @Enclosure.Complex.IsNear.of_eq qz201 (Complex.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz202)))) Bool.false 20923500175 68719476736 1480560909875 4997761384579072 Bool.true 37291103703 274877906944 5902933239187 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 9 qz154 rfl)

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz109 63102 1000 0 1 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 312210326792408295771 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz355) Bool.false 20752195215788806766592 9444732965739290427392 1000000000218181 72727000000000000000 9895417793173221 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep325 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep744 := nat_lit 41031602476778413826715657642501136

noncomputable def ep745 := BSN.cos_dyadic_bound_f 450069538 1073741824 2 1 524288 145597 ep744 ep75 ep744 ep744 ep76 ep744 478900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 450069538) qz280 0 1 ep744 ep75 ep744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 450069538) qz281 0 1 ep744 ep76 ep744 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz423 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 72692131) qz20)

noncomputable def ep746 := @Enclosure.Real.IsNear.cos_image qz202 qz423 Bool.false 72692131 524288 57 65536 Bool.false 478900 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 312210326792408295771 2251799813685248000 31551000006883828731 36363500000000000000000 72692131 524288 57 65536 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 72692131 524288) (BSN.cos_reduce0 qz423 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31670828199822294515712) qz23) 226375608064910080 72057594037927936 Bool.false 478900 524288 22 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 72692131 524288 226375608064910080 72057594037927936 22 31670828199822294515712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478900 524288 31670828199822294515712 75557863725914323419136 450069538 1073741824 145597 145454 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := BSN.sin_dyadic_bound_f 450069538 1073741824 2 1 524288 145597 ep744 ep79 ep744 ep744 ep80 ep744 213381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 450069538) qz284 0 1 ep744 ep79 ep744 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 450069538) qz285 0 1 ep744 ep80 ep744 rfl rfl rfl rfl) rfl rfl

noncomputable def ep748 := @Enclosure.Real.IsNear.sin_image qz202 qz423 Bool.false 72692131 524288 57 65536 Bool.false 213381 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 312210326792408295771 2251799813685248000 31551000006883828731 36363500000000000000000 72692131 524288 57 65536 (ep743 rfl) rfl) (Enclosure.sfrac_false_div 72692131 524288) (BSN.sin_reduce0 qz423 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 31670828199822294515712) qz23) 226375608064910080 72057594037927936 Bool.false 213381 524288 22 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 72692131 524288 226375608064910080 72057594037927936 22 31670828199822294515712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213381 524288 31670828199822294515712 75557863725914323419136 450069538 1073741824 145597 145454 (ep747 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep749 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz107 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz107 (@Neg.neg Real Real.instNeg (Real.sin qz202))) Bool.false 20923500175 68719476736 1480560909875 4997761384579072 Bool.true 37291103703 274877906944 5902933239187 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz107 (Real.cos qz202) 174763 524288 1 524288 119725 131072 4210975 4766236672 20923500175 68719476736 1480560909875 4997761384579072 qz357 (@Enclosure.Real.IsNear.recentre' (Real.cos qz202) Bool.false 478900 524288 4210975 4766236672 119725 131072 4210975 4766236672 (ep746 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz107 (@Neg.neg Real Real.instNeg (Real.sin qz202)) 174763 524288 1 524288 213381 524288 4210975 4766236672 37291103703 274877906944 5902933239187 19991045538316288 qz357 (@Enclosure.Real.IsNear.neg (Real.sin qz202) Bool.false 213381 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz202) Bool.false 213381 524288 4210975 4766236672 213381 524288 4210975 4766236672 (ep748 rfl rfl) rfl)) rfl)

noncomputable def ep750 := @ep741 20923500175 68719476736 1480560909875 4997761384579072 Bool.true 37291103703 274877906944 5902933239187 19991045538316288 Bool.false 33392429194733206634496 485923798911 137438953472 16443625016149 4997761384579072 Bool.false 8734307095483569405952 7943806027 68719476736 8196429875987 2498880692289536 EMRow14.d10 (ep742 ep749) rfl rfl

noncomputable abbrev qz203 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep751 := @Enclosure.Complex.IsNear.of_eq qz200 (Complex.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz203)))) Bool.false 61533322095 274877906944 5612294460307 19991045538316288 Bool.true 61396043835 274877906944 5612234242351 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 10 qz154 rfl)

noncomputable def ep752 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz112 63102 1000 0 1 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 327180986243841157467 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 21747274560655572598784 9444732965739290427392 1000000000218181 72727000000000000000 10369908600166117 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep336 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep753 := nat_lit 1123300473824501165433813784999737163863013694468780527068563042908416404641

noncomputable def ep754 := nat_lit 252917436700130885703978700458005442765462072550802738115261512114662561

noncomputable def ep755 := nat_lit 3369395586600103234530033397598295480703510159261239975729458605701019888801

noncomputable def ep756 := BSN.cos_dyadic_bound_f 842116829 1073741824 3 2 524288 145597 ep753 ep57 ep754 ep755 ep60 ep754 371141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 842116829) qz280 0 2 ep753 ep57 ep754 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 842116829) qz281 0 2 ep755 ep60 ep754 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz424 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 76177759) qz20)

noncomputable def ep757 := @Enclosure.Real.IsNear.cos_image qz203 qz424 Bool.false 76177759 524288 57 65536 Bool.false 371141 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 327180986243841157467 2251799813685248000 31551000006883828731 36363500000000000000000 76177759 524288 57 65536 (ep752 rfl) rfl) (Enclosure.sfrac_false_div 76177759 524288) (BSN.cos_reduce0 qz424 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59258703777749341831168) qz23) 226375608064910080 72057594037927936 Bool.false 371141 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 76177759 524288 226375608064910080 72057594037927936 23 59258703777749341831168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371141 524288 59258703777749341831168 75557863725914323419136 842116829 1073741824 145597 145454 (ep756 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep758 := nat_lit 502908974567098857717318826402288081

noncomputable def ep759 := BSN.sin_dyadic_bound_f 842116829 1073741824 2 1 524288 145597 ep758 ep79 ep758 ep758 ep80 ep758 370313 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 842116829) qz284 0 1 ep758 ep79 ep758 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 842116829) qz285 0 1 ep758 ep80 ep758 rfl rfl rfl rfl) rfl rfl

noncomputable def ep760 := @Enclosure.Real.IsNear.sin_image qz203 qz424 Bool.false 76177759 524288 57 65536 Bool.false 370313 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz203 Bool.false 327180986243841157467 2251799813685248000 31551000006883828731 36363500000000000000000 76177759 524288 57 65536 (ep752 rfl) rfl) (Enclosure.sfrac_false_div 76177759 524288) (BSN.sin_reduce0 qz424 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59258703777749341831168) qz23) 226375608064910080 72057594037927936 Bool.false 370313 524288 23 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 76177759 524288 226375608064910080 72057594037927936 23 59258703777749341831168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370313 524288 59258703777749341831168 75557863725914323419136 842116829 1073741824 145597 145454 (ep759 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep761 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz110 (Real.cos qz203)) (@HMul.hMul Real Real Real qz0 qz110 (@Neg.neg Real Real.instNeg (Real.sin qz203))) Bool.false 61533322095 274877906944 5612294460307 19991045538316288 Bool.true 61396043835 274877906944 5612234242351 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz110 (Real.cos qz203) 165795 524288 1 524288 371141 524288 4210975 4766236672 61533322095 274877906944 5612294460307 19991045538316288 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz203) Bool.false 371141 524288 4210975 4766236672 371141 524288 4210975 4766236672 (ep757 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz110 (@Neg.neg Real Real.instNeg (Real.sin qz203)) 165795 524288 1 524288 370313 524288 4210975 4766236672 61396043835 274877906944 5612234242351 19991045538316288 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz203) Bool.false 370313 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz203) Bool.false 370313 524288 4210975 4766236672 370313 524288 4210975 4766236672 (ep760 rfl rfl) rfl)) rfl)

noncomputable def ep762 := @ep739 61533322095 274877906944 5612294460307 19991045538316288 Bool.true 61396043835 274877906944 5612234242351 19991045538316288 Bool.false 142026792171325121101824 1033380919917 274877906944 71386794524903 19991045538316288 Bool.true 2035527232130826371072 29620819727 274877906944 71183673250247 19991045538316288 (ep740 (BSN.head_sum_c_succ qz144 9 10 rfl rfl) (ep750 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep751 ep761) rfl rfl

noncomputable abbrev qz204 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq qz199 (Complex.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz204)))) Bool.false 36057029505 137438953472 2679272377065 9995522769158144 Bool.true 40846823205 274877906944 5344159717165 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 11 qz154 rfl)

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz115 63102 1000 0 1 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 340723906928661391707 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 22647454054174387339264 9444732965739290427392 1000000000218181 72727000000000000000 10799147631728357 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep350 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep765 := nat_lit 93766911931076588276793641156897761

noncomputable def ep766 := BSN.cos_dyadic_bound_f 553365913 1073741824 2 1 524288 145597 ep765 ep75 ep765 ep765 ep76 ep765 456190 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553365913) qz280 0 1 ep765 ep75 ep765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553365913) qz281 0 1 ep765 ep76 ep765 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39665483) qz43)

noncomputable def ep767 := @Enclosure.Real.IsNear.cos_image qz204 qz425 Bool.false 39665483 262144 57 65536 Bool.false 456190 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 340723906928661391707 2251799813685248000 31551000006883828731 36363500000000000000000 39665483 262144 57 65536 (ep764 rfl) rfl) (Enclosure.sfrac_false_div 39665483 262144) (BSN.cos_reduce0 qz425 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19469832210156152160256) qz312) 226375608064910080 72057594037927936 Bool.false 456190 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 39665483 262144 226375608064910080 72057594037927936 24 19469832210156152160256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 456190 524288 19469832210156152160256 37778931862957161709568 553365913 1073741824 145597 145454 (ep766 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep768 := BSN.sin_dyadic_bound_f 553365913 1073741824 2 1 524288 145597 ep765 ep79 ep765 ep765 ep80 ep765 258395 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553365913) qz284 0 1 ep765 ep79 ep765 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553365913) qz285 0 1 ep765 ep80 ep765 rfl rfl rfl rfl) rfl rfl

noncomputable def ep769 := @Enclosure.Real.IsNear.sin_image qz204 qz425 Bool.false 39665483 262144 57 65536 Bool.false 258395 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz204 Bool.false 340723906928661391707 2251799813685248000 31551000006883828731 36363500000000000000000 39665483 262144 57 65536 (ep764 rfl) rfl) (Enclosure.sfrac_false_div 39665483 262144) (BSN.sin_reduce0 qz425 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19469832210156152160256) qz312) 226375608064910080 72057594037927936 Bool.false 258395 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 39665483 262144 226375608064910080 72057594037927936 24 19469832210156152160256 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 258395 524288 19469832210156152160256 37778931862957161709568 553365913 1073741824 145597 145454 (ep768 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep770 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz113 (Real.cos qz204)) (@HMul.hMul Real Real Real qz0 qz113 (@Neg.neg Real Real.instNeg (Real.sin qz204))) Bool.false 36057029505 137438953472 2679272377065 9995522769158144 Bool.true 40846823205 274877906944 5344159717165 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz113 (Real.cos qz204) 158079 524288 1 524288 228095 262144 4210975 4766236672 36057029505 137438953472 2679272377065 9995522769158144 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz204) Bool.false 456190 524288 4210975 4766236672 228095 262144 4210975 4766236672 (ep767 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz113 (@Neg.neg Real Real.instNeg (Real.sin qz204)) 158079 524288 1 524288 258395 524288 4210975 4766236672 40846823205 274877906944 5344159717165 19991045538316288 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz204) Bool.false 258395 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz204) Bool.false 258395 524288 4210975 4766236672 258395 524288 4210975 4766236672 (ep769 rfl rfl) rfl)) rfl)

noncomputable def ep771 := @ep737 36057029505 137438953472 2679272377065 9995522769158144 Bool.true 40846823205 274877906944 5344159717165 19991045538316288 Bool.false 151938072972277573484544 1105494978927 274877906944 76745339279033 19991045538316288 Bool.true 19369998196425315319808 17616910733 68719476736 19131958241853 4997761384579072 (ep738 (BSN.head_sum_c_succ qz144 10 11 rfl rfl) (ep762 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep763 ep770) rfl rfl

noncomputable abbrev qz205 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep772 := @Enclosure.Complex.IsNear.of_eq qz198 (Complex.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz205)))) Bool.false 76323030465 274877906944 5135323665195 19991045538316288 Bool.false 21708743815 274877906944 5109080127245 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 12 qz154 rfl)

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz118 63102 1000 0 1 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 353087886149023590747 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 23469270914176955449344 9444732965739290427392 1000000000218181 72727000000000000000 11191020447815397 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep774 := nat_lit 14979372747966382041223124453001122128998569294605152627768885900797909213440

noncomputable def ep775 := nat_lit 13861829834451789317536491767460553059448784666357499782898548318893056256

noncomputable def ep776 := nat_lit 39209247567799031020498838294998478966233335834506059025460484471478221086976

noncomputable def ep777 := BSN.sin_dyadic_bound_f 1389080998 1073741824 3 2 524288 145597 ep774 ep64 ep775 ep776 ep66 ep775 504285 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1389080998) qz284 0 2 ep774 ep64 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1389080998) qz285 0 2 ep776 ep66 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz426 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 82209679) qz20)

noncomputable def ep778 := @Enclosure.Real.IsNear.cos_image qz205 qz426 Bool.false 82209679 524288 57 65536 Bool.false 504285 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 353087886149023590747 2251799813685248000 31551000006883828731 36363500000000000000000 82209679 524288 57 65536 (ep773 rfl) rfl) (Enclosure.sfrac_false_div 82209679 524288) (BSN.cos_reduce3 qz426 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97747885428316861104128) qz23) 226375608064910080 72057594037927936 Bool.false 504285 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 82209679 524288 226375608064910080 72057594037927936 24 97747885428316861104128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 504285 524288 97747885428316861104128 75557863725914323419136 1389080998 1073741824 145597 145454 (ep777 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep779 := nat_lit 8328034562129968595931752025786161428581182401299021459775113744140568699136

noncomputable def ep780 := nat_lit 24956380026721002209160183093823563179624649634564349379759544135783919984896

noncomputable def ep781 := BSN.cos_dyadic_bound_f 1389080998 1073741824 3 2 524288 145597 ep779 ep57 ep775 ep780 ep60 ep775 143435 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1389080998) qz280 0 2 ep779 ep57 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1389080998) qz281 0 2 ep780 ep60 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable def ep782 := @Enclosure.Real.IsNear.sin_image qz205 qz426 Bool.false 82209679 524288 57 65536 Bool.true 143435 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 353087886149023590747 2251799813685248000 31551000006883828731 36363500000000000000000 82209679 524288 57 65536 (ep773 rfl) rfl) (Enclosure.sfrac_false_div 82209679 524288) (BSN.sin_reduce3 qz426 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 97747885428316861104128) qz23) 226375608064910080 72057594037927936 Bool.false 143435 524288 24 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 82209679 524288 226375608064910080 72057594037927936 24 97747885428316861104128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 143435 524288 97747885428316861104128 75557863725914323419136 1389080998 1073741824 145597 145454 (ep781 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep783 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz116 (Real.cos qz205)) (@HMul.hMul Real Real Real qz0 qz116 (@Neg.neg Real Real.instNeg (Real.sin qz205))) Bool.false 76323030465 274877906944 5135323665195 19991045538316288 Bool.false 21708743815 274877906944 5109080127245 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz116 (Real.cos qz205) 151349 524288 1 524288 504285 524288 4210975 4766236672 76323030465 274877906944 5135323665195 19991045538316288 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz205) Bool.false 504285 524288 4210975 4766236672 504285 524288 4210975 4766236672 (ep778 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz116 (@Neg.neg Real Real.instNeg (Real.sin qz205)) 151349 524288 1 524288 143435 524288 4210975 4766236672 21708743815 274877906944 5109080127245 19991045538316288 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz205) Bool.true 143435 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz205) Bool.true 143435 524288 4210975 4766236672 143435 524288 4210975 4766236672 (ep782 rfl rfl) rfl)) rfl)

noncomputable def ep784 := @ep735 76323030465 274877906944 5135323665195 19991045538316288 Bool.false 21708743815 274877906944 5109080127245 19991045538316288 Bool.false 324855660810397494018048 73863625587 17179869184 20470165736057 4997761384579072 Bool.true 3350686033543652442112 48758899117 274877906944 81636913094657 19991045538316288 (ep736 (BSN.head_sum_c_succ qz144 11 12 rfl rfl) (ep771 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep772 ep783) rfl rfl

noncomputable abbrev qz206 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep785 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz206)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz206)))) Bool.false 582661877 34359738368 612617713789 2498880692289536 Bool.false 38047224383 137438953472 2468334424531 9995522769158144 (BSN.cpow_neg_s_mk qz153 63102 1000 13 qz154 rfl)

noncomputable def ep786 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz121 63102 1000 0 1 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 72892202499437683167 450359962737049600 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 24225227133228857425920 9444732965739290427392 1000000000218181 72727000000000000000 11551488463034085 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep375 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep787 := BSN.sin_dyadic_bound_f 65692770 1073741824 1 0 524288 145597 0 1 1 0 1 1 32056 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 65692770) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 65692770) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz427 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 21214423) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep788 := @Enclosure.Real.IsNear.cos_image qz206 qz427 Bool.false 21214423 131072 57 65536 Bool.false 32056 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz206 Bool.false 72892202499437683167 450359962737049600 31551000006883828731 36363500000000000000000 21214423 131072 57 65536 (ep786 rfl) rfl) (Enclosure.sfrac_false_div 21214423 131072) (BSN.cos_reduce3 qz427 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1155679436521473048576) qz299) 226375608064910080 72057594037927936 Bool.false 32056 524288 25 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 21214423 131072 226375608064910080 72057594037927936 25 1155679436521473048576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 32056 524288 1155679436521473048576 18889465931478580854784 65692770 1073741824 145597 145454 (ep787 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep789 := BSN.cos_dyadic_bound_f 65692770 1073741824 1 0 524288 145597 0 1 1 0 1 1 523306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 65692770) qz280 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 65692770) qz281 0 0 rfl) rfl rfl

noncomputable def ep790 := @Enclosure.Real.IsNear.sin_image qz206 qz427 Bool.false 21214423 131072 57 65536 Bool.true 523306 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz206 Bool.false 72892202499437683167 450359962737049600 31551000006883828731 36363500000000000000000 21214423 131072 57 65536 (ep786 rfl) rfl) (Enclosure.sfrac_false_div 21214423 131072) (BSN.sin_reduce3 qz427 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1155679436521473048576) qz299) 226375608064910080 72057594037927936 Bool.false 523306 524288 25 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 21214423 131072 226375608064910080 72057594037927936 25 1155679436521473048576 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523306 524288 1155679436521473048576 18889465931478580854784 65692770 1073741824 145597 145454 (ep789 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep791 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz206)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz206))) Bool.false 582661877 34359738368 612617713789 2498880692289536 Bool.false 38047224383 137438953472 2468334424531 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz206) 145411 524288 1 524288 4007 65536 4210975 4766236672 582661877 34359738368 612617713789 2498880692289536 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz206) Bool.false 32056 524288 4210975 4766236672 4007 65536 4210975 4766236672 (ep788 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz119 (@Neg.neg Real Real.instNeg (Real.sin qz206)) 145411 524288 1 524288 261653 262144 4210975 4766236672 38047224383 137438953472 2468334424531 9995522769158144 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz206) Bool.true 261653 262144 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz206) Bool.true 523306 524288 4210975 4766236672 261653 262144 4210975 4766236672 (ep790 rfl rfl) rfl)) rfl)

noncomputable def ep792 := @ep733 582661877 34359738368 612617713789 2498880692289536 Bool.false 38047224383 137438953472 2468334424531 9995522769158144 Bool.false 2547944904906594320384 148309913051 34359738368 21695401163635 4997761384579072 Bool.false 3756969336340456931328 27335549649 274877906944 86573581943719 19991045538316288 (ep734 (BSN.head_sum_c_succ qz144 12 13 rfl rfl) (ep784 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep785 ep791) rfl rfl

noncomputable abbrev qz207 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz207)))) Bool.true 36720249381 137438953472 2379259866147 9995522769158144 Bool.false 1848336111 274877906944 4721361253457 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 14 qz154 rfl)

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz124 63102 1000 0 1 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 374991263453522323803 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 24925158572916270432256 9444732965739290427392 1000000000218181 72727000000000000000 11885241781671653 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep389 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep795 := BSN.cos_dyadic_bound_f 27018351 1073741824 1 0 524288 145597 0 1 1 0 1 1 524122 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 27018351) qz280 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 27018351) qz281 0 0 rfl) rfl rfl

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 87309457) qz20)

noncomputable def ep796 := @Enclosure.Real.IsNear.cos_image qz207 qz428 Bool.false 87309457 524288 57 65536 Bool.true 524122 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 374991263453522323803 2251799813685248000 31551000006883828731 36363500000000000000000 87309457 524288 57 65536 (ep794 rfl) rfl) (Enclosure.sfrac_false_div 87309457 524288) (BSN.cos_reduce2 qz428 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1901247435479936139264) qz23) 226375608064910080 72057594037927936 Bool.false 524122 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 87309457 524288 226375608064910080 72057594037927936 26 1901247435479936139264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524122 524288 1901247435479936139264 75557863725914323419136 27018351 1073741824 145597 145454 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := BSN.sin_dyadic_bound_f 27018351 1073741824 1 0 524288 145597 0 1 1 0 1 1 13191 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 27018351) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 27018351) qz285 0 0 rfl) rfl rfl

noncomputable def ep798 := @Enclosure.Real.IsNear.sin_image qz207 qz428 Bool.false 87309457 524288 57 65536 Bool.true 13191 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 374991263453522323803 2251799813685248000 31551000006883828731 36363500000000000000000 87309457 524288 57 65536 (ep794 rfl) rfl) (Enclosure.sfrac_false_div 87309457 524288) (BSN.sin_reduce2 qz428 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1901247435479936139264) qz23) 226375608064910080 72057594037927936 Bool.false 13191 524288 26 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 87309457 524288 226375608064910080 72057594037927936 26 1901247435479936139264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13191 524288 1901247435479936139264 75557863725914323419136 27018351 1073741824 145597 145454 (ep797 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep799 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz122 (Real.cos qz207)) (@HMul.hMul Real Real Real qz0 qz122 (@Neg.neg Real Real.instNeg (Real.sin qz207))) Bool.true 36720249381 137438953472 2379259866147 9995522769158144 Bool.false 1848336111 274877906944 4721361253457 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ft qz122 (Real.cos qz207) 140121 524288 1 524288 262061 262144 4210975 4766236672 36720249381 137438953472 2379259866147 9995522769158144 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz207) Bool.true 524122 524288 4210975 4766236672 262061 262144 4210975 4766236672 (ep796 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz122 (@Neg.neg Real Real.instNeg (Real.sin qz207)) 140121 524288 1 524288 13191 524288 4210975 4766236672 1848336111 274877906944 4721361253457 19991045538316288 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz207) Bool.true 13191 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz207) Bool.true 13191 524288 4210975 4766236672 13191 524288 4210975 4766236672 (ep798 rfl rfl) rfl)) rfl)

noncomputable def ep800 := @ep731 36720249381 137438953472 2379259866147 9995522769158144 Bool.false 1848336111 274877906944 4721361253457 19991045538316288 Bool.false 19121861077713880612864 556519402823 137438953472 45770062193417 9995522769158144 Bool.false 8022005434201606717440 455998215 4294967296 11411867899647 2498880692289536 (ep732 (BSN.head_sum_c_succ qz144 13 14 rfl rfl) (ep792 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep793 ep799) rfl rfl

noncomputable abbrev qz208 := (@HMul.hMul Real Real Real qz265 qz393 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq qz195 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)))) Bool.false 23243606813 274877906944 4572872305681 19991045538316288 Bool.true 33529636877 137438953472 2298205963249 9995522769158144 (BSN.cpow_neg_s_mk qz153 63102 1000 15 qz154 rfl)

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz127 63102 1000 0 1 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 384794636017286932827 2251799813685248000 31551000006883828731 36363500000000000000000 qz155 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 25576775395801252757504 9444732965739290427392 1000000000218181 72727000000000000000 12195956895733477 4503599627370496 1000000000218181 72727000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep400 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep803 := nat_lit 6962902118467996413564847533028791325719016653815251964710637063952421421056

noncomputable def ep804 := nat_lit 9695111219112863605056149863604905509358327878000083518305188195692773376

noncomputable def ep805 := nat_lit 20869316132965763513484430299359164166138333305689755727095300815465878716416

noncomputable def ep806 := BSN.cos_dyadic_bound_f 1328370124 1073741824 3 2 524288 145597 ep803 ep57 ep804 ep805 ep60 ep804 171703 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1328370124) qz280 0 2 ep803 ep57 ep804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1328370124) qz281 0 2 ep805 ep60 ep804 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz429 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44795991) qz43)

noncomputable def ep807 := @Enclosure.Real.IsNear.cos_image qz208 qz429 Bool.false 44795991 262144 57 65536 Bool.false 171703 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 384794636017286932827 2251799813685248000 31551000006883828731 36363500000000000000000 44795991 262144 57 65536 (ep802 rfl) rfl) (Enclosure.sfrac_false_div 44795991 262144) (BSN.cos_reduce0 qz429 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46737868748025854164992) qz312) 226375608064910080 72057594037927936 Bool.false 171703 524288 27 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 44795991 262144 226375608064910080 72057594037927936 27 46737868748025854164992 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 171703 524288 46737868748025854164992 37778931862957161709568 1328370124 1073741824 145597 145454 (ep806 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep808 := nat_lit 12525467724267103253532680639560940461886743314565053469664502564557804339200

noncomputable def ep809 := nat_lit 32789099573963849599129786956213769457926319007296473237710726888191699255296

noncomputable def ep810 := BSN.sin_dyadic_bound_f 1328370124 1073741824 3 2 524288 145597 ep808 ep64 ep804 ep809 ep66 ep804 495374 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1328370124) qz284 0 2 ep808 ep64 ep804 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1328370124) qz285 0 2 ep809 ep66 ep804 rfl rfl rfl rfl) rfl rfl

noncomputable def ep811 := @Enclosure.Real.IsNear.sin_image qz208 qz429 Bool.false 44795991 262144 57 65536 Bool.false 495374 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz208 Bool.false 384794636017286932827 2251799813685248000 31551000006883828731 36363500000000000000000 44795991 262144 57 65536 (ep802 rfl) rfl) (Enclosure.sfrac_false_div 44795991 262144) (BSN.sin_reduce0 qz429 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46737868748025854164992) qz312) 226375608064910080 72057594037927936 Bool.false 495374 524288 27 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q0 44795991 262144 226375608064910080 72057594037927936 27 46737868748025854164992 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 495374 524288 46737868748025854164992 37778931862957161709568 1328370124 1073741824 145597 145454 (ep810 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep812 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz208)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208))) Bool.false 23243606813 274877906944 4572872305681 19991045538316288 Bool.true 33529636877 137438953472 2298205963249 9995522769158144 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz208) 135371 524288 1 524288 171703 524288 4210975 4766236672 23243606813 274877906944 4572872305681 19991045538316288 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz208) Bool.false 171703 524288 4210975 4766236672 171703 524288 4210975 4766236672 (ep807 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz208)) 135371 524288 1 524288 247687 262144 4210975 4766236672 33529636877 137438953472 2298205963249 9995522769158144 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz208) Bool.false 247687 262144 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' (Real.sin qz208) Bool.false 495374 524288 4210975 4766236672 247687 262144 4210975 4766236672 (ep811 rfl rfl) rfl)) rfl)

noncomputable def ep813 := @ep729 23243606813 274877906944 4572872305681 19991045538316288 Bool.true 33529636877 137438953472 2298205963249 9995522769158144 Bool.false 156169465617004414107648 1136282412459 274877906944 96112996692515 19991045538316288 Bool.true 81336776378770522112 18937693997 137438953472 47945677561837 9995522769158144 (ep730 (BSN.head_sum_c_succ qz144 14 15 rfl rfl) (ep800 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep801 ep812) rfl rfl

noncomputable def ep814 := @Enclosure.Complex.IsNear.mul qz193 (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.false ep720 ep598 ep721 ep600 Bool.false

noncomputable abbrev qz209 := (Complex.re qz422)

noncomputable abbrev qz210 := (Complex.im qz422)

noncomputable def ep815 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz209 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz210 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) 924782036314166329607 13135136673927121600512 106137470001335038321759

noncomputable def ep816 := nat_lit 955279084884697772640436224

noncomputable def ep817 := nat_lit 8756757782618081067008000

noncomputable def ep818 := nat_lit 10641406110081020223133509

noncomputable def ep819 := nat_lit 636852723256465181760290816000

noncomputable def ep820 := nat_lit 6312393792070892086306311504576383209298722816

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ff qz209 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 4832456699 34359738368 554622286963 2498880692289536 191368923493

noncomputable abbrev qz430 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz484 (Real.log (Enclosure.sfrac Bool.false 16 1)))

noncomputable abbrev qz211 := (Real.cos qz430)

noncomputable abbrev qz212 := (@Neg.neg Real Real.instNeg (Real.sin qz430))

noncomputable def ep822 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz130 qz211) (@HMul.hMul Real Real Real qz0 qz130 qz212)) Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (BSN.cpow_neg_s_mk qz153 63102 1000 16 qz154 rfl)

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz133 63102 1000 0 1 3121657384082679 1125899906842624 250000000072727 18181750000000000000 98491412125192605129 562949953421312000 7887750002294609577 9090875000000000000000 qz155 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000072727 18181750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz386 Bool.false 26186360105375033720832 9444732965739290427392 1000000000290908 72727000000000000000 3121657384082679 1125899906842624 250000000072727 18181750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 72727 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep824 := nat_lit 169415037122100595285317074772120801

noncomputable def ep825 := BSN.sin_dyadic_bound_f 641561049 1073741824 2 1 524288 145597 ep824 ep79 ep824 ep824 ep80 ep824 294952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 641561049) qz284 0 1 ep824 ep79 ep824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 641561049) qz285 0 1 ep824 ep80 ep824 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz213 := qz430

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 91727275) qz20)

noncomputable def ep826 := @Enclosure.Real.IsNear.cos_image qz213 qz431 Bool.false 91727275 524288 57 65536 Bool.false 294952 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 98491412125192605129 562949953421312000 7887750002294609577 9090875000000000000000 91727275 524288 57 65536 (ep823 rfl) rfl) (Enclosure.sfrac_false_div 91727275 524288) (BSN.cos_reduce3 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 45145845384703492751360) qz23) 226375608064910080 72057594037927936 Bool.false 294952 524288 27 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 91727275 524288 226375608064910080 72057594037927936 27 45145845384703492751360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 294952 524288 45145845384703492751360 75557863725914323419136 641561049 1073741824 145597 145454 (ep825 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep827 := BSN.cos_dyadic_bound_f 641561049 1073741824 2 1 524288 145597 ep824 ep75 ep824 ep824 ep76 ep824 433451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 641561049) qz280 0 1 ep824 ep75 ep824 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 641561049) qz281 0 1 ep824 ep76 ep824 rfl rfl rfl rfl) rfl rfl

noncomputable def ep828 := @Enclosure.Real.IsNear.sin_image qz213 qz431 Bool.false 91727275 524288 57 65536 Bool.true 433451 524288 1 72727 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 98491412125192605129 562949953421312000 7887750002294609577 9090875000000000000000 91727275 524288 57 65536 (ep823 rfl) rfl) (Enclosure.sfrac_false_div 91727275 524288) (BSN.sin_reduce3 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 45145845384703492751360) qz23) 226375608064910080 72057594037927936 Bool.false 433451 524288 27 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q3 91727275 524288 226375608064910080 72057594037927936 27 45145845384703492751360 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 433451 524288 45145845384703492751360 75557863725914323419136 641561049 1073741824 145597 145454 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz214 := (Real.sin qz430)

noncomputable def ep829 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz130 qz211) (@HMul.hMul Real Real Real qz0 qz130 qz212) Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (@Enclosure.Real.IsNear.mulLit_ff qz130 qz211 131071 524288 1 524288 36869 65536 4210975 4766236672 4832456699 34359738368 554622286963 2498880692289536 qz388 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 294952 524288 4210975 4766236672 36869 65536 4210975 4766236672 (ep826 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz130 qz212 131071 524288 1 524288 433451 524288 4210975 4766236672 56812856021 274877906944 4447050912477 19991045538316288 qz388 (@Enclosure.Real.IsNear.neg qz214 Bool.true 433451 524288 4210975 4766236672 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 433451 524288 4210975 4766236672 433451 524288 4210975 4766236672 (ep828 rfl rfl) rfl)) rfl)

noncomputable def ep830 := @ep821 382282790784 0 1 924782036314166329607 13135136673927121600512 106137470001335038321759 ep816 (@Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (ep822 ep829))

noncomputable def ep831 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.false 191368923493 382282790784 0 1 Bool.false

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) Bool.false 991528101 1991056202 0 1 Bool.true 252408000

noncomputable def ep833 := @ep832 995528101 0 1 Bool.false 1 384 0 1 Bool.false 10517 32000 0 1 Bool.false 382737846986 191368923493 382282790784 0 1 Bool.false 2392913038217 2392913038217 31856899232000 0 1

noncomputable abbrev qz215 := (@HDiv.hDiv Complex Complex Complex qz323 qz352 (@HSub.hSub Complex Complex Complex qz315 qz391 (1 : Complex)))

noncomputable def ep834 := @Enclosure.Complex.IsNear.addLitP qz215 qz71 Bool.true 32000000 15928449616 0 1 Bool.true 4038528000 15928449616 0 1

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq qz215 (Complex.mk (Enclosure.sfrac Bool.true 32000000 15928449616) (Enclosure.sfrac Bool.true 4038528000 15928449616)) Bool.true 32000000 15928449616 0 1 Bool.true 4038528000 15928449616 0 1

noncomputable def ep836 := @ep834 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 15864449616 991528101 1991056202 0 1 Bool.true 4038528000 252408000 995528101 0 1 (ep835 (BSN.N_div_s_sub_one_mk qz153 63102 1000 16 qz154 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 32000000 15928449616) (Enclosure.sfrac Bool.true 4038528000 15928449616) Bool.true 32000000 15928449616 0 1 Bool.true 4038528000 15928449616 0 1 (Enclosure.Real.IsNear.const Bool.true 32000000 15928449616) (Enclosure.Real.IsNear.const Bool.true 4038528000 15928449616))) qz72 rfl

noncomputable def ep837 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138)) Bool.false 1 384 0 1

noncomputable def ep838 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138) Bool.false 0 1 0 1 Bool.false

noncomputable def ep839 := @ep838 0 1 0 1 Bool.false 1 384 0 1 Bool.false 10517 32000 0 1 Bool.false 1 1 384 0 1 Bool.false 10517 10517 32000 0

noncomputable def ep840 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep841 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138 Bool.false 1 384 0 1 Bool.false 10517 32000 0 1

noncomputable def ep842 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 1 384 0 1 0 1 0

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 1 16 0 1 1

noncomputable def ep844 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep845 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz144 Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 (BSN.ascPochhammer_one_eval qz144)

noncomputable def ep847 := ep846 (@Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk qz66 qz153) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_crit_mk qz153 Bool.false 63102 1000 qz154) (@Enclosure.Complex.IsNear.mk qz66 qz153 Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 qz333 qz155))

noncomputable def ep848 := @ep845 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 63102 1000 0 1 0 1 0

noncomputable def ep850 := @ep849 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep851 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) 10517 2000 0 1 0 1 0 1 10517

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 63102 1000 0 1 10517 2000 0

noncomputable def ep853 := @ep852 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep854 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep855 := @ep854 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep443) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep856 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 (@ep844 1 24 0 1 (ep848 rfl) (ep850 rfl) rfl rfl) (@ep851 10517 2000 0 1 (ep853 rfl) (ep855 rfl) rfl rfl)

noncomputable def ep857 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 ep856

noncomputable def ep858 := @ep843 384 0 1 ep857 qz141

noncomputable def ep859 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 10517 2000 0 1 0 1 0 1 0

noncomputable def ep860 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 10517 2000 0 1 ep856

noncomputable def ep861 := @ep859 1 0 1 ep860 qz142

noncomputable def ep862 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 0 1 0 1 10517 32000 0

noncomputable def ep863 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 0 1 0 1 0

noncomputable def ep864 := @ep863 1 0 1 ep857 qz142

noncomputable def ep865 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz73)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 10517 2000 0 1 1 16 0 1 10517

noncomputable def ep866 := @ep865 32000 0 1 ep860 qz141

noncomputable def ep867 := @ep839 1 (@ep840 0 1 0 1 (BSN.bern_sum_base qz144 16) qz87) (ep841 (@ep842 1 1 1 384 0 1 (ep858 rfl) (ep861 rfl) rfl rfl) (@ep862 1 10517 10517 32000 0 1 (ep864 rfl) (ep866 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep868 := ep833 (ep836 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep837 Bool.false 10517 32000 0 1 (BSN.bern_sum_succ qz144 16 0 1 1 rfl rfl) (ep867 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep869 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 56812856021 274877906944 4447050912477 19991045538316288 2392913038217

noncomputable def ep870 := @ep869 31856899232000 0 1 135948223910996091554557 ep817 ep818 ep819 (@Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (ep822 ep829))

noncomputable def ep871 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))) Bool.false 191368923493 382282790784 0 1 Bool.false

noncomputable def ep872 := nat_lit 1327162901759493159864971

noncomputable def ep873 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz209 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz210 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1))))))) 11563648641656184665683 1094594722827260133376000 ep872

noncomputable def ep874 := nat_lit 79606590407058147720036352000

noncomputable def ep875 := nat_lit 2547410893025860727041163264

noncomputable def ep876 := nat_lit 13115790113808574359669911605158580395670765568

noncomputable def ep877 := @Enclosure.Real.IsNear.mulLit_ff qz209 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 4832456699 34359738368 554622286963 2498880692289536 2392913038217

noncomputable def ep878 := @ep877 31856899232000 0 1 11563648641656184665683 1094594722827260133376000 ep872 ep874 (@Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (ep822 ep829))

noncomputable def ep879 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz194 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz52 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz52 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz98 qz99 (@HSub.hSub Nat Nat Nat qz97 (@HMul.hMul Nat Nat Nat qz52 2 k) 1)))))) 56812856021 274877906944 4447050912477 19991045538316288 191368923493

noncomputable def ep880 := @ep879 382282790784 0 1 10872215097301573401353 105081093391416972804096 283675781946428950707387 ep875 (@Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 4832456699 34359738368 554622286963 2498880692289536 Bool.false 56812856021 274877906944 4447050912477 19991045538316288 (ep822 ep829))

noncomputable abbrev qz432 := (ep868 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep881 := @ep814 ep722 ep715 ep723 ep717 (@ep815 ep816 135948223910996091554557 ep817 ep818 ep819 ep820 ep720 ep598 ep721 ep600 (ep830 (@ep831 2392913038217 31856899232000 0 1 qz432) rfl) (ep870 (@ep871 2392913038217 31856899232000 0 1 qz432) rfl) rfl rfl) (@ep873 ep874 10872215097301573401353 105081093391416972804096 283675781946428950707387 ep875 ep876 ep722 ep715 ep723 ep717 (ep878 (@ep871 2392913038217 31856899232000 0 1 qz432) rfl) (ep880 (@ep831 2392913038217 31856899232000 0 1 qz432) rfl) rfl rfl)

noncomputable def ep882 := @ep726 ep716 ep717 (@ep727 9995522769158144 (BSN.head_sum_c_eq qz144 16) (ep728 (BSN.head_sum_c_succ qz144 15 16 rfl rfl) (ep813 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep881 rfl rfl rfl

noncomputable def ep883 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz144 1 16) Bool.false ep597 ep598 ep599 ep600 Bool.true 312097957184070039754679 ep715 ep716 ep717 (@ep718 ep600 Bool.true 312097957184070039754679 ep715 ep716 ep717 (BSN.zetaApproximant_eq_folded' qz144 1 16 rfl) (ep882 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep884 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) (Complex.im (zetaApproximant qz144 1 16)) 79 524288 7462117

noncomputable def ep885 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164)) Bool.true 79 524288 7462117

noncomputable def ep886 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164) qz404 Bool.false 21412371 524288 99

noncomputable def ep887 := BSN.sin_dyadic_bound_f 163268 1073741824 1 0 524288 145597 0 1 1 0 1 1 79 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 163268) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 163268) qz285 0 0 rfl) rfl rfl

noncomputable def ep888 := @ep886 262144 Bool.true 79 524288 1 72727 (@ep605 21412371 524288 99 262144 ep712 rfl) (Enclosure.sfrac_false_div 21412371 524288) (BSN.sin_reduce2 qz404 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11488985477097193472) qz23) 226375608064910080 72057594037927936 Bool.false 79 524288 6 1000000000000000 145454 72727 (BSN.sin_reduce_arg_pos_rat_q2 21412371 524288 226375608064910080 72057594037927936 6 11488985477097193472 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79 524288 11488985477097193472 75557863725914323419136 163268 1073741824 145597 145454 (ep887 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep889 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz144 1 16) Bool.false ep597 ep598 ep599 ep600 Bool.true 312097957184070039754679 ep715 ep716 ep717 (@ep718 ep600 Bool.true 312097957184070039754679 ep715 ep716 ep717 (BSN.zetaApproximant_eq_folded' qz144 1 16 rfl) (ep882 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow14.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 16 qz153) Bool.true ep580 ep581 ep582 ep583 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 16 qz153) ep584 Bool.true ep580 ep581 ep582 ep583 (@Eq.refl Real ep584) (@ep585 Bool.true ep580 ep581 ep582 ep583 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz318 (Complex.im (@HSub.hSub Complex Complex Complex qz45 qz162 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz163 (@Nat.cast Complex Complex.instNatCast j))))) qz164) (zetaApproximant qz144 1 16)) (@ep587 ep588 ep589 ep590 ep591 ep592 ep593 ep594 ep595 ep580 ep581 ep582 ep583 (@ep596 19064946688 ep597 ep598 ep599 ep600 ep586 ep588 ep589 ep590 (@ep601 19064946688 524287 524288 7462117 19064946688 (ep714 rfl rfl) rfl) ep883 rfl) (@ep884 19064946688 312097957184070039754679 ep715 ep716 ep717 ep591 ep592 ep593 ep594 (@ep885 19064946688 79 524288 7462117 19064946688 (ep888 rfl rfl) rfl) ep889 rfl) rfl rfl))

theorem EMRow14.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow14.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow14.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow14.d15 : @Eq Nat (Nat.pow 16 (Nat.succ (Nat.mul 2 3))) 268435456 := @Eq.refl Nat 268435456

noncomputable abbrev qz487 := (@HAdd.hAdd Complex Complex Complex qz490 qz489 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz433 := qz487

noncomputable abbrev qz216 := (@HDiv.hDiv Real Real Real qz268 (@Norm.norm Complex Complex.instNorm qz433) (@HAdd.hAdd Real Real Real qz343 (Complex.re qz270) qz288))

noncomputable abbrev qz217 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz218 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz434 := (@HPow.hPow Complex Complex Complex qz468 qz481 (@HSub.hSub Complex Complex Complex qz474 qz469 qz470))

noncomputable abbrev qz219 := qz434

noncomputable def ep890 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) 1304747575 154618822656 34309927 463856467968 10159074809551789 31525197391593472 5708675153

noncomputable def ep891 := nat_lit 1611916611175202946216361984

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16)) 4427 294912 1 884736 294725 524288 2561 524288 1304747575 154618822656

noncomputable abbrev qz435 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz220 := (@HPow.hPow Real Nat Real qz435 qz269 2)

noncomputable def ep893 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep894 := nat_lit 781950621441006189802102638025

noncomputable def ep895 := nat_lit 19807040628566084398385987584

noncomputable def ep896 := nat_lit 26986075409044041160201671

noncomputable def ep897 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz221 := qz269

noncomputable abbrev qz436 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz221 1)

noncomputable def ep898 := @Enclosure.Real.IsNear.mulLit_ff qz436 qz221 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep894 ep895 ep896 ep897

noncomputable def ep899 := ep898 (@Enclosure.Real.IsNear.of_eq qz436 qz221 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz221) (@Enclosure.Real.IsNear.of_eq qz221 qz266 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz267)) (@Enclosure.Real.IsNear.of_eq qz221 qz266 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz267) rfl

noncomputable def ep900 := @Enclosure.Real.IsNear.inv_image qz220 ep894 ep895 ep896 ep897 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz220 (@HMul.hMul Real Real Real qz0 qz436 qz221) Bool.false ep894 ep895 ep896 ep897 (BSN.pow_succ_r qz221 1 2 rfl) ep899) rfl rfl rfl

noncomputable def ep901 := ep893 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz220) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep900 rfl rfl rfl) rfl)

noncomputable def ep902 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))))) Bool.false 294725 524288 2561 524288

noncomputable def ep903 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))))) Bool.false 294725 524288 2561 524288

noncomputable def ep904 := nat_lit 1391676578991046733389165785716055033673

noncomputable def ep905 := nat_lit 4403649999432844153588761812271104000000

noncomputable def ep906 := nat_lit 29104686700034991885249933404208219623376671683597613027

noncomputable def ep907 := nat_lit 5302702945631032001462335018707913484440561625595904000000

noncomputable def ep908 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16)))) ep904 ep905 ep906 ep907 146082 148643

noncomputable def ep909 := nat_lit 316602081027909578467873701424584725442676375441

noncomputable def ep910 := nat_lit 1002549794767729389257970954720185077989376000000

noncomputable def ep911 := nat_lit 973347732586271220215113813248282918938479646642140159

noncomputable def ep912 := nat_lit 182851825711414896602149483403721154635881435365376000000

noncomputable def ep913 := nat_lit 56566773336606858385881213638779519708801

noncomputable def ep914 := nat_lit 244763133488215182924309315117232685056000000

noncomputable def ep915 := nat_lit 857033647493287596691047675789077123203869073218309

noncomputable def ep916 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16))) ep909 ep910 ep911 ep912 ep913 ep914 ep915

noncomputable def ep917 := nat_lit 5178420845342804688928061541706946762148985962496000000

noncomputable def ep918 := nat_lit 77549228428280239642643741262308786614826515685165943960931954952341783610660457807872000000

noncomputable def ep919 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 16)) (Complex.re (zetaApproximant qz6 1 16)) 562674045098856126781271 1001274085736632549376000 ep174 ep175 562674045098856126781271 1001274085736632549376000 ep174 ep175 ep909

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz6 1 16)) (Complex.im (zetaApproximant qz6 1 16)) 237837703774247825599 15644907589634883584000 ep301 ep302 237837703774247825599 15644907589634883584000 ep301 ep302 ep913

noncomputable def ep921 := @ep890 31525197391593472 ep891 93825895524071701 283726776524341248 63113124753547 851180329573023744 (@ep892 34309927 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow14.d12 EMRow14.d13 rfl) (ep901 rfl)) (ep902 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 16)) (@ep903 294725 524288 2561 524288 (@ep908 262144 (@ep916 ep917 ep918 ep904 ep905 ep906 ep907 (@ep919 ep910 ep911 ep912 ep480 ep480 rfl) (@ep920 ep914 ep915 ep917 ep486 ep486 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz222 := (@Norm.norm Complex Complex.instNorm qz433)

noncomputable abbrev qz437 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep922 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz222 qz437) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) Bool.false 10159074809551789 31525197391593472 5708675153 31525197391593472 (BSN.zrb_shape_eq qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) qz17 3)

noncomputable def ep923 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz222 qz437) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) 31694993 1835008 1 1835008 320526173 17179869184 85 8589934592

noncomputable def ep924 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz437 31694993 524288 1 524288 2 7 0 1 31694993 1835008

noncomputable abbrev qz438 := (Complex.re qz487)

noncomputable abbrev qz439 := (Complex.im qz487)

noncomputable abbrev qz223 := (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz265 qz438 qz438) (@HMul.hMul Real Real Real qz265 qz439 qz439))

noncomputable abbrev qz224 := qz433

noncomputable def ep925 := @Enclosure.Real.IsNear.of_eq qz222 (Real.sqrt qz223) Bool.false 31694993 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz224)

noncomputable def ep926 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz223) Bool.false 31694993 524288 1 524288 31694993

noncomputable def ep927 := @Enclosure.Real.IsNear.sqrt_image qz223 228413369 62500 0 1 15847496 15847497 262144

noncomputable abbrev qz225 := (@HMul.hMul Real Real Real qz265 qz438 qz438)

noncomputable abbrev qz226 := (@HMul.hMul Real Real Real qz265 qz439 qz439)

noncomputable def ep928 := @Enclosure.Real.IsNear.addLit_ff qz225 qz226 49 4 0 1 56911936 15625 0 1

noncomputable abbrev qz227 := qz438

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz227 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz440 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz224 (Complex.mk qz440 qz17) Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 60352 1000 3 qz18)

noncomputable abbrev qz441 := (ep930 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz22))

noncomputable def ep931 := @ep929 0 1 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz441)

noncomputable def ep932 := ep931 (@Enclosure.Complex.IsNear.re_isNear qz224 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz441)

noncomputable abbrev qz228 := qz439

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz228 60352 1000 0 1 60352 1000 0 1 56911936 15625

noncomputable def ep934 := @ep933 0 1 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz441)

noncomputable def ep935 := ep934 (@Enclosure.Complex.IsNear.im_isNear qz224 Bool.false 7 2 0 1 Bool.false 60352 1000 0 1 qz441)

noncomputable def ep936 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))))) Bool.false 320526173 17179869184

noncomputable def ep937 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))))) Bool.false 641052346 34359738368

noncomputable def ep938 := nat_lit 30701651240797137091440205491874990138810233389660447752969

noncomputable def ep939 := nat_lit 88201189505907249729706698246314320409395200000000000000000000

noncomputable def ep940 := nat_lit 57234090472503599912222420027756623568719261593329156919928771

noncomputable def ep941 := nat_lit 155505063137368656137098483562140338946258379577753600000000000000000000

noncomputable def ep942 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) ep938 ep939 ep940 ep941

noncomputable def ep943 := nat_lit 37760671290467578783299324183494301417556436176066221415249

noncomputable def ep944 := nat_lit 176402379011814499459413396492628640818790400000000000000000000

noncomputable def ep945 := nat_lit 21945958520028265881458547112994294765276723051270815031161447

noncomputable def ep946 := nat_lit 103670042091579104091398989041426892630838919718502400000000000000000000

noncomputable def ep947 := nat_lit 23642631191126695399581086800255678860064030603254674090689

noncomputable def ep948 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219))) ep943 ep944 ep945 ep946 ep947

noncomputable def ep949 := nat_lit 48630305384922402180069198716530362841608354032845868746373201

noncomputable def ep950 := nat_lit 311010126274737312274196967124280677892516759155507200000000000000000000

noncomputable def ep951 := nat_lit 10831688636935282962613378389704071734667495551847976494552472955069037010373120664547216623985177395200000000000000000000

noncomputable def ep952 := nat_lit 194321052103130552145897741943

noncomputable def ep953 := nat_lit 13281655733070877163520000000000

noncomputable def ep954 := nat_lit 6987976470780790176499990351

noncomputable def ep955 := nat_lit 965934976499045683471319040000000000

noncomputable def ep956 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) ep952 ep953 ep954 ep955 ep952 ep953 ep954

noncomputable def ep957 := nat_lit 153761605061623545083909684383

noncomputable def ep958 := nat_lit 6523107747786330455469525481

noncomputable def ep959 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219) Bool.true ep952 ep953 ep954 ep955 Bool.true ep957 ep953 ep958

noncomputable def ep960 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219 Bool.true ep952 ep953 ep954 ep955 Bool.true ep957 ep953 ep958 ep955

noncomputable def ep961 := nat_lit 33321370632204900966980273

noncomputable def ep962 := nat_lit 35417748621522339102720000000

noncomputable def ep963 := nat_lit 2575826603997455155923517440000000

noncomputable def ep964 := nat_lit 11364096132253357142705008723

noncomputable def ep965 := nat_lit 830103483316929822720000000000

noncomputable def ep966 := nat_lit 408583437764965638022812811

noncomputable abbrev qz229 := (Complex.re qz434)

noncomputable abbrev qz230 := (Complex.im qz434)

noncomputable def ep967 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) ep961 ep962 1201710577443573248359961 ep963 ep964 ep965 ep966

noncomputable def ep968 := nat_lit 60370936031190355216957440000000000

noncomputable def ep969 := nat_lit 430150885953651421690218370126225531728648795586560000000

noncomputable def ep970 := nat_lit 85860886799915171864117248

noncomputable def ep971 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 682865107 30000000 0 1 48796417170287339 1180591620717411303424 1759806680887523 ep970 ep961

noncomputable def ep972 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 682865107 30000000 0 1 0 1 0 1 682865107

noncomputable def ep973 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2048595321 125000 0 1 682865107 30000000 0

noncomputable def ep974 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow14.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz24)

noncomputable abbrev qz442 := (@HAdd.hAdd Complex Complex Complex qz467 qz466 qz471)

noncomputable abbrev qz231 := qz442

noncomputable def ep975 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz44 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz231) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1

noncomputable abbrev qz232 := (Complex.re qz442)

noncomputable abbrev qz233 := (Complex.im qz442)

noncomputable def ep976 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) 227600869 25000 0 1 113823872 15625 0 1

noncomputable def ep977 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 227600869 62500 0 1 5 2 0 1 227600869 25000

noncomputable abbrev qz443 := (@HAdd.hAdd Complex Complex Complex qz467 qz466 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz234 := qz443

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz44 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz234) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1

noncomputable abbrev qz235 := (Complex.re qz443)

noncomputable abbrev qz236 := (Complex.im qz443)

noncomputable def ep979 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) 3 4 0 1 56911936 15625 0 1

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 1 2 0 1 3 2 0 1 3 4

noncomputable def ep981 := @ep980 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable abbrev qz444 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep982 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz444 qz17) Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 60352 1000 1 qz18)

noncomputable abbrev qz445 := (ep982 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz22))

noncomputable def ep983 := ep981 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz445)

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 60352 1000 0 1 60352 1000 0 1 56911936 15625

noncomputable def ep985 := @ep984 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep986 := ep985 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz445)

noncomputable def ep987 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz234 Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 (@ep979 227600869 227600869 62500 0 1 (ep983 rfl) (ep986 rfl) rfl rfl)

noncomputable def ep988 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235) 3772 125 0 1 11316 125 0 1

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz236 1 2 0 1 60352 1000 0 1 3772 125

noncomputable def ep990 := @ep989 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep991 := ep990 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz445)

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz235 60352 1000 0 1 3 2 0 1 11316 125

noncomputable def ep993 := @ep992 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 60352 1000 0 1 ep445)

noncomputable def ep994 := ep993 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 3 2 0 1 Bool.false 60352 1000 0 1 qz445)

noncomputable abbrev qz237 := (ep978 (BSN.ascPochhammer_succ_eval_c 1 2 qz270 rfl) (ep987 (@ep988 1886000 15088 125 0 1 (ep991 rfl) (ep994 rfl) rfl rfl)))

noncomputable def ep995 := @ep977 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz237)

noncomputable abbrev qz446 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep996 := @Enclosure.Complex.IsNear.of_eq qz231 (Complex.mk qz446 qz17) Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 60352 1000 2 qz18)

noncomputable abbrev qz447 := (ep996 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz22))

noncomputable def ep997 := ep995 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz447)

noncomputable def ep998 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 15088 125 0 1 60352 1000 0 1 113823872 15625

noncomputable def ep999 := @ep998 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz237)

noncomputable def ep1000 := ep999 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz447)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz231 Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 (@ep976 6401860378125 2048595321 125000 0 1 (ep997 rfl) (ep1000 rfl) rfl rfl)

noncomputable def ep1002 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232) 429255238934 1953125 0 1 7544 25 0 1

noncomputable def ep1003 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz233 227600869 62500 0 1 60352 1000 0 1 429255238934 1953125

noncomputable def ep1004 := @ep1003 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz237)

noncomputable def ep1005 := ep1004 (@Enclosure.Complex.IsNear.im_isNear qz231 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz447)

noncomputable def ep1006 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz232 15088 125 0 1 5 2 0 1 7544 25

noncomputable def ep1007 := @ep1006 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 227600869 62500 0 1 Bool.false 15088 125 0 1 qz237)

noncomputable def ep1008 := ep1007 (@Enclosure.Complex.IsNear.re_isNear qz231 Bool.false 5 2 0 1 Bool.false 60352 1000 0 1 qz447)

noncomputable abbrev qz238 := (ep975 (BSN.ascPochhammer_succ_eval_c 2 3 qz270 rfl) (ep1001 (@ep1002 10716646598350 428665863934 1953125 0 1 (ep1005 rfl) (ep1008 rfl) rfl rfl)))

noncomputable def ep1009 := @ep973 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz238)

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 428665863934 1953125 0 1 0 1 0

noncomputable def ep1011 := @ep1010 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz238)

noncomputable def ep1012 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 214332931967 703125000 0 1 0 1 0 1 214332931967

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 428665863934 1953125 0 1 214332931967 703125000 0

noncomputable def ep1014 := @ep1013 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz238)

noncomputable def ep1015 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2048595321 125000 0 1 0 1 0

noncomputable def ep1016 := @ep1015 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 2048595321 125000 0 1 Bool.true 428665863934 1953125 0 1 qz238)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 (@ep972 682865107 30000000 0 1 (ep1009 rfl) (ep1011 rfl) rfl rfl) (@ep1012 214332931967 703125000 0 1 (ep1014 rfl) (ep1016 rfl) rfl rfl)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 ep1017

noncomputable def ep1019 := @Enclosure.Complex.IsNear.re_isNear qz219 Bool.true 48796417170287339 1180591620717411303424 1759806680887523 ep970 Bool.false 53020765535009069 1180591620717411303424 1906302657343733 ep970

noncomputable abbrev qz448 := (@Nat.cast Real Real.instNatCast 268435456)

noncomputable abbrev qz239 := (@Inv.inv Real Real.instInv (Real.sqrt qz448))

noncomputable def ep1020 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (@HMul.hMul Real Real Real qz0 qz239 qz131) (@HMul.hMul Real Real Real qz0 qz239 qz132)) Bool.true 48796417170287339 1180591620717411303424 1759806680887523 ep970 Bool.false 53020765535009069 1180591620717411303424 1906302657343733

noncomputable abbrev qz240 := (Real.sqrt qz448)

noncomputable def ep1021 := @Enclosure.Real.IsNear.inv_image qz240 562949953421313 34359738368 1 34359738368 1048575 1048576 17179869184 (@Enclosure.Real.IsNear.of_eq qz240 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz448 qz19)) Bool.false 562949953421313 34359738368 1 34359738368 (BSN.sqrt_natCast_div_one 268435456) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz448 qz19)) Bool.false 562949953421313 34359738368 1 34359738368 562949953421313 34359738368 1 34359738368 (BSN.sqrt_enclosure 268435456 1 281474976710656 281474976710657 17179869184 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1022 := nat_lit 1716149295865858209928445952

noncomputable def ep1023 := nat_lit 618970019642690137449562112

noncomputable def ep1024 := nat_lit 4766236672000000000000000

noncomputable def ep1025 := BSN.log_dyadic_bound 0 32 1 0 1 17179869184 4766236672 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep1026 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz133 60352 1000 0 1 3121657384082679 1125899906842624 30518159941 145454000000000000000 2943722913189966297 17592186044416000 28778624824363 2272718750000000000000 qz22 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 30518159941 145454000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz386 Bool.false ep1022 ep1023 1000019064946688 ep1024 3121657384082679 1125899906842624 30518159941 145454000000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 17179869184 24973259072661432 36028797018963968 4766236672 1000000000000000 rfl rfl rfl rfl (ep1025 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1027 := nat_lit 511803979497840144061300736

noncomputable def ep1028 := nat_lit 137575257438963594885940689854948405431180749831844017407244190986289348530010527859704350910354768291107679810616607913263355676254305786935203023769183407036561778882379776

noncomputable def ep1029 := nat_lit 7061461093083586024179172776487149921794651295521201685534719608389587370251949717138351715479917319946841476520062230191960740901052279494785699627855717567272383596304793600

noncomputable def ep1030 := nat_lit 1505795996347650772188260526122210603513340412544231282520028852003920807748584183810194311065427064994735211563905498835019402152395854403197594765816570901635792896

noncomputable def ep1031 := nat_lit 834468444243110570963555921443064797519248681735190615102427921846756001467688901039149441762696790805506365568331272711739693546717697280572181728889106637466733525713551360

noncomputable def ep1032 := nat_lit 642592959470606328200304722660330642883313267892429353383659484363452450692927424259590006108672476115162574363325662947468427421995757434025498666134870298621786907263736217600

noncomputable def ep1033 := BSN.cos_dyadic_bound_f 58185375962448 70368744177664 4 3 34359738368 9541782401 ep1028 ep1029 ep1030 ep1031 ep1032 ep1030 23267955989 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 58185375962448) (BSN.cosEvenQ 70368744177664) 0 3 ep1028 ep1029 ep1030 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 58185375962448) (BSN.cosOddQ 70368744177664) 0 3 ep1031 ep1032 ep1030 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 718682351853) (@Nat.cast Real Real.instNatCast 4294967296))

noncomputable def ep1034 := @Enclosure.Real.IsNear.cos_image qz134 qz449 Bool.false 718682351853 4294967296 109 8589934592 Bool.true 23267955989 34359738368 1 4766236672 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 2943722913189966297 17592186044416000 28778624824363 2272718750000000000000 718682351853 4294967296 109 8589934592 (ep1026 rfl) rfl) (Enclosure.sfrac_false_div 718682351853 4294967296) (BSN.cos_reduce2 qz449 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1027) (@Nat.cast Real Real.instNatCast ep1023)) 226375608064910080 72057594037927936 Bool.false 23267955989 34359738368 26 1000000000000000 9532473344 4766236672 (BSN.sin_reduce_arg_pos_rat_q2 718682351853 4294967296 226375608064910080 72057594037927936 26 ep1027 ep1023 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23267955989 34359738368 ep1027 ep1023 58185375962448 70368744177664 9541782401 9532473344 (ep1033 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1035 := nat_lit 850008946146077342564325127909823913921743180776882842771002810042087936415233305888376906169311751407930651443200

noncomputable def ep1036 := nat_lit 218173217903863962044552888054506142846486446937049885358659007423899650824598812662811415688669405940794512407265280

noncomputable def ep1037 := nat_lit 131374403978903611922695426753852181543670971013783444299812749267690217006445752605252931186065713446262931456

noncomputable def ep1038 := nat_lit 2226001205157093862772976685263365918643970958557813700728521948516177858831410127060578630459610480627572042366976

noncomputable def ep1039 := nat_lit 3999842328237505970816802947665945952185584860512581231575415136104826931784311565484875954292272442247899394133196800

noncomputable def ep1040 := BSN.sin_dyadic_bound_f 58185375962448 70368744177664 3 2 34359738368 9541782401 ep1035 ep1036 ep1037 ep1038 ep1039 ep1037 25282283219 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 58185375962448) (BSN.sinEvenQ 70368744177664) 0 2 ep1035 ep1036 ep1037 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 58185375962448) (BSN.sinOddQ 70368744177664) 0 2 ep1038 ep1039 ep1037 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1041 := @Enclosure.Real.IsNear.sin_image qz134 qz449 Bool.false 718682351853 4294967296 109 8589934592 Bool.true 25282283219 34359738368 1 4766236672 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 2943722913189966297 17592186044416000 28778624824363 2272718750000000000000 718682351853 4294967296 109 8589934592 (ep1026 rfl) rfl) (Enclosure.sfrac_false_div 718682351853 4294967296) (BSN.sin_reduce2 qz449 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1027) (@Nat.cast Real Real.instNatCast ep1023)) 226375608064910080 72057594037927936 Bool.false 25282283219 34359738368 26 1000000000000000 9532473344 4766236672 (BSN.sin_reduce_arg_pos_rat_q2 718682351853 4294967296 226375608064910080 72057594037927936 26 ep1027 ep1023 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 25282283219 34359738368 ep1027 ep1023 58185375962448 70368744177664 9541782401 9532473344 (ep1040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz450 := (@Enclosure.Real.IsNear.recentre' qz239 Bool.false 2097151 34359738368 1 34359738368 2097151 34359738368 1 34359738368 (ep1021 rfl rfl) rfl)

noncomputable def ep1042 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz239 qz131) (@HMul.hMul Real Real Real qz0 qz239 qz132) Bool.true 48796417170287339 1180591620717411303424 1759806680887523 ep970 Bool.false 53020765535009069 1180591620717411303424 1906302657343733 ep970 (@Enclosure.Real.IsNear.mulLit_ft qz239 qz131 2097151 34359738368 1 34359738368 23267955989 34359738368 8058315 624720173072384 48796417170287339 1180591620717411303424 1759806680887523 ep970 qz450 (@Enclosure.Real.IsNear.recentre' qz131 Bool.true 23267955989 34359738368 528109731840 40941661262471757824 23267955989 34359738368 8058315 624720173072384 (ep1034 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz239 qz132 2097151 34359738368 1 34359738368 25282283219 34359738368 8058315 624720173072384 53020765535009069 1180591620717411303424 1906302657343733 ep970 qz450 (@Enclosure.Real.IsNear.neg qz135 Bool.true 25282283219 34359738368 8058315 624720173072384 (@Enclosure.Real.IsNear.recentre' qz135 Bool.true 25282283219 34359738368 528109731840 40941661262471757824 25282283219 34359738368 8058315 624720173072384 (ep1041 rfl rfl) rfl)) rfl)

noncomputable def ep1043 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 214332931967 703125000 0 1 53020765535009069 1180591620717411303424 1906302657343733 ep970 ep964

noncomputable def ep1044 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 682865107 30000000 0 1 Bool.false 214332931967 703125000 0 1 ep1017

noncomputable def ep1045 := @Enclosure.Complex.IsNear.im_isNear qz219 Bool.true 48796417170287339 1180591620717411303424 1759806680887523 ep970 Bool.false 53020765535009069 1180591620717411303424 1906302657343733 ep970

noncomputable def ep1046 := nat_lit 36206030730285880148655383

noncomputable def ep1047 := nat_lit 1301747568081412570824431

noncomputable def ep1048 := nat_lit 10458679161592546883728465813

noncomputable def ep1049 := nat_lit 377184525609737546338147741

noncomputable def ep1050 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229) ep1046 ep962 ep1047 ep963 ep1048 ep965 ep1049

noncomputable def ep1051 := nat_lit 340368117232148727046090562886881146093320913551360000000

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz230 682865107 30000000 0 1 53020765535009069 1180591620717411303424 1906302657343733 ep970 ep1046

noncomputable def ep1053 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz229 214332931967 703125000 0 1 48796417170287339 1180591620717411303424 1759806680887523 ep970 ep1048

noncomputable abbrev qz451 := (@ep1020 ep970 (BSN.cpow_neg_s_sub_mk qz17 60352 1000 16 3 268435456 qz18 rfl EMRow14.d15) ep1042)

noncomputable def ep1054 := ep960 (@ep967 ep968 ep969 ep952 ep953 ep954 ep955 (@ep971 ep962 1201710577443573248359961 ep963 ep1018 (ep1019 qz451) rfl) (@ep1043 ep965 ep966 ep968 ep1044 (ep1045 qz451) rfl) rfl rfl) (@ep1050 ep968 ep1051 ep957 ep953 ep958 ep955 (@ep1052 ep962 ep1047 ep963 ep1018 (ep1045 qz451) rfl) (@ep1053 ep965 ep1049 ep968 ep1044 (ep1019 qz451) rfl) rfl rfl)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) ep957 ep953 ep958 ep955 ep957 ep953 ep958

noncomputable def ep1056 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219) Bool.true ep952 ep953 ep954 ep955 Bool.true ep957 ep953 ep958

noncomputable def ep1057 := @ep923 10159074809551789 31525197391593472 5708675153 31525197391593472 (@ep924 1 1835008 (ep925 (@ep926 524288 1 524288 (ep927 (@ep928 228413369 228413369 62500 0 1 (ep932 rfl) (ep935 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep936 85 8589934592 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)) (@ep937 340 34359738368 320526173 17179869184 85 8589934592 (@ep942 320526003 320526343 17179869184 (@ep948 ep944 ep949 ep950 ep951 ep938 ep939 ep940 ep941 (@ep956 ep955 ep943 ep944 ep945 ep946 (@ep959 ep955 ep1054) (@ep959 ep955 ep1054) rfl) (@ep1055 ep955 ep947 ep944 ep949 ep950 (@ep1056 ep955 ep1054) (@ep1056 ep955 ep1054) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow14.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) Bool.false 93825895524071701 283726776524341248 63113124753547 851180329573023744 := ep921 (ep922 ep1057) rfl rfl

noncomputable abbrev qz488 := (@HAdd.hAdd Complex Complex Complex qz490 qz496 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz452 := qz488

noncomputable abbrev qz241 := (@HDiv.hDiv Real Real Real qz268 (@Norm.norm Complex Complex.instNorm qz452) (@HAdd.hAdd Real Real Real qz343 (Complex.re qz391) qz288))

noncomputable abbrev qz453 := (@HPow.hPow Complex Complex Complex qz468 qz481 (@HSub.hSub Complex Complex Complex qz474 qz483 qz470))

noncomputable abbrev qz242 := qz453

noncomputable def ep1058 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) 4861054069 77309411328 6134831 77309411328 24276357096774409 63050394783186944 13555703071

noncomputable def ep1059 := nat_lit 2183282254452811954323980288

noncomputable def ep1060 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16)) 4427 294912 1 884736 1098047 262144 1303 262144 4861054069 77309411328

noncomputable def ep1061 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 16)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 16)) (Complex.im (zetaApproximant qz144 1 16))))) Bool.false 1098047 262144 1303 262144

noncomputable def ep1062 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 16)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 16)) (Complex.im (zetaApproximant qz144 1 16))))) Bool.false 2196094 524288 2606 524288

noncomputable def ep1063 := nat_lit 2432585457643097640953222234784859609972381

noncomputable def ep1064 := nat_lit 138645460851934502489983099344204595200000

noncomputable def ep1065 := nat_lit 30391698096972219912675271632873997736087084584018360310851

noncomputable def ep1066 := nat_lit 730046504014516490009826003008981293897555530409102540800000

noncomputable def ep1067 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 16)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 16)) (Complex.im (zetaApproximant qz144 1 16)))) ep1063 ep1064 ep1065 ep1066 1096744 1099350

noncomputable def ep1068 := nat_lit 12108146285298730772815751526236869574907047587320241

noncomputable def ep1069 := nat_lit 690127261770980987201163232061151730074648576000000

noncomputable def ep1070 := nat_lit 151015699862410059295743656496935674371899065431186373500611

noncomputable def ep1071 := nat_lit 3650232520072582450049130015044906469487777652045512704000000

noncomputable def ep1072 := nat_lit 97405134878469615738569973716895107494502393041

noncomputable def ep1073 := nat_lit 172531815442745246800290808015287932518662144000000

noncomputable def ep1074 := nat_lit 78565885204253355636058472286192859044696457408785671137

noncomputable def ep1075 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 16)) (Complex.re (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 16)) (Complex.im (zetaApproximant qz144 1 16))) ep1068 ep1069 ep1070 ep1071 ep1072 ep1073 ep1074

noncomputable def ep1076 := nat_lit 304186043339381870837427501253742205790648137670459392000000

noncomputable def ep1077 := nat_lit 2089107682187938164119693631886936766312424621814954543098682490136536110352353237623554514616320000000

noncomputable def ep1078 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz144 1 16)) (Complex.re (zetaApproximant qz144 1 16)) ep597 ep598 ep599 ep600 ep597 ep598 ep599 ep600 ep1068

noncomputable def ep1079 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz144 1 16)) (Complex.im (zetaApproximant qz144 1 16)) 312097957184070039754679 ep715 ep716 ep717 312097957184070039754679 ep715 ep716 ep717 ep1072

noncomputable def ep1080 := @ep1058 63050394783186944 ep1059 254167506291159889 567453553048682496 45151857182231 567453553048682496 (@ep1060 6134831 77309411328 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz220)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow14.d12 EMRow14.d13 rfl) (ep901 rfl)) (ep1061 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz144 1 16)) (@ep1062 1098047 262144 1303 262144 (@ep1067 262144 (@ep1075 ep1076 ep1077 ep1063 ep1064 ep1065 ep1066 (@ep1078 ep1069 ep1070 ep1071 ep883 ep883 rfl) (@ep1079 ep1073 ep1074 ep1076 ep889 ep889 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz243 := (@Norm.norm Complex Complex.instNorm qz452)

noncomputable def ep1081 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz243 qz437) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) Bool.false 24276357096774409 63050394783186944 13555703071 63050394783186944 (BSN.zrb_shape_eq qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) qz153 3)

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz243 qz437) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) 33134473 1835008 1 1835008 732661633 34359738368 387 34359738368

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_ff qz243 qz437 33134473 524288 1 524288 2 7 0 1 33134473 1835008

noncomputable abbrev qz454 := (Complex.re qz488)

noncomputable abbrev qz455 := (Complex.im qz488)

noncomputable abbrev qz244 := (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz265 qz454 qz454) (@HMul.hMul Real Real Real qz265 qz455 qz455))

noncomputable abbrev qz245 := qz452

noncomputable def ep1084 := @Enclosure.Real.IsNear.of_eq qz243 (Real.sqrt qz244) Bool.false 33134473 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz245)

noncomputable def ep1085 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz244) Bool.false 33134473 524288 1 524288 33134473

noncomputable def ep1086 := @Enclosure.Real.IsNear.sqrt_image qz244 998528101 250000 0 1 16567236 16567237 262144

noncomputable abbrev qz246 := (@HMul.hMul Real Real Real qz265 qz454 qz454)

noncomputable abbrev qz247 := (@HMul.hMul Real Real Real qz265 qz455 qz455)

noncomputable def ep1087 := @Enclosure.Real.IsNear.addLit_ff qz246 qz247 49 4 0 1 995465601 250000 0 1

noncomputable abbrev qz248 := qz454

noncomputable def ep1088 := @Enclosure.Real.IsNear.mulLit_ff qz248 qz248 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1089 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk qz440 qz153) Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 63102 1000 3 qz154)

noncomputable abbrev qz456 := (ep1089 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz153 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz155))

noncomputable def ep1090 := @ep1088 0 1 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz456)

noncomputable def ep1091 := ep1090 (@Enclosure.Complex.IsNear.re_isNear qz245 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz456)

noncomputable abbrev qz249 := qz455

noncomputable def ep1092 := @Enclosure.Real.IsNear.mulLit_ff qz249 qz249 63102 1000 0 1 63102 1000 0 1 995465601 250000

noncomputable def ep1093 := @ep1092 0 1 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz456)

noncomputable def ep1094 := ep1093 (@Enclosure.Complex.IsNear.im_isNear qz245 Bool.false 7 2 0 1 Bool.false 63102 1000 0 1 qz456)

noncomputable def ep1095 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))))) Bool.false 732661633 34359738368

noncomputable def ep1096 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))))) Bool.false 732661633 34359738368

noncomputable def ep1097 := nat_lit 285180029020432491116016172846523212906912073205321926921873

noncomputable def ep1098 := nat_lit 627208458708673775855692076418235167355699200000000000000000000

noncomputable def ep1099 := nat_lit 1590000826845924350251776152854069852289269077099803073327158951

noncomputable def ep1100 := nat_lit 3317441346930531330924767649325660564186845430992076800000000000000000000

noncomputable def ep1101 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) ep1097 ep1098 ep1099 ep1100

noncomputable def ep1102 := nat_lit 39009771113037452894745828657697364398667402356990341932569

noncomputable def ep1103 := nat_lit 139379657490816394634598239204052259412377600000000000000000000

noncomputable def ep1104 := nat_lit 2020053487336496847806820198623723940373918118968911456647258527

noncomputable def ep1105 := nat_lit 6634882693861062661849535298651321128373690861984153600000000000000000000

noncomputable def ep1106 := nat_lit 350835388837644649886911820438032233961308040316369242321

noncomputable def ep1107 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242))) ep1102 ep1103 ep1104 ep1105 ep1106

noncomputable def ep1108 := nat_lit 2007067067867756082738214644538352535538237440000000000000000

noncomputable def ep1109 := nat_lit 123727804411237530954318091422337681515159470424607433600753

noncomputable def ep1110 := nat_lit 707720820678513350597283765189474253693193691944976384000000000000000

noncomputable def ep1111 := nat_lit 127194543257884672860814890433050226563930519607365066164191743077281222314976097765513809960078000783360000000000000000

noncomputable def ep1112 := nat_lit 197508914009057963061514737413

noncomputable def ep1113 := nat_lit 11805916207174113034240000000000

noncomputable def ep1114 := nat_lit 23438462845995929941669102003

noncomputable def ep1115 := nat_lit 2575826603997455155923517440000000000

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) ep1112 ep1113 ep1114 ep1115 ep1112 ep1113 ep1114

noncomputable def ep1117 := nat_lit 18730600333081816357815965111

noncomputable def ep1118 := nat_lit 1416709944860893564108800000000

noncomputable def ep1119 := nat_lit 136242023861646843830505091

noncomputable def ep1120 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242) Bool.true ep1112 ep1113 ep1114 ep1115 Bool.false ep1117 ep1118 ep1119

noncomputable def ep1121 := nat_lit 20606612831979641247388139520000000

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242 Bool.true ep1112 ep1113 ep1114 ep1115 Bool.false ep1117 ep1118 ep1119 ep1121

noncomputable def ep1123 := nat_lit 4841998835314971295392959

noncomputable def ep1124 := nat_lit 5666839779443574256435200000

noncomputable def ep1125 := nat_lit 27475483775972854996517519360000

noncomputable def ep1126 := nat_lit 622789234747892459780750205989

noncomputable def ep1127 := nat_lit 35417748621522339102720000000000

noncomputable def ep1128 := nat_lit 22336250749868266453747758253

noncomputable abbrev qz250 := (Complex.re qz453)

noncomputable abbrev qz251 := (Complex.im qz453)

noncomputable def ep1129 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) ep1123 ep1124 11756929025361743871161 ep1125 ep1126 ep1127 ep1128

noncomputable def ep1130 := nat_lit 3357754112103689703193788241708070577397134160350412800000

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250 2986084303 120000000 0 1 40538028601958825 1180591620717411303424 1476464807132625 ep970 ep1123

noncomputable def ep1132 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) 2986084303 120000000 0 1 0 1 0 1 2986084303

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 8958252909 500000 0 1 2986084303 120000000 0

noncomputable abbrev qz457 := (@HAdd.hAdd Complex Complex Complex qz467 qz482 qz471)

noncomputable abbrev qz252 := qz457

noncomputable def ep1134 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz44 (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) qz252) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1

noncomputable abbrev qz253 := (Complex.re qz457)

noncomputable abbrev qz254 := (Complex.im qz457)

noncomputable def ep1135 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) 995278101 100000 0 1 995465601 125000 0 1

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz253 995278101 250000 0 1 5 2 0 1 995278101 100000

noncomputable abbrev qz458 := (@HAdd.hAdd Complex Complex Complex qz467 qz482 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz255 := qz458

noncomputable def ep1137 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz44 (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz255) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1

noncomputable abbrev qz256 := (Complex.re qz458)

noncomputable abbrev qz257 := (Complex.im qz458)

noncomputable def ep1138 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) 3 4 0 1 995465601 250000 0 1

noncomputable def ep1139 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz256 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1140 := @ep1139 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep1141 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz444 qz153) Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 63102 1000 1 qz154)

noncomputable abbrev qz459 := (ep1141 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz153 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz155))

noncomputable def ep1142 := ep1140 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz459)

noncomputable def ep1143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 63102 1000 0 1 63102 1000 0 1 995465601 250000

noncomputable def ep1144 := @ep1143 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep1145 := ep1144 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz459)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz255 Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 (@ep1138 3981112404 995278101 250000 0 1 (ep1142 rfl) (ep1145 rfl) rfl rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz256) 31551 1000 0 1 94653 1000 0 1

noncomputable def ep1148 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz257 1 2 0 1 63102 1000 0 1 31551 1000

noncomputable def ep1149 := @ep1148 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep1150 := ep1149 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz459)

noncomputable def ep1151 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz256 63102 1000 0 1 3 2 0 1 94653 1000

noncomputable def ep1152 := @ep1151 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 63102 1000 0 1 ep847)

noncomputable def ep1153 := ep1152 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 3 2 0 1 Bool.false 63102 1000 0 1 qz459)

noncomputable abbrev qz258 := (ep1137 (BSN.ascPochhammer_succ_eval_c 1 2 qz391 rfl) (ep1146 (@ep1147 126204000 31551 250 0 1 (ep1150 rfl) (ep1153 rfl) rfl rfl)))

noncomputable def ep1154 := @ep1136 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz258)

noncomputable def ep1155 := @Enclosure.Complex.IsNear.of_eq qz252 (Complex.mk qz446 qz153) Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 63102 1000 2 qz154)

noncomputable abbrev qz460 := (ep1155 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz153 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz155))

noncomputable def ep1156 := ep1154 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz460)

noncomputable def ep1157 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 31551 250 0 1 63102 1000 0 1 995465601 125000

noncomputable def ep1158 := @ep1157 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz258)

noncomputable def ep1159 := ep1158 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz460)

noncomputable def ep1160 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) qz252 Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 (@ep1135 223956322725000 8958252909 500000 0 1 (ep1156 rfl) (ep1159 rfl) rfl rfl)

noncomputable def ep1161 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz253) 31402019364651 125000000 0 1 31551 100 0 1

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz254 995278101 250000 0 1 63102 1000 0 1 31402019364651 125000000

noncomputable def ep1163 := @ep1162 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz258)

noncomputable def ep1164 := ep1163 (@Enclosure.Complex.IsNear.im_isNear qz252 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz460)

noncomputable def ep1165 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz253 31551 250 0 1 5 2 0 1 31551 100

noncomputable def ep1166 := @ep1165 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 995278101 250000 0 1 Bool.false 31551 250 0 1 qz258)

noncomputable def ep1167 := ep1166 (@Enclosure.Complex.IsNear.re_isNear qz252 Bool.false 5 2 0 1 Bool.false 63102 1000 0 1 qz460)

noncomputable abbrev qz259 := (ep1134 (BSN.ascPochhammer_succ_eval_c 2 3 qz391 rfl) (ep1160 (@ep1161 3136258061465100 31362580614651 125000000 0 1 (ep1164 rfl) (ep1167 rfl) rfl rfl)))

noncomputable def ep1168 := @ep1133 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz259)

noncomputable def ep1169 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 31362580614651 125000000 0 1 0 1 0

noncomputable def ep1170 := @ep1169 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz259)

noncomputable def ep1171 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) 10454193538217 30000000000 0 1 0 1 0 1 10454193538217

noncomputable def ep1172 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 31362580614651 125000000 0 1 10454193538217 30000000000 0

noncomputable def ep1173 := @ep1172 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz259)

noncomputable def ep1174 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 8958252909 500000 0 1 0 1 0

noncomputable def ep1175 := @ep1174 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep974) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 8958252909 500000 0 1 Bool.true 31362580614651 125000000 0 1 qz259)

noncomputable def ep1176 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 (@ep1132 2986084303 120000000 0 1 (ep1168 rfl) (ep1170 rfl) rfl rfl) (@ep1171 10454193538217 30000000000 0 1 (ep1173 rfl) (ep1175 rfl) rfl rfl)

noncomputable def ep1177 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 ep1176

noncomputable def ep1178 := @Enclosure.Complex.IsNear.re_isNear qz242 Bool.false 40538028601958825 1180591620717411303424 1476464807132625 ep970 Bool.false 59573149518533917 1180591620717411303424 2136582862007909 ep970

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq qz242 (Complex.mk (@HMul.hMul Real Real Real qz0 qz239 qz211) (@HMul.hMul Real Real Real qz0 qz239 qz212)) Bool.false 40538028601958825 1180591620717411303424 1476464807132625 ep970 Bool.false 59573149518533917 1180591620717411303424 2136582862007909

noncomputable def ep1180 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz133 63102 1000 0 1 3121657384082679 1125899906842624 30518159941 145454000000000000000 98491412125192605129 562949953421312000 962878464298491 72727000000000000000000 qz155 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 30518159941 145454000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz386 Bool.false ep1022 ep1023 1000019064946688 ep1024 3121657384082679 1125899906842624 30518159941 145454000000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 17179869184 24973259072661432 36028797018963968 4766236672 1000000000000000 rfl rfl rfl rfl (ep1025 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1181 := nat_lit 369835376872234018475606016

noncomputable def ep1182 := nat_lit 231736180804638534572750141347475433276277259717890148919718682469251389048418695244857939011255319802338030444800

noncomputable def ep1183 := nat_lit 9766728251306921600954201463780427029753454296883539884048629522019609097173013081186404486835249037292134656

noncomputable def ep1184 := nat_lit 606912279785455950769848825298160966460773222239898292868022375352622749093034493143925062279356675745777321042176

noncomputable def ep1185 := BSN.sin_dyadic_bound_f 42045414474186 70368744177664 3 2 34359738368 9541782401 ep1182 ep1036 ep1183 ep1184 ep1039 ep1183 19330047575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 42045414474186) (BSN.sinEvenQ 70368744177664) 0 2 ep1182 ep1036 ep1183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 42045414474186) (BSN.sinOddQ 70368744177664) 0 2 ep1184 ep1039 ep1183 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 751429841043) (@Nat.cast Real Real.instNatCast 4294967296))

noncomputable def ep1186 := @Enclosure.Real.IsNear.cos_image qz213 qz461 Bool.false 751429841043 4294967296 57 4294967296 Bool.false 19330047575 34359738368 1 4766236672 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 98491412125192605129 562949953421312000 962878464298491 72727000000000000000000 751429841043 4294967296 57 4294967296 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 751429841043 4294967296) (BSN.cos_reduce3 qz461 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1181) (@Nat.cast Real Real.instNatCast ep1023)) 226375608064910080 72057594037927936 Bool.false 19330047575 34359738368 27 1000000000000000 9532473344 4766236672 (BSN.sin_reduce_arg_pos_rat_q3 751429841043 4294967296 226375608064910080 72057594037927936 27 ep1181 ep1023 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 19330047575 34359738368 ep1181 ep1023 42045414474186 70368744177664 9541782401 9532473344 (ep1185 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1187 := nat_lit 128746663437355322283350502615914698676611701378515364306458845207149447075386907586290493408247104445315480084736

noncomputable def ep1188 := nat_lit 24241468655984884671616987561611793649609605215227765039851000824877738980510979184756823965407711771199390267473920

noncomputable def ep1189 := nat_lit 386220456855563353006849599444816535175775597226952325839608438362404302007966376732709107415767642837871855984896

noncomputable def ep1190 := nat_lit 1090866089519319810222764440272530714232432234685249426793295037119498254122994063314057078443347029703972562036326400

noncomputable def ep1191 := BSN.cos_dyadic_bound_f 42045414474186 70368744177664 3 2 34359738368 9541782401 ep1187 ep1188 ep1183 ep1189 ep1190 ep1183 28406704867 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 42045414474186) (BSN.cosEvenQ 70368744177664) 0 2 ep1187 ep1188 ep1183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 42045414474186) (BSN.cosOddQ 70368744177664) 0 2 ep1189 ep1190 ep1183 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1192 := @Enclosure.Real.IsNear.sin_image qz213 qz461 Bool.false 751429841043 4294967296 57 4294967296 Bool.true 28406704867 34359738368 1 4766236672 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 98491412125192605129 562949953421312000 962878464298491 72727000000000000000000 751429841043 4294967296 57 4294967296 (ep1180 rfl) rfl) (Enclosure.sfrac_false_div 751429841043 4294967296) (BSN.sin_reduce3 qz461 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1181) (@Nat.cast Real Real.instNatCast ep1023)) 226375608064910080 72057594037927936 Bool.false 28406704867 34359738368 27 1000000000000000 9532473344 4766236672 (BSN.sin_reduce_arg_pos_rat_q3 751429841043 4294967296 226375608064910080 72057594037927936 27 ep1181 ep1023 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 28406704867 34359738368 ep1181 ep1023 42045414474186 70368744177664 9541782401 9532473344 (ep1191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1193 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz239 qz211) (@HMul.hMul Real Real Real qz0 qz239 qz212) Bool.false 40538028601958825 1180591620717411303424 1476464807132625 ep970 Bool.false 59573149518533917 1180591620717411303424 2136582862007909 ep970 (@Enclosure.Real.IsNear.mulLit_ff qz239 qz211 2097151 34359738368 1 34359738368 19330047575 34359738368 4210975 312360086536192 40538028601958825 1180591620717411303424 1476464807132625 ep970 qz450 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 19330047575 34359738368 275970457600 20470830631235878912 19330047575 34359738368 4210975 312360086536192 (ep1186 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz239 qz212 2097151 34359738368 1 34359738368 28406704867 34359738368 4210975 312360086536192 59573149518533917 1180591620717411303424 2136582862007909 ep970 qz450 (@Enclosure.Real.IsNear.neg qz214 Bool.true 28406704867 34359738368 4210975 312360086536192 (@Enclosure.Real.IsNear.recentre' qz214 Bool.true 28406704867 34359738368 275970457600 20470830631235878912 28406704867 34359738368 4210975 312360086536192 (ep1192 rfl rfl) rfl)) rfl)

noncomputable def ep1194 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 10454193538217 30000000000 0 1 59573149518533917 1180591620717411303424 2136582862007909 ep970 ep1126

noncomputable def ep1195 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2986084303 120000000 0 1 Bool.false 10454193538217 30000000000 0 1 ep1176

noncomputable def ep1196 := @Enclosure.Complex.IsNear.im_isNear qz242 Bool.false 40538028601958825 1180591620717411303424 1476464807132625 ep970 Bool.false 59573149518533917 1180591620717411303424 2136582862007909 ep970

noncomputable def ep1197 := nat_lit 177890446657566137126804851

noncomputable def ep1198 := nat_lit 141670994486089356410880000000

noncomputable def ep1199 := nat_lit 6380016546300632126752427

noncomputable def ep1200 := nat_lit 10303306415989820623694069760000000

noncomputable def ep1201 := nat_lit 16951695866506154986547916601

noncomputable def ep1202 := nat_lit 41160663589681859859000079

noncomputable def ep1203 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250) ep1197 ep1198 ep1199 ep1200 ep1201 ep1118 ep1202

noncomputable def ep1204 := nat_lit 6868870943993213749129379840000000

noncomputable def ep1205 := nat_lit 2653582776509177467834402119882375086423882260807680000000

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz251 2986084303 120000000 0 1 59573149518533917 1180591620717411303424 2136582862007909 ep970 ep1197

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz250 10454193538217 30000000000 0 1 40538028601958825 1180591620717411303424 1476464807132625 ep970 ep1201

noncomputable abbrev qz462 := (@ep1179 ep970 (BSN.cpow_neg_s_sub_mk qz153 63102 1000 16 3 268435456 qz154 rfl EMRow14.d15) ep1193)

noncomputable def ep1208 := ep1122 (@ep1129 ep1115 ep1130 ep1112 ep1113 ep1114 ep1115 (@ep1131 ep1124 11756929025361743871161 ep1125 ep1177 (ep1178 qz462) rfl) (@ep1194 ep1127 ep1128 ep1115 ep1195 (ep1196 qz462) rfl) rfl rfl) (@ep1203 ep1204 ep1205 ep1117 ep1118 ep1119 ep1121 (@ep1206 ep1198 ep1199 ep1200 ep1177 (ep1196 qz462) rfl) (@ep1207 ep1118 ep1202 ep1204 ep1195 (ep1178 qz462) rfl) rfl rfl)

noncomputable def ep1209 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (Complex.im (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) ep1117 ep1118 ep1119 ep1121 ep1117 ep1118 ep1119

noncomputable def ep1210 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242) Bool.true ep1112 ep1113 ep1114 ep1115 Bool.false ep1117 ep1118 ep1119

noncomputable def ep1211 := @ep1082 24276357096774409 63050394783186944 13555703071 63050394783186944 (@ep1083 1 1835008 (ep1084 (@ep1085 524288 1 524288 (ep1086 (@ep1087 3994112404 998528101 250000 0 1 (ep1091 rfl) (ep1094 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1095 387 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)) (@ep1096 387 34359738368 732661633 34359738368 387 34359738368 (@ep1101 366330623 366331010 17179869184 (@ep1107 ep1108 ep1109 ep1110 ep1111 ep1097 ep1098 ep1099 ep1100 (@ep1116 ep1115 ep1102 ep1103 ep1104 ep1105 (@ep1120 ep1121 ep1208) (@ep1120 ep1121 ep1208) rfl) (@ep1209 ep1121 ep1106 ep1108 ep1109 ep1110 (@ep1210 ep1121 ep1208) (@ep1210 ep1121 ep1208) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow14.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) Bool.false 254167506291159889 567453553048682496 45151857182231 567453553048682496 := ep1080 (ep1081 ep1211) rfl rfl

noncomputable def EMRow14.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz463 := (EMRow14.d3 qz472 qz484 (@Enclosure.dec_le_dec qz472 qz484 60352 1000 63102 1000 (@Eq.refl Real qz472) (@Eq.refl Real qz484) rfl rfl rfl) 16 16 1 1)

noncomputable abbrev qz260 := qz463

noncomputable def ep1212 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz260 (@Enclosure.dec_nonneg qz17 60352 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 16 rfl)

noncomputable abbrev qz261 := (Zeta.Certificates.ZIntervalEM.fstVal qz463)

noncomputable def ep1213 := @Enclosure.Real.IsNear.pos_val qz261 ep159 ep160

noncomputable def ep1214 := @Enclosure.Real.IsNear.of_eq qz261 (hardyZApproximantEM 1 16 qz17) Bool.false

noncomputable abbrev qz262 := (Zeta.Certificates.ZIntervalEM.sndVal qz463)

noncomputable def ep1215 := BSN.mul_neg_of_pos_neg_r qz261 qz262 (@ep1213 ep161 ep162 (@ep1214 ep159 ep160 ep161 ep162 (@Eq.refl Real (hardyZApproximantEM 1 16 qz17)) EMRow14.d9) rfl rfl rfl)

noncomputable def ep1216 := @Enclosure.Real.IsNear.neg_val qz262 ep580 ep581

noncomputable def ep1217 := @Enclosure.Real.IsNear.of_eq qz262 (hardyZApproximantEM 1 16 qz153) Bool.true

noncomputable def ep1218 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz261) (BSN.hardyZErrorBoundStrong 1 16 qz17)

noncomputable def ep1219 := @Enclosure.norm_gt_of_isNear qz261 (BSN.hardyZErrorBoundStrong 1 16 qz17) Bool.false

noncomputable def ep1220 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 16 qz17) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))) Bool.false 93825895524071701 283726776524341248 63113124753547 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 16))) (@HMul.hMul Real Real Real qz0 qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz219)))))

noncomputable def ep1221 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz262) (BSN.hardyZErrorBoundStrong 1 16 qz153)

noncomputable def ep1222 := @Enclosure.norm_gt_of_isNear qz262 (BSN.hardyZErrorBoundStrong 1 16 qz153) Bool.true

noncomputable def ep1223 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 16 qz153) (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))) Bool.false 254167506291159889 567453553048682496 45151857182231 567453553048682496 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz343 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 16))) (@HMul.hMul Real Real Real qz0 qz241 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz44 (@HMul.hMul Complex Complex Complex qz44 (@HDiv.hDiv Complex Complex Complex qz51 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz217)) ↑qz218) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz242)))))

noncomputable def ep1224 := @List.cons EMRow14.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz260 (ep1212 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 16 rfl) (ep1215 (@ep1216 ep582 ep583 (@ep1217 ep580 ep581 ep582 ep583 (@Eq.refl Real (hardyZApproximantEM 1 16 qz153)) EMRow14.d11) rfl rfl rfl)) (ep1218 (hardyZErrorBoundEM 1 16 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 16 qz17 rfl) (@ep1219 Bool.false ep159 ep160 ep161 ep162 93825895524071701 283726776524341248 63113124753547 851180329573023744 (@ep1214 ep159 ep160 ep161 ep162 (@Eq.refl Real (hardyZApproximantEM 1 16 qz17)) EMRow14.d9) (ep1220 EMRow14.d16) rfl rfl rfl rfl rfl)) (ep1221 (hardyZErrorBoundEM 1 16 qz153) (BSN.hardyZErrorBoundEM_le_strong 1 16 qz153 rfl) (@ep1222 Bool.false ep580 ep581 ep582 ep583 254167506291159889 567453553048682496 45151857182231 567453553048682496 (@ep1217 ep580 ep581 ep582 ep583 (@Eq.refl Real (hardyZApproximantEM 1 16 qz153)) EMRow14.d11) (ep1223 EMRow14.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow14.d0)

noncomputable abbrev qz464 := (@Enclosure.dec_le_dec qz472 qz484 60352 1000 63102 1000 (@Eq.refl Real qz472) (@Eq.refl Real qz484) rfl rfl rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1224 (@List.IsChain.singleton EMRow14.d1 EMRow14.d18 (EMRow14.d2 qz278 qz393 qz464))))

noncomputable abbrev qz465 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1225 := And (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz465 qz263)) (@Option.some Real qz17))

noncomputable def ep1226 := ep1225 (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz465 qz263)) (@Option.some Real qz153))

noncomputable def ep1227 := @And.intro (@Eq Nat (@List.length qz465 qz263) 1) ep1226

noncomputable def ep1228 := @And.intro (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz465 qz263)) (@Option.some Real qz17))

noncomputable def ep1229 := @ep1228 (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz465 qz263)) (@Option.some Real qz153))

noncomputable abbrev qz264 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1224 (@List.IsChain.singleton EMRow14.d1 EMRow14.d18 (EMRow14.d2 qz278 qz393 qz464)))

theorem EMRow14.d19 : Zeta.Certificates.BatchSpec 1 60352 1000 63102 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz465 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz465 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz465 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz465 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz153)))) qz264 (ep1227 (@Eq.refl Nat 1) (ep1229 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz153))))

theorem solution : Zeta.Certificates.BatchSpec 1 60352 1000 63102 1000 := EMRow14.d19
#print axioms solution
#check solution
