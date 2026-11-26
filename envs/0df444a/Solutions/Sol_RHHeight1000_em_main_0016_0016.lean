-- Prove2me | solution 1 for RHHeight1000.em_main_0016_0016
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:11:10.638187+00:00
-- url     : https://prove2.me/submissions/c2d34bb8-2c73-460b-85f5-451ba3f60401

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow16.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow16.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow16.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow16.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow16.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz262 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz262

noncomputable abbrev qz1 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz263 := (@HMul.hMul Real Real Real qz0 qz1 Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz263 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 125000000037693 18846500000000000000 4138529546116343 2251799813685248 125000000037693 18846500000000000000 481788 262144

noncomputable abbrev qz264 := (@Enclosure.Real.IsNear.mulLit_ff qz1 Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz264 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 150772 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz265 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz2 := qz265

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 125000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000301544 150772000000000000000 4138529546116343 2251799813685248 125000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 150772 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 125000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000301544 150772000000000000000 4138529546116343 2251799813685248 125000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz266 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz3 := (Real.log qz266)

theorem EMRow16.d4 : Enclosure.Real.IsNear qz3 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz3 (Real.log qz263) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz263) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 150772 600168 524288 1 150772 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 150772 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 150772 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 150772 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 150772 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 150772 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 150772 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow16.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz471 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 65801 1000)))

noncomputable abbrev qz448 := qz471

noncomputable abbrev qz267 := qz448

noncomputable abbrev qz4 := (BSN.headSumC qz267 9)

noncomputable abbrev qz472 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz449 := qz472

noncomputable abbrev qz268 := qz449

noncomputable abbrev qz5 := qz268

noncomputable abbrev qz6 := qz267

noncomputable abbrev qz450 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz269 := qz450

noncomputable abbrev qz451 := (@Neg.neg Complex Complex.instNeg qz471)

noncomputable abbrev qz270 := qz451

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 8) qz270)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz4 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 8) qz7) Bool.true 1151657567 68719476736 7780508230103 2590243236610048 Bool.false 29824012517 137438953472 1946286503629 647560809152512

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 8) qz7 Bool.true 10526573903 137438953472 13935042372731 5180486473220096 Bool.true 36133671141 274877906944 27872503316807 10360972946440192 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 7) qz270)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 7) qz8) Bool.true 10526573903 137438953472 13935042372731 5180486473220096 Bool.true 36133671141 274877906944 27872503316807 10360972946440192

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 7) qz8 Bool.false 13514936173 68719476736 6093849314175 2590243236610048 Bool.false 17822168115 137438953472 12189225081771 5180486473220096 Bool.true

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 6) qz270)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 6) qz9) Bool.false 13514936173 68719476736 6093849314175 2590243236610048 Bool.false 17822168115 137438953472 12189225081771 5180486473220096

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 6) qz9 Bool.false 43998841497 274877906944 20614391533995 10360972946440192 Bool.true 38060846317 137438953472 10299766910167 5180486473220096 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 5) qz270)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 5) qz10) Bool.false 43998841497 274877906944 20614391533995 10360972946440192 Bool.true 38060846317 137438953472 10299766910167 5180486473220096

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 5) qz10 Bool.true 31288216527 274877906944 16493075567607 10360972946440192 Bool.true 173299010967 274877906944 16474698797773 10360972946440192 Bool.false

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 4) qz270)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 4) qz11) Bool.true 31288216527 274877906944 16493075567607 10360972946440192 Bool.true 173299010967 274877906944 16474698797773 10360972946440192

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 4) qz11 Bool.false 26317680723 68719476736 5934672206387 5180486473220096 Bool.true 47205190035 68719476736 5934185665143 5180486473220096 Bool.true

noncomputable abbrev qz452 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz271 := qz452

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz269 qz271 qz270)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 3) qz12) Bool.false 26317680723 68719476736 5934672206387 5180486473220096 Bool.true 47205190035 68719476736 5934185665143 5180486473220096

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 3) qz12 Bool.false 8246408759 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 4294967296 3275338639779 5180486473220096 Bool.true

noncomputable abbrev qz453 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz272 := qz453

noncomputable abbrev qz13 := (@HPow.hPow Complex Complex Complex qz269 qz272 qz270)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 2) qz13) Bool.false 8246408759 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 4294967296 3275338639779 5180486473220096

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 2) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz273 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz14 := qz273

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz6)

noncomputable abbrev qz274 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz15 := (@Inv.inv Real Real.instInv (Real.sqrt qz274))

noncomputable abbrev qz473 := (Enclosure.sfrac Bool.false 65801 1000)

noncomputable abbrev qz454 := qz473

noncomputable abbrev qz275 := qz454

noncomputable abbrev qz16 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz17 := qz275

noncomputable abbrev qz276 := (@Eq.refl Real qz454)

noncomputable abbrev qz18 := qz276

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz13 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)))) Bool.true 343525833 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 4294967296 3275338639779 5180486473220096 (BSN.cpow_neg_s_mk qz17 65801 1000 2 qz18 rfl)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz274) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz274) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz274 qz19)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz274 qz19)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 75386 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz277 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz278 := (BSN.sinOddQ 1073741824)

noncomputable def ep56 := BSN.sin_dyadic_bound_f 60761553 1073741824 1 0 524288 150920 0 1 1 0 1 1 29652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 60761553) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 60761553) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz21 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz22 := (Enclosure.Real.IsNear.const Bool.false 65801 1000)

noncomputable abbrev qz23 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz279 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23912609) qz20)

noncomputable abbrev qz280 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 75386 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 75386 rfl rfl rfl (ep55 rfl)))

noncomputable def ep57 := @Enclosure.Real.IsNear.cos_image qz16 qz279 Bool.false 23912609 524288 459 524288 Bool.true 29652 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 1494538113 32768000 65801 75386000 23912609 524288 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 65801 1000 0 1 181704 262144 1 75386 1494538113 32768000 65801 75386000 qz22 qz280 rfl) rfl) (Enclosure.sfrac_false_div 23912609 524288) (BSN.cos_reduce1 qz279 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4275714186472102821888) qz23) 226375608064910080 72057594037927936 Bool.false 29652 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q1 23912609 524288 226375608064910080 72057594037927936 7 4275714186472102821888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 29652 524288 4275714186472102821888 75557863725914323419136 60761553 1073741824 150920 150772 (ep56 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz281 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz282 := (BSN.cosOddQ 1073741824)

noncomputable def ep58 := BSN.cos_dyadic_bound_f 60761553 1073741824 1 0 524288 150920 0 1 1 0 1 1 523448 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 60761553) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 60761553) qz282 0 0 rfl) rfl rfl

noncomputable def ep59 := @Enclosure.Real.IsNear.sin_image qz16 qz279 Bool.false 23912609 524288 459 524288 Bool.false 523448 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz16 Bool.false 1494538113 32768000 65801 75386000 23912609 524288 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz21 65801 1000 0 1 181704 262144 1 75386 1494538113 32768000 65801 75386000 qz22 qz280 rfl) rfl) (Enclosure.sfrac_false_div 23912609 524288) (BSN.sin_reduce1 qz279 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 4275714186472102821888) qz23) 226375608064910080 72057594037927936 Bool.false 523448 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q1 23912609 524288 226375608064910080 72057594037927936 7 4275714186472102821888 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523448 524288 4275714186472102821888 75557863725914323419136 60761553 1073741824 150920 150772 (ep58 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz283 := (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep60 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz16)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16))) Bool.true 343525833 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 4294967296 3275338639779 5180486473220096 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz16) 46341 65536 1 262144 7413 131072 17563231 19761987584 343525833 8589934592 3256725987151 5180486473220096 qz283 (@Enclosure.Real.IsNear.recentre' (Real.cos qz16) Bool.true 29652 524288 35126462 39523975168 7413 131072 17563231 19761987584 (ep57 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz15 (@Neg.neg Real Real.instNeg (Real.sin qz16)) 46341 65536 1 262144 65431 65536 17563231 19761987584 3032137971 4294967296 3275338639779 5180486473220096 qz283 (@Enclosure.Real.IsNear.neg (Real.sin qz16) Bool.false 65431 65536 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz16) Bool.false 523448 524288 35126462 39523975168 65431 65536 17563231 19761987584 (ep59 rfl rfl) rfl)) rfl)

noncomputable abbrev qz284 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz24 := qz284

noncomputable def ep61 := @ep51 343525833 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 4294967296 3275338639779 5180486473220096 Bool.false 8246408759 8246408759 8589934592 3256725987151 5180486473220096 Bool.true 3032137971 3032137971 4294967296 3275338639779 5180486473220096 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep53 ep60) rfl rfl

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep62 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 39653589349 68719476736 669486554809 1295121618305024 Bool.false 1309017501 68719476736 664711756341 1295121618305024 (BSN.cpow_neg_s_mk qz17 65801 1000 3 qz18 rfl)

noncomputable abbrev qz27 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep63 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz27) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz27) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz27 qz19)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep64 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 75386 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep65 := BSN.cos_dyadic_bound_f 35433326 1073741824 1 0 524288 150920 0 1 1 0 1 1 524002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 35433326) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 35433326) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz28 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18950293) qz28)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 75386 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 75386 rfl rfl rfl (ep64 rfl)))

noncomputable def ep66 := @Enclosure.Real.IsNear.cos_image qz26 qz285 Bool.false 18950293 262144 459 524288 Bool.true 524002 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 9475146597 131072000 65801 75386000 18950293 262144 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 65801 1000 0 1 287994 262144 1 75386 9475146597 131072000 65801 75386000 qz22 qz286 rfl) rfl) (Enclosure.sfrac_false_div 18950293 262144) (BSN.cos_reduce2 qz285 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1246699361456751640576) qz30) 226375608064910080 72057594037927936 Bool.false 524002 524288 11 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 18950293 262144 226375608064910080 72057594037927936 11 1246699361456751640576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524002 524288 1246699361456751640576 37778931862957161709568 35433326 1073741824 150920 150772 (ep65 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 35433326 1073741824 1 0 524288 150920 0 1 1 0 1 1 17298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 35433326) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 35433326) qz278 0 0 rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz26 qz285 Bool.false 18950293 262144 459 524288 Bool.true 17298 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 9475146597 131072000 65801 75386000 18950293 262144 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz29 65801 1000 0 1 287994 262144 1 75386 9475146597 131072000 65801 75386000 qz22 qz286 rfl) rfl) (Enclosure.sfrac_false_div 18950293 262144) (BSN.sin_reduce2 qz285 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1246699361456751640576) qz30) 226375608064910080 72057594037927936 Bool.false 17298 524288 11 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 18950293 262144 226375608064910080 72057594037927936 11 1246699361456751640576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 17298 524288 1246699361456751640576 37778931862957161709568 35433326 1073741824 150920 150772 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep63 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 39653589349 68719476736 669486554809 1295121618305024 Bool.false 1309017501 68719476736 664711756341 1295121618305024 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz26) 151349 262144 1 262144 262001 262144 17563231 19761987584 39653589349 68719476736 669486554809 1295121618305024 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 524002 524288 35126462 39523975168 262001 262144 17563231 19761987584 (ep66 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 151349 262144 1 262144 8649 262144 17563231 19761987584 1309017501 68719476736 664711756341 1295121618305024 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 8649 262144 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 17298 524288 35126462 39523975168 8649 262144 17563231 19761987584 (ep68 rfl rfl) rfl)) rfl)

noncomputable def ep70 := @ep49 39653589349 68719476736 669486554809 1295121618305024 Bool.false 1309017501 68719476736 664711756341 1295121618305024 Bool.false 226067156023709270016 26317680723 68719476736 5934672206387 5180486473220096 Bool.true 202744747401790095360 47205190035 68719476736 5934185665143 5180486473220096 (ep50 (BSN.head_sum_c_succ qz6 2 3 rfl rfl) (ep61 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep62 ep69) rfl rfl

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz288))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 136558939419 274877906944 4623731154833 10360972946440192 Bool.false 15521749173 274877906944 4606327467487 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 4 qz18 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz288) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz288) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz288 qz19)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := nat_lit 471225594319403171539306640625

noncomputable def ep74 := nat_lit 73155514365408823868279100600

noncomputable def ep75 := BSN.log_dyadic_bound 3 5 13 12 ep73 262144 75386 ep74 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep74 ep73 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep76 := nat_lit 218104547316128408188501092848656

noncomputable def ep77 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep78 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep79 := BSN.cos_dyadic_bound_f 121525154 1073741824 2 1 524288 150920 ep76 ep77 ep76 ep76 ep78 ep76 520933 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 121525154) qz281 0 1 ep76 ep77 ep76 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 121525154) qz282 0 1 ep76 ep78 ep76 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz33 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 47825219) qz20)

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 75386 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 75386 rfl rfl rfl (ep75 rfl)))

noncomputable def ep80 := @Enclosure.Real.IsNear.cos_image qz32 qz289 Bool.false 47825219 524288 459 524288 Bool.true 520933 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 1494538113 16384000 65801 75386000 47825219 524288 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 65801 1000 0 1 363408 262144 1 75386 1494538113 16384000 65801 75386000 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 47825219 524288) (BSN.cos_reduce2 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8551572488132281499648) qz23) 226375608064910080 72057594037927936 Bool.false 520933 524288 14 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 47825219 524288 226375608064910080 72057594037927936 14 8551572488132281499648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 520933 524288 8551572488132281499648 75557863725914323419136 121525154 1073741824 150920 150772 (ep79 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep81 := BSN.sin_dyadic_bound_f 121525154 1073741824 1 0 524288 150920 0 1 1 0 1 1 59211 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 121525154) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 121525154) qz278 0 0 rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz32 qz289 Bool.false 47825219 524288 459 524288 Bool.true 59211 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 1494538113 16384000 65801 75386000 47825219 524288 459 524288 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz33 65801 1000 0 1 363408 262144 1 75386 1494538113 16384000 65801 75386000 qz22 qz290 rfl) rfl) (Enclosure.sfrac_false_div 47825219 524288) (BSN.sin_reduce2 qz289 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8551572488132281499648) qz23) 226375608064910080 72057594037927936 Bool.false 59211 524288 14 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 47825219 524288 226375608064910080 72057594037927936 14 8551572488132281499648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 59211 524288 8551572488132281499648 75557863725914323419136 121525154 1073741824 150920 150772 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz291 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 136558939419 274877906944 4623731154833 10360972946440192 Bool.false 15521749173 274877906944 4606327467487 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz32) 262143 524288 1 524288 520933 524288 17563231 19761987584 136558939419 274877906944 4623731154833 10360972946440192 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 520933 524288 35126462 39523975168 520933 524288 17563231 19761987584 (ep80 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 262143 524288 1 524288 59211 524288 17563231 19761987584 15521749173 274877906944 4606327467487 10360972946440192 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 59211 524288 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 59211 524288 35126462 39523975168 59211 524288 17563231 19761987584 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep47 136558939419 274877906944 4623731154833 10360972946440192 Bool.false 15521749173 274877906944 4606327467487 10360972946440192 Bool.true 2150109867738107215872 31288216527 274877906944 16493075567607 10360972946440192 Bool.true 11909017352518565363712 173299010967 274877906944 16474698797773 10360972946440192 (ep48 (BSN.head_sum_c_succ qz6 3 4 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz292))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 9410882253 34359738368 1030328991597 2590243236610048 Bool.false 97177318333 274877906944 4124835022561 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 5 qz18 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz292) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz292) (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz292 qz19)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz292 qz19)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 39510257877627786146545168145625

noncomputable def ep88 := nat_lit 8181717556663416291180905432700

noncomputable def ep89 := nat_lit 6646766139202842132480000

noncomputable def ep90 := BSN.log_dyadic_bound 2 3 16 15 ep87 262144 75386 ep88 ep89 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 250915008832927338603244895516102656

noncomputable def ep92 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep93 := nat_lit 1116551516459329333239197930635489443840

noncomputable def ep94 := BSN.sin_dyadic_bound_f 707752904 1073741824 2 1 524288 150920 ep91 ep92 ep91 ep91 ep93 ep91 321096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 707752904) qz277 0 1 ep91 ep92 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 707752904) qz278 0 1 ep91 ep93 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz36 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 27761705) qz28)

noncomputable abbrev qz294 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 75386 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 75386 rfl rfl rfl (ep90 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz35 qz293 Bool.false 27761705 262144 229 262144 Bool.false 321096 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 1735106569 16384000 65801 75386000 27761705 262144 229 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 65801 1000 0 1 421904 262144 1 75386 1735106569 16384000 65801 75386000 qz22 qz294 rfl) rfl) (Enclosure.sfrac_false_div 27761705 262144) (BSN.cos_reduce3 qz293 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24901841543386544209920) qz30) 226375608064910080 72057594037927936 Bool.false 321096 524288 16 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 27761705 262144 226375608064910080 72057594037927936 16 24901841543386544209920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 321096 524288 24901841543386544209920 37778931862957161709568 707752904 1073741824 150920 150772 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := BSN.cos_dyadic_bound_f 707752904 1073741824 2 1 524288 150920 ep91 ep77 ep91 ep91 ep78 ep91 414457 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 707752904) qz281 0 1 ep91 ep77 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 707752904) qz282 0 1 ep91 ep78 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep97 := @Enclosure.Real.IsNear.sin_image qz35 qz293 Bool.false 27761705 262144 229 262144 Bool.true 414457 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 1735106569 16384000 65801 75386000 27761705 262144 229 262144 (@Enclosure.Real.IsNear.mulLit_ff qz17 qz36 65801 1000 0 1 421904 262144 1 75386 1735106569 16384000 65801 75386000 qz22 qz294 rfl) rfl) (Enclosure.sfrac_false_div 27761705 262144) (BSN.sin_reduce3 qz293 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24901841543386544209920) qz30) 226375608064910080 72057594037927936 Bool.false 414457 524288 16 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 27761705 262144 226375608064910080 72057594037927936 16 24901841543386544209920 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 414457 524288 24901841543386544209920 37778931862957161709568 707752904 1073741824 150920 150772 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz295 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep86 rfl rfl) rfl)

noncomputable def ep98 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 9410882253 34359738368 1030328991597 2590243236610048 Bool.false 97177318333 274877906944 4124835022561 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 234469 524288 1 524288 40137 65536 8762769 9880993792 9410882253 34359738368 1030328991597 2590243236610048 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 321096 524288 17525538 19761987584 40137 65536 8762769 9880993792 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 234469 524288 1 524288 414457 524288 8762769 9880993792 97177318333 274877906944 4124835022561 10360972946440192 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 414457 524288 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 414457 524288 17525538 19761987584 414457 524288 8762769 9880993792 (ep97 rfl rfl) rfl)) rfl)

noncomputable def ep99 := @ep45 9410882253 34359738368 1030328991597 2590243236610048 Bool.false 97177318333 274877906944 4124835022561 10360972946440192 Bool.false 1511788682332021456896 43998841497 274877906944 20614391533995 10360972946440192 Bool.true 20924171544268422250496 38060846317 137438953472 10299766910167 5180486473220096 (ep46 (BSN.head_sum_c_succ qz6 4 5 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep98) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep100 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.false 10060903195 274877906944 3761005722705 10360972946440192 Bool.false 1746344201 4294967296 472364542901 1295121618305024 (BSN.cpow_neg_s_mk qz17 65801 1000 6 qz18 rfl)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 6) qz19)

noncomputable def ep101 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt qz297) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz297) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep102 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 75386 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz39 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable def ep103 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz39 65801 1000 0 1 4034681531866359 2251799813685248 250000000037693 18846500000000000000 265486079478338288559 2251799813685248000 16450250002480237093 18846500000000000000000 qz22 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz297) Bool.false 16922680887833197019136 9444732965739290427392 1000000000150772 75386000000000000000 4034681531866359 2251799813685248 250000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep104 := BSN.sin_dyadic_bound_f 96397632 1073741824 1 0 524288 150920 0 1 1 0 1 1 47005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 96397632) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 96397632) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 30906647) qz28)

noncomputable def ep105 := @Enclosure.Real.IsNear.cos_image qz38 qz298 Bool.false 30906647 262144 459 524288 Bool.false 47005 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 265486079478338288559 2251799813685248000 16450250002480237093 18846500000000000000000 30906647 262144 459 524288 (ep103 rfl) rfl) (Enclosure.sfrac_false_div 30906647 262144) (BSN.cos_reduce3 qz298 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3391690156502557917184) qz30) 226375608064910080 72057594037927936 Bool.false 47005 524288 18 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 30906647 262144 226375608064910080 72057594037927936 18 3391690156502557917184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 47005 524288 3391690156502557917184 37778931862957161709568 96397632 1073741824 150920 150772 (ep104 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep106 := nat_lit 86350620465041913498342864715776

noncomputable def ep107 := BSN.cos_dyadic_bound_f 96397632 1073741824 2 1 524288 150920 ep106 ep77 ep106 ep106 ep78 ep106 522176 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 96397632) qz281 0 1 ep106 ep77 ep106 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 96397632) qz282 0 1 ep106 ep78 ep106 rfl rfl rfl rfl) rfl rfl

noncomputable def ep108 := @Enclosure.Real.IsNear.sin_image qz38 qz298 Bool.false 30906647 262144 459 524288 Bool.true 522176 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 265486079478338288559 2251799813685248000 16450250002480237093 18846500000000000000000 30906647 262144 459 524288 (ep103 rfl) rfl) (Enclosure.sfrac_false_div 30906647 262144) (BSN.sin_reduce3 qz298 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3391690156502557917184) qz30) 226375608064910080 72057594037927936 Bool.false 522176 524288 18 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 30906647 262144 226375608064910080 72057594037927936 18 3391690156502557917184 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522176 524288 3391690156502557917184 37778931862957161709568 96397632 1073741824 150920 150772 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep101 rfl rfl) rfl)

noncomputable def ep109 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.false 10060903195 274877906944 3761005722705 10360972946440192 Bool.false 1746344201 4294967296 472364542901 1295121618305024 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz38) 214039 524288 1 524288 47005 524288 17563231 19761987584 10060903195 274877906944 3761005722705 10360972946440192 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 47005 524288 35126462 39523975168 47005 524288 17563231 19761987584 (ep105 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 214039 524288 1 524288 8159 8192 17563231 19761987584 1746344201 4294967296 472364542901 1295121618305024 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.true 8159 8192 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.true 522176 524288 35126462 39523975168 8159 8192 17563231 19761987584 (ep108 rfl rfl) rfl)) rfl)

noncomputable def ep110 := @ep43 10060903195 274877906944 3761005722705 10360972946440192 Bool.false 1746344201 4294967296 472364542901 1295121618305024 Bool.false 14859829470863973941248 13514936173 68719476736 6093849314175 2590243236610048 Bool.false 76545629197738967040 17822168115 137438953472 12189225081771 5180486473220096 (ep44 (BSN.head_sum_c_succ qz6 5 6 rfl rfl) (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep100 ep109) rfl rfl

noncomputable abbrev qz300 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz300))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 37556446249 137438953472 1747343744381 5180486473220096 Bool.true 71778007371 274877906944 3494053153265 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 7 qz18 rfl)

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 7) qz19)

noncomputable def ep112 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz300) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz300) (Real.sqrt qz301) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz301) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep113 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 75386 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz42 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable def ep114 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz42 65801 1000 0 1 4381792198794487 2251799813685248 250000000037693 18846500000000000000 288326308472876039087 2251799813685248000 16450250002480237093 18846500000000000000000 qz22 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 18378568546572512002048 9444732965739290427392 1000000000150772 75386000000000000000 4381792198794487 2251799813685248 250000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep115 := nat_lit 566834078788479688673435720874328801

noncomputable def ep116 := BSN.sin_dyadic_bound_f 867688793 1073741824 2 1 524288 150920 ep115 ep92 ep115 ep115 ep93 ep115 379046 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 867688793) qz277 0 1 ep115 ep92 ep115 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 867688793) qz278 0 1 ep115 ep93 ep115 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 67131199) qz20)

noncomputable def ep117 := @Enclosure.Real.IsNear.cos_image qz41 qz302 Bool.false 67131199 524288 459 524288 Bool.true 379046 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 288326308472876039087 2251799813685248000 16450250002480237093 18846500000000000000000 67131199 524288 459 524288 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 67131199 524288) (BSN.cos_reduce1 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 61058170750725980684288) qz23) 226375608064910080 72057594037927936 Bool.false 379046 524288 20 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q1 67131199 524288 226375608064910080 72057594037927936 20 61058170750725980684288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379046 524288 61058170750725980684288 75557863725914323419136 867688793 1073741824 150920 150772 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep118 := nat_lit 1266120201377083902780723658605478440324530787869463287025998030853826169281

noncomputable def ep119 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep120 := nat_lit 321300872875984399323568179318689158186968346593315068000794292258097601

noncomputable def ep121 := nat_lit 3797718002385499739543523839457797942657218426915203230941992503976962312641

noncomputable def ep122 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable def ep123 := BSN.cos_dyadic_bound_f 867688793 1073741824 3 2 524288 150920 ep118 ep119 ep120 ep121 ep122 ep120 362217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 867688793) qz281 0 2 ep118 ep119 ep120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 867688793) qz282 0 2 ep121 ep122 ep120 rfl rfl rfl rfl) rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.sin_image qz41 qz302 Bool.false 67131199 524288 459 524288 Bool.false 362217 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 288326308472876039087 2251799813685248000 16450250002480237093 18846500000000000000000 67131199 524288 459 524288 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 67131199 524288) (BSN.sin_reduce1 qz302 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 61058170750725980684288) qz23) 226375608064910080 72057594037927936 Bool.false 362217 524288 20 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q1 67131199 524288 226375608064910080 72057594037927936 20 61058170750725980684288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 362217 524288 61058170750725980684288 75557863725914323419136 867688793 1073741824 150920 150772 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep112 rfl rfl) rfl)

noncomputable def ep125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 37556446249 137438953472 1747343744381 5180486473220096 Bool.true 71778007371 274877906944 3494053153265 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 198163 524288 1 524288 189523 262144 17563231 19761987584 37556446249 137438953472 1747343744381 5180486473220096 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 379046 524288 35126462 39523975168 189523 262144 17563231 19761987584 (ep117 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 198163 524288 1 524288 362217 524288 17563231 19761987584 71778007371 274877906944 3494053153265 10360972946440192 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.false 362217 524288 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.false 362217 524288 35126462 39523975168 362217 524288 17563231 19761987584 (ep124 rfl rfl) rfl)) rfl)

noncomputable def ep126 := @ep41 37556446249 137438953472 1747343744381 5180486473220096 Bool.true 71778007371 274877906944 3494053153265 10360972946440192 Bool.true 723380650436993220608 10526573903 137438953472 13935042372731 5180486473220096 Bool.true 4966173946720448151552 36133671141 274877906944 27872503316807 10360972946440192 (ep42 (BSN.head_sum_c_succ qz6 6 7 rfl rfl) (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep111 ep125) rfl rfl

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz304))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep127 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.false 8223258769 137438953472 1625974087475 5180486473220096 Bool.false 95781696175 274877906944 3268080741257 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 8 qz18 rfl)

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 8) qz19)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz304) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz304) (Real.sqrt qz305) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz305) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep129 := BSN.log_dyadic_bound 0 16 1 0 1 262144 75386 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz45 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz45 65801 1000 0 1 9364972152248037 4503599627370496 500000000113079 37693000000000000000 616224532590073082637 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 19639770079031275290624 9444732965739290427392 1000000000226158 75386000000000000000 9364972152248037 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep131 := BSN.sin_dyadic_bound_f 182591859 1073741824 1 0 524288 150920 0 1 1 0 1 1 88726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 182591859) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 182591859) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 71737977) qz20)

noncomputable def ep132 := @Enclosure.Real.IsNear.cos_image qz44 qz306 Bool.false 71737977 524288 229 262144 Bool.false 88726 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 616224532590073082637 4503599627370496000 32900500007440711279 37693000000000000000000 71737977 524288 229 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 71737977 524288) (BSN.cos_reduce3 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12848759837627686846464) qz23) 226375608064910080 72057594037927936 Bool.false 88726 524288 21 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 71737977 524288 226375608064910080 72057594037927936 21 12848759837627686846464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 88726 524288 12848759837627686846464 75557863725914323419136 182591859 1073741824 150920 150772 (ep131 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep133 := nat_lit 1111541395410080215479602183926161

noncomputable def ep134 := BSN.cos_dyadic_bound_f 182591859 1073741824 2 1 524288 150920 ep133 ep77 ep133 ep133 ep78 ep133 516725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 182591859) qz281 0 1 ep133 ep77 ep133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 182591859) qz282 0 1 ep133 ep78 ep133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep135 := @Enclosure.Real.IsNear.sin_image qz44 qz306 Bool.false 71737977 524288 229 262144 Bool.true 516725 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 616224532590073082637 4503599627370496000 32900500007440711279 37693000000000000000000 71737977 524288 229 262144 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 71737977 524288) (BSN.sin_reduce3 qz306 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12848759837627686846464) qz23) 226375608064910080 72057594037927936 Bool.false 516725 524288 21 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 71737977 524288 226375608064910080 72057594037927936 21 12848759837627686846464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 516725 524288 12848759837627686846464 75557863725914323419136 182591859 1073741824 150920 150772 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep128 rfl rfl) rfl)

noncomputable def ep136 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.false 8223258769 137438953472 1625974087475 5180486473220096 Bool.false 95781696175 274877906944 3268080741257 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz43 (Real.cos qz44) 185363 524288 1 524288 44363 262144 8762769 9880993792 8223258769 137438953472 1625974087475 5180486473220096 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.false 88726 524288 17525538 19761987584 44363 262144 8762769 9880993792 (ep132 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 185363 524288 1 524288 516725 524288 8762769 9880993792 95781696175 274877906944 3268080741257 10360972946440192 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.true 516725 524288 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.true 516725 524288 17525538 19761987584 516725 524288 8762769 9880993792 (ep135 rfl rfl) rfl)) rfl)

noncomputable def ep137 := @ep39 8223258769 137438953472 1625974087475 5180486473220096 Bool.false 95781696175 274877906944 3268080741257 10360972946440192 Bool.true 316565221533179445248 1151657567 68719476736 7780508230103 2590243236610048 Bool.false 16395924274689234436096 29824012517 137438953472 1946286503629 647560809152512 (ep40 (BSN.head_sum_c_succ qz6 7 8 rfl rfl) (ep126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep127 ep136) rfl rfl

theorem EMRow16.d6 : Enclosure.Complex.IsNear qz4 Bool.true 1151657567 68719476736 7780508230103 2590243236610048 Bool.false 29824012517 137438953472 1946286503629 647560809152512 := ep38 (BSN.head_sum_c_succ qz6 8 9 rfl rfl) (ep137 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow16.d7 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow16.d8 : @Eq Nat (Nat.pow 14 1) 14 := @Eq.refl Nat 14

noncomputable def ep138 := nat_lit 39326387007577491180921324389789

noncomputable def ep139 := nat_lit 34945225134435478930070700032000

noncomputable def ep140 := nat_lit 35381785139175694937551068407332591297

noncomputable def ep141 := nat_lit 7092693807687411198582765929495527424000

noncomputable abbrev qz474 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz455 := qz474

noncomputable abbrev qz308 := qz455

noncomputable abbrev qz46 := qz308

noncomputable abbrev qz456 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz309 := qz456

noncomputable abbrev qz47 := qz309

noncomputable abbrev qz475 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz476 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz457 := (@HAdd.hAdd Complex Complex Complex qz472 (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz473) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz310 := qz457

noncomputable abbrev qz48 := (Complex.Stirling.logGammaStirling 1 qz310)

noncomputable abbrev qz458 := (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz473) (2 : Complex))))

noncomputable abbrev qz311 := qz458

noncomputable abbrev qz49 := qz311

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz262 (@HDiv.hDiv Real Real Real qz265 qz275 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz312 := (@instHSub Real Real.instSub)

noncomputable def ep142 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50))) (zetaApproximant qz6 1 14))

noncomputable def ep143 := @Enclosure.Real.IsNear.of_eq ep142 (@HSub.hSub Real Real Real qz312 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 14))))

noncomputable def ep144 := nat_lit 5618076043858496313060981185267

noncomputable def ep145 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 14))) ep144

noncomputable def ep146 := nat_lit 4992175019205068418581528576000

noncomputable def ep147 := nat_lit 246897711917013114542468618485982141467

noncomputable def ep148 := nat_lit 49648856653811878390079361506468691968000

noncomputable def ep149 := nat_lit 3632485799575262638597677

noncomputable def ep150 := nat_lit 873630628360886973251767500800

noncomputable def ep151 := nat_lit 193696014304187505097215091336499403

noncomputable def ep152 := nat_lit 12412214163452969597519840376617172992000

noncomputable def ep153 := nat_lit 4908105170370477879306433324693049797804089543105751652761600

noncomputable def ep154 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.re (zetaApproximant qz6 1 14)) 524287 524288 7913823

noncomputable def ep155 := nat_lit 10715650099770729224758541

noncomputable def ep156 := nat_lit 9521818197641503178752000

noncomputable def ep157 := nat_lit 11356814920784693645490595141

noncomputable def ep158 := nat_lit 2512341253265908255216893952000

noncomputable def ep159 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.false 524287 524288 15827646

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 23059457) qz20)

noncomputable def ep160 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz313 Bool.false 23059457 524288 203

noncomputable def ep161 := nat_lit 2964298137600000000000000000

noncomputable def ep162 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) Bool.false 79231691787257536079 1801439850948198400 1141239341759043343466669 ep161

noncomputable def ep163 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50 735389188605265696651 9007199254740992000 397168213859043343466669 ep161 4936456821 131072000

noncomputable def ep164 := nat_lit 51925281529697098844733440000

noncomputable def ep165 := nat_lit 1235124224000000000000000000

noncomputable def ep166 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 116270397691885675133 2251799813685248000 289592952405628781075231 ep165 Bool.false 735389188605265696651 9007199254740992000

noncomputable def ep167 := @Enclosure.Complex.IsNear.subLitP qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 100535439301011352133 2251799813685248000 281400952393277538835231 ep165 Bool.false 763275678178835328651 9007199254740992000 357846613856079045329069

noncomputable def ep168 := nat_lit 261817659859697852359437425242537984

noncomputable def ep169 := nat_lit 206993654735935374655927204295213056

noncomputable abbrev qz477 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz459 := qz477

noncomputable abbrev qz314 := (@HSub.hSub Complex Complex Complex qz456 qz457 qz459)

noncomputable abbrev qz315 := (Complex.log qz457)

noncomputable abbrev qz51 := (@HSub.hSub Complex Complex Complex qz309 (@HMul.hMul Complex Complex Complex qz308 qz314 qz315) qz310)

noncomputable abbrev qz316 := qz459

noncomputable abbrev qz52 := (@HMul.hMul Complex Complex Complex qz308 qz316 ↑(Real.log qz266))

noncomputable abbrev qz460 := qz476

noncomputable abbrev qz317 := qz460

noncomputable abbrev qz53 := qz317

noncomputable abbrev qz54 := (@instHMul Nat instMulNat)

noncomputable abbrev qz461 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz318 := qz461

noncomputable abbrev qz55 := qz318

noncomputable abbrev qz56 := qz310

noncomputable abbrev qz319 := (@instHSub Int Int.instSub)

noncomputable abbrev qz57 := qz319

noncomputable abbrev qz320 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz58 := qz320

noncomputable abbrev qz321 := (@instHMul Int Int.instMul)

noncomputable abbrev qz59 := qz321

noncomputable abbrev qz322 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz60 := qz322

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 100535439301011352133

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz51 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 100535827539683224133 2251799813685248000

noncomputable def ep172 := nat_lit 863592847773673714271949684736

noncomputable def ep173 := nat_lit 655648815122063715185091359539200

noncomputable def ep174 := @ep171 34350649539932304593 150772000000000000000000 Bool.false 152659677234495572303 1801439850948198400 1820025002493429643 15077200000000000000000 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000 Bool.true ep172 100535439301011352133 2251799813685248000 281400952393277538835231 ep165 Bool.false ep173

noncomputable def ep175 := @Enclosure.Complex.IsNear.addLitP qz51 qz52 Bool.true 102605091243288472133 2251799813685248000 33775500003799492093 150772000000000000000000

noncomputable def ep176 := nat_lit 13177431987281359553560576

noncomputable def ep177 := @ep175 Bool.false 152659677234495572303 1801439850948198400 1820025002493429643 15077200000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep176 100535827539683224133 2251799813685248000 34350649539932304593 150772000000000000000000 Bool.false 152659677234495572303 152659677234495572303 1801439850948198400

noncomputable abbrev qz61 := (@HMul.hMul Complex Complex Complex qz308 qz314 qz315)

noncomputable def ep178 := @Enclosure.Complex.IsNear.subLitP qz61 qz56 Bool.true 97538541662496664133 2251799813685248000 33775500003799492093 150772000000000000000000 Bool.false 1059639745253083868811

noncomputable def ep179 := nat_lit 3053193544689911446060000

noncomputable def ep180 := @ep178 9007199254740992000 1820025002493429643 15077200000000000000000 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 Bool.true 410420364973153888532000 102605091243288472133 2251799813685248000 33775500003799492093 150772000000000000000000 Bool.false ep179 152659677234495572303 1801439850948198400 1820025002493429643 15077200000000000000000

noncomputable abbrev qz62 := qz314

noncomputable abbrev qz63 := qz315

noncomputable def ep181 := @Enclosure.Complex.IsNear.mul qz62 qz63 Bool.true 97538541662496664133 2251799813685248000 33775500003799492093 150772000000000000000000 Bool.false 1059639745253083868811 9007199254740992000 1820025002493429643

noncomputable abbrev qz64 := (Complex.re qz314)

noncomputable abbrev qz65 := (Complex.re qz315)

noncomputable abbrev qz66 := (Complex.im qz314)

noncomputable abbrev qz67 := (Complex.im qz315)

noncomputable def ep182 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz64 qz65) (@HMul.hMul Real Real Real qz0 qz66 qz67) 110206431711131077 18014398509481984 175000000263851 30154400000000000000 55657172813194024379 1125899906842624000

noncomputable def ep183 := nat_lit 878549079770963152019822884931239936

noncomputable def ep184 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz65 7000 4000 0 1 15743775958733011 4503599627370496 25000000037693 7538600000000000000

noncomputable def ep185 := @Enclosure.Complex.IsNear.re_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable abbrev qz323 := (Enclosure.sfrac Bool.false 131602 4000)

noncomputable abbrev qz68 := qz323

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq qz62 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz68) Bool.false 7000 4000 0 1 Bool.false 131602 4000 0

noncomputable abbrev qz324 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz69 := (Complex.mk qz324 qz323)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.log qz69) Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000

noncomputable def ep188 := BSN.log_dyadic_bound 1016086404 33784086404 2 1 3424093482458812953648 524288 150772 1032431580393651216 1032431580393651216 31546 34800172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1016086404) (BSN.artanhQ 33784086404) 0 1 1032431580393651216 3424093482458812953648 1032431580393651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz70 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz325 := (Real.log (Enclosure.sfrac Bool.false 17400086404 16000000))

noncomputable abbrev qz326 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep189 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz325 1 2 0 1 15743775958733011 2251799813685248 25000000037693 3769300000000000000 15743775958733011 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 17400086404 16000000 15743775958733011 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17400086404) qz327)) Bool.false 132068364957635405938688 18889465931478580854784 1000000001507720 150772000000000000000 15743775958733011 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 17400086404 16000000 10 34800172808 32768000000 31546 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep190 := BSN.arctan_dyadic_bound_f 9000 131602 1 0 524288 150772 0 1 1 0 1 1 35799 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz262 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz72 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz326 BSN.pi_near_15 rfl)

noncomputable abbrev qz328 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 131602)))

noncomputable def ep191 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz328 884279719003555 562949953421312 1 2000000000000000 35799 524288 1 150772 443464199934406295552 845840835446179 562949953421312 500000000037693 75386000000000000000 qz72 (ep190 rfl) rfl rfl

noncomputable abbrev qz329 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 131602) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep192 := @Enclosure.Complex.IsNear.re_isNear qz63 Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (ep187 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 65801 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz325) Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 9000 131602 4000 17400086404 16000000 rfl rfl rfl) (ep189 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz329 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 9000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz329 (@HSub.hSub Real Real Real qz312 qz71 qz328) Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 131602 9000 rfl rfl) ep191))))

noncomputable def ep193 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz67 131602 4000 0 1 845840835446179 562949953421312 500000000037693 75386000000000000000

noncomputable def ep194 := @Enclosure.Complex.IsNear.im_isNear qz62 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable def ep195 := @Enclosure.Complex.IsNear.im_isNear qz63 Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (ep187 (@congrArg Complex Complex qz56 qz69 Complex.log (BSN.w_shift_mk qz17 Bool.false 65801 1000 2 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz69) Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz69)) (@HMul.hMul Real Real Real qz0 qz70 qz325) Bool.false 15743775958733011 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 9000 131602 4000 17400086404 16000000 rfl rfl rfl) (ep189 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz69)) qz329 Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 9000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz329 (@HSub.hSub Real Real Real qz312 qz71 qz328) Bool.false 845840835446179 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 131602 9000 rfl rfl) ep191))))

noncomputable abbrev qz330 := (Enclosure.Real.IsNear.const Bool.false 131602 4000)

noncomputable abbrev qz73 := (@ep186 1 (BSN.w_sub_half_mk qz275 Bool.false 65801 1000 2 qz276 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz323 Bool.false 7000 4000 0 1 Bool.false 131602 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz330))

noncomputable def ep196 := @ep182 32900500002480237093 150772000000000000000000 ep183 97538541662496664133 2251799813685248000 33775500003799492093 150772000000000000000000 (@ep184 110206431711131077 18014398509481984 175000000263851 30154400000000000000 (ep185 qz73) ep192 rfl) (@ep193 55657172813194024379 1125899906842624000 32900500002480237093 150772000000000000000000 (ep194 qz73) ep195 rfl) rfl

noncomputable def ep197 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz64 qz67) (@HMul.hMul Real Real Real qz0 qz66 qz65) 5920885848123253 2251799813685248 3500000000263851 301544000000000000000 1035956201860590856811 9007199254740992000

noncomputable def ep198 := nat_lit 2386096580934377909617111547278000128

noncomputable def ep199 := @Enclosure.Real.IsNear.mulLit_ff qz64 qz67 7000 4000 0 1 845840835446179 562949953421312 500000000037693 75386000000000000000

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz66 qz65 131602 4000 0 1 15743775958733011 4503599627370496 25000000037693 7538600000000000000

noncomputable def ep201 := @ep197 1645025002480237093 15077200000000000000000 ep198 1059639745253083868811 9007199254740992000 1820025002493429643 15077200000000000000000 (@ep199 5920885848123253 2251799813685248 3500000000263851 301544000000000000000 (ep185 qz73) ep195 rfl) (@ep200 1035956201860590856811 9007199254740992000 1645025002480237093 15077200000000000000000 (ep194 qz73) ep192 rfl) rfl

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz56 qz69 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 (BSN.w_shift_mk qz17 Bool.false 65801 1000 2 qz18 rfl)

noncomputable abbrev qz331 := (ep202 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 131602 4000) Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 131602 4000)))

noncomputable abbrev qz74 := qz331

noncomputable def ep203 := ep180 (@ep181 15077200000000000000000 (ep196 rfl) (ep201 rfl)) qz74 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz75 := qz316

noncomputable def ep204 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.re ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.im ↑qz3)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.re ↑qz3) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz76 := (@Enclosure.Complex.IsNear.of_eq qz316 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz273) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz273 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz326 qz284))

noncomputable def ep206 := ep205 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow16.d4)

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.im ↑qz3) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep208 := ep207 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep209 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz75) (Complex.im ↑qz3)) (@HMul.hMul Real Real Real qz0 (Complex.im qz75) (Complex.re ↑qz3)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep210 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz75) (Complex.im ↑qz3) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep211 := ep210 (@Enclosure.Complex.IsNear.re_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz3) qz14 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz3) (0 : Real) qz14 (Complex.ofReal_im qz3) Enclosure.sfrac_zero_eq) qz24)

noncomputable def ep212 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz75) (Complex.re ↑qz3) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep213 := ep212 (@Enclosure.Complex.IsNear.im_isNear qz75 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz76) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz3) qz3 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz3) EMRow16.d4)

noncomputable def ep214 := @ep177 1820025002493429643 15077200000000000000000 (ep203 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep204 131072 1 262144 (ep206 rfl) (ep208 rfl) rfl rfl) (@ep209 1 0 1 (ep211 rfl) (ep213 rfl) rfl rfl))

noncomputable abbrev qz77 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz332 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz308 (@HMul.hMul Complex Complex Complex qz308 (2 : Complex) qz332) (@HSub.hSub Complex Complex Complex qz309 (@HMul.hMul Complex Complex Complex qz308 (2 : Complex) qz332) (1 : Complex)))

noncomputable abbrev qz333 := (@HPow.hPow Complex Int Complex qz461 qz457 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz79 := qz333

noncomputable def ep215 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79)) Bool.false 1481013 8589934592 3 8589934592

noncomputable def ep216 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79) Bool.false 0 1 0 1 Bool.false

noncomputable def ep217 := @ep216 0 1 0 1 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000 Bool.false 1481013 1481013 8589934592 3 8589934592 Bool.true 10828015157 10828015157 4294967296000 65801

noncomputable def ep218 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz56 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep219 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz79 Bool.false 1481013 8589934592 3 8589934592 Bool.true 10828015157 4294967296000 65801 12884901888000

noncomputable abbrev qz80 := (Complex.re qz333)

noncomputable abbrev qz81 := (Complex.im qz333)

noncomputable def ep220 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) 1481013 8589934592 3 8589934592 0 1 0

noncomputable def ep221 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 1 12 0 1 4443039 2147483648 9 2147483648 1481013

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz334 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz14 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz24)

noncomputable def ep223 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep222 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz334)

noncomputable def ep224 := @Enclosure.Complex.IsNear.re_isNear qz79 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801 1073741824000

noncomputable abbrev qz462 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz335 := (@HPow.hPow Complex Nat Complex qz462 qz457 1)

noncomputable abbrev qz82 := (@Inv.inv Complex Complex.instInv qz335)

noncomputable def ep225 := @Enclosure.Complex.IsNear.of_eq qz79 qz82 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801

noncomputable def ep226 := @Enclosure.Complex.IsNear.of_parts qz82 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801

noncomputable abbrev qz83 := (Complex.re qz335)

noncomputable abbrev qz84 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz85 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz86 := qz335

noncomputable def ep227 := @Enclosure.Real.IsNear.mulLit_ff qz83 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) 9000 4000 0 1 493671 536870912 1 536870912

noncomputable def ep228 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable def ep229 := @Enclosure.Complex.IsNear.of_eq qz86 qz56 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0

noncomputable def ep230 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) Bool.false 493671 536870912 1 536870912 493671 536870912 1

noncomputable abbrev qz87 := (Complex.im qz335)

noncomputable abbrev qz336 := (@instHAdd Real Real.instAdd)

noncomputable def ep231 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86) (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 qz83 qz83) (@HMul.hMul Real Real Real qz0 qz87 qz87)) Bool.false 4350021601 4000000 0 1

noncomputable def ep232 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz83 qz83) (@HMul.hMul Real Real Real qz0 qz87 qz87) 81 16 0 1 4329771601 4000000

noncomputable def ep233 := @Enclosure.Real.IsNear.mulLit_ff qz83 qz83 9000 4000 0 1 9000 4000 0 1

noncomputable def ep234 := @Enclosure.Real.IsNear.mulLit_ff qz87 qz87 131602 4000 0 1 131602 4000 0 1

noncomputable def ep235 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 9000 4000 0 1 Bool.false 131602 4000 0 1

noncomputable abbrev qz88 := (ep228 (@ep229 1 (BSN.pow_one_c qz310) qz331))

noncomputable abbrev qz89 := (ep235 (@ep229 1 (BSN.pow_one_c qz310) qz331))

noncomputable def ep236 := @ep232 0 1 69600345616 4350021601 4000000 0 1 (@ep233 81 16 0 1 qz88 qz88 rfl) (@ep234 4329771601 4000000 0 1 qz89 qz89 rfl)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86) 4350021601 4000000 0 1 246835 246836 268435456 (ep231 (Enclosure.Complex.normSq_eq_mul_add_mul qz86) (ep236 rfl rfl)) rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.of_eq (Complex.re qz82) (@HMul.hMul Real Real Real qz0 qz83 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86))) Bool.false 4443039 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz86) (@ep227 4443039 2147483648 9 2147483648 qz88 (@ep230 536870912 (ep237 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep239 := @Enclosure.Real.IsNear.of_eq (Complex.im qz82) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz87) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86))) Bool.true 32484045471 1073741824000 65801 1073741824000 (Enclosure.Complex.inv_im_eq_mul qz86)

noncomputable def ep240 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz87) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz86)) 131602 4000 0 1 493671 536870912 1

noncomputable def ep241 := @ep240 536870912 32484045471 1073741824000 65801 1073741824000 (@Enclosure.Real.IsNear.neg qz87 Bool.false 131602 4000 0 1 qz89) (@ep230 536870912 (ep237 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 0 1 0 1 32484045471 1073741824000 65801 1073741824000 0

noncomputable def ep243 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep222 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz334)

noncomputable def ep244 := @Enclosure.Complex.IsNear.im_isNear qz79 Bool.false 4443039 2147483648 9 2147483648 Bool.true 32484045471 1073741824000 65801 1073741824000

noncomputable abbrev qz90 := (@ep225 1073741824000 (BSN.zpow_one_sub_two_mul qz310 1 1 rfl rfl) (@ep226 1073741824000 ep238 (ep239 ep241)))

noncomputable def ep245 := @ep220 1 1481013 1481013 8589934592 3 8589934592 (@ep221 8589934592 3 8589934592 ep223 (ep224 qz90) rfl) (@ep242 1 0 1 ep243 (ep244 qz90) rfl) rfl

noncomputable def ep246 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80) 10828015157 4294967296000 65801 12884901888000 0 1 0

noncomputable def ep247 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz81 1 12 0 1 32484045471 1073741824000 65801 1073741824000 10828015157

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz80 0 1 0 1 4443039 2147483648 9 2147483648 0

noncomputable def ep249 := @ep246 1 10828015157 10828015157 4294967296000 65801 12884901888000 (@ep247 4294967296000 65801 12884901888000 ep223 (ep244 qz90) rfl) (@ep248 1 0 1 ep243 (ep224 qz90) rfl) rfl

noncomputable abbrev qz91 := (@Enclosure.Complex.IsNear.mk qz273 qz273 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz284 qz284)

noncomputable def ep250 := @ep217 12884901888000 (@ep218 0 1 0 1 (BSN.stirling_sum_base qz56) qz91) (ep219 (ep245 rfl) (ep249 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep251 := @ep174 763275678178835328651 9007199254740992000 357846613856079045329069 ep161 (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep215 Bool.true 10828015157 4294967296000 65801 12884901888000 (BSN.stirling_sum_succ qz56 0 1 rfl) (ep250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz17 2) Bool.false 15734958390874323 2251799813685248 25000000037693 3769300000000000000 Bool.false 871452799174051 281474976710656

noncomputable abbrev qz92 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz311 qz332))

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 1) qz92) Bool.false 15734958390874323 2251799813685248 25000000037693 3769300000000000000 Bool.false 871452799174051 281474976710656 500000000037693 37693000000000000000

noncomputable def ep254 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 1) qz92 Bool.false 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000 Bool.false

noncomputable def ep255 := nat_lit 141727905491663720821325788348416

noncomputable def ep256 := nat_lit 981168625407807941990441549824

noncomputable abbrev qz93 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz311 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz17 0) qz93) Bool.false 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000

noncomputable def ep258 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz17 0) qz93 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz337 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68))

noncomputable def ep259 := @Enclosure.Complex.IsNear.of_eq qz93 qz337 Bool.false 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000

noncomputable def ep260 := BSN.log_dyadic_bound 936086404 33704086404 2 1 3407896320984892953648 524288 150772 876257755753651216 876257755753651216 29130 34640172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 936086404) (BSN.artanhQ 33704086404) 0 1 876257755753651216 3407896320984892953648 876257755753651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep261 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 17320086404 16000000)) 1 2 0 1 15733399317745875 2251799813685248 25000000037693 3769300000000000000 15733399317745875 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 17320086404 16000000 15733399317745875 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17320086404) qz327)) Bool.false 131981319384037588992000 18889465931478580854784 1000000001507720 150772000000000000000 15733399317745875 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 17320086404 16000000 10 34640172808 32768000000 29130 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep260 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep262 := BSN.arctan_dyadic_bound_f 1000 131602 1 0 524288 150772 0 1 1 0 1 1 3983 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 131602)

noncomputable def ep263 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz338 qz339)) 884279719003555 562949953421312 1 2000000000000000 3983 524288 1 150772 461375015652458758144 880003005318563 562949953421312 500000000037693 75386000000000000000 qz72 (ep262 rfl) rfl rfl

noncomputable abbrev qz94 := (@HAdd.hAdd Complex Complex Complex qz268 qz311 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz340 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz68)

noncomputable def ep264 := @ep258 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000 Bool.false 15733399317745875 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 880003005318563 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz17 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz17) qz91) (ep259 (@congrArg Complex Complex qz94 qz340 Complex.log (BSN.w_shift_mk qz17 Bool.false 65801 1000 0 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz337 Bool.false 15733399317745875 4503599627370496 25000000037693 7538600000000000000 Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz337) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 17320086404 16000000))) Bool.false 15733399317745875 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 1000 131602 4000 17320086404 16000000 rfl rfl rfl) (ep261 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz337) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz339 qz338)) Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 1000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz339 qz338)) (@HSub.hSub Real Real Real qz312 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz338 qz339))) Bool.false 880003005318563 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 131602 1000 rfl rfl) ep263)))) rfl rfl

noncomputable abbrev qz341 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68))

noncomputable def ep265 := @Enclosure.Complex.IsNear.of_eq qz92 qz341 Bool.false 15736517464002771 4503599627370496 25000000037693 7538600000000000000 Bool.false 862902593029539 562949953421312 500000000037693 75386000000000000000

noncomputable def ep266 := BSN.log_dyadic_bound 960086404 33728086404 2 1 3412751437427068953648 524288 150772 921765903145651216 921765903145651216 29856 34688172808 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 960086404) (BSN.artanhQ 33728086404) 0 1 921765903145651216 3412751437427068953648 921765903145651216 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep267 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 17344086404 16000000)) 1 2 0 1 15736517464002771 2251799813685248 25000000037693 3769300000000000000 15736517464002771 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 17344086404 16000000 15736517464002771 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17344086404) qz327)) Bool.false 132007476290673356832768 18889465931478580854784 1000000001507720 150772000000000000000 15736517464002771 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 17344086404 16000000 10 34688172808 32768000000 29856 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep266 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep268 := BSN.arctan_dyadic_bound_f 5000 131602 1 0 524288 150772 0 1 1 0 1 1 19909 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 131602) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 131602) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep269 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz339)) 884279719003555 562949953421312 1 2000000000000000 19909 524288 1 150772 452409474694270943232 862902593029539 562949953421312 500000000037693 75386000000000000000 qz72 (ep268 rfl) rfl rfl

noncomputable abbrev qz95 := (@HAdd.hAdd Complex Complex Complex qz268 qz311 qz332)

noncomputable abbrev qz343 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz68)

noncomputable def ep270 := @ep254 15736517464002771 4503599627370496 25000000037693 7538600000000000000 Bool.false 862902593029539 562949953421312 500000000037693 75386000000000000000 Bool.false ep255 15734958390874323 2251799813685248 25000000037693 3769300000000000000 Bool.false ep256 871452799174051 281474976710656 500000000037693 37693000000000000000 (ep257 (BSN.log_sum_c_succ qz17 0 1 rfl) (ep264 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep265 (@congrArg Complex Complex qz95 qz343 Complex.log (BSN.w_shift_mk qz17 Bool.false 65801 1000 1 qz18 rfl)) (@Enclosure.Complex.IsNear.of_parts qz341 Bool.false 15736517464002771 4503599627370496 25000000037693 7538600000000000000 Bool.false 862902593029539 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz341) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 17344086404 16000000))) Bool.false 15736517464002771 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 5000 131602 4000 17344086404 16000000 rfl rfl rfl) (ep267 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz341) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz339 qz342)) Bool.false 862902593029539 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 5000 131602 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz339 qz342)) (@HSub.hSub Real Real Real qz312 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz339))) Bool.false 862902593029539 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 131602 5000 rfl rfl) ep269)))) rfl rfl

noncomputable def ep271 := @ep167 ep161 Bool.false 15734958390874323 2251799813685248 25000000037693 3769300000000000000 Bool.false 871452799174051 281474976710656 500000000037693 37693000000000000000 Bool.true ep168 116270397691885675133 2251799813685248000 289592952405628781075231 ep165 Bool.false ep169 735389188605265696651 9007199254740992000 397168213859043343466669 ep161 (@ep170 2251799813685248000 281400952393277538835231 ep165 Bool.false 763275678178835328651 9007199254740992000 357846613856079045329069 ep161 (BSN.logGammaStirling_unfold 1 qz56) (ep251 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep252 500000000037693 37693000000000000000 (BSN.log_sum_c_eq qz17 2) (ep253 (BSN.log_sum_c_succ qz17 1 2 rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz96 := (@HDiv.hDiv Real Real Real qz265 qz275 (2 : Real))

noncomputable def ep272 := @Enclosure.Real.IsNear.mulLit_ff qz96 (Real.log Real.pi) 65801 2000 0 1 75021 65536 1 131072 4936456821 131072000 65801 262144000 (@Enclosure.Real.IsNear.of_eq qz96 (Enclosure.sfrac Bool.false 65801 2000) Bool.false 65801 2000 0 1 (BSN.t_half_eq qz17 Bool.false 65801 1000 qz18) (Enclosure.Real.IsNear.const Bool.false 65801 2000)) EMRow16.d5 rfl

noncomputable def ep273 := @ep163 65801 262144000 ep164 79231691787257536079 1801439850948198400 1141239341759043343466669 ep161 (@ep166 397168213859043343466669 ep161 (ep271 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep272 rfl rfl

noncomputable def ep274 := BSN.cos_dyadic_bound_f 135970 1073741824 1 0 524288 150920 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 135970) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 135970) qz282 0 0 rfl) rfl rfl

noncomputable def ep275 := @ep160 524288 Bool.false 524287 524288 1 75386 (@ep162 23059457 524288 203 524288 ep273 rfl) (Enclosure.sfrac_false_div 23059457 524288) (BSN.cos_reduce0 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9568050315089936384) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 23059457 524288 226375608064910080 72057594037927936 7 9568050315089936384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 9568050315089936384 75557863725914323419136 135970 1073741824 150920 150772 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep276 := nat_lit 3332636369174526112563200

noncomputable def ep277 := nat_lit 50680946586785898403981203

noncomputable def ep278 := nat_lit 11215809166365661853646848000

noncomputable abbrev qz97 := qz269

noncomputable abbrev qz98 := qz270

noncomputable abbrev qz463 := (@Nat.cast Complex Complex.instNatCast 14)

noncomputable abbrev qz344 := (@HPow.hPow Complex Complex Complex qz450 qz463 qz451)

noncomputable abbrev qz99 := qz344

noncomputable abbrev qz345 := qz463

noncomputable abbrev qz100 := (@HAdd.hAdd Complex Complex Complex qz268 (@HDiv.hDiv Complex Complex Complex qz317 qz345 (@HSub.hSub Complex Complex Complex qz309 qz267 (1 : Complex))) qz316)

noncomputable abbrev qz101 := (@instHSub Nat instSubNat)

noncomputable abbrev qz346 := qz462

noncomputable abbrev qz102 := qz346

noncomputable abbrev qz103 := qz345

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz6 1 14) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz98) (@HMul.hMul Complex Complex Complex qz46 qz99 (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false ep155 ep156 ep157

noncomputable def ep280 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz98) (@HMul.hMul Complex Complex Complex qz46 qz99 (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 171620244667 137438953472 11289039920923 2590243236610048

noncomputable def ep281 := nat_lit 407294697263559149360643141

noncomputable def ep282 := nat_lit 1819053480068449668288703

noncomputable def ep283 := nat_lit 1472747735484621411789099746933604352

noncomputable def ep284 := nat_lit 15128637781682583004497153955463168

noncomputable def ep285 := @ep280 Bool.true 5210060765 137438953472 22568891155385 5180486473220096 Bool.true 1174259765461511605113459 ep156 ep281 ep158 Bool.false 236409510927702918277869 ep276 ep282 ep278 Bool.false ep283 ep155 ep156 ep157 ep158 Bool.false ep284 110075327259856443593869 ep276

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz98) (BSN.headSumC qz6 14) Bool.false 171620244667 137438953472 11289039920923 2590243236610048 Bool.true 5210060765 137438953472 22568891155385

noncomputable abbrev qz104 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 13) qz270)

noncomputable def ep287 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 13) qz104) Bool.false 171620244667 137438953472 11289039920923 2590243236610048 Bool.true 5210060765 137438953472 22568891155385 5180486473220096

noncomputable def ep288 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 13) qz104 Bool.false 73520348141 68719476736 21297496639763 5180486473220096 Bool.true 68690816971 274877906944 42574254025531 10360972946440192 Bool.false

noncomputable abbrev qz105 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 12) qz270)

noncomputable def ep289 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 12) qz105) Bool.false 73520348141 68719476736 21297496639763 5180486473220096 Bool.true 68690816971 274877906944 42574254025531 10360972946440192

noncomputable def ep290 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 12) qz105 Bool.false 107790300669 137438953472 19958623944297 5180486473220096 Bool.true 28555325467 137438953472 9978293752293 2590243236610048 Bool.false

noncomputable abbrev qz106 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 11) qz270)

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 11) qz106) Bool.false 107790300669 137438953472 19958623944297 5180486473220096 Bool.true 28555325467 137438953472 9978293752293 2590243236610048

noncomputable def ep292 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 11) qz106 Bool.false 76205167995 137438953472 18565874133219 5180486473220096 Bool.true 1729951483 137438953472 9282486314869 2590243236610048 Bool.false

noncomputable abbrev qz107 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 10) qz270)

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz6 10) qz107) Bool.false 76205167995 137438953472 18565874133219 5180486473220096 Bool.true 1729951483 137438953472 9282486314869 2590243236610048

noncomputable def ep294 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz6 10) qz107 Bool.false 21704546625 68719476736 2138198249259 647560809152512 Bool.false 53579379859 274877906944 34211313449973 10360972946440192 Bool.false

noncomputable abbrev qz108 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 9) qz270)

noncomputable def ep295 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz6 10) (@HAdd.hAdd Complex Complex Complex qz5 qz4 qz108) Bool.false 21704546625 68719476736 2138198249259 647560809152512 Bool.false 53579379859 274877906944 34211313449973 10360972946440192

noncomputable def ep296 := @Enclosure.Complex.IsNear.addLitP qz4 qz108 Bool.true 1151657567 68719476736 7780508230103 2590243236610048 Bool.false 29824012517 137438953472 1946286503629 647560809152512 Bool.false

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz109 := (@Inv.inv Real Real.instInv (Real.sqrt qz347))

noncomputable abbrev qz110 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep297 := @Enclosure.Complex.IsNear.of_eq qz108 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)))) Bool.false 714256381 2147483648 772284766933 2590243236610048 Bool.true 6068645175 274877906944 3070729391909 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 9 qz18 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9) qz19)

noncomputable def ep298 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz347) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz347) (Real.sqrt qz348) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep299 := BSN.log_dyadic_bound 1 17 2 1 867 262144 75386 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz111 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable def ep300 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz111 65801 1000 0 1 9895417793173221 4503599627370496 500000000113079 37693000000000000000 651128386208591115021 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 20752195215788806766592 9444732965739290427392 1000000000226158 75386000000000000000 9895417793173221 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep301 := BSN.cos_dyadic_bound_f 71169757 1073741824 1 0 524288 150920 0 1 1 0 1 1 523136 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 71169757) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 71169757) qz282 0 0 rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9475165) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep302 := @Enclosure.Real.IsNear.cos_image qz110 qz349 Bool.false 9475165 65536 459 524288 Bool.false 523136 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 651128386208591115021 4503599627370496000 32900500007440711279 37693000000000000000000 9475165 65536 459 524288 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 9475165 65536) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 626015811707779153920) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 523136 524288 23 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 9475165 65536 226375608064910080 72057594037927936 23 626015811707779153920 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523136 524288 626015811707779153920 9444732965739290427392 71169757 1073741824 150920 150772 (ep301 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep303 := BSN.sin_dyadic_bound_f 71169757 1073741824 1 0 524288 150920 0 1 1 0 1 1 34725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 71169757) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 71169757) qz278 0 0 rfl) rfl rfl

noncomputable def ep304 := @Enclosure.Real.IsNear.sin_image qz110 qz349 Bool.false 9475165 65536 459 524288 Bool.false 34725 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz110 Bool.false 651128386208591115021 4503599627370496000 32900500007440711279 37693000000000000000000 9475165 65536 459 524288 (ep300 rfl) rfl) (Enclosure.sfrac_false_div 9475165 65536) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 626015811707779153920) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 34725 524288 23 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 9475165 65536 226375608064910080 72057594037927936 23 626015811707779153920 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 34725 524288 626015811707779153920 9444732965739290427392 71169757 1073741824 150920 150772 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz109 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep298 rfl rfl) rfl)

noncomputable def ep305 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz110)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110))) Bool.false 714256381 2147483648 772284766933 2590243236610048 Bool.true 6068645175 274877906944 3070729391909 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz110) 174763 524288 1 524288 4087 4096 17563231 19761987584 714256381 2147483648 772284766933 2590243236610048 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz110) Bool.false 523136 524288 35126462 39523975168 4087 4096 17563231 19761987584 (ep302 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz109 (@Neg.neg Real Real.instNeg (Real.sin qz110)) 174763 524288 1 524288 34725 524288 17563231 19761987584 6068645175 274877906944 3070729391909 10360972946440192 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz110) Bool.false 34725 524288 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz110) Bool.false 34725 524288 35126462 39523975168 34725 524288 17563231 19761987584 (ep304 rfl rfl) rfl)) rfl)

noncomputable def ep306 := @ep296 714256381 2147483648 772284766933 2590243236610048 Bool.true 6068645175 274877906944 3070729391909 10360972946440192 Bool.false 46610158964441088000 21704546625 68719476736 2138198249259 647560809152512 Bool.false 7363893895499714920448 53579379859 274877906944 34211313449973 10360972946440192 EMRow16.d6 (ep297 ep305) rfl rfl

noncomputable abbrev qz351 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz112 := (@Inv.inv Real Real.instInv (Real.sqrt qz351))

noncomputable abbrev qz113 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq qz107 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)))) Bool.false 32796074745 137438953472 1460288139147 5180486473220096 Bool.true 57039282825 274877906944 2918631809503 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 10 qz18 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10) qz19)

noncomputable def ep308 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz351) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz351) (Real.sqrt qz352) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep309 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 75386 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz114 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep310 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz114 65801 1000 0 1 10369908600166117 4503599627370496 500000000113079 37693000000000000000 682350355799530664717 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 21747274560655572598784 9444732965739290427392 1000000000226158 75386000000000000000 10369908600166117 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep309 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep311 := nat_lit 779226067166231266275023013970238513195237806026196006128123054666938932161

noncomputable def ep312 := nat_lit 121723303034229876888005790196120378230084651462230981152509085607353281

noncomputable def ep313 := nat_lit 2337434754892625339071293030330323298829253248775663556422064145829602089921

noncomputable def ep314 := BSN.cos_dyadic_bound_f 768549273 1073741824 3 2 524288 150920 ep311 ep119 ep312 ep313 ep122 ep312 395622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 768549273) qz281 0 2 ep311 ep119 ep312 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 768549273) qz282 0 2 ep313 ep122 ep312 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19859009) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep315 := @Enclosure.Real.IsNear.cos_image qz113 qz353 Bool.false 19859009 131072 229 262144 Bool.false 395622 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 682350355799530664717 4503599627370496000 32900500007440711279 37693000000000000000000 19859009 131072 229 262144 (ep310 rfl) rfl) (Enclosure.sfrac_false_div 19859009 131072) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13520461807860620197888) qz354) 226375608064910080 72057594037927936 Bool.false 395622 524288 24 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 19859009 131072 226375608064910080 72057594037927936 24 13520461807860620197888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 395622 524288 13520461807860620197888 18889465931478580854784 768549273 1073741824 150920 150772 (ep314 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep316 := nat_lit 348888668538016403270719214084303841

noncomputable def ep317 := BSN.sin_dyadic_bound_f 768549273 1073741824 2 1 524288 150920 ep316 ep92 ep316 ep316 ep93 ep316 344035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 768549273) qz277 0 1 ep316 ep92 ep316 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 768549273) qz278 0 1 ep316 ep93 ep316 rfl rfl rfl rfl) rfl rfl

noncomputable def ep318 := @Enclosure.Real.IsNear.sin_image qz113 qz353 Bool.false 19859009 131072 229 262144 Bool.false 344035 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz113 Bool.false 682350355799530664717 4503599627370496000 32900500007440711279 37693000000000000000000 19859009 131072 229 262144 (ep310 rfl) rfl) (Enclosure.sfrac_false_div 19859009 131072) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13520461807860620197888) qz354) 226375608064910080 72057594037927936 Bool.false 344035 524288 24 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 19859009 131072 226375608064910080 72057594037927936 24 13520461807860620197888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 344035 524288 13520461807860620197888 18889465931478580854784 768549273 1073741824 150920 150772 (ep317 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.recentre' qz112 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep308 rfl rfl) rfl)

noncomputable def ep319 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz113)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113))) Bool.false 32796074745 137438953472 1460288139147 5180486473220096 Bool.true 57039282825 274877906944 2918631809503 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz113) 165795 524288 1 524288 197811 262144 8762769 9880993792 32796074745 137438953472 1460288139147 5180486473220096 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz113) Bool.false 395622 524288 17525538 19761987584 197811 262144 8762769 9880993792 (ep315 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz113)) 165795 524288 1 524288 344035 524288 8762769 9880993792 57039282825 274877906944 2918631809503 10360972946440192 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz113) Bool.false 344035 524288 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz113) Bool.false 344035 524288 17525538 19761987584 344035 524288 8762769 9880993792 (ep318 rfl rfl) rfl)) rfl)

noncomputable def ep320 := @ep294 32796074745 137438953472 1460288139147 5180486473220096 Bool.true 57039282825 274877906944 2918631809503 10360972946440192 Bool.false 5236779269195374264320 76205167995 137438953472 18565874133219 5180486473220096 Bool.true 951050885523417595904 1729951483 137438953472 9282486314869 2590243236610048 (ep295 (BSN.head_sum_c_succ qz6 9 10 rfl rfl) (ep306 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep307 ep319) rfl rfl

noncomputable abbrev qz356 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz115 := (@Inv.inv Real Real.instInv (Real.sqrt qz356))

noncomputable abbrev qz116 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq qz106 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz116)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116)))) Bool.false 15792566337 68719476736 696374905539 2590243236610048 Bool.true 838292937 4294967296 43487964839 161890202288128 (BSN.cpow_neg_s_mk qz17 65801 1000 11 qz18 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11) qz19)

noncomputable def ep322 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz356) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz356) (Real.sqrt qz357) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep323 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 75386 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz117 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep324 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz117 65801 1000 0 1 10799147631728357 4503599627370496 500000000113079 37693000000000000000 710594713315357618957 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 22647454054174387339264 9444732965739290427392 1000000000226158 75386000000000000000 10799147631728357 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep325 := nat_lit 326670802146728947617366200979027121

noncomputable def ep326 := BSN.cos_dyadic_bound_f 756010069 1073741824 2 1 524288 150920 ep325 ep77 ep325 ep325 ep78 ep325 399612 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 756010069) qz281 0 1 ep325 ep77 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 756010069) qz282 0 1 ep325 ep78 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 5170257) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz359 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep327 := @Enclosure.Real.IsNear.cos_image qz116 qz358 Bool.false 5170257 32768 229 262144 Bool.false 399612 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 710594713315357618957 4503599627370496000 32900500007440711279 37693000000000000000000 5170257 32768 229 262144 (ep324 rfl) rfl) (Enclosure.sfrac_false_div 5170257 32768) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3324967448413003055104) qz359) 226375608064910080 72057594037927936 Bool.false 399612 524288 25 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 5170257 32768 226375608064910080 72057594037927936 25 3324967448413003055104 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 399612 524288 3324967448413003055104 4722366482869645213696 756010069 1073741824 150920 150772 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep328 := BSN.sin_dyadic_bound_f 756010069 1073741824 2 1 524288 150920 ep325 ep92 ep325 ep325 ep93 ep325 339392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 756010069) qz277 0 1 ep325 ep92 ep325 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 756010069) qz278 0 1 ep325 ep93 ep325 rfl rfl rfl rfl) rfl rfl

noncomputable def ep329 := @Enclosure.Real.IsNear.sin_image qz116 qz358 Bool.false 5170257 32768 229 262144 Bool.false 339392 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz116 Bool.false 710594713315357618957 4503599627370496000 32900500007440711279 37693000000000000000000 5170257 32768 229 262144 (ep324 rfl) rfl) (Enclosure.sfrac_false_div 5170257 32768) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3324967448413003055104) qz359) 226375608064910080 72057594037927936 Bool.false 339392 524288 25 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 5170257 32768 226375608064910080 72057594037927936 25 3324967448413003055104 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 339392 524288 3324967448413003055104 4722366482869645213696 756010069 1073741824 150920 150772 (ep328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz115 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep322 rfl rfl) rfl)

noncomputable def ep330 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz116)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116))) Bool.false 15792566337 68719476736 696374905539 2590243236610048 Bool.true 838292937 4294967296 43487964839 161890202288128 (@Enclosure.Real.IsNear.mulLit_ff qz115 (Real.cos qz116) 158079 524288 1 524288 99903 131072 8762769 9880993792 15792566337 68719476736 696374905539 2590243236610048 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz116) Bool.false 399612 524288 17525538 19761987584 99903 131072 8762769 9880993792 (ep327 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz115 (@Neg.neg Real Real.instNeg (Real.sin qz116)) 158079 524288 1 524288 5303 8192 8762769 9880993792 838292937 4294967296 43487964839 161890202288128 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz116) Bool.false 5303 8192 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz116) Bool.false 339392 524288 17525538 19761987584 5303 8192 8762769 9880993792 (ep329 rfl rfl) rfl)) rfl)

noncomputable def ep331 := @ep292 15792566337 68719476736 696374905539 2590243236610048 Bool.true 838292937 4294967296 43487964839 161890202288128 Bool.false 7407293059189790736384 107790300669 137438953472 19958623944297 5180486473220096 Bool.true 122644189007400927232 28555325467 137438953472 9978293752293 2590243236610048 (ep293 (BSN.head_sum_c_succ qz6 10 11 rfl rfl) (ep320 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep321 ep330) rfl rfl

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz118 := (@Inv.inv Real Real.instInv (Real.sqrt qz361))

noncomputable abbrev qz119 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep332 := @Enclosure.Complex.IsNear.of_eq qz105 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz119)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119)))) Bool.false 39250395613 137438953472 669436347733 2590243236610048 Bool.true 11580166037 274877906944 2661079016359 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 12 qz18 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 12) qz19)

noncomputable def ep333 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz361) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz361) (Real.sqrt qz362) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep334 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 75386 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz120 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz120 65801 1000 0 1 11191020447815397 4503599627370496 500000000113079 37693000000000000000 736380336486700937997 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 23469270914176955449344 9444732965739290427392 1000000000226158 75386000000000000000 11191020447815397 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep334 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep336 := nat_lit 611632555987304172008443464450625

noncomputable def ep337 := BSN.cos_dyadic_bound_f 157261585 1073741824 2 1 524288 150920 ep336 ep77 ep336 ep336 ep78 ep336 518674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 157261585) qz281 0 1 ep336 ep77 ep336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 157261585) qz282 0 1 ep336 ep78 ep336 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 85725953) qz20)

noncomputable def ep338 := @Enclosure.Real.IsNear.cos_image qz119 qz363 Bool.false 85725953 524288 459 524288 Bool.false 518674 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 736380336486700937997 4503599627370496000 32900500007440711279 37693000000000000000000 85725953 524288 459 524288 (ep335 rfl) rfl) (Enclosure.sfrac_false_div 85725953 524288) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11066300258881011449856) qz23) 226375608064910080 72057594037927936 Bool.false 518674 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 85725953 524288 226375608064910080 72057594037927936 26 11066300258881011449856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 518674 524288 11066300258881011449856 75557863725914323419136 157261585 1073741824 150920 150772 (ep337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep339 := BSN.sin_dyadic_bound_f 157261585 1073741824 1 0 524288 150920 0 1 1 0 1 1 76513 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 157261585) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 157261585) qz278 0 0 rfl) rfl rfl

noncomputable def ep340 := @Enclosure.Real.IsNear.sin_image qz119 qz363 Bool.false 85725953 524288 459 524288 Bool.false 76513 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 736380336486700937997 4503599627370496000 32900500007440711279 37693000000000000000000 85725953 524288 459 524288 (ep335 rfl) rfl) (Enclosure.sfrac_false_div 85725953 524288) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 11066300258881011449856) qz23) 226375608064910080 72057594037927936 Bool.false 76513 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 85725953 524288 226375608064910080 72057594037927936 26 11066300258881011449856 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 76513 524288 11066300258881011449856 75557863725914323419136 157261585 1073741824 150920 150772 (ep339 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz118 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep333 rfl rfl) rfl)

noncomputable def ep341 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz119)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119))) Bool.false 39250395613 137438953472 669436347733 2590243236610048 Bool.true 11580166037 274877906944 2661079016359 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz118 (Real.cos qz119) 151349 524288 1 524288 259337 262144 17563231 19761987584 39250395613 137438953472 669436347733 2590243236610048 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz119) Bool.false 518674 524288 35126462 39523975168 259337 262144 17563231 19761987584 (ep338 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz118 (@Neg.neg Real Real.instNeg (Real.sin qz119)) 151349 524288 1 524288 76513 524288 17563231 19761987584 11580166037 274877906944 2661079016359 10360972946440192 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz119) Bool.false 76513 524288 17563231 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz119) Bool.false 76513 524288 35126462 39523975168 76513 524288 17563231 19761987584 (ep340 rfl rfl) rfl)) rfl)

noncomputable def ep342 := @ep290 39250395613 137438953472 669436347733 2590243236610048 Bool.true 11580166037 274877906944 2661079016359 10360972946440192 Bool.false 20209119414792281391104 73520348141 68719476736 21297496639763 5180486473220096 Bool.true 9440793997630936973312 68690816971 274877906944 42574254025531 10360972946440192 (ep291 (BSN.head_sum_c_succ qz6 11 12 rfl rfl) (ep331 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep332 ep341) rfl rfl

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz121 := (@Inv.inv Real Real.instInv (Real.sqrt qz365))

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz262 qz275 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep343 := @Enclosure.Complex.IsNear.of_eq qz104 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)))) Bool.false 24579548385 137438953472 1280583202083 5180486473220096 Bool.false 58270695441 274877906944 2563528285239 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 13 qz18 rfl)

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 13) qz19)

noncomputable def ep344 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz365) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz365) (Real.sqrt qz366) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz366) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep345 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 75386 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz123 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep346 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz123 65801 1000 0 1 11551488463034085 4503599627370496 500000000113079 37693000000000000000 152019898471221165417 900719925474099200 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 24225227133228857425920 9444732965739290427392 1000000000226158 75386000000000000000 11551488463034085 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep345 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep347 := nat_lit 320580692103024186349949581742668816

noncomputable def ep348 := BSN.sin_dyadic_bound_f 752461598 1073741824 2 1 524288 150920 ep347 ep92 ep347 ep347 ep93 ep347 338070 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 752461598) qz277 0 1 ep347 ep92 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 752461598) qz278 0 1 ep347 ep93 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 88487227) qz20)

noncomputable def ep349 := @Enclosure.Real.IsNear.cos_image qz122 qz367 Bool.false 88487227 524288 229 262144 Bool.false 338070 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 152019898471221165417 900719925474099200 32900500007440711279 37693000000000000000000 88487227 524288 229 262144 (ep346 rfl) rfl) (Enclosure.sfrac_false_div 88487227 524288) (BSN.cos_reduce3 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52949777694445130481664) qz23) 226375608064910080 72057594037927936 Bool.false 338070 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 88487227 524288 226375608064910080 72057594037927936 26 52949777694445130481664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338070 524288 52949777694445130481664 75557863725914323419136 752461598 1073741824 150920 150772 (ep348 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep350 := BSN.cos_dyadic_bound_f 752461598 1073741824 2 1 524288 150920 ep347 ep77 ep347 ep347 ep78 ep347 400731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 752461598) qz281 0 1 ep347 ep77 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 752461598) qz282 0 1 ep347 ep78 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable def ep351 := @Enclosure.Real.IsNear.sin_image qz122 qz367 Bool.false 88487227 524288 229 262144 Bool.true 400731 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 152019898471221165417 900719925474099200 32900500007440711279 37693000000000000000000 88487227 524288 229 262144 (ep346 rfl) rfl) (Enclosure.sfrac_false_div 88487227 524288) (BSN.sin_reduce3 qz367 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52949777694445130481664) qz23) 226375608064910080 72057594037927936 Bool.false 400731 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 88487227 524288 226375608064910080 72057594037927936 26 52949777694445130481664 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400731 524288 52949777694445130481664 75557863725914323419136 752461598 1073741824 150920 150772 (ep350 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep344 rfl rfl) rfl)

noncomputable def ep352 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122))) Bool.false 24579548385 137438953472 1280583202083 5180486473220096 Bool.false 58270695441 274877906944 2563528285239 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz122) 145411 524288 1 524288 169035 262144 8762769 9880993792 24579548385 137438953472 1280583202083 5180486473220096 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz122) Bool.false 338070 524288 17525538 19761987584 169035 262144 8762769 9880993792 (ep349 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)) 145411 524288 1 524288 400731 524288 8762769 9880993792 58270695441 274877906944 2563528285239 10360972946440192 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz122) Bool.true 400731 524288 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz122) Bool.true 400731 524288 17525538 19761987584 400731 524288 8762769 9880993792 (ep351 rfl rfl) rfl)) rfl)

noncomputable def ep353 := @ep288 24579548385 137438953472 1280583202083 5180486473220096 Bool.false 58270695441 274877906944 2563528285239 10360972946440192 Bool.false 11793653410820534566912 171620244667 137438953472 11289039920923 2590243236610048 Bool.true 2864261196268510904320 5210060765 137438953472 22568891155385 5180486473220096 (ep289 (BSN.head_sum_c_succ qz6 12 13 rfl rfl) (ep342 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep343 ep352) rfl rfl

noncomputable def ep354 := @Enclosure.Complex.IsNear.mul qz99 (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 1174259765461511605113459 ep156 ep281 ep158 Bool.false

noncomputable abbrev qz124 := (Complex.re qz344)

noncomputable abbrev qz125 := (Complex.im qz344)

noncomputable def ep355 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz124 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 181077250731066194145 2082897730734078820352 450150734323497483906901

noncomputable def ep356 := nat_lit 3768511879898862382825340928

noncomputable def ep357 := nat_lit 2425346334836463023154213

noncomputable def ep358 := nat_lit 66652727383490522251264000

noncomputable def ep359 := nat_lit 321582623143682480268127423

noncomputable def ep360 := nat_lit 7537023759797724765650681856000

noncomputable def ep361 := nat_lit 17121041005404799036533979428419612236868222976

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_tf qz124 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 744743115 4294967296 617133771629 2590243236610048 729421650569

noncomputable abbrev qz126 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable abbrev qz369 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz454 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable abbrev qz127 := (Real.cos qz369)

noncomputable abbrev qz128 := (@Neg.neg Real Real.instNeg (Real.sin qz369))

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz99 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 qz127) (@HMul.hMul Real Real Real qz0 qz126 qz128)) Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (BSN.cpow_neg_s_mk qz17 65801 1000 14 qz18 rfl)

noncomputable abbrev qz129 := (@HDiv.hDiv Real Real Real qz265 (@Nat.cast Real Real.instNatCast 14) (@Nat.cast Real Real.instNatCast 1))

noncomputable def ep364 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) (Real.sqrt qz129) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz129) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep365 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 75386 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz370 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz130 := qz370

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz130 65801 1000 0 1 11885241781671653 4503599627370496 500000000113079 37693000000000000000 782060794475776439053 4503599627370496000 32900500007440711279 37693000000000000000000 qz22 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz129) Bool.false 24925158572916270432256 9444732965739290427392 1000000000226158 75386000000000000000 11885241781671653 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep367 := nat_lit 1660670468262233438914357688399277016640366726293046926151032716881187594496

noncomputable def ep368 := nat_lit 552662875502827299528359624775987650409451848705221175954181458876457216

noncomputable def ep369 := nat_lit 4980906079035694662144016345948279074620281275181730336101189787725809869056

noncomputable def ep370 := BSN.cos_dyadic_bound_f 928554794 1073741824 3 2 524288 150920 ep367 ep119 ep368 ep369 ep122 ep368 340160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 928554794) qz281 0 2 ep367 ep119 ep368 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 928554794) qz282 0 2 ep369 ep122 ep368 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz131 := qz369

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 91043859) qz20)

noncomputable def ep371 := @Enclosure.Real.IsNear.cos_image qz131 qz371 Bool.false 91043859 524288 229 262144 Bool.true 340160 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 782060794475776439053 4503599627370496000 32900500007440711279 37693000000000000000000 91043859 524288 229 262144 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 91043859 524288) (BSN.cos_reduce2 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65341234811789952155648) qz23) 226375608064910080 72057594037927936 Bool.false 340160 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 91043859 524288 226375608064910080 72057594037927936 27 65341234811789952155648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 340160 524288 65341234811789952155648 75557863725914323419136 928554794 1073741824 150920 150772 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep372 := nat_lit 743412991212036393162384347377294096

noncomputable def ep373 := BSN.sin_dyadic_bound_f 928554794 1073741824 2 1 524288 150920 ep372 ep92 ep372 ep372 ep93 ep372 398959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 928554794) qz277 0 1 ep372 ep92 ep372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 928554794) qz278 0 1 ep372 ep93 ep372 rfl rfl rfl rfl) rfl rfl

noncomputable def ep374 := @Enclosure.Real.IsNear.sin_image qz131 qz371 Bool.false 91043859 524288 229 262144 Bool.true 398959 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 782060794475776439053 4503599627370496000 32900500007440711279 37693000000000000000000 91043859 524288 229 262144 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 91043859 524288) (BSN.sin_reduce2 qz371 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 65341234811789952155648) qz23) 226375608064910080 72057594037927936 Bool.false 398959 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 91043859 524288 226375608064910080 72057594037927936 27 65341234811789952155648 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 398959 524288 65341234811789952155648 75557863725914323419136 928554794 1073741824 150920 150772 (ep373 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz132 := (Real.sin qz369)

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep364 rfl rfl) rfl)

noncomputable def ep375 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 qz127) (@HMul.hMul Real Real Real qz0 qz126 qz128) Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ft qz126 qz127 140121 524288 1 524288 5315 8192 8762769 9880993792 744743115 4294967296 617133771629 2590243236610048 qz372 (@Enclosure.Real.IsNear.recentre' qz127 Bool.true 340160 524288 17525538 19761987584 5315 8192 8762769 9880993792 (ep371 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz126 qz128 140121 524288 1 524288 398959 524288 8762769 9880993792 55902534039 274877906944 2470751397223 10360972946440192 qz372 (@Enclosure.Real.IsNear.neg qz132 Bool.true 398959 524288 8762769 9880993792 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 398959 524288 17525538 19761987584 398959 524288 8762769 9880993792 (ep374 rfl rfl) rfl)) rfl)

noncomputable def ep376 := @ep362 1454887257936 0 1 181077250731066194145 2082897730734078820352 450150734323497483906901 ep356 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (ep363 ep375))

noncomputable def ep377 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 729421650569 1454887257936 0 1 Bool.false

noncomputable def ep378 := @Enclosure.Complex.IsNear.addLitP qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 4316021601 8660043202 0 1 Bool.true 921214000

noncomputable def ep379 := @ep378 4330021601 0 1 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1 Bool.false 1458843301138 729421650569 1454887257936 0 1 Bool.false 130155799367401 130155799367401 727443628968000 0 1

noncomputable abbrev qz133 := (@HDiv.hDiv Complex Complex Complex qz317 qz345 (@HSub.hSub Complex Complex Complex qz309 qz267 (1 : Complex)))

noncomputable def ep380 := @Enclosure.Complex.IsNear.addLitP qz133 qz75 Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk (Enclosure.sfrac Bool.true 28000000 17320086404) (Enclosure.sfrac Bool.true 3684856000 17320086404)) Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1

noncomputable def ep382 := @ep380 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 17264086404 4316021601 8660043202 0 1 Bool.true 3684856000 921214000 4330021601 0 1 (ep381 (BSN.N_div_s_sub_one_mk qz17 65801 1000 14 qz18 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 28000000 17320086404) (Enclosure.sfrac Bool.true 3684856000 17320086404) Bool.true 28000000 17320086404 0 1 Bool.true 3684856000 17320086404 0 1 (Enclosure.Real.IsNear.const Bool.true 28000000 17320086404) (Enclosure.Real.IsNear.const Bool.true 3684856000 17320086404))) qz76 rfl

noncomputable abbrev qz134 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz373 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz462 qz463 1))

noncomputable abbrev qz135 := qz373

noncomputable def ep383 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135)) Bool.false 1 336 0 1

noncomputable def ep384 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135) Bool.false 0 1 0 1 Bool.false

noncomputable def ep385 := @ep384 0 1 0 1 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1 Bool.false 1 1 336 0 1 Bool.false 65801 65801 168000 0

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep387 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz135 Bool.false 1 336 0 1 Bool.false 65801 168000 0 1

noncomputable abbrev qz136 := (Complex.re qz373)

noncomputable abbrev qz137 := (Complex.im qz373)

noncomputable def ep388 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 1 336 0 1 0 1 0

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 1 24 0 1 1 14 0 1 1

noncomputable def ep390 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep392 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz14) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow16.d7 rfl) qz334

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz6 Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 (BSN.ascPochhammer_one_eval qz6)

noncomputable def ep394 := ep393 (@Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk qz70 qz17) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_crit_mk qz17 Bool.false 65801 1000 qz18) (@Enclosure.Complex.IsNear.mk qz70 qz17 Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 qz326 qz22))

noncomputable def ep395 := @ep391 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep396 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 65801 1000 0 1 0 1 0

noncomputable def ep397 := @ep396 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep398 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) 65801 12000 0 1 0 1 0 1 65801

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 65801 1000 0 1 65801 12000 0

noncomputable def ep400 := @ep399 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep401 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep402 := @ep401 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep403 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 (@ep390 1 24 0 1 (ep395 rfl) (ep397 rfl) rfl rfl) (@ep398 65801 12000 0 1 (ep400 rfl) (ep402 rfl) rfl rfl)

noncomputable def ep404 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 ep403

noncomputable abbrev qz138 := (@Enclosure.Complex.IsNear.re_isNear qz373 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz373 (Complex.mk (Enclosure.sfrac Bool.false 1 14) qz273) Bool.false 1 14 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 14 1 14 EMRow16.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 14) qz273 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 14) qz284)))

noncomputable def ep405 := @ep389 336 0 1 ep404 qz138

noncomputable def ep406 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 65801 12000 0 1 0 1 0 1 0

noncomputable def ep407 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 65801 12000 0 1 ep403

noncomputable abbrev qz139 := (@Enclosure.Complex.IsNear.im_isNear qz373 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz373 (Complex.mk (Enclosure.sfrac Bool.false 1 14) qz273) Bool.false 1 14 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 14 1 14 EMRow16.d8 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 14) qz273 Bool.false 1 14 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 14) qz284)))

noncomputable def ep408 := @ep406 1 0 1 ep407 qz139

noncomputable def ep409 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) 0 1 0 1 65801 168000 0

noncomputable def ep410 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 0 1 0 1 0

noncomputable def ep411 := @ep410 1 0 1 ep404 qz139

noncomputable def ep412 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 65801 12000 0 1 1 14 0 1 65801

noncomputable def ep413 := @ep412 168000 0 1 ep407 qz138

noncomputable def ep414 := @ep385 1 (@ep386 0 1 0 1 (BSN.bern_sum_base qz6 14) qz91) (ep387 (@ep388 1 1 1 336 0 1 (ep405 rfl) (ep408 rfl) rfl rfl) (@ep409 1 65801 65801 168000 0 1 (ep411 rfl) (ep413 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep415 := ep379 (ep382 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep383 Bool.false 65801 168000 0 1 (BSN.bern_sum_succ qz6 14 0 1 1 rfl rfl) (ep414 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep416 := @Enclosure.Real.IsNear.mulLit_ff qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 55902534039 274877906944 2470751397223 10360972946440192 130155799367401

noncomputable def ep417 := @ep416 727443628968000 0 1 ep357 ep358 ep359 ep360 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (ep363 ep375))

noncomputable def ep418 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 729421650569 1454887257936 0 1 Bool.false

noncomputable def ep419 := nat_lit 80323539362991591401266229

noncomputable def ep420 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz124 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 6462175697079550012941 208289773073407882035200 ep419

noncomputable def ep421 := nat_lit 1884255939949431191412670464000

noncomputable def ep422 := nat_lit 1802219562308063622969887

noncomputable def ep423 := nat_lit 15074047519595449531301363712

noncomputable def ep424 := nat_lit 1969667335341063269988601042975583739473559552

noncomputable def ep425 := @Enclosure.Real.IsNear.mulLit_tf qz124 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 744743115 4294967296 617133771629 2590243236610048 130155799367401

noncomputable def ep426 := @ep425 727443628968000 0 1 6462175697079550012941 208289773073407882035200 ep419 ep421 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (ep363 ep375))

noncomputable def ep427 := @Enclosure.Real.IsNear.mulLit_ff qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz100 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 55902534039 274877906944 2470751397223 10360972946440192 729421650569

noncomputable def ep428 := @ep427 1454887257936 0 1 13592172883239028739397 133305454766981044502528 ep422 ep423 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.true 744743115 4294967296 617133771629 2590243236610048 Bool.false 55902534039 274877906944 2470751397223 10360972946440192 (ep363 ep375))

noncomputable abbrev qz374 := (ep415 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep429 := @ep354 236409510927702918277869 ep276 ep282 ep278 (@ep355 ep356 ep357 ep358 ep359 ep360 ep361 1174259765461511605113459 ep156 ep281 ep158 (ep376 (@ep377 130155799367401 727443628968000 0 1 qz374) rfl) (ep417 (@ep418 130155799367401 727443628968000 0 1 qz374) rfl) rfl rfl) (@ep420 ep421 13592172883239028739397 133305454766981044502528 ep422 ep423 ep424 236409510927702918277869 ep276 ep282 ep278 (ep426 (@ep418 130155799367401 727443628968000 0 1 qz374) rfl) (ep428 (@ep377 130155799367401 727443628968000 0 1 qz374) rfl) rfl rfl)

noncomputable def ep430 := @ep285 ep277 ep278 (@ep286 5180486473220096 (BSN.head_sum_c_eq qz6 14) (ep287 (BSN.head_sum_c_succ qz6 13 14 rfl rfl) (ep353 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep429 rfl rfl rfl

noncomputable def ep431 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz6 1 14) Bool.false ep155 ep156 ep157 ep158 Bool.false 110075327259856443593869 ep276 ep277 ep278 (@ep279 ep158 Bool.false 110075327259856443593869 ep276 ep277 ep278 (BSN.zetaApproximant_eq_folded' qz6 1 14 rfl) (ep430 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep432 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) (Complex.im (zetaApproximant qz6 1 14)) 33 262144 7913823

noncomputable def ep433 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50)) Bool.false 66 524288 15827646

noncomputable def ep434 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) qz313 Bool.false 23059457 524288 203

noncomputable def ep435 := BSN.sin_dyadic_bound_f 135970 1073741824 1 0 524288 150920 0 1 1 0 1 1 66 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 135970) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 135970) qz278 0 0 rfl) rfl rfl

noncomputable def ep436 := @ep434 524288 Bool.false 66 524288 1 75386 (@ep162 23059457 524288 203 524288 ep273 rfl) (Enclosure.sfrac_false_div 23059457 524288) (BSN.sin_reduce0 qz313 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9568050315089936384) qz23) 226375608064910080 72057594037927936 Bool.false 66 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 23059457 524288 226375608064910080 72057594037927936 7 9568050315089936384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 66 524288 9568050315089936384 75557863725914323419136 135970 1073741824 150920 150772 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep437 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz6 1 14) Bool.false ep155 ep156 ep157 ep158 Bool.false 110075327259856443593869 ep276 ep277 ep278 (@ep279 ep158 Bool.false 110075327259856443593869 ep276 ep277 ep278 (BSN.zetaApproximant_eq_folded' qz6 1 14 rfl) (ep430 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow16.d9 : Enclosure.Real.IsNear (hardyZApproximantEM 1 14 qz17) Bool.false ep138 ep139 ep140 ep141 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 14 qz17) ep142 Bool.false ep138 ep139 ep140 ep141 (@Eq.refl Real ep142) (@ep143 Bool.false ep138 ep139 ep140 ep141 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz48 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz49 (@Nat.cast Complex Complex.instNatCast j))))) qz50) (zetaApproximant qz6 1 14)) (@ep145 ep146 ep147 ep148 ep149 ep150 ep151 ep152 ep153 ep138 ep139 ep140 ep141 (@ep154 19761987584 ep155 ep156 ep157 ep158 ep144 ep146 ep147 ep148 (@ep159 39523975168 524287 524288 7913823 19761987584 (ep275 rfl rfl) rfl) ep431 rfl) (@ep432 19761987584 110075327259856443593869 ep276 ep277 ep278 ep149 ep150 ep151 ep152 (@ep433 39523975168 33 262144 7913823 19761987584 (ep436 rfl rfl) rfl) ep437 rfl) rfl rfl))

noncomputable abbrev qz478 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 68454 1000)))

noncomputable abbrev qz464 := qz478

noncomputable abbrev qz375 := qz464

noncomputable abbrev qz140 := (BSN.headSumC qz375 9)

noncomputable abbrev qz141 := qz375

noncomputable abbrev qz465 := (@Neg.neg Complex Complex.instNeg qz478)

noncomputable abbrev qz376 := qz465

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 8) qz376)

noncomputable def ep438 := @Enclosure.Complex.IsNear.of_eq qz140 (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 8) qz142) Bool.false 101905133827 274877906944 32392306658465 10360972946440192 Bool.false 32105078227 274877906944 32318417145951 10360972946440192

noncomputable def ep439 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 8) qz142 Bool.false 156487864259 274877906944 28999852021293 10360972946440192 Bool.true 24151120001 137438953472 1807544447357 647560809152512 Bool.true

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 7) qz376)

noncomputable def ep440 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 8) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 7) qz143) Bool.false 156487864259 274877906944 28999852021293 10360972946440192 Bool.true 24151120001 137438953472 1807544447357 647560809152512

noncomputable def ep441 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 7) qz143 Bool.false 124537251117 274877906944 25378925398511 10360972946440192 Bool.false 25278658719 137438953472 6321764411063 2590243236610048 Bool.false

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 6) qz376)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 7) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 6) qz144) Bool.false 124537251117 274877906944 25378925398511 10360972946440192 Bool.false 25278658719 137438953472 6321764411063 2590243236610048

noncomputable def ep443 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 6) qz144 Bool.false 235794723317 274877906944 21454878038911 10360972946440192 Bool.false 8976801011 68719476736 10690011585487 5180486473220096 Bool.true

noncomputable abbrev qz145 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 5) qz376)

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 6) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 5) qz145) Bool.false 235794723317 274877906944 21454878038911 10360972946440192 Bool.false 8976801011 68719476736 10690011585487 5180486473220096

noncomputable def ep445 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 5) qz145 Bool.false 355851761139 274877906944 17158445219227 10360972946440192 Bool.false 9489816283 274877906944 17098643767007 10360972946440192 Bool.true

noncomputable abbrev qz146 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 4) qz376)

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 5) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 4) qz146) Bool.false 355851761139 274877906944 17158445219227 10360972946440192 Bool.false 9489816283 274877906944 17098643767007 10360972946440192

noncomputable def ep447 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 4) qz146 Bool.false 61597766979 68719476736 6180376288467 5180486473220096 Bool.false 46300996145 137438953472 6152369861765 5180486473220096 Bool.false

noncomputable abbrev qz147 := (@HPow.hPow Complex Complex Complex qz269 qz271 qz376)

noncomputable def ep448 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 4) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 3) qz147) Bool.false 61597766979 68719476736 6180376288467 5180486473220096 Bool.false 46300996145 137438953472 6152369861765 5180486473220096

noncomputable def ep449 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 3) qz147 Bool.false 5666679439 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 34359738368 1693839183485 2590243236610048 Bool.false

noncomputable abbrev qz148 := (@HPow.hPow Complex Complex Complex qz269 qz272 qz376)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 3) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 2) qz148) Bool.false 5666679439 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 34359738368 1693839183485 2590243236610048

noncomputable def ep451 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 2) qz148 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep452 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz14) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz141)

noncomputable abbrev qz479 := (Enclosure.sfrac Bool.false 68454 1000)

noncomputable abbrev qz466 := qz479

noncomputable abbrev qz377 := qz466

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 2 1)))

noncomputable abbrev qz150 := qz377

noncomputable abbrev qz378 := (@Eq.refl Real qz466)

noncomputable abbrev qz151 := qz378

noncomputable def ep453 := @Enclosure.Complex.IsNear.of_eq qz148 (Complex.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 11513189745 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 34359738368 1693839183485 2590243236610048 (BSN.cpow_neg_s_mk qz150 68454 1000 2 qz151 rfl)

noncomputable def ep454 := nat_lit 14776687663802335055932070670893056

noncomputable def ep455 := BSN.cos_dyadic_bound_f 348653696 1073741824 2 1 524288 150920 ep454 ep77 ep454 ep454 ep78 ep454 496890 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 348653696) qz281 0 1 ep454 ep77 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 348653696) qz282 0 1 ep454 ep78 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz379 := (Enclosure.Real.IsNear.const Bool.false 68454 1000)

noncomputable abbrev qz152 := qz379

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24876731) qz20)

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 24534322743406841823232)

noncomputable def ep456 := @Enclosure.Real.IsNear.cos_image qz149 qz380 Bool.false 24876731 524288 477 524288 Bool.true 496890 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 777397851 16384000 34227 37693000 24876731 524288 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz21 68454 1000 0 1 181704 262144 1 75386 777397851 16384000 34227 37693000 qz152 qz280 rfl) rfl) (Enclosure.sfrac_false_div 24876731 524288) (BSN.cos_reduce2 qz380 (@HDiv.hDiv Real Real Real qz2 qz381 qz23) 226375608064910080 72057594037927936 Bool.false 496890 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 24876731 524288 226375608064910080 72057594037927936 7 24534322743406841823232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496890 524288 24534322743406841823232 75557863725914323419136 348653696 1073741824 150920 150772 (ep455 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep457 := BSN.sin_dyadic_bound_f 348653696 1073741824 2 1 524288 150920 ep454 ep92 ep454 ep454 ep93 ep454 167265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 348653696) qz277 0 1 ep454 ep92 ep454 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 348653696) qz278 0 1 ep454 ep93 ep454 rfl rfl rfl rfl) rfl rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image qz149 qz380 Bool.false 24876731 524288 477 524288 Bool.true 167265 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 777397851 16384000 34227 37693000 24876731 524288 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz21 68454 1000 0 1 181704 262144 1 75386 777397851 16384000 34227 37693000 qz152 qz280 rfl) rfl) (Enclosure.sfrac_false_div 24876731 524288) (BSN.sin_reduce2 qz380 (@HDiv.hDiv Real Real Real qz2 qz381 qz23) 226375608064910080 72057594037927936 Bool.false 167265 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 24876731 524288 226375608064910080 72057594037927936 7 24534322743406841823232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 167265 524288 24534322743406841823232 75557863725914323419136 348653696 1073741824 150920 150772 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz15 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz15 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 11513189745 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 34359738368 1693839183485 2590243236610048 (@Enclosure.Real.IsNear.mulLit_ft qz15 (Real.cos qz149) 46341 65536 1 262144 248445 262144 18241705 19761987584 11513189745 17179869184 3400102922095 5180486473220096 qz283 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 496890 524288 36483410 39523975168 248445 262144 18241705 19761987584 (ep456 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz15 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 46341 65536 1 262144 167265 524288 18241705 19761987584 7751227365 34359738368 1693839183485 2590243236610048 qz283 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 167265 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 167265 524288 36483410 39523975168 167265 524288 18241705 19761987584 (ep458 rfl rfl) rfl)) rfl)

noncomputable def ep460 := @ep451 11513189745 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 34359738368 1693839183485 2590243236610048 Bool.false 5666679439 5666679439 17179869184 3400102922095 5180486473220096 Bool.false 7751227365 7751227365 34359738368 1693839183485 2590243236610048 (ep452 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz14 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz24)) (ep453 ep459) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz147 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 38931049223 68719476736 695068341593 1295121618305024 Bool.false 15296086685 137438953472 2764691494795 5180486473220096 (BSN.cpow_neg_s_mk qz150 68454 1000 3 qz151 rfl)

noncomputable def ep462 := nat_lit 19222032091252900822476385994109773343710961188762635854078751316183309561505

noncomputable def ep463 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep464 := nat_lit 22814163178330590403576508919208453061347618765587600338147142003553676961

noncomputable def ep465 := nat_lit 50306480165278395483927601351084973642857954587805475883944491407712438136481

noncomputable def ep466 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep467 := BSN.sin_dyadic_bound_f 1478344221 1073741824 3 2 524288 150920 ep462 ep463 ep464 ep465 ep466 ep464 514454 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1478344221) qz277 0 2 ep462 ep463 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1478344221) qz278 0 2 ep465 ep466 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 19714341) qz28)

noncomputable def ep468 := @Enclosure.Real.IsNear.cos_image qz153 qz382 Bool.false 19714341 262144 477 524288 Bool.false 514454 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 4928585319 65536000 34227 37693000 19714341 262144 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz29 68454 1000 0 1 287994 262144 1 75386 4928585319 65536000 34227 37693000 qz152 qz286 rfl) rfl) (Enclosure.sfrac_false_div 19714341 262144) (BSN.cos_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52014613179870490918912) qz30) 226375608064910080 72057594037927936 Bool.false 514454 524288 11 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 19714341 262144 226375608064910080 72057594037927936 11 52014613179870490918912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 514454 524288 52014613179870490918912 37778931862957161709568 1478344221 1073741824 150920 150772 (ep467 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep469 := nat_lit 10689046345441980719332915111802855614533355157652836630194038349881195835041

noncomputable def ep470 := nat_lit 32021510709969280977191592317570149937477370235427334689905820765636480151201

noncomputable def ep471 := BSN.cos_dyadic_bound_f 1478344221 1073741824 3 2 524288 150920 ep469 ep119 ep464 ep470 ep122 ep464 101065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1478344221) qz281 0 2 ep469 ep119 ep464 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1478344221) qz282 0 2 ep470 ep122 ep464 rfl rfl rfl rfl) rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.sin_image qz153 qz382 Bool.false 19714341 262144 477 524288 Bool.true 101065 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 4928585319 65536000 34227 37693000 19714341 262144 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz29 68454 1000 0 1 287994 262144 1 75386 4928585319 65536000 34227 37693000 qz152 qz286 rfl) rfl) (Enclosure.sfrac_false_div 19714341 262144) (BSN.sin_reduce3 qz382 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 52014613179870490918912) qz30) 226375608064910080 72057594037927936 Bool.false 101065 524288 11 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 19714341 262144 226375608064910080 72057594037927936 11 52014613179870490918912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 101065 524288 52014613179870490918912 37778931862957161709568 1478344221 1073741824 150920 150772 (ep471 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep473 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 38931049223 68719476736 695068341593 1295121618305024 Bool.false 15296086685 137438953472 2764691494795 5180486473220096 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz153) 151349 262144 1 262144 257227 262144 18241705 19761987584 38931049223 68719476736 695068341593 1295121618305024 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 514454 524288 36483410 39523975168 257227 262144 18241705 19761987584 (ep468 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 151349 262144 1 262144 101065 524288 18241705 19761987584 15296086685 137438953472 2764691494795 5180486473220096 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 101065 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 101065 524288 36483410 39523975168 101065 524288 18241705 19761987584 (ep472 rfl rfl) rfl)) rfl)

noncomputable def ep474 := @ep449 38931049223 68719476736 695068341593 1295121618305024 Bool.false 15296086685 137438953472 2764691494795 5180486473220096 Bool.false 1058241578725734875136 61597766979 68719476736 6180376288467 5180486473220096 Bool.false 1590890113719976591360 46300996145 137438953472 6152369861765 5180486473220096 (ep450 (BSN.head_sum_c_succ qz141 2 3 rfl rfl) (ep460 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep461 ep473) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep475 := @Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 109460693223 274877906944 4797692642293 10360972946440192 Bool.true 83112176007 274877906944 4793904043477 10360972946440192 (BSN.cpow_neg_s_mk qz150 68454 1000 4 qz151 rfl)

noncomputable def ep476 := nat_lit 236427002620837360894913130734288896

noncomputable def ep477 := BSN.cos_dyadic_bound_f 697307392 1073741824 2 1 524288 150920 ep476 ep77 ep476 ep476 ep78 ep476 417561 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 697307392) qz281 0 1 ep476 ep77 ep476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 697307392) qz282 0 1 ep476 ep78 ep476 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24876731) qz28)

noncomputable def ep478 := @Enclosure.Real.IsNear.cos_image qz154 qz383 Bool.false 24876731 262144 477 524288 Bool.false 417561 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 777397851 8192000 34227 37693000 24876731 262144 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz33 68454 1000 0 1 363408 262144 1 75386 777397851 8192000 34227 37693000 qz152 qz290 rfl) rfl) (Enclosure.sfrac_false_div 24876731 262144) (BSN.cos_reduce0 qz383 (@HDiv.hDiv Real Real Real qz2 qz381 qz30) 226375608064910080 72057594037927936 Bool.false 417561 524288 15 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 24876731 262144 226375608064910080 72057594037927936 15 24534322743406841823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 417561 524288 24534322743406841823232 37778931862957161709568 697307392 1073741824 150920 150772 (ep477 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep479 := BSN.sin_dyadic_bound_f 697307392 1073741824 2 1 524288 150920 ep476 ep92 ep476 ep476 ep93 ep476 317049 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 697307392) qz277 0 1 ep476 ep92 ep476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 697307392) qz278 0 1 ep476 ep93 ep476 rfl rfl rfl rfl) rfl rfl

noncomputable def ep480 := @Enclosure.Real.IsNear.sin_image qz154 qz383 Bool.false 24876731 262144 477 524288 Bool.false 317049 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 777397851 8192000 34227 37693000 24876731 262144 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz33 68454 1000 0 1 363408 262144 1 75386 777397851 8192000 34227 37693000 qz152 qz290 rfl) rfl) (Enclosure.sfrac_false_div 24876731 262144) (BSN.sin_reduce0 qz383 (@HDiv.hDiv Real Real Real qz2 qz381 qz30) 226375608064910080 72057594037927936 Bool.false 317049 524288 15 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 24876731 262144 226375608064910080 72057594037927936 15 24534322743406841823232 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 317049 524288 24534322743406841823232 37778931862957161709568 697307392 1073741824 150920 150772 (ep479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep481 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 109460693223 274877906944 4797692642293 10360972946440192 Bool.true 83112176007 274877906944 4793904043477 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz154) 262143 524288 1 524288 417561 524288 18241705 19761987584 109460693223 274877906944 4797692642293 10360972946440192 qz291 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 417561 524288 36483410 39523975168 417561 524288 18241705 19761987584 (ep478 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 262143 524288 1 524288 317049 524288 18241705 19761987584 83112176007 274877906944 4793904043477 10360972946440192 qz291 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 317049 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 317049 524288 36483410 39523975168 317049 524288 18241705 19761987584 (ep480 rfl rfl) rfl)) rfl)

noncomputable def ep482 := @ep447 109460693223 274877906944 4797692642293 10360972946440192 Bool.true 83112176007 274877906944 4793904043477 10360972946440192 Bool.false 24453946821056139362304 355851761139 274877906944 17158445219227 10360972946440192 Bool.false 1304270418577064984576 9489816283 274877906944 17098643767007 10360972946440192 (ep448 (BSN.head_sum_c_succ qz141 3 4 rfl rfl) (ep474 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep475 ep481) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep483 := @Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 60028518911 137438953472 1074108204921 2590243236610048 Bool.false 26417387761 274877906944 4281379403967 10360972946440192 (BSN.cpow_neg_s_mk qz150 68454 1000 5 qz151 rfl)

noncomputable def ep484 := nat_lit 2925177226006055083518744281864881

noncomputable def ep485 := BSN.cos_dyadic_bound_f 232561621 1073741824 2 1 524288 150920 ep484 ep77 ep484 ep484 ep78 ep484 512038 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 232561621) qz281 0 1 ep484 ep77 ep484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 232561621) qz282 0 1 ep484 ep78 ep484 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3610127) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep486 := @Enclosure.Real.IsNear.cos_image qz155 qz384 Bool.false 3610127 32768 477 524288 Bool.true 512038 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 902531763 8192000 34227 37693000 3610127 32768 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz36 68454 1000 0 1 421904 262144 1 75386 902531763 8192000 34227 37693000 qz152 qz294 rfl) rfl) (Enclosure.sfrac_false_div 3610127 32768) (BSN.cos_reduce2 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1022816827757186514944) qz359) 226375608064910080 72057594037927936 Bool.false 512038 524288 17 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 3610127 32768 226375608064910080 72057594037927936 17 1022816827757186514944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512038 524288 1022816827757186514944 4722366482869645213696 232561621 1073741824 150920 150772 (ep485 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep487 := BSN.sin_dyadic_bound_f 232561621 1073741824 2 1 524288 150920 ep484 ep92 ep484 ep484 ep93 ep484 112669 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 232561621) qz277 0 1 ep484 ep92 ep484 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 232561621) qz278 0 1 ep484 ep93 ep484 rfl rfl rfl rfl) rfl rfl

noncomputable def ep488 := @Enclosure.Real.IsNear.sin_image qz155 qz384 Bool.false 3610127 32768 477 524288 Bool.true 112669 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 902531763 8192000 34227 37693000 3610127 32768 477 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz36 68454 1000 0 1 421904 262144 1 75386 902531763 8192000 34227 37693000 qz152 qz294 rfl) rfl) (Enclosure.sfrac_false_div 3610127 32768) (BSN.sin_reduce2 qz384 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1022816827757186514944) qz359) 226375608064910080 72057594037927936 Bool.false 112669 524288 17 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 3610127 32768 226375608064910080 72057594037927936 17 1022816827757186514944 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 112669 524288 1022816827757186514944 4722366482869645213696 232561621 1073741824 150920 150772 (ep487 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep489 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 60028518911 137438953472 1074108204921 2590243236610048 Bool.false 26417387761 274877906944 4281379403967 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz155) 234469 524288 1 524288 256019 262144 18241705 19761987584 60028518911 137438953472 1074108204921 2590243236610048 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 512038 524288 36483410 39523975168 256019 262144 18241705 19761987584 (ep486 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 234469 524288 1 524288 112669 524288 18241705 19761987584 26417387761 274877906944 4281379403967 10360972946440192 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 112669 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 112669 524288 36483410 39523975168 112669 524288 18241705 19761987584 (ep488 rfl rfl) rfl)) rfl)

noncomputable def ep490 := @ep445 60028518911 137438953472 1074108204921 2590243236610048 Bool.false 26417387761 274877906944 4281379403967 10360972946440192 Bool.false 32407380006908276506624 235794723317 274877906944 21454878038911 10360972946440192 Bool.false 9870097091825852481536 8976801011 68719476736 10690011585487 5180486473220096 (ep446 (BSN.head_sum_c_succ qz141 4 5 rfl rfl) (ep482 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep483 ep489) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 6 1)))

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 13907184025 34359738368 245252959975 647560809152512 Bool.false 7325056697 137438953472 1953517236639 5180486473220096 (BSN.cpow_neg_s_mk qz150 68454 1000 6 qz151 rfl)

noncomputable def ep492 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz39 68454 1000 0 1 4034681531866359 2251799813685248 250000000037693 18846500000000000000 138095044791189869493 1125899906842624000 8556750001290118311 9423250000000000000000 qz152 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 250000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz297) Bool.false 16922680887833197019136 9444732965739290427392 1000000000150772 75386000000000000000 4034681531866359 2251799813685248 250000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep102 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep493 := nat_lit 390556281841353262948593174057216

noncomputable def ep494 := BSN.cos_dyadic_bound_f 140579148 1073741824 2 1 524288 150920 ep493 ep77 ep493 ep493 ep78 ep493 519800 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 140579148) qz281 0 1 ep493 ep77 ep493 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 140579148) qz282 0 1 ep493 ep78 ep493 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 16076379) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep495 := @Enclosure.Real.IsNear.cos_image qz156 qz385 Bool.false 16076379 131072 477 524288 Bool.true 519800 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 138095044791189869493 1125899906842624000 8556750001290118311 9423250000000000000000 16076379 131072 477 524288 (ep492 rfl) rfl) (Enclosure.sfrac_false_div 16076379 131072) (BSN.cos_reduce2 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2473094541596015198208) qz354) 226375608064910080 72057594037927936 Bool.false 519800 524288 19 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 16076379 131072 226375608064910080 72057594037927936 19 2473094541596015198208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 519800 524288 2473094541596015198208 18889465931478580854784 140579148 1073741824 150920 150772 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := BSN.sin_dyadic_bound_f 140579148 1073741824 1 0 524288 150920 0 1 1 0 1 1 68446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 140579148) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 140579148) qz278 0 0 rfl) rfl rfl

noncomputable def ep497 := @Enclosure.Real.IsNear.sin_image qz156 qz385 Bool.false 16076379 131072 477 524288 Bool.true 68446 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 138095044791189869493 1125899906842624000 8556750001290118311 9423250000000000000000 16076379 131072 477 524288 (ep492 rfl) rfl) (Enclosure.sfrac_false_div 16076379 131072) (BSN.sin_reduce2 qz385 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 2473094541596015198208) qz354) 226375608064910080 72057594037927936 Bool.false 68446 524288 19 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 16076379 131072 226375608064910080 72057594037927936 19 2473094541596015198208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68446 524288 2473094541596015198208 18889465931478580854784 140579148 1073741824 150920 150772 (ep496 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep498 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 13907184025 34359738368 245252959975 647560809152512 Bool.false 7325056697 137438953472 1953517236639 5180486473220096 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz156) 214039 524288 1 524288 64975 65536 18241705 19761987584 13907184025 34359738368 245252959975 647560809152512 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 519800 524288 36483410 39523975168 64975 65536 18241705 19761987584 (ep495 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 214039 524288 1 524288 34223 262144 18241705 19761987584 7325056697 137438953472 1953517236639 5180486473220096 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 34223 262144 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 68446 524288 36483410 39523975168 34223 262144 18241705 19761987584 (ep497 rfl rfl) rfl)) rfl)

noncomputable def ep499 := @ep443 13907184025 34359738368 245252959975 647560809152512 Bool.false 7325056697 137438953472 1953517236639 5180486473220096 Bool.false 4279067365450035757056 124537251117 274877906944 25378925398511 10360972946440192 Bool.false 1737136199757604061184 25278658719 137438953472 6321764411063 2590243236610048 (ep444 (BSN.head_sum_c_succ qz141 5 6 rfl rfl) (ep490 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep491 ep498) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 7 1)))

noncomputable def ep500 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 15975306571 137438953472 1810463311391 5180486473220096 Bool.true 1544680585 4294967296 908413378365 2590243236610048 (BSN.cpow_neg_s_mk qz150 68454 1000 7 qz151 rfl)

noncomputable def ep501 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz42 68454 1000 0 1 4381792198794487 2251799813685248 250000000037693 18846500000000000000 149975601588138906549 1125899906842624000 8556750001290118311 9423250000000000000000 qz152 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 250000000037693 18846500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz301) Bool.false 18378568546572512002048 9444732965739290427392 1000000000150772 75386000000000000000 4381792198794487 2251799813685248 250000000037693 18846500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep502 := nat_lit 7449967282926370199276991972106378236813281291752338793783682707813936800000

noncomputable def ep503 := nat_lit 11096767216977426459932152880117650279776434825053439826752193440100000000

noncomputable def ep504 := nat_lit 22327708314345155744911111610558899409880291005606909501697543736561610400000

noncomputable def ep505 := BSN.cos_dyadic_bound_f 1350981990 1073741824 3 2 524288 150920 ep502 ep119 ep503 ep504 ep122 ep503 161234 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1350981990) qz281 0 2 ep502 ep119 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1350981990) qz282 0 2 ep504 ep122 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 69837831) qz20)

noncomputable def ep506 := @Enclosure.Real.IsNear.cos_image qz157 qz386 Bool.false 69837831 524288 477 524288 Bool.false 161234 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 149975601588138906549 1125899906842624000 8556750001290118311 9423250000000000000000 69837831 524288 477 524288 (ep501 rfl) rfl) (Enclosure.sfrac_false_div 69837831 524288) (BSN.cos_reduce0 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95066906079449183158272) qz23) 226375608064910080 72057594037927936 Bool.false 161234 524288 21 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 69837831 524288 226375608064910080 72057594037927936 21 95066906079449183158272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 161234 524288 95066906079449183158272 75557863725914323419136 1350981990 1073741824 150920 150772 (ep505 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep507 := nat_lit 13401063695493884417530639827487386706040085177294167076949227119313006240000

noncomputable def ep508 := nat_lit 35080057769846971926883214157803917558223442188910827251337996046916759200000

noncomputable def ep509 := BSN.sin_dyadic_bound_f 1350981990 1073741824 3 2 524288 150920 ep507 ep463 ep503 ep508 ep466 ep503 498880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1350981990) qz277 0 2 ep507 ep463 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1350981990) qz278 0 2 ep508 ep466 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable def ep510 := @Enclosure.Real.IsNear.sin_image qz157 qz386 Bool.false 69837831 524288 477 524288 Bool.false 498880 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 149975601588138906549 1125899906842624000 8556750001290118311 9423250000000000000000 69837831 524288 477 524288 (ep501 rfl) rfl) (Enclosure.sfrac_false_div 69837831 524288) (BSN.sin_reduce0 qz386 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 95066906079449183158272) qz23) 226375608064910080 72057594037927936 Bool.false 498880 524288 21 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 69837831 524288 226375608064910080 72057594037927936 21 95066906079449183158272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 498880 524288 95066906079449183158272 75557863725914323419136 1350981990 1073741824 150920 150772 (ep509 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep511 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 15975306571 137438953472 1810463311391 5180486473220096 Bool.true 1544680585 4294967296 908413378365 2590243236610048 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz157) 198163 524288 1 524288 80617 262144 18241705 19761987584 15975306571 137438953472 1810463311391 5180486473220096 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 161234 524288 36483410 39523975168 80617 262144 18241705 19761987584 (ep506 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 198163 524288 1 524288 7795 8192 18241705 19761987584 1544680585 4294967296 908413378365 2590243236610048 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 7795 8192 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 498880 524288 36483410 39523975168 7795 8192 18241705 19761987584 (ep510 rfl rfl) rfl)) rfl)

noncomputable def ep512 := @ep441 15975306571 137438953472 1810463311391 5180486473220096 Bool.true 1544680585 4294967296 908413378365 2590243236610048 Bool.false 21507528294825352757248 156487864259 274877906944 28999852021293 10360972946440192 Bool.true 103728270566066487296 24151120001 137438953472 1807544447357 647560809152512 (ep442 (BSN.head_sum_c_succ qz141 6 7 rfl rfl) (ep499 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep500 ep511) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 8 1)))

noncomputable def ep513 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 852855163 4294967296 848113659293 2590243236610048 Bool.false 80407318229 274877906944 3397705988239 10360972946440192 (BSN.cpow_neg_s_mk qz150 68454 1000 8 qz151 rfl)

noncomputable def ep514 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz45 68454 1000 0 1 9364972152248037 4503599627370496 500000000113079 37693000000000000000 320534901854993562399 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 19639770079031275290624 9444732965739290427392 1000000000226158 75386000000000000000 9364972152248037 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep515 := nat_lit 2677488449161125320162913202030419972286931979478459171483269756406988800000

noncomputable def ep516 := nat_lit 1436057074798962542799483379989063159875543523915318546289760665600000000

noncomputable def ep517 := nat_lit 8029593233333778035403140639331281790541044851387546877357229747889766400000

noncomputable def ep518 := BSN.cos_dyadic_bound_f 1046276480 1073741824 3 2 524288 150920 ep515 ep119 ep516 ep517 ep122 ep516 294464 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1046276480) qz281 0 2 ep515 ep119 ep516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1046276480) qz282 0 2 ep517 ep122 ep516 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 74630347) qz20)

noncomputable def ep519 := @Enclosure.Real.IsNear.cos_image qz158 qz387 Bool.false 74630347 524288 477 524288 Bool.true 294464 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 320534901854993562399 2251799813685248000 17113500003870354933 18846500000000000000000 74630347 524288 477 524288 (ep514 rfl) rfl) (Enclosure.sfrac_false_div 74630347 524288) (BSN.cos_reduce2 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 73625161969184207273984) qz23) 226375608064910080 72057594037927936 Bool.false 294464 524288 22 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 74630347 524288 226375608064910080 72057594037927936 22 73625161969184207273984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 294464 524288 73625161969184207273984 75557863725914323419136 1046276480 1073741824 150920 150772 (ep518 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep520 := nat_lit 4818330362830186406259004176950764699588577128242094253832853753000099840000

noncomputable def ep521 := nat_lit 12617111619767480362751907014160591920473141598738193482392052597732147200000

noncomputable def ep522 := BSN.sin_dyadic_bound_f 1046276480 1073741824 3 2 524288 150920 ep520 ep463 ep516 ep521 ep466 ep516 433783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1046276480) qz277 0 2 ep520 ep463 ep516 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1046276480) qz278 0 2 ep521 ep466 ep516 rfl rfl rfl rfl) rfl rfl

noncomputable def ep523 := @Enclosure.Real.IsNear.sin_image qz158 qz387 Bool.false 74630347 524288 477 524288 Bool.true 433783 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 320534901854993562399 2251799813685248000 17113500003870354933 18846500000000000000000 74630347 524288 477 524288 (ep514 rfl) rfl) (Enclosure.sfrac_false_div 74630347 524288) (BSN.sin_reduce2 qz387 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 73625161969184207273984) qz23) 226375608064910080 72057594037927936 Bool.false 433783 524288 22 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 74630347 524288 226375608064910080 72057594037927936 22 73625161969184207273984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 433783 524288 73625161969184207273984 75557863725914323419136 1046276480 1073741824 150920 150772 (ep522 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep524 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 852855163 4294967296 848113659293 2590243236610048 Bool.false 80407318229 274877906944 3397705988239 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz158) 185363 524288 1 524288 4601 8192 18241705 19761987584 852855163 4294967296 848113659293 2590243236610048 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 294464 524288 36483410 39523975168 4601 8192 18241705 19761987584 (ep519 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 185363 524288 1 524288 433783 524288 18241705 19761987584 80407318229 274877906944 3397705988239 10360972946440192 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 433783 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 433783 524288 36483410 39523975168 433783 524288 18241705 19761987584 (ep523 rfl rfl) rfl)) rfl)

noncomputable def ep525 := @ep439 852855163 4294967296 848113659293 2590243236610048 Bool.false 80407318229 274877906944 3397705988239 10360972946440192 Bool.false 437679217081468321792 101905133827 274877906944 32392306658465 10360972946440192 Bool.false 4412488352655573254144 32105078227 274877906944 32318417145951 10360972946440192 (ep440 (BSN.head_sum_c_succ qz141 7 8 rfl rfl) (ep512 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep513 ep524) rfl rfl

theorem EMRow16.d10 : Enclosure.Complex.IsNear qz140 Bool.false 101905133827 274877906944 32392306658465 10360972946440192 Bool.false 32105078227 274877906944 32318417145951 10360972946440192 := ep438 (BSN.head_sum_c_succ qz141 8 9 rfl rfl) (ep525 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep526 := nat_lit 3856353088438573671062795892047

noncomputable def ep527 := nat_lit 2363734138774531614579884032000

noncomputable def ep528 := nat_lit 54475582374247765007044962190580153371

noncomputable def ep529 := nat_lit 10074912693130144921956351682390523904000

noncomputable abbrev qz467 := (@HAdd.hAdd Complex Complex Complex qz472 (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz479) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz388 := qz467

noncomputable abbrev qz159 := (Complex.Stirling.logGammaStirling 1 qz388)

noncomputable abbrev qz468 := (@HAdd.hAdd Complex Complex Complex qz472 qz475 (@HMul.hMul Complex Complex Complex qz474 Complex.I (@HDiv.hDiv Complex Complex Complex qz476 (↑qz479) (2 : Complex))))

noncomputable abbrev qz389 := qz468

noncomputable abbrev qz160 := qz389

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz262 (@HDiv.hDiv Real Real Real qz265 qz377 (2 : Real)) (Real.log Real.pi))

noncomputable def ep530 := Complex.re (@HMul.hMul Complex Complex Complex qz46 (Complex.exp (@HMul.hMul Complex Complex Complex qz46 Complex.I ↑(@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161))) (zetaApproximant qz141 1 14))

noncomputable def ep531 := @Enclosure.Real.IsNear.of_eq ep530 (@HSub.hSub Real Real Real qz312 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.im (zetaApproximant qz141 1 14))))

noncomputable def ep532 := nat_lit 1928157692217268796264335573411

noncomputable def ep533 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.im (zetaApproximant qz141 1 14))) ep532

noncomputable def ep534 := nat_lit 1181867069387265807289942016000

noncomputable def ep535 := nat_lit 2262653984942695519706232935326759699

noncomputable def ep536 := nat_lit 419788028880422705081514653432938496000

noncomputable def ep537 := nat_lit 1508160161443141364989809

noncomputable def ep538 := nat_lit 94549365550981264583195361280

noncomputable def ep539 := nat_lit 34377347124614506819074348547584119

noncomputable def ep540 := nat_lit 2014982538626028984391270336478104780800

noncomputable def ep541 := nat_lit 182307868926217141725951283496064833656213369618625021870080

noncomputable def ep542 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.re (zetaApproximant qz141 1 14)) 524287 524288 8215367

noncomputable def ep543 := nat_lit 3677675952707713134722653

noncomputable def ep544 := nat_lit 2254232538961917509632000

noncomputable def ep545 := nat_lit 2401127145979173789103847771

noncomputable def ep546 := nat_lit 509812722546549340143353856000

noncomputable def ep547 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) Bool.true 524287 524288 16430734

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 24706765) qz20)

noncomputable def ep548 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161) qz390 Bool.false 24706765 524288 211

noncomputable def ep549 := nat_lit 494049689600000000000000000

noncomputable def ep550 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161) Bool.false 212229501114756749593 4503599627370496000 197379972737898632500821 ep549

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161 77736701835024450821 900719925474099200 68368141637898632500821 ep549 2567743767 65536000

noncomputable def ep552 := nat_lit 2781734517011339668265369600

noncomputable def ep553 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 24196946743079943727 450359962737049600 300459640406447977216799 ep165 Bool.false 77736701835024450821 900719925474099200

noncomputable def ep554 := @Enclosure.Complex.IsNear.subLitP qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 21014378132805392727 450359962737049600 292267640394096734976799 ep165 Bool.false 80526939930280934021 900719925474099200 61814541637404582811221

noncomputable def ep555 := nat_lit 54486680167819285690311168330039296

noncomputable def ep556 := nat_lit 21880936338576716833525291418648576

noncomputable abbrev qz391 := (@HSub.hSub Complex Complex Complex qz456 qz467 qz459)

noncomputable abbrev qz392 := (Complex.log qz467)

noncomputable abbrev qz162 := (@HSub.hSub Complex Complex Complex qz309 (@HMul.hMul Complex Complex Complex qz308 qz391 qz392) qz388)

noncomputable abbrev qz163 := qz388

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq qz159 (@HAdd.hAdd Complex Complex Complex qz5 (@HAdd.hAdd Complex Complex Complex qz5 qz162 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k)))))) Bool.true 21014378132805392727

noncomputable def ep558 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz5 qz162 qz52) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) Bool.true 21014449904005290327 450359962737049600

noncomputable def ep559 := nat_lit 180512133652353412989802512384

noncomputable def ep560 := nat_lit 864651433618782829281321943040000

noncomputable def ep561 := @ep558 17838574770016152061 75386000000000000000000 Bool.false 402645617486333093017 4503599627370496000 471587500648357293 3769300000000000000000 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000 Bool.true ep559 21014378132805392727 450359962737049600 292267640394096734976799 ep165 Bool.false ep560

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP qz162 qz52 Bool.true 21428302644726339927 450359962737049600 17551000001949745811 75386000000000000000000

noncomputable def ep563 := nat_lit 2754405977817781413740544

noncomputable def ep564 := @ep562 Bool.false 402645617486333093017 4503599627370496000 471587500648357293 3769300000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep563 21014449904005290327 450359962737049600 17838574770016152061 75386000000000000000000 Bool.false 402645617486333093017 402645617486333093017 4503599627370496000

noncomputable abbrev qz164 := (@HMul.hMul Complex Complex Complex qz308 qz391 qz392)

noncomputable def ep565 := @Enclosure.Complex.IsNear.subLitP qz164 qz163 Bool.true 20414992728567978327 450359962737049600 17551000001949745811 75386000000000000000000 Bool.false 556790321932343059609

noncomputable def ep566 := nat_lit 1610582469945332372068000

noncomputable def ep567 := @ep565 4503599627370496000 471587500648357293 3769300000000000000000 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 Bool.true 85713210578905359708000 21428302644726339927 450359962737049600 17551000001949745811 75386000000000000000000 Bool.false ep566 402645617486333093017 4503599627370496000 471587500648357293 3769300000000000000000

noncomputable abbrev qz165 := qz391

noncomputable abbrev qz166 := qz392

noncomputable def ep568 := @Enclosure.Complex.IsNear.mul qz165 qz166 Bool.true 20414992728567978327 450359962737049600 17551000001949745811 75386000000000000000000 Bool.false 556790321932343059609 4503599627370496000 471587500648357293

noncomputable abbrev qz167 := (Complex.re qz391)

noncomputable abbrev qz168 := (Complex.re qz392)

noncomputable abbrev qz169 := (Complex.im qz391)

noncomputable abbrev qz170 := (Complex.im qz392)

noncomputable def ep569 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz167 qz168) (@HMul.hMul Real Real Real qz0 qz169 qz170) 111446934230332869 18014398509481984 175000000263851 30154400000000000000 5800291521081575013 112589990684262400

noncomputable def ep570 := nat_lit 91940953645150132583584805727240192

noncomputable def ep571 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz168 7000 4000 0 1 15920990604333267 4503599627370496 25000000037693 7538600000000000000

noncomputable def ep572 := @Enclosure.Complex.IsNear.re_isNear qz165 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable abbrev qz393 := (Enclosure.sfrac Bool.false 136908 4000)

noncomputable abbrev qz171 := qz393

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz171) Bool.false 7000 4000 0 1 Bool.false 136908 4000 0

noncomputable abbrev qz172 := (Complex.mk qz324 qz393)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.log qz172) Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000

noncomputable def ep575 := nat_lit 23051339978007009906919893655738620917514240

noncomputable def ep576 := nat_lit 37032879697222267227740796621164265340928

noncomputable def ep577 := nat_lit 106475665571606223424683475305879502848

noncomputable def ep578 := BSN.log_dyadic_bound 2440800464 35208800464 3 2 ep575 524288 150772 ep576 ep577 72807 37649600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2440800464) (BSN.artanhQ 35208800464) 0 2 ep576 ep575 ep577 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz394 := (Real.log (Enclosure.sfrac Bool.false 18824800464 16000000))

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_ff qz70 qz394 1 2 0 1 15920990604333267 2251799813685248 25000000037693 3769300000000000000 15920990604333267 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 18824800464 16000000 15920990604333267 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18824800464) qz327)) Bool.false 133554949151434878222336 18889465931478580854784 1000000001507720 150772000000000000000 15920990604333267 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 18824800464 16000000 10 37649600928 32768000000 72807 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep578 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep580 := BSN.arctan_dyadic_bound_f 9000 136908 1 0 524288 150772 0 1 1 0 1 1 34415 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz395 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 136908)))

noncomputable def ep581 := @Enclosure.Real.IsNear.subLit_ff_p qz71 qz395 884279719003555 562949953421312 1 2000000000000000 34415 524288 1 150772 444243322669941391360 847326894130595 562949953421312 500000000037693 75386000000000000000 qz72 (ep580 rfl) rfl rfl

noncomputable abbrev qz396 := (Real.arctan (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 136908) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep582 := @Enclosure.Complex.IsNear.re_isNear qz166 Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (ep574 (@congrArg Complex Complex qz163 qz172 Complex.log (BSN.w_shift_mk qz150 Bool.false 68454 1000 2 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz172) Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz172)) (@HMul.hMul Real Real Real qz0 qz70 qz394) Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 9000 136908 4000 18824800464 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz172)) qz396 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 9000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz396 (@HSub.hSub Real Real Real qz312 qz71 qz395) Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 136908 9000 rfl rfl) ep581))))

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff qz169 qz170 136908 4000 0 1 847326894130595 562949953421312 500000000037693 75386000000000000000

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear qz165 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable def ep585 := @Enclosure.Complex.IsNear.im_isNear qz166 Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (ep574 (@congrArg Complex Complex qz163 qz172 Complex.log (BSN.w_shift_mk qz150 Bool.false 68454 1000 2 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts (Complex.log qz172) Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re (Complex.log qz172)) (@HMul.hMul Real Real Real qz0 qz70 qz394) Bool.false 15920990604333267 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 9000 136908 4000 18824800464 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im (Complex.log qz172)) qz396 Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 9000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz396 (@HSub.hSub Real Real Real qz312 qz71 qz395) Bool.false 847326894130595 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 136908 9000 rfl rfl) ep581))))

noncomputable abbrev qz397 := (Enclosure.Real.IsNear.const Bool.false 136908 4000)

noncomputable abbrev qz173 := (@ep573 1 (BSN.w_sub_half_mk qz377 Bool.false 68454 1000 2 qz378 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz393 Bool.false 7000 4000 0 1 Bool.false 136908 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz397))

noncomputable def ep586 := @ep569 17113500001290118311 75386000000000000000000 ep570 20414992728567978327 450359962737049600 17551000001949745811 75386000000000000000000 (@ep571 111446934230332869 18014398509481984 175000000263851 30154400000000000000 (ep572 qz173) ep582 rfl) (@ep583 5800291521081575013 112589990684262400 17113500001290118311 75386000000000000000000 (ep584 qz173) ep585 rfl) rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz167 qz170) (@HMul.hMul Real Real Real qz0 qz169 qz168) 5931288258914165 2251799813685248 3500000000263851 301544000000000000000 544927745414514729609 4503599627370496000

noncomputable def ep588 := nat_lit 1253780343188999354802888270027948032

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz167 qz170 7000 4000 0 1 847326894130595 562949953421312 500000000037693 75386000000000000000

noncomputable def ep590 := @Enclosure.Real.IsNear.mulLit_ff qz169 qz168 136908 4000 0 1 15920990604333267 4503599627370496 25000000037693 7538600000000000000

noncomputable def ep591 := @ep587 855675001290118311 7538600000000000000000 ep588 556790321932343059609 4503599627370496000 471587500648357293 3769300000000000000000 (@ep589 5931288258914165 2251799813685248 3500000000263851 301544000000000000000 (ep572 qz173) ep585 rfl) (@ep590 544927745414514729609 4503599627370496000 855675001290118311 7538600000000000000000 (ep584 qz173) ep582 rfl) rfl

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq qz163 qz172 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 (BSN.w_shift_mk qz150 Bool.false 68454 1000 2 qz151 rfl)

noncomputable abbrev qz398 := (ep592 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 136908 4000) Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 136908 4000)))

noncomputable abbrev qz174 := qz398

noncomputable def ep593 := ep567 (@ep568 3769300000000000000000 (ep586 rfl) (ep591 rfl)) qz174 rfl rfl rfl rfl rfl rfl

noncomputable def ep594 := @ep564 471587500648357293 3769300000000000000000 (ep593 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz75 (↑qz3) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep204 131072 1 262144 (ep206 rfl) (ep208 rfl) rfl rfl) (@ep209 1 0 1 (ep211 rfl) (ep213 rfl) rfl rfl))

noncomputable abbrev qz399 := (@HPow.hPow Complex Int Complex qz461 qz467 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz175 := qz399

noncomputable def ep595 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz175)) Bool.false 1368927 8589934592 3 8589934592

noncomputable def ep596 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz175) Bool.false 0 1 0 1 Bool.false

noncomputable def ep597 := @ep596 0 1 0 1 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000 Bool.false 1368927 1368927 8589934592 3 8589934592 Bool.true 5206029381 5206029381 2147483648000 11409

noncomputable def ep598 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz47 (@HMul.hMul Complex Complex Complex qz46 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz55 qz163 (@HSub.hSub Int Int Int qz57 qz58 (@HMul.hMul Int Int Int qz59 qz60 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep599 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78) qz175 Bool.false 1368927 8589934592 3 8589934592 Bool.true 5206029381 2147483648000 11409 2147483648000

noncomputable abbrev qz176 := (Complex.re qz399)

noncomputable abbrev qz177 := (Complex.im qz399)

noncomputable def ep600 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz176) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz177) 1368927 8589934592 3 8589934592 0 1 0

noncomputable def ep601 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz176 1 12 0 1 4106781 2147483648 9 2147483648 1368927

noncomputable def ep602 := @Enclosure.Complex.IsNear.re_isNear qz175 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227 536870912000

noncomputable abbrev qz400 := (@HPow.hPow Complex Nat Complex qz462 qz467 1)

noncomputable abbrev qz178 := (@Inv.inv Complex Complex.instInv qz400)

noncomputable def ep603 := @Enclosure.Complex.IsNear.of_eq qz175 qz178 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_parts qz178 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227

noncomputable abbrev qz179 := (Complex.re qz400)

noncomputable abbrev qz180 := qz400

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff qz179 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180)) 9000 4000 0 1 456309 536870912 1 536870912

noncomputable def ep606 := @Enclosure.Complex.IsNear.re_isNear qz180 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq qz180 qz163 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0

noncomputable def ep608 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180)) Bool.false 456309 536870912 1 536870912 456309 536870912 1

noncomputable abbrev qz181 := (Complex.im qz400)

noncomputable def ep609 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180) (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 qz179 qz179) (@HMul.hMul Real Real Real qz0 qz181 qz181)) Bool.false 1176550029 1000000 0 1

noncomputable def ep610 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz179 qz179) (@HMul.hMul Real Real Real qz0 qz181 qz181) 81 16 0 1 1171487529 1000000

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff qz179 qz179 9000 4000 0 1 9000 4000 0 1

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_ff qz181 qz181 136908 4000 0 1 136908 4000 0 1

noncomputable def ep613 := @Enclosure.Complex.IsNear.im_isNear qz180 Bool.false 9000 4000 0 1 Bool.false 136908 4000 0 1

noncomputable abbrev qz182 := (ep606 (@ep607 1 (BSN.pow_one_c qz388) qz398))

noncomputable abbrev qz183 := (ep613 (@ep607 1 (BSN.pow_one_c qz388) qz398))

noncomputable def ep614 := @ep610 0 1 18824800464 1176550029 1000000 0 1 (@ep611 81 16 0 1 qz182 qz182 rfl) (@ep612 1171487529 1000000 0 1 qz183 qz183 rfl)

noncomputable def ep615 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180) 1176550029 1000000 0 1 228154 228155 268435456 (ep609 (Enclosure.Complex.normSq_eq_mul_add_mul qz180) (ep614 rfl rfl)) rfl

noncomputable def ep616 := @Enclosure.Real.IsNear.of_eq (Complex.re qz178) (@HMul.hMul Real Real Real qz0 qz179 (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180))) Bool.false 4106781 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz180) (@ep605 4106781 2147483648 9 2147483648 qz182 (@ep608 536870912 (ep615 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep617 := @Enclosure.Real.IsNear.of_eq (Complex.im qz178) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz181) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180))) Bool.true 15618088143 536870912000 34227 536870912000 (Enclosure.Complex.inv_im_eq_mul qz180)

noncomputable def ep618 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz181) (@Inv.inv Real Real.instInv (@DFunLike.coe qz84 Complex (fun (x : Complex) => Real) qz85 Complex.normSq qz180)) 136908 4000 0 1 456309 536870912 1

noncomputable def ep619 := @ep618 536870912 15618088143 536870912000 34227 536870912000 (@Enclosure.Real.IsNear.neg qz181 Bool.false 136908 4000 0 1 qz183) (@ep608 536870912 (ep615 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep620 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz177 0 1 0 1 15618088143 536870912000 34227 536870912000 0

noncomputable def ep621 := @Enclosure.Complex.IsNear.im_isNear qz175 Bool.false 4106781 2147483648 9 2147483648 Bool.true 15618088143 536870912000 34227 536870912000

noncomputable abbrev qz184 := (@ep603 536870912000 (BSN.zpow_one_sub_two_mul qz388 1 1 rfl rfl) (@ep604 536870912000 ep616 (ep617 ep619)))

noncomputable def ep622 := @ep600 1 1368927 1368927 8589934592 3 8589934592 (@ep601 8589934592 3 8589934592 ep223 (ep602 qz184) rfl) (@ep620 1 0 1 ep243 (ep621 qz184) rfl) rfl

noncomputable def ep623 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz177) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz176) 5206029381 2147483648000 11409 2147483648000 0 1 0

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz177 1 12 0 1 15618088143 536870912000 34227 536870912000 5206029381

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 (@Rat.cast Complex Complex.instRatCast (bernoulli qz77)) qz78)) qz176 0 1 0 1 4106781 2147483648 9 2147483648 0

noncomputable def ep626 := @ep623 1 5206029381 5206029381 2147483648000 11409 2147483648000 (@ep624 2147483648000 11409 2147483648000 ep223 (ep621 qz184) rfl) (@ep625 1 0 1 ep243 (ep602 qz184) rfl) rfl

noncomputable def ep627 := @ep597 2147483648000 (@ep598 0 1 0 1 (BSN.stirling_sum_base qz163) qz91) (ep599 (ep622 rfl) (ep626 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep628 := @ep561 80526939930280934021 900719925474099200 61814541637404582811221 ep549 (ep594 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep595 Bool.true 5206029381 2147483648000 11409 2147483648000 (BSN.stirling_sum_succ qz163 0 1 rfl) (ep627 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz150 2) Bool.false 15912843051372755 2251799813685248 25000000037693 3769300000000000000 Bool.false 871949404767651 281474976710656

noncomputable abbrev qz185 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz389 qz332))

noncomputable def ep630 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 2) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz150 1) qz185) Bool.false 15912843051372755 2251799813685248 25000000037693 3769300000000000000 Bool.false 871949404767651 281474976710656 500000000037693 37693000000000000000

noncomputable def ep631 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz150 1) qz185 Bool.false 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000 Bool.false

noncomputable def ep632 := nat_lit 143330148073135051910247570472960

noncomputable def ep633 := nat_lit 981727753599379707983743156224

noncomputable abbrev qz186 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz268 qz389 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 1) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.logSumC qz150 0) qz186) Bool.false 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000

noncomputable def ep635 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz150 0) qz186 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz401 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz171))

noncomputable def ep636 := @Enclosure.Complex.IsNear.of_eq qz186 qz401 Bool.false 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000

noncomputable def ep637 := nat_lit 22842547683866237241398680883111369717514240

noncomputable def ep638 := nat_lit 34481844115873700844582703059963625340928

noncomputable def ep639 := nat_lit 93187654775584986757793589855639502848

noncomputable def ep640 := BSN.log_dyadic_bound 2360800464 35128800464 3 2 ep637 524288 150772 ep638 ep639 70575 37489600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2360800464) (BSN.artanhQ 35128800464) 0 2 ep638 ep637 ep639 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep641 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 18744800464 16000000)) 1 2 0 1 15911404237328595 2251799813685248 25000000037693 3769300000000000000 15911404237328595 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 18744800464 16000000 15911404237328595 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18744800464) qz327)) Bool.false 133474532876488550645760 18889465931478580854784 1000000001507720 150772000000000000000 15911404237328595 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 18744800464 16000000 10 37489600928 32768000000 70575 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep640 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep642 := BSN.arctan_dyadic_bound_f 1000 136908 1 0 524288 150772 0 1 1 0 1 1 3829 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz402 := (@Nat.cast Real Real.instNatCast 136908)

noncomputable def ep643 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz338 qz402)) 884279719003555 562949953421312 1 2000000000000000 3829 524288 1 150772 461461709945285640192 880168361559459 562949953421312 500000000037693 75386000000000000000 qz72 (ep642 rfl) rfl rfl

noncomputable abbrev qz187 := (@HAdd.hAdd Complex Complex Complex qz268 qz389 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz403 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz171)

noncomputable def ep644 := @ep635 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000 Bool.false 15911404237328595 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 880168361559459 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 0) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz150) qz91) (ep636 (@congrArg Complex Complex qz187 qz403 Complex.log (BSN.w_shift_mk qz150 Bool.false 68454 1000 0 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz401 Bool.false 15911404237328595 4503599627370496 25000000037693 7538600000000000000 Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz401) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 18744800464 16000000))) Bool.false 15911404237328595 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 1000 136908 4000 18744800464 16000000 rfl rfl rfl) (ep641 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz401) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz402 qz338)) Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 1000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz402 qz338)) (@HSub.hSub Real Real Real qz312 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz338 qz402))) Bool.false 880168361559459 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 136908 1000 rfl rfl) ep643)))) rfl rfl

noncomputable abbrev qz404 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz171))

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq qz185 qz404 Bool.false 15914281865416915 4503599627370496 25000000037693 7538600000000000000 Bool.false 863730447975843 562949953421312 500000000037693 75386000000000000000

noncomputable def ep646 := nat_lit 22905035808733370960551818510739545077514240

noncomputable def ep647 := nat_lit 35236404135321276264284155576323817340928

noncomputable def ep648 := nat_lit 97035231166096224280619723490711502848

noncomputable def ep649 := BSN.log_dyadic_bound 2384800464 35152800464 3 2 ep646 524288 150772 ep647 ep648 71245 37537600928 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2384800464) (BSN.artanhQ 35152800464) 0 2 ep647 ep646 ep648 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep650 := @Enclosure.Real.IsNear.mulLit_ff qz70 (Real.log (Enclosure.sfrac Bool.false 18768800464 16000000)) 1 2 0 1 15914281865416915 2251799813685248 25000000037693 3769300000000000000 15914281865416915 4503599627370496 25000000037693 7538600000000000000 qz326 (BSN.isNear_log_sfrac 18768800464 16000000 15914281865416915 2251799813685248 25000000037693 3769300000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 18768800464) qz327)) Bool.false 133498672170491256504320 18889465931478580854784 1000000001507720 150772000000000000000 15914281865416915 2251799813685248 25000000037693 3769300000000000000 (BSN.log_rat_reduce_isNear 18768800464 16000000 10 37537600928 32768000000 71245 524288 24973259072661432 36028797018963968 150772 1000000000000000 rfl rfl rfl rfl (ep649 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep651 := BSN.arctan_dyadic_bound_f 5000 136908 1 0 524288 150772 0 1 1 0 1 1 19138 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 136908) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 136908) 0 0 rfl) rfl rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.subLit_ff_p qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz402)) 884279719003555 562949953421312 1 2000000000000000 19138 524288 1 150772 452843509108358774784 863730447975843 562949953421312 500000000037693 75386000000000000000 qz72 (ep651 rfl) rfl rfl

noncomputable abbrev qz188 := (@HAdd.hAdd Complex Complex Complex qz268 qz389 qz332)

noncomputable abbrev qz405 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz171)

noncomputable def ep653 := @ep631 15914281865416915 4503599627370496 25000000037693 7538600000000000000 Bool.false 863730447975843 562949953421312 500000000037693 75386000000000000000 Bool.false ep632 15912843051372755 2251799813685248 25000000037693 3769300000000000000 Bool.false ep633 871949404767651 281474976710656 500000000037693 37693000000000000000 (ep634 (BSN.log_sum_c_succ qz150 0 1 rfl) (ep644 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep645 (@congrArg Complex Complex qz188 qz405 Complex.log (BSN.w_shift_mk qz150 Bool.false 68454 1000 1 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz404 Bool.false 15914281865416915 4503599627370496 25000000037693 7538600000000000000 Bool.false 863730447975843 562949953421312 500000000037693 75386000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz404) (@HMul.hMul Real Real Real qz0 qz70 (Real.log (Enclosure.sfrac Bool.false 18768800464 16000000))) Bool.false 15914281865416915 4503599627370496 25000000037693 7538600000000000000 (Enclosure.clog_re_eq 5000 136908 4000 18768800464 16000000 rfl rfl rfl) (ep650 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz404) (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz402 qz342)) Bool.false 863730447975843 562949953421312 500000000037693 75386000000000000000 (Enclosure.clog_im_eq 5000 136908 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz402 qz342)) (@HSub.hSub Real Real Real qz312 qz71 (Real.arctan (@HDiv.hDiv Real Real Real qz2 qz342 qz402))) Bool.false 863730447975843 562949953421312 500000000037693 75386000000000000000 (BSN.arctan_recip 136908 5000 rfl rfl) ep652)))) rfl rfl

noncomputable def ep654 := @ep554 ep549 Bool.false 15912843051372755 2251799813685248 25000000037693 3769300000000000000 Bool.false 871949404767651 281474976710656 500000000037693 37693000000000000000 Bool.true ep555 24196946743079943727 450359962737049600 300459640406447977216799 ep165 Bool.false ep556 77736701835024450821 900719925474099200 68368141637898632500821 ep549 (@ep557 450359962737049600 292267640394096734976799 ep165 Bool.false 80526939930280934021 900719925474099200 61814541637404582811221 ep549 (BSN.logGammaStirling_unfold 1 qz163) (ep628 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep629 500000000037693 37693000000000000000 (BSN.log_sum_c_eq qz150 2) (ep630 (BSN.log_sum_c_succ qz150 1 2 rfl) (ep653 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz189 := (@HDiv.hDiv Real Real Real qz265 qz377 (2 : Real))

noncomputable def ep655 := @Enclosure.Real.IsNear.mulLit_ff qz189 (Real.log Real.pi) 68454 2000 0 1 75021 65536 1 131072 2567743767 65536000 34227 131072000 (@Enclosure.Real.IsNear.of_eq qz189 (Enclosure.sfrac Bool.false 68454 2000) Bool.false 68454 2000 0 1 (BSN.t_half_eq qz150 Bool.false 68454 1000 qz151) (Enclosure.Real.IsNear.const Bool.false 68454 2000)) EMRow16.d5 rfl

noncomputable def ep656 := @ep551 34227 131072000 ep552 212229501114756749593 4503599627370496000 197379972737898632500821 ep549 (@ep553 68368141637898632500821 ep549 (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep655 rfl rfl

noncomputable def ep657 := BSN.cos_dyadic_bound_f 563328 1073741824 1 0 524288 150920 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 563328) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 563328) qz282 0 0 rfl) rfl rfl

noncomputable def ep658 := @ep548 524288 Bool.true 524287 524288 1 75386 (@ep550 24706765 524288 211 524288 ep656 rfl) (Enclosure.sfrac_false_div 24706765 524288) (BSN.cos_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39640686905922682880) qz23) 226375608064910080 72057594037927936 Bool.false 524287 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 24706765 524288 226375608064910080 72057594037927936 7 39640686905922682880 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 39640686905922682880 75557863725914323419136 563328 1073741824 150920 150772 (ep657 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep659 := nat_lit 4508465077923835019264000

noncomputable def ep660 := nat_lit 149742626082223245713932999

noncomputable def ep661 := nat_lit 31863295159159333758959616000

noncomputable abbrev qz190 := qz376

noncomputable abbrev qz406 := (@HPow.hPow Complex Complex Complex qz450 qz463 qz465)

noncomputable abbrev qz191 := qz406

noncomputable abbrev qz192 := (@HAdd.hAdd Complex Complex Complex qz268 (@HDiv.hDiv Complex Complex Complex qz317 qz345 (@HSub.hSub Complex Complex Complex qz309 qz375 (1 : Complex))) qz316)

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz141 1 14) (@HAdd.hAdd Complex Complex Complex qz5 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz190) (@HMul.hMul Complex Complex Complex qz46 qz191 (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) Bool.false ep543 ep544 ep545

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz190) (@HMul.hMul Complex Complex Complex qz46 qz191 (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) Bool.false 462909655069 274877906944 46993610396013 10360972946440192

noncomputable def ep664 := nat_lit 88801789844097060460013771

noncomputable def ep665 := nat_lit 2784015786977200480423937

noncomputable def ep666 := nat_lit 15931647579579666879479808000

noncomputable def ep667 := nat_lit 1010911868298577315877339946582802432

noncomputable def ep668 := nat_lit 37687264410346893533882350710030336

noncomputable def ep669 := @ep663 Bool.true 45379262079 274877906944 46881186198809 10360972946440192 Bool.true 118576786035555494284347 ep544 ep664 ep546 Bool.false 607191592043010943620381 ep659 ep665 ep666 Bool.false ep667 ep543 ep544 ep545 ep546 Bool.true ep668 137105469222103760453619 ep659

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 14, @HPow.hPow Complex Complex Complex qz97 (@Nat.cast Complex Complex.instNatCast n) qz190) (BSN.headSumC qz141 14) Bool.false 462909655069 274877906944 46993610396013 10360972946440192 Bool.true 45379262079 274877906944 46881186198809

noncomputable abbrev qz193 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 13) qz376)

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 14) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 13) qz193) Bool.false 462909655069 274877906944 46993610396013 10360972946440192 Bool.true 45379262079 274877906944 46881186198809 10360972946440192

noncomputable def ep672 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 13) qz193 Bool.false 195626356895 137438953472 5540309111597 1295121618305024 Bool.true 17433091 67108864 22110938417179 5180486473220096 Bool.false

noncomputable abbrev qz194 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 12) qz376)

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 13) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 12) qz194) Bool.false 195626356895 137438953472 5540309111597 1295121618305024 Bool.true 17433091 67108864 22110938417179 5180486473220096

noncomputable def ep674 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 12) qz194 Bool.false 80000233567 68719476736 2596490362867 647560809152512 Bool.true 9120615421 68719476736 10363074299561 2590243236610048 Bool.false

noncomputable abbrev qz195 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 11) qz376)

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 12) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 11) qz195) Bool.false 80000233567 68719476736 2596490362867 647560809152512 Bool.true 9120615421 68719476736 10363074299561 2590243236610048

noncomputable def ep676 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 11) qz195 Bool.false 261227952463 274877906944 38646183010537 10360972946440192 Bool.false 5488097285 68719476736 9638678757059 2590243236610048 Bool.false

noncomputable abbrev qz196 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 10) qz376)

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 11) (@HAdd.hAdd Complex Complex Complex qz5 (BSN.headSumC qz141 10) qz196) Bool.false 261227952463 274877906944 38646183010537 10360972946440192 Bool.false 5488097285 68719476736 9638678757059 2590243236610048

noncomputable def ep678 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 10) qz196 Bool.false 186731948293 274877906944 35598595494811 10360972946440192 Bool.false 66742405775 274877906944 35513881080399 10360972946440192 Bool.false

noncomputable abbrev qz197 := (@HPow.hPow Complex Complex Complex qz269 (@Nat.cast Complex Complex.instNatCast 9) qz376)

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 10) (@HAdd.hAdd Complex Complex Complex qz5 qz140 qz197) Bool.false 186731948293 274877906944 35598595494811 10360972946440192 Bool.false 66742405775 274877906944 35513881080399 10360972946440192

noncomputable def ep680 := @Enclosure.Complex.IsNear.addLitP qz140 qz197 Bool.false 101905133827 274877906944 32392306658465 10360972946440192 Bool.false 32105078227 274877906944 32318417145951 10360972946440192 Bool.false

noncomputable abbrev qz198 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 9 1)))

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq qz197 (Complex.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz198)))) Bool.false 42413407233 137438953472 1603144418173 5180486473220096 Bool.false 8659331887 68719476736 199716495903 647560809152512 (BSN.cpow_neg_s_mk qz150 68454 1000 9 qz151 rfl)

noncomputable def ep682 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz111 68454 1000 0 1 9895417793173221 4503599627370496 500000000113079 37693000000000000000 338690464806939835167 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 20752195215788806766592 9444732965739290427392 1000000000226158 75386000000000000000 9895417793173221 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep683 := nat_lit 10475846656265150457961378063945101166767757653986105940728275756676437991680

noncomputable def ep684 := nat_lit 6783488724374940314700604420440972936606066115663053925832575829097799936

noncomputable def ep685 := nat_lit 27425758451331167962722665379365979575827717367681108709836993287572131635456

noncomputable def ep686 := BSN.sin_dyadic_bound_f 1270374122 1073741824 3 2 524288 150920 ep683 ep463 ep684 ep685 ep466 ep684 485382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1270374122) qz277 0 2 ep683 ep463 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1270374122) qz278 0 2 ep685 ep466 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39428759) qz28)

noncomputable def ep687 := @Enclosure.Real.IsNear.cos_image qz198 qz407 Bool.false 39428759 262144 477 524288 Bool.false 485382 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 338690464806939835167 2251799813685248000 17113500003870354933 18846500000000000000000 39428759 262144 477 524288 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 39428759 262144) (BSN.cos_reduce3 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44697315828655034728448) qz30) 226375608064910080 72057594037927936 Bool.false 485382 524288 23 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 39428759 262144 226375608064910080 72057594037927936 23 44697315828655034728448 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 485382 524288 44697315828655034728448 37778931862957161709568 1270374122 1073741824 150920 150772 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := nat_lit 5822929692913694672340632526378585525065023614932575768816078787410953462016

noncomputable def ep689 := nat_lit 17455222101292334136392496370294874629321858712566401198596571210574664786176

noncomputable def ep690 := BSN.cos_dyadic_bound_f 1270374122 1073741824 3 2 524288 150920 ep688 ep119 ep684 ep689 ep122 ep684 198196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1270374122) qz281 0 2 ep688 ep119 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1270374122) qz282 0 2 ep689 ep122 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable def ep691 := @Enclosure.Real.IsNear.sin_image qz198 qz407 Bool.false 39428759 262144 477 524288 Bool.true 198196 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz198 Bool.false 338690464806939835167 2251799813685248000 17113500003870354933 18846500000000000000000 39428759 262144 477 524288 (ep682 rfl) rfl) (Enclosure.sfrac_false_div 39428759 262144) (BSN.sin_reduce3 qz407 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44697315828655034728448) qz30) 226375608064910080 72057594037927936 Bool.false 198196 524288 23 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 39428759 262144 226375608064910080 72057594037927936 23 44697315828655034728448 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 198196 524288 44697315828655034728448 37778931862957161709568 1270374122 1073741824 150920 150772 (ep690 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep692 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz109 (Real.cos qz198)) (@HMul.hMul Real Real Real qz0 qz109 (@Neg.neg Real Real.instNeg (Real.sin qz198))) Bool.false 42413407233 137438953472 1603144418173 5180486473220096 Bool.false 8659331887 68719476736 199716495903 647560809152512 (@Enclosure.Real.IsNear.mulLit_ff qz109 (Real.cos qz198) 174763 524288 1 524288 242691 262144 18241705 19761987584 42413407233 137438953472 1603144418173 5180486473220096 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz198) Bool.false 485382 524288 36483410 39523975168 242691 262144 18241705 19761987584 (ep687 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz109 (@Neg.neg Real Real.instNeg (Real.sin qz198)) 174763 524288 1 524288 49549 131072 18241705 19761987584 8659331887 68719476736 199716495903 647560809152512 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz198) Bool.true 49549 131072 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz198) Bool.true 198196 524288 36483410 39523975168 49549 131072 18241705 19761987584 (ep691 rfl rfl) rfl)) rfl)

noncomputable def ep693 := @ep680 42413407233 137438953472 1603144418173 5180486473220096 Bool.false 8659331887 68719476736 199716495903 647560809152512 Bool.false 25664243553177536823296 186731948293 274877906944 35598595494811 10360972946440192 Bool.false 4586503200959784550400 66742405775 274877906944 35513881080399 10360972946440192 EMRow16.d10 (ep681 ep692) rfl rfl

noncomputable abbrev qz199 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep694 := @Enclosure.Complex.IsNear.of_eq qz196 (Complex.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz199)))) Bool.false 37248002085 137438953472 1523793757863 5180486473220096 Bool.true 44790016635 274877906944 3040833947837 10360972946440192 (BSN.cpow_neg_s_mk qz150 68454 1000 10 qz151 rfl)

noncomputable def ep695 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz114 68454 1000 0 1 10369908600166117 4503599627370496 500000000113079 37693000000000000000 354930861657885686559 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 21747274560655572598784 9444732965739290427392 1000000000226158 75386000000000000000 10369908600166117 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep309 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep696 := nat_lit 114143782755876677855704256337900721

noncomputable def ep697 := BSN.cos_dyadic_bound_f 581250133 1073741824 2 1 524288 150920 ep696 ep77 ep696 ep696 ep78 ep696 449326 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 581250133) qz281 0 1 ep696 ep77 ep696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 581250133) qz282 0 1 ep696 ep78 ep696 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 20659695) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep698 := @Enclosure.Real.IsNear.cos_image qz199 qz408 Bool.false 20659695 131072 239 262144 Bool.false 449326 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 354930861657885686559 2251799813685248000 17113500003870354933 18846500000000000000000 20659695 131072 239 262144 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 20659695 131072) (BSN.cos_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10225460486429778903040) qz354) 226375608064910080 72057594037927936 Bool.false 449326 524288 25 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 20659695 131072 226375608064910080 72057594037927936 25 10225460486429778903040 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 449326 524288 10225460486429778903040 18889465931478580854784 581250133 1073741824 150920 150772 (ep697 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep699 := BSN.sin_dyadic_bound_f 581250133 1073741824 2 1 524288 150920 ep696 ep92 ep696 ep696 ep93 ep696 270153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 581250133) qz277 0 1 ep696 ep92 ep696 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 581250133) qz278 0 1 ep696 ep93 ep696 rfl rfl rfl rfl) rfl rfl

noncomputable def ep700 := @Enclosure.Real.IsNear.sin_image qz199 qz408 Bool.false 20659695 131072 239 262144 Bool.false 270153 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz199 Bool.false 354930861657885686559 2251799813685248000 17113500003870354933 18846500000000000000000 20659695 131072 239 262144 (ep695 rfl) rfl) (Enclosure.sfrac_false_div 20659695 131072) (BSN.sin_reduce0 qz408 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 10225460486429778903040) qz354) 226375608064910080 72057594037927936 Bool.false 270153 524288 25 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 20659695 131072 226375608064910080 72057594037927936 25 10225460486429778903040 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 270153 524288 10225460486429778903040 18889465931478580854784 581250133 1073741824 150920 150772 (ep699 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep701 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz112 (Real.cos qz199)) (@HMul.hMul Real Real Real qz0 qz112 (@Neg.neg Real Real.instNeg (Real.sin qz199))) Bool.false 37248002085 137438953472 1523793757863 5180486473220096 Bool.true 44790016635 274877906944 3040833947837 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz112 (Real.cos qz199) 165795 524288 1 524288 224663 262144 9139699 9880993792 37248002085 137438953472 1523793757863 5180486473220096 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz199) Bool.false 449326 524288 18279398 19761987584 224663 262144 9139699 9880993792 (ep698 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz112 (@Neg.neg Real Real.instNeg (Real.sin qz199)) 165795 524288 1 524288 270153 524288 9139699 9880993792 44790016635 274877906944 3040833947837 10360972946440192 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz199) Bool.false 270153 524288 9139699 9880993792 (@Enclosure.Real.IsNear.recentre' (Real.sin qz199) Bool.false 270153 524288 18279398 19761987584 270153 524288 9139699 9880993792 (ep700 rfl rfl) rfl)) rfl)

noncomputable def ep702 := @ep678 37248002085 137438953472 1523793757863 5180486473220096 Bool.true 44790016635 274877906944 3040833947837 10360972946440192 Bool.false 35902896404148084801536 261227952463 274877906944 38646183010537 10360972946440192 Bool.false 6034226779223396188160 5488097285 68719476736 9638678757059 2590243236610048 (ep679 (BSN.head_sum_c_succ qz141 9 10 rfl rfl) (ep693 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep694 ep701) rfl rfl

noncomputable abbrev qz200 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq qz195 (Complex.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz200)))) Bool.false 58772981805 274877906944 2897662795335 10360972946440192 Bool.true 7304356353 34359738368 362197771251 1295121618305024 (BSN.cpow_neg_s_mk qz150 68454 1000 11 qz151 rfl)

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz117 68454 1000 0 1 10799147631728357 4503599627370496 500000000113079 37693000000000000000 369622425991166475039 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 22647454054174387339264 9444732965739290427392 1000000000226158 75386000000000000000 10799147631728357 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep705 := nat_lit 1113192221498555128399428626603952816977270405710456099088958255533058921601

noncomputable def ep706 := nat_lit 248387063385514771391998165107373994464659409902959701208379974696277121

noncomputable def ep707 := nat_lit 3339079890368894355655501883481643702942881898311562377864458006649784210561

noncomputable def ep708 := BSN.cos_dyadic_bound_f 840216337 1073741824 3 2 524288 150920 ep705 ep119 ep706 ep707 ep122 ep706 371795 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 840216337) qz281 0 2 ep705 ep119 ep706 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 840216337) qz282 0 2 ep707 ep122 ep706 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz409 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 86059427) qz20)

noncomputable def ep709 := @Enclosure.Real.IsNear.cos_image qz200 qz409 Bool.false 86059427 524288 477 524288 Bool.false 371795 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 369622425991166475039 2251799813685248000 17113500003870354933 18846500000000000000000 86059427 524288 477 524288 (ep704 rfl) rfl) (Enclosure.sfrac_false_div 86059427 524288) (BSN.cos_reduce0 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59124968487288972509184) qz23) 226375608064910080 72057594037927936 Bool.false 371795 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 86059427 524288 226375608064910080 72057594037927936 26 59124968487288972509184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 371795 524288 59124968487288972509184 75557863725914323419136 840216337 1073741824 150920 150772 (ep708 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep710 := nat_lit 498384453394680813043164110220509761

noncomputable def ep711 := BSN.sin_dyadic_bound_f 840216337 1073741824 2 1 524288 150920 ep710 ep92 ep710 ep710 ep93 ep710 369656 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 840216337) qz277 0 1 ep710 ep92 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 840216337) qz278 0 1 ep710 ep93 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.sin_image qz200 qz409 Bool.false 86059427 524288 477 524288 Bool.false 369656 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz200 Bool.false 369622425991166475039 2251799813685248000 17113500003870354933 18846500000000000000000 86059427 524288 477 524288 (ep704 rfl) rfl) (Enclosure.sfrac_false_div 86059427 524288) (BSN.sin_reduce0 qz409 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 59124968487288972509184) qz23) 226375608064910080 72057594037927936 Bool.false 369656 524288 26 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 86059427 524288 226375608064910080 72057594037927936 26 59124968487288972509184 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 369656 524288 59124968487288972509184 75557863725914323419136 840216337 1073741824 150920 150772 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz115 (Real.cos qz200)) (@HMul.hMul Real Real Real qz0 qz115 (@Neg.neg Real Real.instNeg (Real.sin qz200))) Bool.false 58772981805 274877906944 2897662795335 10360972946440192 Bool.true 7304356353 34359738368 362197771251 1295121618305024 (@Enclosure.Real.IsNear.mulLit_ff qz115 (Real.cos qz200) 158079 524288 1 524288 371795 524288 18241705 19761987584 58772981805 274877906944 2897662795335 10360972946440192 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz200) Bool.false 371795 524288 36483410 39523975168 371795 524288 18241705 19761987584 (ep709 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz115 (@Neg.neg Real Real.instNeg (Real.sin qz200)) 158079 524288 1 524288 46207 65536 18241705 19761987584 7304356353 34359738368 362197771251 1295121618305024 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz200) Bool.false 46207 65536 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz200) Bool.false 369656 524288 36483410 39523975168 46207 65536 18241705 19761987584 (ep712 rfl rfl) rfl)) rfl)

noncomputable def ep714 := @ep676 58772981805 274877906944 2897662795335 10360972946440192 Bool.true 7304356353 34359738368 362197771251 1295121618305024 Bool.false 87961187031712364756992 80000233567 68719476736 2596490362867 647560809152512 Bool.true 313381959620706172928 9120615421 68719476736 10363074299561 2590243236610048 (ep677 (BSN.head_sum_c_succ qz141 10 11 rfl rfl) (ep702 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep703 ep713) rfl rfl

noncomputable abbrev qz201 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz194 (Complex.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz201)))) Bool.false 35625889761 137438953472 347328385863 1295121618305024 Bool.true 8730869763 68719476736 1384789818057 5180486473220096 (BSN.cpow_neg_s_mk qz150 68454 1000 12 qz151 rfl)

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz120 68454 1000 0 1 11191020447815397 4503599627370496 500000000113079 37693000000000000000 383035056867377593119 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 23469270914176955449344 9444732965739290427392 1000000000226158 75386000000000000000 11191020447815397 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep334 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := nat_lit 57336774381203582776221083968573696

noncomputable def ep718 := BSN.cos_dyadic_bound_f 489337292 1073741824 2 1 524288 150920 ep717 ep77 ep717 ep717 ep78 ep717 470778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 489337292) qz281 0 1 ep717 ep77 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 489337292) qz282 0 1 ep717 ep78 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 44591149) qz28)

noncomputable def ep719 := @Enclosure.Real.IsNear.cos_image qz201 qz410 Bool.false 44591149 262144 477 524288 Bool.false 470778 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 383035056867377593119 2251799813685248000 17113500003870354933 18846500000000000000000 44591149 262144 477 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 44591149 262144) (BSN.cos_reduce0 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17217025392191385632768) qz30) 226375608064910080 72057594037927936 Bool.false 470778 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 44591149 262144 226375608064910080 72057594037927936 27 17217025392191385632768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 470778 524288 17217025392191385632768 37778931862957161709568 489337292 1073741824 150920 150772 (ep718 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep720 := BSN.sin_dyadic_bound_f 489337292 1073741824 2 1 524288 150920 ep717 ep92 ep717 ep717 ep93 ep717 230748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 489337292) qz277 0 1 ep717 ep92 ep717 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 489337292) qz278 0 1 ep717 ep93 ep717 rfl rfl rfl rfl) rfl rfl

noncomputable def ep721 := @Enclosure.Real.IsNear.sin_image qz201 qz410 Bool.false 44591149 262144 477 524288 Bool.false 230748 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz201 Bool.false 383035056867377593119 2251799813685248000 17113500003870354933 18846500000000000000000 44591149 262144 477 524288 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 44591149 262144) (BSN.sin_reduce0 qz410 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 17217025392191385632768) qz30) 226375608064910080 72057594037927936 Bool.false 230748 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q0 44591149 262144 226375608064910080 72057594037927936 27 17217025392191385632768 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230748 524288 17217025392191385632768 37778931862957161709568 489337292 1073741824 150920 150772 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz118 (Real.cos qz201)) (@HMul.hMul Real Real Real qz0 qz118 (@Neg.neg Real Real.instNeg (Real.sin qz201))) Bool.false 35625889761 137438953472 347328385863 1295121618305024 Bool.true 8730869763 68719476736 1384789818057 5180486473220096 (@Enclosure.Real.IsNear.mulLit_ff qz118 (Real.cos qz201) 151349 524288 1 524288 235389 262144 18241705 19761987584 35625889761 137438953472 347328385863 1295121618305024 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz201) Bool.false 470778 524288 36483410 39523975168 235389 262144 18241705 19761987584 (ep719 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz118 (@Neg.neg Real Real.instNeg (Real.sin qz201)) 151349 524288 1 524288 57687 131072 18241705 19761987584 8730869763 68719476736 1384789818057 5180486473220096 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz201) Bool.false 57687 131072 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz201) Bool.false 230748 524288 36483410 39523975168 57687 131072 18241705 19761987584 (ep721 rfl rfl) rfl)) rfl)

noncomputable def ep723 := @ep674 35625889761 137438953472 347328385863 1295121618305024 Bool.true 8730869763 68719476736 1384789818057 5180486473220096 Bool.false 13443340881594385694720 195626356895 137438953472 5540309111597 1295121618305024 Bool.true 1226744720804936679424 17433091 67108864 22110938417179 5180486473220096 (ep675 (BSN.head_sum_c_succ qz141 11 12 rfl rfl) (ep714 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep715 ep722) rfl rfl

noncomputable abbrev qz202 := (@HMul.hMul Real Real Real qz262 qz377 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq qz193 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz202)))) Bool.false 71656941279 274877906944 2671137503237 10360972946440192 Bool.false 26026678657 274877906944 2659309364451 10360972946440192 (BSN.cpow_neg_s_mk qz150 68454 1000 13 qz151 rfl)

noncomputable def ep725 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz123 68454 1000 0 1 11551488463034085 4503599627370496 500000000113079 37693000000000000000 79074559124853525459 450359962737049600 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 24225227133228857425920 9444732965739290427392 1000000000226158 75386000000000000000 11551488463034085 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep345 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep726 := nat_lit 11938603285952716857605734485999399085292347816524233502719991911003623730625

noncomputable def ep727 := nat_lit 8808529456771278675135443139940174590805898107496589493288491173187890625

noncomputable def ep728 := nat_lit 31253509082184247794921942460152808750237701398722759933658464114538615090625

noncomputable def ep729 := BSN.sin_dyadic_bound_f 1312541145 1073741824 3 2 524288 150920 ep726 ep463 ep727 ep728 ep466 ep727 492789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1312541145) qz277 0 2 ep726 ep463 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1312541145) qz278 0 2 ep728 ep466 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46027451) qz28)

noncomputable def ep730 := @Enclosure.Real.IsNear.cos_image qz202 qz411 Bool.false 46027451 262144 477 524288 Bool.false 492789 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 79074559124853525459 450359962737049600 17113500003870354933 18846500000000000000000 46027451 262144 477 524288 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 46027451 262144) (BSN.cos_reduce3 qz411 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46180936054215962263552) qz30) 226375608064910080 72057594037927936 Bool.false 492789 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 46027451 262144 226375608064910080 72057594037927936 27 46180936054215962263552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 492789 524288 46180936054215962263552 37778931862957161709568 1312541145 1073741824 150920 150772 (ep729 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep731 := nat_lit 6636472283065629933636579355839639569424995852783461541285901502190096690625

noncomputable def ep732 := nat_lit 19891799790283347243559467181239038359093375762135391444871127524223914290625

noncomputable def ep733 := BSN.cos_dyadic_bound_f 1312541145 1073741824 3 2 524288 150920 ep731 ep119 ep727 ep732 ep122 ep727 178987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1312541145) qz281 0 2 ep731 ep119 ep727 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1312541145) qz282 0 2 ep732 ep122 ep727 rfl rfl rfl rfl) rfl rfl

noncomputable def ep734 := @Enclosure.Real.IsNear.sin_image qz202 qz411 Bool.false 46027451 262144 477 524288 Bool.true 178987 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz202 Bool.false 79074559124853525459 450359962737049600 17113500003870354933 18846500000000000000000 46027451 262144 477 524288 (ep725 rfl) rfl) (Enclosure.sfrac_false_div 46027451 262144) (BSN.sin_reduce3 qz411 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 46180936054215962263552) qz30) 226375608064910080 72057594037927936 Bool.false 178987 524288 27 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 46027451 262144 226375608064910080 72057594037927936 27 46180936054215962263552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 178987 524288 46180936054215962263552 37778931862957161709568 1312541145 1073741824 150920 150772 (ep733 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep735 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz202)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz202))) Bool.false 71656941279 274877906944 2671137503237 10360972946440192 Bool.false 26026678657 274877906944 2659309364451 10360972946440192 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz202) 145411 524288 1 524288 492789 524288 18241705 19761987584 71656941279 274877906944 2671137503237 10360972946440192 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz202) Bool.false 492789 524288 36483410 39523975168 492789 524288 18241705 19761987584 (ep730 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz121 (@Neg.neg Real Real.instNeg (Real.sin qz202)) 145411 524288 1 524288 178987 524288 18241705 19761987584 26026678657 274877906944 2659309364451 10360972946440192 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz202) Bool.true 178987 524288 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' (Real.sin qz202) Bool.true 178987 524288 36483410 39523975168 178987 524288 18241705 19761987584 (ep734 rfl rfl) rfl)) rfl)

noncomputable def ep736 := @ep672 71656941279 274877906944 2671137503237 10360972946440192 Bool.false 26026678657 274877906944 2659309364451 10360972946440192 Bool.false 63621818544767859949568 462909655069 274877906944 46993610396013 10360972946440192 Bool.true 3045350727279968256 45379262079 274877906944 46881186198809 10360972946440192 (ep673 (BSN.head_sum_c_succ qz141 12 13 rfl rfl) (ep723 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep724 ep735) rfl rfl

noncomputable def ep737 := @Enclosure.Complex.IsNear.mul qz191 (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.true 118576786035555494284347 ep544 ep664 ep546 Bool.false

noncomputable abbrev qz203 := (Complex.re qz406)

noncomputable abbrev qz204 := (Complex.im qz406)

noncomputable def ep738 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz203 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz204 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 29513689015516783407 18033860311695340077056 126156203839505775704749

noncomputable def ep739 := nat_lit 1019625445093098680286707712

noncomputable def ep740 := nat_lit 8574562641448057535879757

noncomputable def ep741 := nat_lit 169937574182183113381117952000

noncomputable def ep742 := nat_lit 1069198597787497227375744347001679505277321216

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff qz203 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 448527321 137438953472 639076374649 2590243236610048 197403954901

noncomputable abbrev qz412 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz466 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable abbrev qz205 := (Real.cos qz412)

noncomputable abbrev qz206 := (@Neg.neg Real Real.instNeg (Real.sin qz412))

noncomputable def ep744 := @Enclosure.Complex.IsNear.of_eq qz191 (Complex.mk (@HMul.hMul Real Real Real qz0 qz126 qz205) (@HMul.hMul Real Real Real qz0 qz126 qz206)) Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (BSN.cpow_neg_s_mk qz150 68454 1000 14 qz151 rfl)

noncomputable def ep745 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz130 68454 1000 0 1 11885241781671653 4503599627370496 500000000113079 37693000000000000000 406796170461275667231 2251799813685248000 17113500003870354933 18846500000000000000000 qz152 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 500000000113079 37693000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz129) Bool.false 24925158572916270432256 9444732965739290427392 1000000000226158 75386000000000000000 11885241781671653 4503599627370496 500000000113079 37693000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 75386 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep746 := BSN.sin_dyadic_bound_f 13112469 1073741824 1 0 524288 150920 0 1 1 0 1 1 6402 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 13112469) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 13112469) qz278 0 0 rfl) rfl rfl

noncomputable abbrev qz207 := qz412

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 47357307) qz28)

noncomputable def ep747 := @Enclosure.Real.IsNear.cos_image qz207 qz413 Bool.false 47357307 262144 477 524288 Bool.false 6402 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 406796170461275667231 2251799813685248000 17113500003870354933 18846500000000000000000 47357307 262144 477 524288 (ep745 rfl) rfl) (Enclosure.sfrac_false_div 47357307 262144) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 461354005750196731904) qz30) 226375608064910080 72057594037927936 Bool.false 6402 524288 28 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 47357307 262144 226375608064910080 72057594037927936 28 461354005750196731904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 6402 524288 461354005750196731904 37778931862957161709568 13112469 1073741824 150920 150772 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep748 := BSN.cos_dyadic_bound_f 13112469 1073741824 1 0 524288 150920 0 1 1 0 1 1 524248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 13112469) qz281 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 13112469) qz282 0 0 rfl) rfl rfl

noncomputable def ep749 := @Enclosure.Real.IsNear.sin_image qz207 qz413 Bool.false 47357307 262144 477 524288 Bool.true 524248 524288 1 75386 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 406796170461275667231 2251799813685248000 17113500003870354933 18846500000000000000000 47357307 262144 477 524288 (ep745 rfl) rfl) (Enclosure.sfrac_false_div 47357307 262144) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 461354005750196731904) qz30) 226375608064910080 72057594037927936 Bool.false 524248 524288 28 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q3 47357307 262144 226375608064910080 72057594037927936 28 461354005750196731904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524248 524288 461354005750196731904 37778931862957161709568 13112469 1073741824 150920 150772 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz208 := (Real.sin qz412)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz126 qz205) (@HMul.hMul Real Real Real qz0 qz126 qz206) Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (@Enclosure.Real.IsNear.mulLit_ff qz126 qz205 140121 524288 1 524288 3201 262144 18241705 19761987584 448527321 137438953472 639076374649 2590243236610048 qz372 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 6402 524288 36483410 39523975168 3201 262144 18241705 19761987584 (ep747 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz126 qz206 140121 524288 1 524288 65531 65536 18241705 19761987584 9182269251 34359738368 1287912333937 5180486473220096 qz372 (@Enclosure.Real.IsNear.neg qz208 Bool.true 65531 65536 18241705 19761987584 (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 524248 524288 36483410 39523975168 65531 65536 18241705 19761987584 (ep749 rfl rfl) rfl)) rfl)

noncomputable def ep751 := @ep743 393640809744 0 1 29513689015516783407 18033860311695340077056 126156203839505775704749 ep739 (@Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (ep744 ep750))

noncomputable def ep752 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 197403954901 393640809744 0 1 Bool.false

noncomputable def ep753 := @Enclosure.Complex.IsNear.addLitP qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) Bool.false 1168050029 2343100058 0 1 Bool.true 239589000

noncomputable def ep754 := @ep753 1171550029 0 1 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1 Bool.false 394807909802 197403954901 393640809744 0 1 Bool.false 6657722280861 6657722280861 32803400812000 0 1

noncomputable abbrev qz209 := (@HDiv.hDiv Complex Complex Complex qz317 qz345 (@HSub.hSub Complex Complex Complex qz309 qz375 (1 : Complex)))

noncomputable def ep755 := @Enclosure.Complex.IsNear.addLitP qz209 qz75 Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1

noncomputable def ep756 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (Enclosure.sfrac Bool.true 28000000 18744800464) (Enclosure.sfrac Bool.true 3833424000 18744800464)) Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1

noncomputable def ep757 := @ep755 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 18688800464 1168050029 2343100058 0 1 Bool.true 3833424000 239589000 1171550029 0 1 (ep756 (BSN.N_div_s_sub_one_mk qz150 68454 1000 14 qz151 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 28000000 18744800464) (Enclosure.sfrac Bool.true 3833424000 18744800464) Bool.true 28000000 18744800464 0 1 Bool.true 3833424000 18744800464 0 1 (Enclosure.Real.IsNear.const Bool.true 28000000 18744800464) (Enclosure.Real.IsNear.const Bool.true 3833424000 18744800464))) qz76 rfl

noncomputable def ep758 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz5 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135)) Bool.false 1 336 0 1

noncomputable def ep759 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135) Bool.false 0 1 0 1 Bool.false

noncomputable def ep760 := @ep759 0 1 0 1 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1 Bool.false 1 1 336 0 1 Bool.false 11409 11409 28000 0

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (Complex.mk qz14 qz14) Bool.false 0 1 0 1 Bool.false

noncomputable def ep762 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135 Bool.false 1 336 0 1 Bool.false 11409 28000 0 1

noncomputable def ep763 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 1 336 0 1 0 1 0

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 1 24 0 1 1 14 0 1 1

noncomputable def ep765 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep766 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz141 Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 (BSN.ascPochhammer_one_eval qz141)

noncomputable def ep768 := ep767 (@Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk qz70 qz150) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_crit_mk qz150 Bool.false 68454 1000 qz151) (@Enclosure.Complex.IsNear.mk qz70 qz150 Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 qz326 qz152))

noncomputable def ep769 := @ep766 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep770 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 68454 1000 0 1 0 1 0

noncomputable def ep771 := @ep770 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep772 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 11409 2000 0 1 0 1 0 1 11409

noncomputable def ep773 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 68454 1000 0 1 11409 2000 0

noncomputable def ep774 := @ep773 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep775 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep776 := @ep775 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep392) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep777 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 (@ep765 1 24 0 1 (ep769 rfl) (ep771 rfl) rfl rfl) (@ep772 11409 2000 0 1 (ep774 rfl) (ep776 rfl) rfl rfl)

noncomputable def ep778 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 ep777

noncomputable def ep779 := @ep764 336 0 1 ep778 qz138

noncomputable def ep780 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 11409 2000 0 1 0 1 0 1 0

noncomputable def ep781 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 11409 2000 0 1 ep777

noncomputable def ep782 := @ep780 1 0 1 ep781 qz139

noncomputable def ep783 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) 0 1 0 1 11409 28000 0

noncomputable def ep784 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 0 1 0 1 0

noncomputable def ep785 := @ep784 1 0 1 ep778 qz139

noncomputable def ep786 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz77)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 11409 2000 0 1 1 14 0 1 11409

noncomputable def ep787 := @ep786 28000 0 1 ep781 qz138

noncomputable def ep788 := @ep760 1 (@ep761 0 1 0 1 (BSN.bern_sum_base qz141 14) qz91) (ep762 (@ep763 1 1 1 336 0 1 (ep779 rfl) (ep782 rfl) rfl rfl) (@ep783 1 11409 11409 28000 0 1 (ep785 rfl) (ep787 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep789 := ep754 (ep757 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep758 Bool.false 11409 28000 0 1 (BSN.bern_sum_succ qz141 14 0 1 1 rfl rfl) (ep788 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep790 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 9182269251 34359738368 1287912333937 5180486473220096 6657722280861

noncomputable def ep791 := @ep790 32803400812000 0 1 61132998581247546105111 1127116269480958754816000 ep740 ep741 (@Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (ep744 ep750))

noncomputable def ep792 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))) Bool.false 197403954901 393640809744 0 1 Bool.false

noncomputable def ep793 := nat_lit 4254793018672519238292789

noncomputable def ep794 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz203 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz204 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1))))))) 2986170338596593903381 ep659 ep793

noncomputable def ep795 := nat_lit 84968787091091556690558976000

noncomputable def ep796 := nat_lit 2039250890186197360573415424

noncomputable def ep797 := nat_lit 2737502088334890777373297528150434499038019584

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_ff qz203 (Complex.im (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 448527321 137438953472 639076374649 2590243236610048 6657722280861

noncomputable def ep799 := @ep798 32803400812000 0 1 2986170338596593903381 ep659 ep793 ep795 (@Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (ep744 ep750))

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Complex.re (@HAdd.hAdd Complex Complex Complex qz5 qz192 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz54 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz54 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz102 qz103 (@HSub.hSub Nat Nat Nat qz101 (@HMul.hMul Nat Nat Nat qz54 2 k) 1)))))) 9182269251 34359738368 1287912333937 5180486473220096 197403954901

noncomputable def ep801 := @ep800 393640809744 0 1 604205421704414349717 4508465077923835019264 254238988284941199775237 ep796 (@Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 448527321 137438953472 639076374649 2590243236610048 Bool.false 9182269251 34359738368 1287912333937 5180486473220096 (ep744 ep750))

noncomputable abbrev qz414 := (ep789 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep802 := @ep737 607191592043010943620381 ep659 ep665 ep666 (@ep738 ep739 61132998581247546105111 1127116269480958754816000 ep740 ep741 ep742 118576786035555494284347 ep544 ep664 ep546 (ep751 (@ep752 6657722280861 32803400812000 0 1 qz414) rfl) (ep791 (@ep792 6657722280861 32803400812000 0 1 qz414) rfl) rfl rfl) (@ep794 ep795 604205421704414349717 4508465077923835019264 254238988284941199775237 ep796 ep797 607191592043010943620381 ep659 ep665 ep666 (ep799 (@ep792 6657722280861 32803400812000 0 1 qz414) rfl) (ep801 (@ep752 6657722280861 32803400812000 0 1 qz414) rfl) rfl rfl)

noncomputable def ep803 := @ep669 ep660 ep661 (@ep670 10360972946440192 (BSN.head_sum_c_eq qz141 14) (ep671 (BSN.head_sum_c_succ qz141 13 14 rfl rfl) (ep736 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep802 rfl rfl rfl

noncomputable def ep804 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz141 1 14) Bool.false ep543 ep544 ep545 ep546 Bool.true 137105469222103760453619 ep659 ep660 ep661 (@ep662 ep546 Bool.true 137105469222103760453619 ep659 ep660 ep661 (BSN.zetaApproximant_eq_folded' qz141 1 14 rfl) (ep803 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep805 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) (Complex.im (zetaApproximant qz141 1 14)) 275 524288 8215367

noncomputable def ep806 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161)) Bool.true 275 524288 16430734

noncomputable def ep807 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161) qz390 Bool.false 24706765 524288 211

noncomputable def ep808 := BSN.sin_dyadic_bound_f 563328 1073741824 1 0 524288 150920 0 1 1 0 1 1 275 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 563328) qz277 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 563328) qz278 0 0 rfl) rfl rfl

noncomputable def ep809 := @ep807 524288 Bool.true 275 524288 1 75386 (@ep550 24706765 524288 211 524288 ep656 rfl) (Enclosure.sfrac_false_div 24706765 524288) (BSN.sin_reduce2 qz390 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 39640686905922682880) qz23) 226375608064910080 72057594037927936 Bool.false 275 524288 7 1000000000000000 150772 75386 (BSN.sin_reduce_arg_pos_rat_q2 24706765 524288 226375608064910080 72057594037927936 7 39640686905922682880 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 275 524288 39640686905922682880 75557863725914323419136 563328 1073741824 150920 150772 (ep808 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep810 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz141 1 14) Bool.false ep543 ep544 ep545 ep546 Bool.true 137105469222103760453619 ep659 ep660 ep661 (@ep662 ep546 Bool.true 137105469222103760453619 ep659 ep660 ep661 (BSN.zetaApproximant_eq_folded' qz141 1 14 rfl) (ep803 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow16.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 14 qz150) Bool.true ep526 ep527 ep528 ep529 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 14 qz150) ep530 Bool.true ep526 ep527 ep528 ep529 (@Eq.refl Real ep530) (@ep531 Bool.true ep526 ep527 ep528 ep529 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz312 (Complex.im (@HSub.hSub Complex Complex Complex qz47 qz159 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz5 qz160 (@Nat.cast Complex Complex.instNatCast j))))) qz161) (zetaApproximant qz141 1 14)) (@ep533 ep534 ep535 ep536 ep537 ep538 ep539 ep540 ep541 ep526 ep527 ep528 ep529 (@ep542 19761987584 ep543 ep544 ep545 ep546 ep532 ep534 ep535 ep536 (@ep547 39523975168 524287 524288 8215367 19761987584 (ep658 rfl rfl) rfl) ep804 rfl) (@ep805 19761987584 137105469222103760453619 ep659 ep660 ep661 ep537 ep538 ep539 ep540 (@ep806 39523975168 275 524288 8215367 19761987584 (ep809 rfl rfl) rfl) ep810 rfl) rfl rfl))

theorem EMRow16.d12 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow16.d13 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow16.d14 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow16.d15 : @Eq Nat (Nat.pow 14 (Nat.succ (Nat.mul 2 3))) 105413504 := @Eq.refl Nat 105413504

noncomputable abbrev qz469 := (@HAdd.hAdd Complex Complex Complex qz472 qz471 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz415 := qz469

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz265 (@Norm.norm Complex Complex.instNorm qz415) (@HAdd.hAdd Real Real Real qz336 (Complex.re qz267) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz211 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz212 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz416 := (@HPow.hPow Complex Complex Complex qz450 qz463 (@HSub.hSub Complex Complex Complex qz456 qz451 qz452))

noncomputable abbrev qz213 := qz416

noncomputable def ep811 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) 871043239 51539607552 33117889 463856467968 6388853698641 8796093022208 1000115859

noncomputable def ep812 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14)) 4427 294912 1 884736 590271 524288 2449 524288 871043239 51539607552

noncomputable abbrev qz417 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz214 := (@HPow.hPow Real Nat Real qz417 qz266 2)

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214) 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep814 := nat_lit 781950621441006189802102638025

noncomputable def ep815 := nat_lit 19807040628566084398385987584

noncomputable def ep816 := nat_lit 26986075409044041160201671

noncomputable def ep817 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz215 := qz266

noncomputable abbrev qz418 := (@HPow.hPow Real Nat Real (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid))) qz215 1)

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff qz418 qz215 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep814 ep815 ep816 ep817

noncomputable def ep819 := ep818 (@Enclosure.Real.IsNear.of_eq qz418 qz215 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz215) (@Enclosure.Real.IsNear.of_eq qz215 qz263 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz264)) (@Enclosure.Real.IsNear.of_eq qz215 qz263 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz264) rfl

noncomputable def ep820 := @Enclosure.Real.IsNear.inv_image qz214 ep814 ep815 ep816 ep817 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz214 (@HMul.hMul Real Real Real qz0 qz418 qz215) Bool.false ep814 ep815 ep816 ep817 (BSN.pow_succ_r qz215 1 2 rfl) ep819) rfl rfl rfl

noncomputable def ep821 := ep813 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv qz214) Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep820 rfl rfl rfl) rfl)

noncomputable def ep822 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14)) (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))))) Bool.false 590271 524288 2449 524288

noncomputable def ep823 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))))) Bool.false 590271 524288 2449 524288

noncomputable def ep824 := nat_lit 1300519915591906378177412758755206221279369

noncomputable def ep825 := nat_lit 1025996282935842869128178801989124096000000

noncomputable def ep826 := nat_lit 66360995421918199683561276070458653536310716647101238267887

noncomputable def ep827 := nat_lit 6311858572861714567260017476464096521639790506414178304000000

noncomputable def ep828 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14)))) ep824 ep825 ep826 ep827 293911 296360

noncomputable def ep829 := nat_lit 114825157060716439188766129773388019609179752448681

noncomputable def ep830 := nat_lit 90665021788936884091159801028636920464277504000000

noncomputable def ep831 := nat_lit 64348017747756802788819098764387891425076226172797164092143

noncomputable def ep832 := nat_lit 12116577671364495070829742017579621248614389161

noncomputable def ep833 := nat_lit 11106465169144768301167075626008022756873994240000

noncomputable def ep834 := nat_lit 1123313434241850945726661443119844928144246916464327107

noncomputable def ep835 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14))) ep829 ep830 ep831 ep827 ep832 ep833 ep834

noncomputable def ep836 := nat_lit 3522242507177296075479920466776839576807918809382912000000

noncomputable def ep837 := nat_lit 1276400157215006201032806194783115954140700411583978616858722193657416687895596801127762823741440000

noncomputable def ep838 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz6 1 14)) (Complex.re (zetaApproximant qz6 1 14)) ep155 ep156 ep157 ep158 ep155 ep156 ep157 ep158 ep829

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz6 1 14)) (Complex.im (zetaApproximant qz6 1 14)) 110075327259856443593869 ep276 ep277 ep278 110075327259856443593869 ep276 ep277 ep278 ep832

noncomputable def ep840 := @ep811 1970324836974592 336940789691710170988544 19612535234291 26388279066624 3825227581825 53198770598313984 (@ep812 33117889 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow16.d12 EMRow16.d13 rfl) (ep821 rfl)) (ep822 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz6 1 14)) (@ep823 590271 524288 2449 524288 (@ep828 262144 (@ep835 ep836 ep837 ep824 ep825 ep826 ep827 (@ep838 ep830 ep831 ep827 ep431 ep431 rfl) (@ep839 ep833 ep834 ep836 ep437 ep437 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz216 := (@Norm.norm Complex Complex.instNorm qz415)

noncomputable abbrev qz419 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep841 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz216 qz419) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) Bool.false 6388853698641 8796093022208 1000115859 1970324836974592 (BSN.zrb_shape_eq qz216 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) qz17 3)

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz216 qz419) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) 4935349 262144 1 1835008 1294509 33554432 111 4294967296

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff qz216 qz419 34547443 524288 1 524288 2 7 0 1 4935349 262144

noncomputable abbrev qz420 := (Complex.re qz469)

noncomputable abbrev qz421 := (Complex.im qz469)

noncomputable abbrev qz217 := (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz262 qz420 qz420) (@HMul.hMul Real Real Real qz262 qz421 qz421))

noncomputable abbrev qz218 := qz415

noncomputable def ep844 := @Enclosure.Real.IsNear.of_eq qz216 (Real.sqrt qz217) Bool.false 34547443 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz218)

noncomputable def ep845 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz217) Bool.false 34547443 524288 1 524288 34547443

noncomputable def ep846 := @Enclosure.Real.IsNear.sqrt_image qz217 4342021601 1000000 0 1 17273721 17273722 262144

noncomputable abbrev qz219 := (@HMul.hMul Real Real Real qz262 qz420 qz420)

noncomputable abbrev qz220 := (@HMul.hMul Real Real Real qz262 qz421 qz421)

noncomputable def ep847 := @Enclosure.Real.IsNear.addLit_ff qz219 qz220 49 4 0 1 4329771601 1000000 0 1

noncomputable abbrev qz221 := qz420

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff qz221 qz221 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz422 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep849 := @Enclosure.Complex.IsNear.of_eq qz218 (Complex.mk qz422 qz17) Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 65801 1000 3 qz18)

noncomputable abbrev qz423 := (ep849 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz17 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz22))

noncomputable def ep850 := @ep848 0 1 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz423)

noncomputable def ep851 := ep850 (@Enclosure.Complex.IsNear.re_isNear qz218 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz423)

noncomputable abbrev qz222 := qz421

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz222 qz222 65801 1000 0 1 65801 1000 0 1 4329771601 1000000

noncomputable def ep853 := @ep852 0 1 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz423)

noncomputable def ep854 := ep853 (@Enclosure.Complex.IsNear.im_isNear qz218 Bool.false 7 2 0 1 Bool.false 65801 1000 0 1 qz423)

noncomputable def ep855 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))))) Bool.false 1294509 33554432

noncomputable def ep856 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))))) Bool.false 662788608 17179869184

noncomputable def ep857 := nat_lit 33606615196456116705061536571039409851648657476850668654032441

noncomputable def ep858 := nat_lit 22579504513512255930804914751056466024805171200000000000000000000

noncomputable def ep859 := nat_lit 73673397974658025386525575869222473171501929725118750799275478965338691

noncomputable def ep860 := nat_lit 36987087290570557991706730362078125366549753706010285713653760000000000000000000

noncomputable def ep861 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) ep857 ep858 ep859 ep860

noncomputable def ep862 := nat_lit 535906756005914991336706510272618097330523340174454879354441

noncomputable def ep863 := nat_lit 557518629963265578538392956816209037649510400000000000000000000

noncomputable def ep864 := nat_lit 9928834838781377007999152515254207996333370486085965690986608801813771

noncomputable def ep865 := nat_lit 8219352731237901775934828969350694525899945268002285714145280000000000000000000

noncomputable def ep866 := nat_lit 23804783156433119111849845809996753819524924399570492080355161

noncomputable def ep867 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213))) ep862 ep863 ep864 ep865 ep866

noncomputable def ep868 := nat_lit 45159009027024511861609829502112932049610342400000000000000000000

noncomputable def ep869 := nat_lit 57987282400283657701058779101157074376003525075463810379671478714353443

noncomputable def ep870 := nat_lit 73974174581141115983413460724156250733099507412020571427307520000000000000000000

noncomputable def ep871 := nat_lit 37472628124061750948002709926920723762813175683179629839112448815764924935736718924103538746234778733772800000000000000000000

noncomputable def ep872 := nat_lit 732056525144004840552421219229

noncomputable def ep873 := nat_lit 23611832414348226068480000000000

noncomputable def ep874 := nat_lit 124887629813451147049794417897553

noncomputable def ep875 := nat_lit 6410675756594581416489957457920000000000

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) ep872 ep873 ep874 ep875 ep872 ep873 ep874

noncomputable def ep877 := nat_lit 4879014568171847456535439705381

noncomputable def ep878 := nat_lit 212506491729134034616320000000000

noncomputable def ep879 := nat_lit 328312655335756057638201501967019

noncomputable def ep880 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213) Bool.true ep872 ep873 ep874 ep875 Bool.true ep877 ep878 ep879

noncomputable def ep881 := nat_lit 19232027269783744249469872373760000000000

noncomputable def ep882 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213 Bool.true ep872 ep873 ep874 ep875 Bool.true ep877 ep878 ep879 ep881

noncomputable def ep883 := nat_lit 242176353667466593098400243

noncomputable def ep884 := nat_lit 141670994486089356410880000000

noncomputable def ep885 := nat_lit 283283969433489780753950693

noncomputable def ep886 := nat_lit 261660234963044139448569692160000000

noncomputable def ep887 := nat_lit 2075081398598281225108063536187

noncomputable def ep888 := nat_lit 70835497243044678205440000000000

noncomputable def ep889 := nat_lit 39315724187443549140440875306351

noncomputable abbrev qz223 := (Complex.re qz416)

noncomputable abbrev qz224 := (Complex.im qz416)

noncomputable def ep890 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz223) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224) ep883 ep884 ep885 ep886 ep887 ep888 ep889

noncomputable def ep891 := nat_lit 2136891918864860472163319152640000000000

noncomputable def ep892 := nat_lit 311133527811546132196522585473126501623814771242434560000000

noncomputable def ep893 := nat_lit 26711148985810755902041489408

noncomputable def ep894 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz223 12988064803 480000000 0 1 18646069090410481 295147905179352825856 1068743859288010919 ep893 ep883

noncomputable def ep895 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 12988064803 480000000 0 1 0 1 0 1 12988064803

noncomputable def ep896 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 38964194409 2000000 0 1 12988064803 480000000 0

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz14) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow16.d14 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz14 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz24)

noncomputable abbrev qz424 := (@HAdd.hAdd Complex Complex Complex qz449 qz448 qz453)

noncomputable abbrev qz225 := qz424

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz225) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1

noncomputable abbrev qz226 := (Complex.re qz424)

noncomputable abbrev qz227 := (Complex.im qz424)

noncomputable def ep899 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz226) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227) 4329021601 400000 0 1 4329771601 500000 0 1

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz226 4329021601 1000000 0 1 5 2 0 1 4329021601 400000

noncomputable abbrev qz425 := (@HAdd.hAdd Complex Complex Complex qz449 qz448 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz228 := qz425

noncomputable def ep901 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz228) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1

noncomputable abbrev qz229 := (Complex.re qz425)

noncomputable abbrev qz230 := (Complex.im qz425)

noncomputable def ep902 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz229) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230) 3 4 0 1 4329771601 1000000 0 1

noncomputable def ep903 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz229 1 2 0 1 3 2 0 1 3 4

noncomputable def ep904 := @ep903 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable abbrev qz426 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep905 := @Enclosure.Complex.IsNear.of_eq qz228 (Complex.mk qz426 qz17) Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 65801 1000 1 qz18)

noncomputable abbrev qz427 := (ep905 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz17 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz22))

noncomputable def ep906 := ep904 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz427)

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230 65801 1000 0 1 65801 1000 0 1 4329771601 1000000

noncomputable def ep908 := @ep907 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep909 := ep908 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz427)

noncomputable def ep910 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) qz228 Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 (@ep902 17316086404 4329021601 1000000 0 1 (ep906 rfl) (ep909 rfl) rfl rfl)

noncomputable def ep911 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz229) 65801 2000 0 1 197403 2000 0 1

noncomputable def ep912 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz230 1 2 0 1 65801 1000 0 1 65801 2000

noncomputable def ep913 := @ep912 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep914 := ep913 (@Enclosure.Complex.IsNear.im_isNear qz228 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz427)

noncomputable def ep915 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1))) qz229 65801 1000 0 1 3 2 0 1 197403 2000

noncomputable def ep916 := @ep915 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 65801 1000 0 1 ep394)

noncomputable def ep917 := ep916 (@Enclosure.Complex.IsNear.re_isNear qz228 Bool.false 3 2 0 1 Bool.false 65801 1000 0 1 qz427)

noncomputable abbrev qz231 := (ep901 (BSN.ascPochhammer_succ_eval_c 1 2 qz267 rfl) (ep910 (@ep911 526408000 65801 500 0 1 (ep914 rfl) (ep917 rfl) rfl rfl)))

noncomputable def ep918 := @ep900 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz231)

noncomputable abbrev qz428 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep919 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk qz428 qz17) Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 (BSN.s_add_nat_mk qz17 Bool.false 65801 1000 2 qz18)

noncomputable abbrev qz429 := (ep919 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz17 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz22))

noncomputable def ep920 := ep918 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz429)

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227 65801 500 0 1 65801 1000 0 1 4329771601 500000

noncomputable def ep922 := @ep921 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz231)

noncomputable def ep923 := ep922 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz429)

noncomputable def ep924 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) qz225 Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 (@ep899 3896419440900000 38964194409 2000000 0 1 (ep920 rfl) (ep923 rfl) rfl rfl)

noncomputable def ep925 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz226) 284853950367401 1000000000 0 1 65801 200 0 1

noncomputable def ep926 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz227 4329021601 1000000 0 1 65801 1000 0 1 284853950367401 1000000000

noncomputable def ep927 := @ep926 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz231)

noncomputable def ep928 := ep927 (@Enclosure.Complex.IsNear.im_isNear qz225 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz429)

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2))) qz226 65801 500 0 1 5 2 0 1 65801 200

noncomputable def ep930 := @ep929 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4329021601 1000000 0 1 Bool.false 65801 500 0 1 qz231)

noncomputable def ep931 := ep930 (@Enclosure.Complex.IsNear.re_isNear qz225 Bool.false 5 2 0 1 Bool.false 65801 1000 0 1 qz429)

noncomputable abbrev qz232 := (ep898 (BSN.ascPochhammer_succ_eval_c 2 3 qz267 rfl) (ep924 (@ep925 56904989073480200 284524945367401 1000000000 0 1 (ep928 rfl) (ep931 rfl) rfl rfl)))

noncomputable def ep932 := @ep896 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz232)

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 284524945367401 1000000000 0 1 0 1 0

noncomputable def ep934 := @ep933 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz232)

noncomputable def ep935 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) 284524945367401 720000000000 0 1 0 1 0 1 284524945367401

noncomputable def ep936 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 284524945367401 1000000000 0 1 284524945367401 720000000000 0

noncomputable def ep937 := @ep936 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz232)

noncomputable def ep938 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 38964194409 2000000 0 1 0 1 0

noncomputable def ep939 := @ep938 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 38964194409 2000000 0 1 Bool.true 284524945367401 1000000000 0 1 qz232)

noncomputable def ep940 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 (@ep895 12988064803 480000000 0 1 (ep932 rfl) (ep934 rfl) rfl rfl) (@ep935 284524945367401 720000000000 0 1 (ep937 rfl) (ep939 rfl) rfl rfl)

noncomputable def ep941 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 ep940

noncomputable def ep942 := @Enclosure.Complex.IsNear.re_isNear qz213 Bool.true 18646069090410481 295147905179352825856 1068743859288010919 ep893 Bool.false 21879432004657161 295147905179352825856 1243622126805380559 ep893

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast 105413504)

noncomputable abbrev qz233 := (@Inv.inv Real Real.instInv (Real.sqrt qz430))

noncomputable def ep943 := @Enclosure.Complex.IsNear.of_eq qz213 (Complex.mk (@HMul.hMul Real Real Real qz0 qz233 qz127) (@HMul.hMul Real Real Real qz0 qz233 qz128)) Bool.true 18646069090410481 295147905179352825856 1068743859288010919 ep893 Bool.false 21879432004657161 295147905179352825856 1243622126805380559

noncomputable abbrev qz234 := (Real.sqrt qz430)

noncomputable def ep944 := @Enclosure.Real.IsNear.inv_image qz234 176387570092723 17179869184 1 17179869184 836645 836646 8589934592 (@Enclosure.Real.IsNear.of_eq qz234 (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz430 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 (BSN.sqrt_natCast_div_one 105413504) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz2 qz430 qz19)) Bool.false 176387570092723 17179869184 1 17179869184 176387570092723 17179869184 1 17179869184 (BSN.sqrt_enclosure 105413504 1 88193785046361 88193785046362 8589934592 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep945 := nat_lit 90500893000000000000000000

noncomputable def ep946 := nat_lit 816748683538471975894646784

noncomputable def ep947 := nat_lit 309485009821345068724781056

noncomputable def ep948 := nat_lit 2896028576000000000000000

noncomputable def ep949 := nat_lit 103769785630983789875522764800

noncomputable def ep950 := nat_lit 2694100009858475599347056640

noncomputable def ep951 := BSN.log_dyadic_bound 6 22 9 8 ep949 8589934592 2896028576 ep950 5718460310160998400 4807063014 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 6) (BSN.artanhQ 22) 0 8 ep950 ep949 5718460310160998400 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep952 := @Enclosure.Real.IsNear.mulLit_ff qz17 qz130 65801 1000 0 1 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 782061835714775872269 4503599627370496000 2056299115147780879 ep945 qz22 (BSN.isNear_log_sfrac 14 1 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz129) Bool.false ep946 ep947 1000008688085728 ep948 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 4807063014 8589934592 24973259072661432 36028797018963968 2896028576 1000000000000000 rfl rfl rfl rfl (ep951 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep953 := nat_lit 1070837186802058894141030400

noncomputable def ep954 := nat_lit 1237940039285380274899124224

noncomputable def ep955 := nat_lit 40231241651651103874200789874188392360775642161748864888370242927270730343861002379443347403948630877026069125353994516181305916390199401146594099329425593050045819285761

noncomputable def ep956 := nat_lit 1723989524678609869184368353634558086375647288945605880257499904391989104065417411410730399287089189440146844853530817917959165259045966673531664948206962296697359276441600

noncomputable def ep957 := nat_lit 631660434800245446997223479428600769828250898221216357107143159845051025849459816866429914575622117549949093245194075728806794520387923785503556527208180815130881

noncomputable def ep958 := nat_lit 244015321452984941790061243675387562541957967797188360867910684758926224642951105042635790902162346211391377695390186793673850753225005145667204221986988764358926644441345

noncomputable def ep959 := nat_lit 156883046745753498095777520180744785860183903294050135103432491299671008469952984438376466335125116239053362881671304430534284038573182967291381510286833568999459694156185600

noncomputable def ep960 := BSN.cos_dyadic_bound_f 30435023370559 35184372088832 4 3 17179869184 5797713458 ep955 ep956 ep957 ep958 ep959 ep957 11143351091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 30435023370559) (BSN.cosEvenQ 35184372088832) 0 3 ep955 ep956 ep957 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 30435023370559) (BSN.cosOddQ 35184372088832) 0 3 ep958 ep959 ep957 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 1491664573125) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep961 := @Enclosure.Real.IsNear.cos_image qz131 qz431 Bool.false 1491664573125 8589934592 49 2147483648 Bool.true 11143351091 17179869184 1 2896028576 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 782061835714775872269 4503599627370496000 2056299115147780879 ep945 1491664573125 8589934592 49 2147483648 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 1491664573125 8589934592) (BSN.cos_reduce2 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep953) (@Nat.cast Real Real.instNatCast ep954)) 226375608064910080 72057594037927936 Bool.false 11143351091 17179869184 27 1000000000000000 5792057152 2896028576 (BSN.sin_reduce_arg_pos_rat_q2 1491664573125 8589934592 226375608064910080 72057594037927936 27 ep953 ep954 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11143351091 17179869184 ep953 ep954 30435023370559 35184372088832 5797713458 5792057152 (ep960 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep962 := nat_lit 3977003424548989524423998783475493377255503861820661088042475742379414974091186125854496342483567849911868061185

noncomputable def ep963 := nat_lit 852239132436968601736534718962914620494087683347851114682261747749608011033589111964107092533864866956228564090880

noncomputable def ep964 := nat_lit 736188648434119186923965724755351814665899550998592173505940110674308789093204950162617436979847187584120321

noncomputable def ep965 := nat_lit 10414769425530841132903072297929069227969241515019162271830331612719280813151717521604369992558996044798803965441

noncomputable def ep966 := nat_lit 15624384094677757698503136514320101375724940861377270435841465375409480202282467052675296696454189227530857008332800

noncomputable def ep967 := BSN.sin_dyadic_bound_f 30435023370559 35184372088832 3 2 17179869184 5797713458 ep962 ep963 ep964 ep965 ep966 ep964 13075688571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 30435023370559) (BSN.sinEvenQ 35184372088832) 0 2 ep962 ep963 ep964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 30435023370559) (BSN.sinOddQ 35184372088832) 0 2 ep965 ep966 ep964 rfl rfl rfl rfl) rfl rfl

noncomputable def ep968 := @Enclosure.Real.IsNear.sin_image qz131 qz431 Bool.false 1491664573125 8589934592 49 2147483648 Bool.true 13075688571 17179869184 1 2896028576 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 782061835714775872269 4503599627370496000 2056299115147780879 ep945 1491664573125 8589934592 49 2147483648 (ep952 rfl) rfl) (Enclosure.sfrac_false_div 1491664573125 8589934592) (BSN.sin_reduce2 qz431 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep953) (@Nat.cast Real Real.instNatCast ep954)) 226375608064910080 72057594037927936 Bool.false 13075688571 17179869184 27 1000000000000000 5792057152 2896028576 (BSN.sin_reduce_arg_pos_rat_q2 1491664573125 8589934592 226375608064910080 72057594037927936 27 ep953 ep954 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 13075688571 17179869184 ep953 ep954 30435023370559 35184372088832 5797713458 5792057152 (ep967 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz432 := (@Enclosure.Real.IsNear.recentre' qz233 Bool.false 1673291 17179869184 1 17179869184 1673291 17179869184 1 17179869184 (ep944 rfl rfl) rfl)

noncomputable def ep969 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz233 qz127) (@HMul.hMul Real Real Real qz0 qz233 qz128) Bool.true 18646069090410481 295147905179352825856 1068743859288010919 ep893 Bool.false 21879432004657161 295147905179352825856 1243622126805380559 ep893 (@Enclosure.Real.IsNear.mulLit_ft qz233 qz127 1673291 17179869184 1 17179869184 11143351091 17179869184 4501652621 194349187846897664 18646069090410481 295147905179352825856 1068743859288010919 ep893 qz432 (@Enclosure.Real.IsNear.recentre' qz127 Bool.true 11143351091 17179869184 144052883872 6219174011100725248 11143351091 17179869184 4501652621 194349187846897664 (ep961 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz233 qz128 1673291 17179869184 1 17179869184 13075688571 17179869184 4501652621 194349187846897664 21879432004657161 295147905179352825856 1243622126805380559 ep893 qz432 (@Enclosure.Real.IsNear.neg qz132 Bool.true 13075688571 17179869184 4501652621 194349187846897664 (@Enclosure.Real.IsNear.recentre' qz132 Bool.true 13075688571 17179869184 144052883872 6219174011100725248 13075688571 17179869184 4501652621 194349187846897664 (ep968 rfl rfl) rfl)) rfl)

noncomputable def ep970 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224 284524945367401 720000000000 0 1 21879432004657161 295147905179352825856 1243622126805380559 ep893 ep887

noncomputable def ep971 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12988064803 480000000 0 1 Bool.false 284524945367401 720000000000 0 1 ep940

noncomputable def ep972 := @Enclosure.Complex.IsNear.im_isNear qz213 Bool.true 18646069090410481 295147905179352825856 1068743859288010919 ep893 Bool.false 21879432004657161 295147905179352825856 1243622126805380559 ep893

noncomputable def ep973 := nat_lit 94723826909773134955334761

noncomputable def ep974 := nat_lit 47223664828696452136960000000

noncomputable def ep975 := nat_lit 109879216145530381424274591

noncomputable def ep976 := nat_lit 87220078321014713149523230720000000

noncomputable def ep977 := nat_lit 5305271789265826563834446129881

noncomputable def ep978 := nat_lit 304084288175666608534148954651519

noncomputable def ep979 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz223) ep973 ep974 ep975 ep976 ep977 ep878 ep978

noncomputable def ep980 := nat_lit 230404948661674481115236157512130659740253830260981760000000

noncomputable def ep981 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz224 12988064803 480000000 0 1 21879432004657161 295147905179352825856 1243622126805380559 ep893 ep973

noncomputable def ep982 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3)))) qz223 284524945367401 720000000000 0 1 18646069090410481 295147905179352825856 1068743859288010919 ep893 ep977

noncomputable abbrev qz433 := (@ep943 ep893 (BSN.cpow_neg_s_sub_mk qz17 65801 1000 14 3 105413504 qz18 rfl EMRow16.d15) ep969)

noncomputable def ep983 := ep882 (@ep890 ep891 ep892 ep872 ep873 ep874 ep875 (@ep894 ep884 ep885 ep886 ep941 (ep942 qz433) rfl) (@ep970 ep888 ep889 ep891 ep971 (ep972 qz433) rfl) rfl rfl) (@ep979 ep881 ep980 ep877 ep878 ep879 ep881 (@ep981 ep974 ep975 ep976 ep941 (ep972 qz433) rfl) (@ep982 ep878 ep978 ep881 ep971 (ep942 qz433) rfl) rfl rfl)

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) ep877 ep878 ep879 ep881 ep877 ep878 ep879

noncomputable def ep985 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213) Bool.true ep872 ep873 ep874 ep875 Bool.true ep877 ep878 ep879

noncomputable def ep986 := @ep842 6388853698641 8796093022208 1000115859 1970324836974592 (@ep843 1 1835008 (ep844 (@ep845 524288 1 524288 (ep846 (@ep847 17368086404 4342021601 1000000 0 1 (ep851 rfl) (ep854 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep855 111 4294967296 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)) (@ep856 444 17179869184 1294509 33554432 111 4294967296 (@ep861 331394082 331394526 8589934592 (@ep867 ep868 ep869 ep870 ep871 ep857 ep858 ep859 ep860 (@ep876 ep875 ep862 ep863 ep864 ep865 (@ep880 ep881 ep983) (@ep880 ep881 ep983) rfl) (@ep984 ep881 ep866 ep868 ep869 ep870 (@ep985 ep881 ep983) (@ep985 ep881 ep983) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow16.d16 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) Bool.false 19612535234291 26388279066624 3825227581825 53198770598313984 := ep840 (ep841 ep986) rfl rfl

noncomputable abbrev qz470 := (@HAdd.hAdd Complex Complex Complex qz472 qz478 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz434 := qz470

noncomputable abbrev qz235 := (@HDiv.hDiv Real Real Real qz265 (@Norm.norm Complex Complex.instNorm qz434) (@HAdd.hAdd Real Real Real qz336 (Complex.re qz375) (@Nat.cast Real Real.instNatCast 3)))

noncomputable abbrev qz435 := (@HPow.hPow Complex Complex Complex qz450 qz463 (@HSub.hSub Complex Complex Complex qz456 qz465 qz452))

noncomputable abbrev qz236 := qz435

noncomputable def ep987 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 qz235 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) 3787285219 154618822656 34365983 463856467968 26814913220304987 31525197391593472 17600389805

noncomputable def ep988 := nat_lit 4265485225853605954547875840

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14)) 4427 294912 1 884736 855497 524288 2523 524288 3787285219 154618822656

noncomputable def ep990 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14)) (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 14)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 14)) (Complex.im (zetaApproximant qz141 1 14))))) Bool.false 855497 524288 2523 524288

noncomputable def ep991 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 14)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 14)) (Complex.im (zetaApproximant qz141 1 14))))) Bool.false 855497 524288 2523 524288

noncomputable def ep992 := nat_lit 46195209954784572901420988141218649188993

noncomputable def ep993 := nat_lit 17349884218097502836028015351169024000000

noncomputable def ep994 := nat_lit 4080002969120471154066373560299506848701718256726561494173

noncomputable def ep995 := nat_lit 259909012070324897910290380284247574787060408030068736000000

noncomputable def ep996 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 14)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 14)) (Complex.im (zetaApproximant qz141 1 14)))) ep992 ep993 ep994 ep995 426487 429010

noncomputable def ep997 := nat_lit 13525300413124585457468932136540275995371231358409

noncomputable def ep998 := nat_lit 5081564339714692943094050907368628812775424000000

noncomputable def ep999 := nat_lit 3999972409922345257241512017815017542842092980758115986749

noncomputable def ep1000 := nat_lit 18797909690613241536644251892260571220650197161

noncomputable def ep1001 := nat_lit 20326257358858771772376203629474515251101696000000

noncomputable def ep1002 := nat_lit 357279282134490610825274743234327258301898553430560301

noncomputable def ep1003 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 14)) (Complex.re (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 14)) (Complex.im (zetaApproximant qz141 1 14))) ep997 ep998 ep999 ep995 ep1000 ep1001 ep1002

noncomputable def ep1004 := nat_lit 1160308089599664722813796340554676673156519678705664000000

noncomputable def ep1005 := nat_lit 275014259840594188637911882861657775127514007475836465022792393509829054868353017001099132928000000

noncomputable def ep1006 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz141 1 14)) (Complex.re (zetaApproximant qz141 1 14)) ep543 ep544 ep545 ep546 ep543 ep544 ep545 ep546 ep997

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz141 1 14)) (Complex.im (zetaApproximant qz141 1 14)) 137105469222103760453619 ep659 ep660 ep661 137105469222103760453619 ep659 ep660 ep661 ep1000

noncomputable def ep1008 := @ep987 31525197391593472 ep988 248283917657891635 283726776524341248 63537064257599 851180329573023744 (@ep989 34365983 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) (@Inv.inv Real Real.instInv qz214)) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow16.d12 EMRow16.d13 rfl) (ep821 rfl)) (ep990 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz141 1 14)) (@ep991 855497 524288 2523 524288 (@ep996 262144 (@ep1003 ep1004 ep1005 ep992 ep993 ep994 ep995 (@ep1006 ep998 ep999 ep995 ep804 ep804 rfl) (@ep1007 ep1001 ep1002 ep1004 ep810 ep810 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz237 := (@Norm.norm Complex Complex.instNorm qz434)

noncomputable def ep1009 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz235 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz237 qz419) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) Bool.false 26814913220304987 31525197391593472 17600389805 31525197391593472 (BSN.zrb_shape_eq qz237 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) qz150 3)

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz237 qz419) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) 35936491 1835008 1 1835008 746175057 17179869184 469 17179869184

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz237 qz419 35936491 524288 1 524288 2 7 0 1 35936491 1835008

noncomputable abbrev qz436 := (Complex.re qz470)

noncomputable abbrev qz437 := (Complex.im qz470)

noncomputable abbrev qz238 := (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz262 qz436 qz436) (@HMul.hMul Real Real Real qz262 qz437 qz437))

noncomputable abbrev qz239 := qz434

noncomputable def ep1012 := @Enclosure.Real.IsNear.of_eq qz237 (Real.sqrt qz238) Bool.false 35936491 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz239)

noncomputable def ep1013 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz238) Bool.false 35936491 524288 1 524288 35936491

noncomputable def ep1014 := @Enclosure.Real.IsNear.sqrt_image qz238 1174550029 250000 0 1 17968245 17968246 262144

noncomputable abbrev qz240 := (@HMul.hMul Real Real Real qz262 qz436 qz436)

noncomputable abbrev qz241 := (@HMul.hMul Real Real Real qz262 qz437 qz437)

noncomputable def ep1015 := @Enclosure.Real.IsNear.addLit_ff qz240 qz241 49 4 0 1 1171487529 250000 0 1

noncomputable abbrev qz242 := qz436

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff qz242 qz242 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1017 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz422 qz150) Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 68454 1000 3 qz151)

noncomputable abbrev qz438 := (Enclosure.Real.IsNear.const Bool.false 7 2)

noncomputable abbrev qz243 := (ep1017 (@Enclosure.Complex.IsNear.mk qz422 qz377 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz438 qz379))

noncomputable def ep1018 := @ep1016 0 1 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz243)

noncomputable def ep1019 := ep1018 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz243)

noncomputable abbrev qz244 := qz437

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ff qz244 qz244 68454 1000 0 1 68454 1000 0 1 1171487529 250000

noncomputable def ep1021 := @ep1020 0 1 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz243)

noncomputable def ep1022 := ep1021 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 7 2 0 1 Bool.false 68454 1000 0 1 qz243)

noncomputable def ep1023 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))))) Bool.false 746175057 17179869184

noncomputable def ep1024 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))))) Bool.false 746175057 17179869184

noncomputable def ep1025 := nat_lit 14789846603705439999505876725843680882065923758196648527221

noncomputable def ep1026 := nat_lit 7840105733858422198196150955227939591946240000000000000000000

noncomputable def ep1027 := nat_lit 84275778649390167714343479057878832356741332241981321977182702891839

noncomputable def ep1028 := nat_lit 35674274007108948680272695179473500546440734670148809523200000000000000000000

noncomputable def ep1029 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)))) ep1025 ep1026 ep1027 ep1028

noncomputable def ep1030 := nat_lit 146996551443327439971355224397942205292190902604062653343241

noncomputable def ep1031 := nat_lit 78401057338584221981961509552279395919462400000000000000000000

noncomputable def ep1032 := nat_lit 167031861835184891707879383719615486632043540749017485380538162377143

noncomputable def ep1033 := nat_lit 71348548014217897360545390358947001092881469340297619046400000000000000000000

noncomputable def ep1034 := nat_lit 100212732636328891522615873388289280940926108655981325441

noncomputable def ep1035 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236))) ep1030 ep1031 ep1032 ep1033 ep1034

noncomputable def ep1036 := nat_lit 8711228593176024664662389950253266213273600000000000000000000

noncomputable def ep1037 := nat_lit 303939092719088744161514879228435616287824746989031714765448681307

noncomputable def ep1038 := nat_lit 14269709602843579472109078071789400218576293868059523809280000000000000000000

noncomputable def ep1039 := nat_lit 1288377346228861464621669361926697617251307782932346837632367756270510287027759214509738931211206656000000000000000000000

noncomputable def ep1040 := nat_lit 383401292959905705077718232829

noncomputable def ep1041 := nat_lit 8854437155380584775680000000000

noncomputable def ep1042 := nat_lit 21662334741642944918968439052839

noncomputable def ep1043 := nat_lit 801334469574322677061244682240000000000

noncomputable def ep1044 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) ep1040 ep1041 ep1042 ep1043 ep1040 ep1041 ep1042

noncomputable def ep1045 := nat_lit 10010630980928669289623212479

noncomputable def ep1046 := nat_lit 2951479051793528258560000000000

noncomputable def ep1047 := nat_lit 838710448558729171880723337641

noncomputable def ep1048 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236) Bool.true ep1040 ep1041 ep1042 ep1043 Bool.false ep1045 ep1046 ep1047

noncomputable def ep1049 := nat_lit 267111489858107559020414894080000000000

noncomputable def ep1050 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236 Bool.true ep1040 ep1041 ep1042 ep1043 Bool.false ep1045 ep1046 ep1047 ep1049

noncomputable def ep1051 := nat_lit 1257966951045744418871329

noncomputable def ep1052 := nat_lit 35417748621522339102720000000

noncomputable def ep1053 := nat_lit 41188197543733095553284113

noncomputable def ep1054 := nat_lit 457905411185327244034996961280000000

noncomputable def ep1055 := nat_lit 127905261565889047060812021693

noncomputable def ep1056 := nat_lit 7196751798647137333916730618363

noncomputable abbrev qz245 := (Complex.re qz435)

noncomputable abbrev qz246 := (Complex.im qz435)

noncomputable def ep1057 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz245) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) ep1051 ep1052 ep1053 ep1054 ep1055 ep1046 ep1056

noncomputable def ep1058 := nat_lit 4526403538406860927217584212510658656136627969064960000000

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz245 3514150087 120000000 0 1 357971890756567 295147905179352825856 82044698054506193 ep893 ep1051

noncomputable def ep1060 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 3514150087 120000000 0 1 0 1 0 1 3514150087

noncomputable def ep1061 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 10542450261 500000 0 1 3514150087 120000000 0

noncomputable abbrev qz439 := (@HAdd.hAdd Complex Complex Complex qz449 qz464 qz453)

noncomputable abbrev qz247 := qz439

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz247) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1

noncomputable abbrev qz248 := (Complex.re qz439)

noncomputable abbrev qz249 := (Complex.im qz439)

noncomputable def ep1063 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz248) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) 1171300029 100000 0 1 1171487529 125000 0 1

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz248 1171300029 250000 0 1 5 2 0 1 1171300029 100000

noncomputable abbrev qz440 := (@HAdd.hAdd Complex Complex Complex qz449 qz464 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz250 := qz440

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz46 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz250) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1

noncomputable abbrev qz251 := (Complex.re qz440)

noncomputable abbrev qz252 := (Complex.im qz440)

noncomputable def ep1066 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz251) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) 3 4 0 1 1171487529 250000 0 1

noncomputable def ep1067 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz251 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1068 := @ep1067 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq qz250 (Complex.mk qz426 qz150) Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 68454 1000 1 qz151)

noncomputable abbrev qz441 := (Enclosure.Real.IsNear.const Bool.false 3 2)

noncomputable abbrev qz253 := (ep1069 (@Enclosure.Complex.IsNear.mk qz426 qz377 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz441 qz379))

noncomputable def ep1070 := ep1068 (@Enclosure.Complex.IsNear.re_isNear qz250 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz253)

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 68454 1000 0 1 68454 1000 0 1 1171487529 250000

noncomputable def ep1072 := @ep1071 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep1073 := ep1072 (@Enclosure.Complex.IsNear.im_isNear qz250 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz253)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz250 Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 (@ep1066 4685200116 1171300029 250000 0 1 (ep1070 rfl) (ep1073 rfl) rfl rfl)

noncomputable def ep1075 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz251) 34227 1000 0 1 102681 1000 0 1

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz252 1 2 0 1 68454 1000 0 1 34227 1000

noncomputable def ep1077 := @ep1076 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep1078 := ep1077 (@Enclosure.Complex.IsNear.im_isNear qz250 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz253)

noncomputable def ep1079 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz251 68454 1000 0 1 3 2 0 1 102681 1000

noncomputable def ep1080 := @ep1079 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 68454 1000 0 1 ep768)

noncomputable def ep1081 := ep1080 (@Enclosure.Complex.IsNear.re_isNear qz250 Bool.false 3 2 0 1 Bool.false 68454 1000 0 1 qz253)

noncomputable abbrev qz254 := (ep1065 (BSN.ascPochhammer_succ_eval_c 1 2 qz375 rfl) (ep1074 (@ep1075 136908000 34227 250 0 1 (ep1078 rfl) (ep1081 rfl) rfl rfl)))

noncomputable def ep1082 := @ep1064 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz254)

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz428 qz150) Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 68454 1000 2 qz151)

noncomputable abbrev qz442 := (Enclosure.Real.IsNear.const Bool.false 5 2)

noncomputable abbrev qz255 := (ep1083 (@Enclosure.Complex.IsNear.mk qz428 qz377 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz442 qz379))

noncomputable def ep1084 := ep1082 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz255)

noncomputable def ep1085 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 34227 250 0 1 68454 1000 0 1 1171487529 125000

noncomputable def ep1086 := @ep1085 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz254)

noncomputable def ep1087 := ep1086 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz255)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz247 Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 (@ep1063 263561256525000 10542450261 500000 0 1 (ep1084 rfl) (ep1087 rfl) rfl rfl)

noncomputable def ep1089 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz249) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz248) 40090086092583 125000000 0 1 34227 100 0 1

noncomputable def ep1090 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz249 1171300029 250000 0 1 68454 1000 0 1 40090086092583 125000000

noncomputable def ep1091 := @ep1090 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz254)

noncomputable def ep1092 := ep1091 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz255)

noncomputable def ep1093 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz248 34227 250 0 1 5 2 0 1 34227 100

noncomputable def ep1094 := @ep1093 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 1171300029 250000 0 1 Bool.false 34227 250 0 1 qz254)

noncomputable def ep1095 := ep1094 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 5 2 0 1 Bool.false 68454 1000 0 1 qz255)

noncomputable abbrev qz256 := (ep1062 (BSN.ascPochhammer_succ_eval_c 2 3 qz375 rfl) (ep1088 (@ep1089 4004730234258300 40047302342583 125000000 0 1 (ep1092 rfl) (ep1095 rfl) rfl rfl)))

noncomputable def ep1096 := @ep1061 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz256)

noncomputable def ep1097 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 40047302342583 125000000 0 1 0 1 0

noncomputable def ep1098 := @ep1097 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz256)

noncomputable def ep1099 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 4449700260287 10000000000 0 1 0 1 0 1 4449700260287

noncomputable def ep1100 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 40047302342583 125000000 0 1 4449700260287 10000000000 0

noncomputable def ep1101 := @ep1100 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz256)

noncomputable def ep1102 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 10542450261 500000 0 1 0 1 0

noncomputable def ep1103 := @ep1102 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep897) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 10542450261 500000 0 1 Bool.true 40047302342583 125000000 0 1 qz256)

noncomputable def ep1104 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 (@ep1060 3514150087 120000000 0 1 (ep1096 rfl) (ep1098 rfl) rfl rfl) (@ep1099 4449700260287 10000000000 0 1 (ep1101 rfl) (ep1103 rfl) rfl rfl)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 ep1104

noncomputable def ep1106 := @Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 357971890756567 295147905179352825856 82044698054506193 ep893 Bool.false 28744691571121539 295147905179352825856 1617356535872138949 ep893

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk (@HMul.hMul Real Real Real qz0 qz233 qz205) (@HMul.hMul Real Real Real qz0 qz233 qz206)) Bool.false 357971890756567 295147905179352825856 82044698054506193 ep893 Bool.false 28744691571121539 295147905179352825856 1617356535872138949

noncomputable def ep1108 := nat_lit 45250446500000000000000000

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz130 68454 1000 0 1 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 406796712071391525663 2251799813685248000 1069603042722194133 ep1108 qz152 (BSN.isNear_log_sfrac 14 1 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz129) Bool.false ep946 ep947 1000008688085728 ep948 11885257605732069 4503599627370496 31250271502679 90500893000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 4807063014 8589934592 24973259072661432 36028797018963968 2896028576 1000000000000000 rfl rfl rfl rfl (ep951 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1110 := nat_lit 30831767987588589477167104

noncomputable def ep1111 := nat_lit 2475880078570760549798248448

noncomputable def ep1112 := BSN.sin_dyadic_bound_f 438145775484 35184372088832 1 0 17179869184 5797713458 0 1 1 0 1 1 213932837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 438145775484) (BSN.sinEvenQ 35184372088832) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 438145775484) (BSN.sinOddQ 35184372088832) 0 0 rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast 3103612610407) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1113 := @Enclosure.Real.IsNear.cos_image qz207 qz443 Bool.false 3103612610407 17179869184 51 2147483648 Bool.false 213932837 17179869184 1 2896028576 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 406796712071391525663 2251799813685248000 1069603042722194133 ep1108 3103612610407 17179869184 51 2147483648 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 3103612610407 17179869184) (BSN.cos_reduce3 qz443 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1110) (@Nat.cast Real Real.instNatCast ep1111)) 226375608064910080 72057594037927936 Bool.false 213932837 17179869184 28 1000000000000000 5792057152 2896028576 (BSN.sin_reduce_arg_pos_rat_q3 3103612610407 17179869184 226375608064910080 72057594037927936 28 ep1110 ep1111 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213932837 17179869184 ep1110 ep1111 438145775484 35184372088832 5797713458 5792057152 (ep1112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1114 := nat_lit 36853141500324590389180513083369294744898273536

noncomputable def ep1115 := nat_lit 36779892980781332600600328651607420406849738932406452224

noncomputable def ep1116 := nat_lit 551698394711719989009004929774111306102746083986096783360

noncomputable def ep1117 := BSN.cos_dyadic_bound_f 438145775484 35184372088832 2 1 17179869184 5797713458 ep1114 ep1115 ep1114 ep1114 ep1116 ep1114 17178537129 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 438145775484) (BSN.cosEvenQ 35184372088832) 0 1 ep1114 ep1115 ep1114 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 438145775484) (BSN.cosOddQ 35184372088832) 0 1 ep1114 ep1116 ep1114 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1118 := @Enclosure.Real.IsNear.sin_image qz207 qz443 Bool.false 3103612610407 17179869184 51 2147483648 Bool.true 17178537129 17179869184 1 2896028576 (@Enclosure.Real.IsNear.recentre' qz207 Bool.false 406796712071391525663 2251799813685248000 1069603042722194133 ep1108 3103612610407 17179869184 51 2147483648 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 3103612610407 17179869184) (BSN.sin_reduce3 qz443 (@HDiv.hDiv Real Real Real qz2 (@Nat.cast Real Real.instNatCast ep1110) (@Nat.cast Real Real.instNatCast ep1111)) 226375608064910080 72057594037927936 Bool.false 17178537129 17179869184 28 1000000000000000 5792057152 2896028576 (BSN.sin_reduce_arg_pos_rat_q3 3103612610407 17179869184 226375608064910080 72057594037927936 28 ep1110 ep1111 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 17178537129 17179869184 ep1110 ep1111 438145775484 35184372088832 5797713458 5792057152 (ep1117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1119 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz233 qz205) (@HMul.hMul Real Real Real qz0 qz233 qz206) Bool.false 357971890756567 295147905179352825856 82044698054506193 ep893 Bool.false 28744691571121539 295147905179352825856 1617356535872138949 ep893 (@Enclosure.Real.IsNear.mulLit_ff qz233 qz205 1673291 17179869184 1 17179869184 213932837 17179869184 4682654407 194349187846897664 357971890756567 295147905179352825856 82044698054506193 ep893 qz432 (@Enclosure.Real.IsNear.recentre' qz205 Bool.false 213932837 17179869184 149844941024 6219174011100725248 213932837 17179869184 4682654407 194349187846897664 (ep1113 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz233 qz206 1673291 17179869184 1 17179869184 17178537129 17179869184 4682654407 194349187846897664 28744691571121539 295147905179352825856 1617356535872138949 ep893 qz432 (@Enclosure.Real.IsNear.neg qz208 Bool.true 17178537129 17179869184 4682654407 194349187846897664 (@Enclosure.Real.IsNear.recentre' qz208 Bool.true 17178537129 17179869184 149844941024 6219174011100725248 17178537129 17179869184 4682654407 194349187846897664 (ep1118 rfl rfl) rfl)) rfl)

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 4449700260287 10000000000 0 1 28744691571121539 295147905179352825856 1617356535872138949 ep893 ep1055

noncomputable def ep1121 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 3514150087 120000000 0 1 Bool.false 4449700260287 10000000000 0 1 ep1104

noncomputable def ep1122 := @Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 357971890756567 295147905179352825856 82044698054506193 ep893 Bool.false 28744691571121539 295147905179352825856 1617356535872138949 ep893

noncomputable def ep1123 := nat_lit 33671053461814974321474631

noncomputable def ep1124 := nat_lit 11805916207174113034240000000

noncomputable def ep1125 := nat_lit 270649219583099795643068503

noncomputable def ep1126 := nat_lit 152635137061775748011665653760000000

noncomputable def ep1127 := nat_lit 1592867615474925709254554729

noncomputable def ep1128 := nat_lit 365074314288304529505353457391

noncomputable def ep1129 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz245) ep1123 ep1124 ep1125 ep1126 ep1127 ep1046 ep1128

noncomputable def ep1130 := nat_lit 118184670541785066012052299312252550024054922280960000000

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz246 3514150087 120000000 0 1 28744691571121539 295147905179352825856 1617356535872138949 ep893 ep1123

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz245 4449700260287 10000000000 0 1 357971890756567 295147905179352825856 82044698054506193 ep893 ep1127

noncomputable abbrev qz444 := (@ep1107 ep893 (BSN.cpow_neg_s_sub_mk qz150 68454 1000 14 3 105413504 qz151 rfl EMRow16.d15) ep1119)

noncomputable def ep1133 := ep1050 (@ep1057 ep1049 ep1058 ep1040 ep1041 ep1042 ep1043 (@ep1059 ep1052 ep1053 ep1054 ep1105 (ep1106 qz444) rfl) (@ep1120 ep1046 ep1056 ep1049 ep1121 (ep1122 qz444) rfl) rfl rfl) (@ep1129 ep1049 ep1130 ep1045 ep1046 ep1047 ep1049 (@ep1131 ep1124 ep1125 ep1126 ep1105 (ep1122 qz444) rfl) (@ep1132 ep1046 ep1128 ep1049 ep1121 (ep1106 qz444) rfl) rfl rfl)

noncomputable def ep1134 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (Complex.im (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) ep1045 ep1046 ep1047 ep1049 ep1045 ep1046 ep1047

noncomputable def ep1135 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236) Bool.true ep1040 ep1041 ep1042 ep1043 Bool.false ep1045 ep1046 ep1047

noncomputable def ep1136 := @ep1010 26814913220304987 31525197391593472 17600389805 31525197391593472 (@ep1011 1 1835008 (ep1012 (@ep1013 524288 1 524288 (ep1014 (@ep1015 4698200116 1174550029 250000 0 1 (ep1019 rfl) (ep1022 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1023 469 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)) (@ep1024 469 17179869184 746175057 17179869184 469 17179869184 (@ep1029 373087294 373087763 8589934592 (@ep1035 ep1036 ep1037 ep1038 ep1039 ep1025 ep1026 ep1027 ep1028 (@ep1044 ep1043 ep1030 ep1031 ep1032 ep1033 (@ep1048 ep1049 ep1133) (@ep1048 ep1049 ep1133) rfl) (@ep1134 ep1049 ep1034 ep1036 ep1037 ep1038 (@ep1135 ep1049 ep1133) (@ep1135 ep1049 ep1133) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow16.d17 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 qz235 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)))) Bool.false 248283917657891635 283726776524341248 63537064257599 851180329573023744 := ep1008 (ep1009 ep1136) rfl rfl

noncomputable def EMRow16.d18 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz445 := (EMRow16.d3 qz454 qz466 (@Enclosure.dec_le_dec qz454 qz466 65801 1000 68454 1000 (@Eq.refl Real qz454) (@Eq.refl Real qz466) rfl rfl rfl) 14 14 1 1)

noncomputable abbrev qz257 := qz445

noncomputable def ep1137 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz257 (@Enclosure.dec_nonneg qz17 65801 1000 qz18) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 14 rfl)

noncomputable abbrev qz258 := (Zeta.Certificates.ZIntervalEM.fstVal qz445)

noncomputable def ep1138 := @Enclosure.Real.IsNear.pos_val qz258 ep138 ep139

noncomputable def ep1139 := @Enclosure.Real.IsNear.of_eq qz258 (hardyZApproximantEM 1 14 qz17) Bool.false

noncomputable abbrev qz259 := (Zeta.Certificates.ZIntervalEM.sndVal qz445)

noncomputable def ep1140 := BSN.mul_neg_of_pos_neg_r qz258 qz259 (@ep1138 ep140 ep141 (@ep1139 ep138 ep139 ep140 ep141 (@Eq.refl Real (hardyZApproximantEM 1 14 qz17)) EMRow16.d9) rfl rfl rfl)

noncomputable def ep1141 := @Enclosure.Real.IsNear.neg_val qz259 ep526 ep527

noncomputable def ep1142 := @Enclosure.Real.IsNear.of_eq qz259 (hardyZApproximantEM 1 14 qz150) Bool.true

noncomputable def ep1143 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz258) (BSN.hardyZErrorBoundStrong 1 14 qz17)

noncomputable def ep1144 := @Enclosure.norm_gt_of_isNear qz258 (BSN.hardyZErrorBoundStrong 1 14 qz17) Bool.false

noncomputable def ep1145 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 14 qz17) (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))) Bool.false 19612535234291 26388279066624 3825227581825 53198770598313984 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz6 1 14))) (@HMul.hMul Real Real Real qz0 qz210 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz6 (@ascPochhammer Complex Complex.instSemiring 3))) qz213)))))

noncomputable def ep1146 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz259) (BSN.hardyZErrorBoundStrong 1 14 qz150)

noncomputable def ep1147 := @Enclosure.norm_gt_of_isNear qz259 (BSN.hardyZErrorBoundStrong 1 14 qz150) Bool.true

noncomputable def ep1148 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 14 qz150) (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 qz235 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)))) Bool.false 248283917657891635 283726776524341248 63537064257599 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz336 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 14))) (@HMul.hMul Real Real Real qz0 qz235 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz46 (@HMul.hMul Complex Complex Complex qz46 (@HDiv.hDiv Complex Complex Complex qz53 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz211)) ↑qz212) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz236)))))

noncomputable def ep1149 := @List.cons EMRow16.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz257 (ep1137 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 14 rfl) (ep1140 (@ep1141 ep528 ep529 (@ep1142 ep526 ep527 ep528 ep529 (@Eq.refl Real (hardyZApproximantEM 1 14 qz150)) EMRow16.d11) rfl rfl rfl)) (ep1143 (hardyZErrorBoundEM 1 14 qz17) (BSN.hardyZErrorBoundEM_le_strong 1 14 qz17 rfl) (@ep1144 Bool.false ep138 ep139 ep140 ep141 19612535234291 26388279066624 3825227581825 53198770598313984 (@ep1139 ep138 ep139 ep140 ep141 (@Eq.refl Real (hardyZApproximantEM 1 14 qz17)) EMRow16.d9) (ep1145 EMRow16.d16) rfl rfl rfl rfl rfl)) (ep1146 (hardyZErrorBoundEM 1 14 qz150) (BSN.hardyZErrorBoundEM_le_strong 1 14 qz150 rfl) (@ep1147 Bool.false ep526 ep527 ep528 ep529 248283917657891635 283726776524341248 63537064257599 851180329573023744 (@ep1142 ep526 ep527 ep528 ep529 (@Eq.refl Real (hardyZApproximantEM 1 14 qz150)) EMRow16.d11) (ep1148 EMRow16.d17) rfl rfl rfl rfl rfl)))) (@List.nil EMRow16.d0)

noncomputable abbrev qz446 := (@Enclosure.dec_le_dec qz454 qz466 65801 1000 68454 1000 (@Eq.refl Real qz454) (@Eq.refl Real qz466) rfl rfl rfl)

noncomputable abbrev qz260 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1149 (@List.IsChain.singleton EMRow16.d1 EMRow16.d18 (EMRow16.d2 qz275 qz377 qz446))))

noncomputable abbrev qz447 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1150 := And (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz447 qz260)) (@Option.some Real qz17))

noncomputable def ep1151 := ep1150 (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz447 qz260)) (@Option.some Real qz150))

noncomputable def ep1152 := @And.intro (@Eq Nat (@List.length qz447 qz260) 1) ep1151

noncomputable def ep1153 := @And.intro (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz447 qz260)) (@Option.some Real qz17))

noncomputable def ep1154 := @ep1153 (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz447 qz260)) (@Option.some Real qz150))

noncomputable abbrev qz261 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1149 (@List.IsChain.singleton EMRow16.d1 EMRow16.d18 (EMRow16.d2 qz275 qz377 qz446)))

theorem EMRow16.d19 : Zeta.Certificates.BatchSpec 1 65801 1000 68454 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz447 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz447 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz17)) (@Eq (Option Real) (@Option.map qz447 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz447 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz150)))) qz261 (ep1152 (@Eq.refl Nat 1) (ep1154 (@Eq.refl (Option Real) (@Option.some Real qz17)) (@Eq.refl (Option Real) (@Option.some Real qz150))))

theorem solution : Zeta.Certificates.BatchSpec 1 65801 1000 68454 1000 := EMRow16.d19
#print axioms solution
#check solution
