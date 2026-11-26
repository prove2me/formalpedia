-- Prove2me | solution 1 for RHHeight1000.em_main_0032_0032
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:17:42.09088+00:00
-- url     : https://prove2.me/submissions/4c4c14c2-aa78-402e-9ede-c5134ecf72d5

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow32.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow32.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow32.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow32.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow32.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 25000000013477 6738500000000000000 4138529546116343 2251799813685248 25000000013477 6738500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 269540 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 25000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000539080 269540000000000000000 4138529546116343 2251799813685248 25000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 269540 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 25000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000539080 269540000000000000000 4138529546116343 2251799813685248 25000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow32.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 269540 1200336 1048576 1 269540 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 269540 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 269540 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 269540 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 269540 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 269540 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 269540 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow32.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz599 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 104500 1000)))

noncomputable abbrev qz534 := qz599

noncomputable abbrev qz271 := qz534

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz600 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz535 := qz600

noncomputable abbrev qz272 := qz535

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz536 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz536

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz537 := (@Neg.neg Complex Complex.instNeg qz599)

noncomputable abbrev qz274 := qz537

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz275 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz7)) Bool.false 348830576303 1099511627776 195898957597379 74090591037685760 Bool.false 58085757325 549755813888 12246889768879 4630661939855360

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz7) Bool.false 683889931633 1099511627776 35061748270929 14818118207537152 Bool.true 632288355 8589934592 17538509536553 7409059103768576 Bool.true

noncomputable abbrev qz276 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7)) Bool.false 683889931633 1099511627776 35061748270929 14818118207537152 Bool.true 632288355 8589934592 17538509536553 7409059103768576

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) Bool.false 956260324633 1099511627776 153315610728217 74090591037685760 Bool.false 232943411835 1099511627776 153384907710207 74090591037685760 Bool.true

noncomputable abbrev qz277 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7)) Bool.false 956260324633 1099511627776 153315610728217 74090591037685760 Bool.false 232943411835 1099511627776 153384907710207 74090591037685760

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) Bool.false 817617522745 1099511627776 129588566375257 74090591037685760 Bool.true 48495478815 274877906944 64806242037271 37045295518842880 Bool.false

noncomputable abbrev qz278 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7)) Bool.false 817617522745 1099511627776 129588566375257 74090591037685760 Bool.true 48495478815 274877906944 64806242037271 37045295518842880

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) Bool.false 190804621515 274877906944 5182133532507 3704529551884288 Bool.true 682679451503 1099511627776 20720836161967 14818118207537152 Bool.false

noncomputable abbrev qz279 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7)) Bool.false 190804621515 274877906944 5182133532507 3704529551884288 Bool.true 682679451503 1099511627776 20720836161967 14818118207537152

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) Bool.false 7738386213 34359738368 9322098031241 9261323879710720 Bool.true 491899800795 1099511627776 74580041303903 74090591037685760 Bool.false

noncomputable abbrev qz538 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz280 := qz538

noncomputable abbrev qz8 := qz280

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 7738386213 34359738368 9322098031241 9261323879710720 Bool.true 491899800795 1099511627776 74580041303903 74090591037685760

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 167100527303 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 1099511627776 41024147224309 74090591037685760 Bool.true

noncomputable abbrev qz539 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz281 := qz539

noncomputable abbrev qz9 := qz281

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 167100527303 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 1099511627776 41024147224309 74090591037685760

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz282 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz282

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz540 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz540))

noncomputable abbrev qz601 := (Enclosure.sfrac Bool.false 104500 1000)

noncomputable abbrev qz541 := qz601

noncomputable abbrev qz283 := qz541

noncomputable abbrev qz284 := (Real.log (Enclosure.sfrac Bool.false 2 1))

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz283 qz284)

noncomputable abbrev qz13 := qz283

noncomputable abbrev qz285 := (@Eq.refl Real qz541)

noncomputable abbrev qz14 := qz285

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.true 382655286585 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 1099511627776 41024147224309 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz540) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz540) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz540 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz540 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 134770 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 20921564565936714913839073992585681

noncomputable def ep57 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep58 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz286 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz287 := (BSN.cosOddQ 2147483648)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 380319453 2147483648 2 1 1048576 269804 ep56 ep57 ep56 ep56 ep58 ep56 1032174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 380319453) qz286 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 380319453) qz287 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (Enclosure.Real.IsNear.const Bool.false 104500 1000)

noncomputable abbrev qz288 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4747017) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz289 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 134770 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 134770 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz12 qz288 Bool.false 4747017 65536 209 269540 Bool.true 1032174 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz284 104500 1000 0 1 363408 524288 1 134770 4747017 65536 209 269540 qz16 qz289 rfl) (Enclosure.sfrac_false_div 4747017 65536) (BSN.cos_reduce2 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1672662647755551801344) qz290) 226375608064910080 72057594037927936 Bool.false 1032174 1048576 11 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 4747017 65536 226375608064910080 72057594037927936 11 1672662647755551801344 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1032174 1048576 1672662647755551801344 9444732965739290427392 380319453 2147483648 269804 269540 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep62 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz291 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz292 := (BSN.sinOddQ 2147483648)

noncomputable def ep63 := BSN.sin_dyadic_bound_f 380319453 2147483648 2 1 1048576 269804 ep56 ep61 ep56 ep56 ep62 ep56 184733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 380319453) qz291 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 380319453) qz292 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz12 qz288 Bool.false 4747017 65536 209 269540 Bool.true 184733 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz284 104500 1000 0 1 363408 524288 1 134770 4747017 65536 209 269540 qz16 qz289 rfl) (Enclosure.sfrac_false_div 4747017 65536) (BSN.sin_reduce2 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1672662647755551801344) qz290) 226375608064910080 72057594037927936 Bool.false 184733 1048576 11 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 4747017 65536 226375608064910080 72057594037927936 11 1672662647755551801344 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 184733 1048576 1672662647755551801344 9444732965739290427392 380319453 2147483648 269804 269540 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz293 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.true 382655286585 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 1099511627776 41024147224309 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz11 (Real.cos qz12) 741455 1048576 1 1048576 516087 524288 211 269540 382655286585 549755813888 20540626018047 37045295518842880 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.true 1032174 1048576 28436470 36325905800 516087 524288 211 269540 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 184733 1048576 211 269540 136971206515 1099511627776 41024147224309 74090591037685760 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 184733 1048576 211 269540 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 184733 1048576 28436470 36325905800 184733 1048576 211 269540 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz294 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz17 := qz294

noncomputable def ep66 := @ep51 382655286585 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 1099511627776 41024147224309 74090591037685760 Bool.false 167100527303 167100527303 549755813888 20540626018047 37045295518842880 Bool.false 136971206515 136971206515 1099511627776 41024147224309 74090591037685760 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz17)) (ep53 ep65) rfl rfl

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz18 := (@Inv.inv Real Real.instInv (Real.sqrt qz295))

noncomputable abbrev qz296 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz19 := (@HMul.hMul Real Real Real qz267 qz283 qz296)

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)))) Bool.true 43286347895 549755813888 16747766106917 37045295518842880 Bool.true 314435503655 549755813888 16777947039797 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 3 qz14 rfl)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz295) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz295) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 134770 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := BSN.sin_dyadic_bound_f 293785540 2147483648 1 0 1048576 269804 0 1 1 0 1 1 143002 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 293785540) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 293785540) qz292 0 0 rfl) rfl rfl

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz21 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 120381701) qz20)

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 134770 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 134770 rfl rfl rfl (ep69 rfl)))

noncomputable def ep71 := @Enclosure.Real.IsNear.cos_image qz19 qz297 Bool.false 120381701 1048576 209 269540 Bool.true 143002 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz296 104500 1000 0 1 575989 524288 1 134770 120381701 1048576 209 269540 qz16 qz298 rfl) (Enclosure.sfrac_false_div 120381701 1048576) (BSN.cos_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20673319540652802834432) qz21) 226375608064910080 72057594037927936 Bool.false 143002 1048576 18 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 120381701 1048576 226375608064910080 72057594037927936 18 20673319540652802834432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 143002 1048576 20673319540652802834432 151115727451828646838272 293785540 2147483648 269804 269540 (ep70 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep72 := nat_lit 7449406349233062762820589990560000

noncomputable def ep73 := BSN.cos_dyadic_bound_f 293785540 2147483648 2 1 1048576 269804 ep72 ep57 ep72 ep72 ep58 ep72 1038778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 293785540) qz286 0 1 ep72 ep57 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 293785540) qz287 0 1 ep72 ep58 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable def ep74 := @Enclosure.Real.IsNear.sin_image qz19 qz297 Bool.false 120381701 1048576 209 269540 Bool.false 1038778 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz296 104500 1000 0 1 575989 524288 1 134770 120381701 1048576 209 269540 qz16 qz298 rfl) (Enclosure.sfrac_false_div 120381701 1048576) (BSN.sin_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20673319540652802834432) qz21) 226375608064910080 72057594037927936 Bool.false 1038778 1048576 18 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 120381701 1048576 226375608064910080 72057594037927936 18 20673319540652802834432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1038778 1048576 20673319540652802834432 151115727451828646838272 293785540 2147483648 269804 269540 (ep73 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz299 := (@Enclosure.Real.IsNear.recentre' qz18 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep68 rfl rfl) rfl)

noncomputable def ep75 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz19)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19))) Bool.true 43286347895 549755813888 16747766106917 37045295518842880 Bool.true 314435503655 549755813888 16777947039797 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz18 (Real.cos qz19) 605395 1048576 1 1048576 71501 524288 211 269540 43286347895 549755813888 16747766106917 37045295518842880 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz19) Bool.true 143002 1048576 28436470 36325905800 71501 524288 211 269540 (ep71 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz18 (@Neg.neg Real Real.instNeg (Real.sin qz19)) 605395 1048576 1 1048576 519389 524288 211 269540 314435503655 549755813888 16777947039797 37045295518842880 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz19) Bool.false 519389 524288 211 269540 (@Enclosure.Real.IsNear.recentre' (Real.sin qz19) Bool.false 1038778 1048576 28436470 36325905800 519389 524288 211 269540 (ep74 rfl rfl) rfl)) rfl)

noncomputable def ep76 := @ep49 43286347895 549755813888 16747766106917 37045295518842880 Bool.true 314435503655 549755813888 16777947039797 37045295518842880 Bool.false 68067564971319890018304 7738386213 34359738368 9322098031241 9261323879710720 Bool.true 270424775337400294440960 491899800795 1099511627776 74580041303903 74090591037685760 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep75) rfl rfl

noncomputable abbrev qz542 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz542))

noncomputable abbrev qz300 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz283 qz300)

noncomputable def ep77 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 128897531811 274877906944 7266471600053 18522647759421440 Bool.true 47694912677 274877906944 7256034876483 18522647759421440 (BSN.cpow_neg_s_mk qz13 104500 1000 4 qz14 rfl)

noncomputable def ep78 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz542) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz542) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz542 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz542 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep79 := nat_lit 318077276165597140789031982421875

noncomputable def ep80 := nat_lit 49379992292270016474244603430625

noncomputable def ep81 := nat_lit 20095619060363156210525625

noncomputable def ep82 := BSN.log_dyadic_bound 3 5 14 13 ep79 524288 134770 ep80 ep81 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep80 ep79 ep81 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep83 := nat_lit 335499151247772813450833582432937841

noncomputable def ep84 := BSN.cos_dyadic_bound_f 761066939 2147483648 2 1 1048576 269804 ep83 ep57 ep83 ep83 ep58 ep83 983412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 761066939) qz286 0 1 ep83 ep57 ep83 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 761066939) qz287 0 1 ep83 ep58 ep83 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151904753) qz20)

noncomputable abbrev qz302 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 134770 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 134770 rfl rfl rfl (ep82 rfl)))

noncomputable def ep85 := @Enclosure.Real.IsNear.cos_image qz23 qz301 Bool.false 151904753 1048576 209 269540 Bool.false 983412 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz300 104500 1000 0 1 726817 524288 1 134770 151904753 1048576 209 269540 qz16 qz302 rfl) (Enclosure.sfrac_false_div 151904753 1048576) (BSN.cos_reduce0 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53555324802485511520256) qz21) 226375608064910080 72057594037927936 Bool.false 983412 1048576 23 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 151904753 1048576 226375608064910080 72057594037927936 23 53555324802485511520256 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 983412 1048576 53555324802485511520256 151115727451828646838272 761066939 2147483648 269804 269540 (ep84 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep86 := BSN.sin_dyadic_bound_f 761066939 2147483648 2 1 1048576 269804 ep83 ep61 ep83 ep83 ep62 ep83 363884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 761066939) qz291 0 1 ep83 ep61 ep83 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 761066939) qz292 0 1 ep83 ep62 ep83 rfl rfl rfl rfl) rfl rfl

noncomputable def ep87 := @Enclosure.Real.IsNear.sin_image qz23 qz301 Bool.false 151904753 1048576 209 269540 Bool.false 363884 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz300 104500 1000 0 1 726817 524288 1 134770 151904753 1048576 209 269540 qz16 qz302 rfl) (Enclosure.sfrac_false_div 151904753 1048576) (BSN.sin_reduce0 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53555324802485511520256) qz21) 226375608064910080 72057594037927936 Bool.false 363884 1048576 23 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 151904753 1048576 226375608064910080 72057594037927936 23 53555324802485511520256 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 363884 1048576 53555324802485511520256 151115727451828646838272 761066939 2147483648 269804 269540 (ep86 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep78 rfl rfl) rfl)

noncomputable def ep88 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 128897531811 274877906944 7266471600053 18522647759421440 Bool.true 47694912677 274877906944 7256034876483 18522647759421440 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 524287 1048576 1 1048576 245853 262144 211 269540 128897531811 274877906944 7266471600053 18522647759421440 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 983412 1048576 28436470 36325905800 245853 262144 211 269540 (ep85 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 524287 1048576 1 1048576 90971 262144 211 269540 47694912677 274877906944 7256034876483 18522647759421440 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 90971 262144 211 269540 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 363884 1048576 28436470 36325905800 90971 262144 211 269540 (ep87 rfl rfl) rfl)) rfl)

noncomputable def ep89 := @ep47 128897531811 274877906944 7266471600053 18522647759421440 Bool.true 47694912677 274877906944 7256034876483 18522647759421440 Bool.false 6555996874660663787520 190804621515 274877906944 5182133532507 3704529551884288 Bool.true 187653498742822594936832 682679451503 1099511627776 20720836161967 14818118207537152 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep76 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep77 ep88) rfl rfl

noncomputable abbrev qz543 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz543))

noncomputable abbrev qz304 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz283 qz304)

noncomputable def ep90 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 54399036685 1099511627776 25945895725117 74090591037685760 Bool.false 488697536243 1099511627776 26008303264707 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 5 qz14 rfl)

noncomputable def ep91 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz543) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz543) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep92 := nat_lit 11734546589655452485523914939250625

noncomputable def ep93 := nat_lit 2429970938528035899633153341031900

noncomputable def ep94 := nat_lit 824199001261152424427520000

noncomputable def ep95 := BSN.log_dyadic_bound 2 3 17 16 ep92 524288 134770 ep93 ep94 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep93 ep92 ep94 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep96 := BSN.sin_dyadic_bound_f 238067260 2147483648 1 0 1048576 269804 0 1 1 0 1 1 116005 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 238067260) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 238067260) qz292 0 0 rfl) rfl rfl

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5511121) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz306 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 134770 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 134770 rfl rfl rfl (ep95 rfl)))

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep97 := @Enclosure.Real.IsNear.cos_image qz25 qz305 Bool.false 5511121 32768 209 269540 Bool.false 116005 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz304 104500 1000 0 1 843808 524288 1 134770 5511121 32768 209 269540 qz16 qz306 rfl) (Enclosure.sfrac_false_div 5511121 32768) (BSN.cos_reduce3 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 523515441204724498432) qz307) 226375608064910080 72057594037927936 Bool.false 116005 1048576 26 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 5511121 32768 226375608064910080 72057594037927936 26 523515441204724498432 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 116005 1048576 523515441204724498432 4722366482869645213696 238067260 2147483648 269804 269540 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep98 := nat_lit 3212171275221905712107525337760000

noncomputable def ep99 := BSN.cos_dyadic_bound_f 238067260 2147483648 2 1 1048576 269804 ep98 ep57 ep98 ep98 ep58 ep98 1042139 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 238067260) qz286 0 1 ep98 ep57 ep98 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 238067260) qz287 0 1 ep98 ep58 ep98 rfl rfl rfl rfl) rfl rfl

noncomputable def ep100 := @Enclosure.Real.IsNear.sin_image qz25 qz305 Bool.false 5511121 32768 209 269540 Bool.true 1042139 1048576 1 134770 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz304 104500 1000 0 1 843808 524288 1 134770 5511121 32768 209 269540 qz16 qz306 rfl) (Enclosure.sfrac_false_div 5511121 32768) (BSN.sin_reduce3 qz305 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 523515441204724498432) qz307) 226375608064910080 72057594037927936 Bool.false 1042139 1048576 26 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 5511121 32768 226375608064910080 72057594037927936 26 523515441204724498432 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042139 1048576 523515441204724498432 4722366482869645213696 238067260 2147483648 269804 269540 (ep99 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep91 rfl rfl) rfl)

noncomputable def ep101 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 54399036685 1099511627776 25945895725117 74090591037685760 Bool.false 488697536243 1099511627776 26008303264707 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz25) 468937 1048576 1 1048576 116005 1048576 211 269540 54399036685 1099511627776 25945895725117 74090591037685760 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 116005 1048576 28436470 36325905800 116005 1048576 211 269540 (ep97 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 468937 1048576 1 1048576 1042139 1048576 211 269540 488697536243 1099511627776 26008303264707 74090591037685760 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 1042139 1048576 211 269540 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 1042139 1048576 28436470 36325905800 1042139 1048576 211 269540 (ep100 rfl rfl) rfl)) rfl)

noncomputable def ep102 := @ep45 54399036685 1099511627776 25945895725117 74090591037685760 Bool.false 488697536243 1099511627776 26008303264707 74090591037685760 Bool.false 224744993332883913441280 817617522745 1099511627776 129588566375257 74090591037685760 Bool.true 213285371406628694261760 48495478815 274877906944 64806242037271 37045295518842880 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep89 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep90 ep101) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz26 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz544 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz283 qz544)

noncomputable def ep103 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 4332587559 34359738368 74147013603 231533096992768 Bool.false 426925327095 1099511627776 4754484727133 14818118207537152 (BSN.cpow_neg_s_mk qz13 104500 1000 6 qz14 rfl)

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep104 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz310) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz310) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep105 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 134770 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep106 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz544 104500 1000 0 1 4034681531866359 2251799813685248 50000000013477 6738500000000000000 843248440160069031 4503599627370496 10450000002816693 13477000000000000000 qz16 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 33845361775666394038272 18889465931478580854784 1000000000269540 134770000000000000000 4034681531866359 2251799813685248 50000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep105 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep107 := nat_lit 206756406255998504170588192509670416

noncomputable def ep108 := BSN.sin_dyadic_bound_f 674317986 2147483648 2 1 1048576 269804 ep107 ep61 ep107 ep107 ep62 ep107 323872 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 674317986) qz291 0 1 ep107 ep61 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 674317986) qz292 0 1 ep107 ep62 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 196334077) qz20)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz27 qz311 Bool.false 196334077 1048576 407 524288 Bool.false 323872 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 843248440160069031 4503599627370496 10450000002816693 13477000000000000000 196334077 1048576 407 524288 (ep106 rfl) rfl) (Enclosure.sfrac_false_div 196334077 1048576) (BSN.cos_reduce3 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47450909884301520666624) qz21) 226375608064910080 72057594037927936 Bool.false 323872 1048576 29 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 196334077 1048576 226375608064910080 72057594037927936 29 47450909884301520666624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 323872 1048576 47450909884301520666624 151115727451828646838272 674317986 2147483648 269804 269540 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := BSN.cos_dyadic_bound_f 674317986 2147483648 2 1 1048576 269804 ep107 ep57 ep107 ep107 ep58 ep107 997305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 674317986) qz286 0 1 ep107 ep57 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 674317986) qz287 0 1 ep107 ep58 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz27 qz311 Bool.false 196334077 1048576 407 524288 Bool.true 997305 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 843248440160069031 4503599627370496 10450000002816693 13477000000000000000 196334077 1048576 407 524288 (ep106 rfl) rfl) (Enclosure.sfrac_false_div 196334077 1048576) (BSN.sin_reduce3 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47450909884301520666624) qz21) 226375608064910080 72057594037927936 Bool.false 997305 1048576 29 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 196334077 1048576 226375608064910080 72057594037927936 29 47450909884301520666624 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 997305 1048576 47450909884301520666624 151115727451828646838272 674317986 2147483648 269804 269540 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz312 := (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep104 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 4332587559 34359738368 74147013603 231533096992768 Bool.false 426925327095 1099511627776 4754484727133 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ff qz26 (Real.cos qz27) 428079 1048576 1 1048576 10121 32768 27687839 35329146880 4332587559 34359738368 74147013603 231533096992768 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 323872 1048576 55375678 70658293760 10121 32768 27687839 35329146880 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz26 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 428079 1048576 1 1048576 997305 1048576 27687839 35329146880 426925327095 1099511627776 4754484727133 14818118207537152 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 997305 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 997305 1048576 55375678 70658293760 997305 1048576 27687839 35329146880 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep43 4332587559 34359738368 74147013603 231533096992768 Bool.false 426925327095 1099511627776 4754484727133 14818118207537152 Bool.false 32856854566088625618944 956260324633 1099511627776 153315610728217 74090591037685760 Bool.false 64030997481598998282240 232943411835 1099511627776 153384907710207 74090591037685760 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep102 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep103 ep112) rfl rfl

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz313))

noncomputable abbrev qz545 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz283 qz545)

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 34046299125 137438953472 5498282656607 18522647759421440 Bool.true 313876321275 1099511627776 22000187655323 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 7 qz14 rfl)

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz313) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz313) (Real.sqrt qz314) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz314) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 134770 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz545 104500 1000 0 1 4381796493761783 2251799813685248 50000000013477 6738500000000000000 915795467196212647 4503599627370496 10450000002816693 13477000000000000000 qz16 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 50000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 36757173121942042968064 18889465931478580854784 1000000000269540 134770000000000000000 4381796493761783 2251799813685248 50000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 5549509813524096063205781461658367121

noncomputable def ep119 := BSN.sin_dyadic_bound_f 1534841933 2147483648 2 1 1048576 269804 ep118 ep61 ep118 ep118 ep62 ep118 687240 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1534841933) qz291 0 1 ep118 ep61 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1534841933) qz292 0 1 ep118 ep62 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6663289) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep120 := @Enclosure.Real.IsNear.cos_image qz29 qz315 Bool.false 6663289 32768 407 524288 Bool.true 687240 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 915795467196212647 4503599627370496 10450000002816693 13477000000000000000 6663289 32768 407 524288 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 6663289 32768) (BSN.cos_reduce1 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3375153104626015797248) qz307) 226375608064910080 72057594037927936 Bool.false 687240 1048576 32 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 6663289 32768 226375608064910080 72057594037927936 32 3375153104626015797248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 687240 1048576 3375153104626015797248 4722366482869645213696 1534841933 2147483648 269804 269540 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep121 := nat_lit 198312832191850701186739290535391490965193690713737943713347262080646637337121

noncomputable def ep122 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep123 := nat_lit 30797059170400247460704981603080981659921534074211743263500934828013828641

noncomputable def ep124 := nat_lit 594876902457211303065296461642968310932261229073065407653514784372283884354081

noncomputable def ep125 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep126 := BSN.cos_dyadic_bound_f 1534841933 2147483648 3 2 1048576 269804 ep121 ep122 ep123 ep124 ep125 ep123 791967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1534841933) qz286 0 2 ep121 ep122 ep123 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1534841933) qz287 0 2 ep124 ep125 ep123 rfl rfl rfl rfl) rfl rfl

noncomputable def ep127 := @Enclosure.Real.IsNear.sin_image qz29 qz315 Bool.false 6663289 32768 407 524288 Bool.false 791967 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 915795467196212647 4503599627370496 10450000002816693 13477000000000000000 6663289 32768 407 524288 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 6663289 32768) (BSN.sin_reduce1 qz315 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3375153104626015797248) qz307) 226375608064910080 72057594037927936 Bool.false 791967 1048576 32 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 6663289 32768 226375608064910080 72057594037927936 32 3375153104626015797248 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 791967 1048576 3375153104626015797248 4722366482869645213696 1534841933 2147483648 269804 269540 (ep126 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz316 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep115 rfl rfl) rfl)

noncomputable def ep128 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 34046299125 137438953472 5498282656607 18522647759421440 Bool.true 313876321275 1099511627776 22000187655323 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 396325 1048576 1 1048576 85905 131072 27687839 35329146880 34046299125 137438953472 5498282656607 18522647759421440 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 687240 1048576 55375678 70658293760 85905 131072 27687839 35329146880 (ep120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 791967 1048576 27687839 35329146880 313876321275 1099511627776 22000187655323 74090591037685760 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 791967 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 791967 1048576 55375678 70658293760 791967 1048576 27687839 35329146880 (ep127 rfl rfl) rfl)) rfl)

noncomputable def ep129 := @ep41 34046299125 137438953472 5498282656607 18522647759421440 Bool.true 313876321275 1099511627776 22000187655323 74090591037685760 Bool.false 93993116493677147979776 683889931633 1099511627776 35061748270929 14818118207537152 Bool.true 88986674999021996605440 632288355 8589934592 17538509536553 7409059103768576 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep128) rfl rfl

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz317))

noncomputable abbrev qz546 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz267 qz283 qz546)

noncomputable def ep130 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz275 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.true 167529677665 549755813888 10295108121367 37045295518842880 Bool.false 98552212045 549755813888 10282570468267 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 8 qz14 rfl)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep131 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz317) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz317) (Real.sqrt qz318) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep132 := BSN.log_dyadic_bound 0 16 1 0 1 524288 134770 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep133 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz546 104500 1000 0 1 9364972152248037 4503599627370496 100000000040431 13477000000000000000 1957279179819839733 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 39279540158062550581248 18889465931478580854784 1000000000404310 134770000000000000000 9364972152248037 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep134 := nat_lit 1700360482688600134082442516606236641

noncomputable def ep135 := BSN.cos_dyadic_bound_f 1141918873 2147483648 2 1 1048576 269804 ep134 ep57 ep134 ep134 ep58 ep134 903790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1141918873) qz286 0 1 ep134 ep57 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1141918873) qz287 0 1 ep134 ep58 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227857285) qz20)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz31 qz319 Bool.false 227857285 1048576 407 524288 Bool.true 903790 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 1957279179819839733 9007199254740992 20900000008450079 26954000000000000000 227857285 1048576 407 524288 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 227857285 1048576) (BSN.cos_reduce2 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80355397115474062868480) qz21) 226375608064910080 72057594037927936 Bool.false 903790 1048576 34 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 227857285 1048576 226375608064910080 72057594037927936 34 80355397115474062868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903790 1048576 80355397115474062868480 151115727451828646838272 1141918873 2147483648 269804 269540 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := BSN.sin_dyadic_bound_f 1141918873 2147483648 2 1 1048576 269804 ep134 ep61 ep134 ep134 ep62 ep134 531670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1141918873) qz291 0 1 ep134 ep61 ep134 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1141918873) qz292 0 1 ep134 ep62 ep134 rfl rfl rfl rfl) rfl rfl

noncomputable def ep138 := @Enclosure.Real.IsNear.sin_image qz31 qz319 Bool.false 227857285 1048576 407 524288 Bool.true 531670 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 1957279179819839733 9007199254740992 20900000008450079 26954000000000000000 227857285 1048576 407 524288 (ep133 rfl) rfl) (Enclosure.sfrac_false_div 227857285 1048576) (BSN.sin_reduce2 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80355397115474062868480) qz21) 226375608064910080 72057594037927936 Bool.false 531670 1048576 34 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 227857285 1048576 226375608064910080 72057594037927936 34 80355397115474062868480 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 531670 1048576 80355397115474062868480 151115727451828646838272 1141918873 2147483648 269804 269540 (ep137 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep131 rfl rfl) rfl)

noncomputable def ep139 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.true 167529677665 549755813888 10295108121367 37045295518842880 Bool.false 98552212045 549755813888 10282570468267 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz31) 370727 1048576 1 1048576 451895 524288 27687839 35329146880 167529677665 549755813888 10295108121367 37045295518842880 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.true 903790 1048576 55375678 70658293760 451895 524288 27687839 35329146880 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 370727 1048576 1 1048576 265835 524288 27687839 35329146880 98552212045 549755813888 10282570468267 37045295518842880 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 265835 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 531670 1048576 55375678 70658293760 265835 524288 27687839 35329146880 (ep138 rfl rfl) rfl)) rfl)

noncomputable def ep140 := @ep39 167529677665 549755813888 10295108121367 37045295518842880 Bool.false 98552212045 549755813888 10282570468267 37045295518842880 Bool.false 191771637384475851096064 348830576303 1099511627776 195898957597379 74090591037685760 Bool.false 498952856148534886400 58085757325 549755813888 12246889768879 4630661939855360 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep129 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep130 ep139) rfl rfl

theorem EMRow32.d6 : Enclosure.Complex.IsNear qz3 Bool.false 348830576303 1099511627776 195898957597379 74090591037685760 Bool.false 58085757325 549755813888 12246889768879 4630661939855360 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep140 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz32 := (BSN.headSumC qz271 17)

noncomputable abbrev qz33 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 16) qz274)

noncomputable def ep141 := @Enclosure.Complex.IsNear.of_eq qz32 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz33) Bool.false 269391073475 549755813888 41175807633389 9261323879710720 Bool.false 5041728619 274877906944 164716827411471 37045295518842880

noncomputable def ep142 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz33 Bool.false 330146465395 1099511627776 62967285724551 14818118207537152 Bool.false 199131678433 1099511627776 62974249883439 14818118207537152 Bool.false

noncomputable abbrev qz34 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz274)

noncomputable def ep143 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz34) Bool.false 330146465395 1099511627776 62967285724551 14818118207537152 Bool.false 199131678433 1099511627776 62974249883439 14818118207537152

noncomputable def ep144 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz34 Bool.false 27459778883 549755813888 149887702653807 37045295518842880 Bool.false 268738106569 1099511627776 299861403190159 74090591037685760 Bool.false

noncomputable abbrev qz35 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz274)

noncomputable def ep145 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz35) Bool.false 27459778883 549755813888 149887702653807 37045295518842880 Bool.false 268738106569 1099511627776 299861403190159 74090591037685760

noncomputable def ep146 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz35 Bool.true 10861917371 68719476736 71050427490073 18522647759421440 Bool.false 21057719875 274877906944 8884323017071 2315330969927680 Bool.false

noncomputable abbrev qz547 := (@Nat.cast Complex Complex.instNatCast 13)

noncomputable abbrev qz36 := (@HPow.hPow Complex Complex Complex qz273 qz547 qz274)

noncomputable def ep147 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz36) Bool.true 10861917371 68719476736 71050427490073 18522647759421440 Bool.false 21057719875 274877906944 8884323017071 2315330969927680

noncomputable def ep148 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz36 Bool.true 9448636397 1099511627776 53611810997963 14818118207537152 Bool.true 86323339147 549755813888 26813424067957 7409059103768576 Bool.true

noncomputable abbrev qz548 := (@Nat.cast Complex Complex.instNatCast 12)

noncomputable abbrev qz37 := (@HPow.hPow Complex Complex Complex qz273 qz548 qz274)

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz37) Bool.true 9448636397 1099511627776 53611810997963 14818118207537152 Bool.true 86323339147 549755813888 26813424067957 7409059103768576

noncomputable def ep150 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz37 Bool.false 8767432573 68719476736 125631808178623 37045295518842880 Bool.false 13402387223 137438953472 31413728910167 9261323879710720 Bool.true

noncomputable abbrev qz549 := (@Nat.cast Complex Complex.instNatCast 11)

noncomputable abbrev qz38 := (@HPow.hPow Complex Complex Complex qz273 qz549 qz274)

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz38) Bool.false 8767432573 68719476736 125631808178623 37045295518842880 Bool.false 13402387223 137438953472 31413728910167 9261323879710720

noncomputable def ep152 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz38 Bool.true 51430809841 549755813888 14606520644867 4630661939855360 Bool.true 118134766403 1099511627776 233754336254677 74090591037685760 Bool.false

noncomputable abbrev qz550 := (@Nat.cast Complex Complex.instNatCast 10)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz273 qz550 qz274)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz39) Bool.true 51430809841 549755813888 14606520644867 4630661939855360 Bool.true 118134766403 1099511627776 233754336254677 74090591037685760

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz39 Bool.true 2017417061 549755813888 53830556456113 18522647759421440 Bool.false 26902576025 137438953472 107662285613381 37045295518842880 Bool.true

noncomputable abbrev qz321 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 (@HPow.hPow Complex Complex Complex qz6 qz321 qz7)) Bool.true 2017417061 549755813888 53830556456113 18522647759421440 Bool.false 26902576025 137438953472 107662285613381 37045295518842880

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP qz3 (@HPow.hPow Complex Complex Complex qz6 qz321 qz7) Bool.false 348830576303 1099511627776 195898957597379 74090591037685760 Bool.false 58085757325 549755813888 12246889768879 4630661939855360 Bool.true

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz322))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz267 qz283 qz551)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz321 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.true 352865410425 1099511627776 19423268227073 74090591037685760 Bool.false 49524546775 549755813888 9687167462349 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 9 qz14 rfl)

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep158 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz322) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz322) (Real.sqrt qz323) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz323) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep159 := BSN.log_dyadic_bound 1 17 2 1 867 524288 134770 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep160 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 104500 1000 0 1 9895417793173221 4503599627370496 100000000040431 13477000000000000000 2068142318773203189 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 41504390431577613533184 18889465931478580854784 1000000000404310 134770000000000000000 9895417793173221 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep161 := nat_lit 119275274510207355046629863486918656

noncomputable def ep162 := BSN.cos_dyadic_bound_f 587675528 2147483648 2 1 1048576 269804 ep161 ep57 ep161 ep161 ep58 ep161 1009557 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 587675528) qz286 0 1 ep161 ep57 ep161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 587675528) qz287 0 1 ep161 ep58 ep161 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240763453) qz20)

noncomputable def ep163 := @Enclosure.Real.IsNear.cos_image qz41 qz324 Bool.false 240763453 1048576 407 524288 Bool.true 1009557 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 2068142318773203189 9007199254740992 20900000008450079 26954000000000000000 240763453 1048576 407 524288 (ep160 rfl) rfl) (Enclosure.sfrac_false_div 240763453 1048576) (BSN.cos_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41353988955897474318336) qz21) 226375608064910080 72057594037927936 Bool.false 1009557 1048576 36 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 240763453 1048576 226375608064910080 72057594037927936 36 41353988955897474318336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1009557 1048576 41353988955897474318336 151115727451828646838272 587675528 2147483648 269804 269540 (ep162 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep164 := BSN.sin_dyadic_bound_f 587675528 2147483648 2 1 1048576 269804 ep161 ep61 ep161 ep161 ep62 ep161 283382 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 587675528) qz291 0 1 ep161 ep61 ep161 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 587675528) qz292 0 1 ep161 ep62 ep161 rfl rfl rfl rfl) rfl rfl

noncomputable def ep165 := @Enclosure.Real.IsNear.sin_image qz41 qz324 Bool.false 240763453 1048576 407 524288 Bool.true 283382 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 2068142318773203189 9007199254740992 20900000008450079 26954000000000000000 240763453 1048576 407 524288 (ep160 rfl) rfl) (Enclosure.sfrac_false_div 240763453 1048576) (BSN.sin_reduce2 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41353988955897474318336) qz21) 226375608064910080 72057594037927936 Bool.false 283382 1048576 36 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 240763453 1048576 226375608064910080 72057594037927936 36 41353988955897474318336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 283382 1048576 41353988955897474318336 151115727451828646838272 587675528 2147483648 269804 269540 (ep164 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep158 rfl rfl) rfl)

noncomputable def ep166 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.true 352865410425 1099511627776 19423268227073 74090591037685760 Bool.false 49524546775 549755813888 9687167462349 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz41) 349525 1048576 1 1048576 1009557 1048576 27687839 35329146880 352865410425 1099511627776 19423268227073 74090591037685760 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.true 1009557 1048576 55375678 70658293760 1009557 1048576 27687839 35329146880 (ep163 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 349525 1048576 1 1048576 141691 524288 27687839 35329146880 49524546775 549755813888 9687167462349 37045295518842880 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 141691 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 283382 1048576 55375678 70658293760 141691 524288 27687839 35329146880 (ep165 rfl rfl) rfl)) rfl)

noncomputable def ep167 := @ep156 352865410425 1099511627776 19423268227073 74090591037685760 Bool.false 49524546775 549755813888 9687167462349 37045295518842880 Bool.true 4436347033286367772672 2017417061 549755813888 53830556456113 18522647759421440 Bool.false 59159390313230683340800 26902576025 137438953472 107662285613381 37045295518842880 EMRow32.d6 (ep157 ep166) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz267 qz283 qz552)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.true 12353348195 137438953472 919105224671 3704529551884288 Bool.true 333355374603 1099511627776 3685953005583 14818118207537152 (BSN.cpow_neg_s_mk qz13 104500 1000 10 qz14 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep169 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep170 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 134770 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep171 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz552 104500 1000 0 1 10369917190100709 4503599627370496 100000000040431 13477000000000000000 2167312692731048181 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000404310 134770000000000000000 10369917190100709 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep170 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep172 := nat_lit 146735705742615557140831377328052496

noncomputable def ep173 := BSN.sin_dyadic_bound_f 618919194 2147483648 2 1 1048576 269804 ep172 ep61 ep172 ep172 ep62 ep172 298040 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 618919194) qz291 0 1 ep172 ep61 ep172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 618919194) qz292 0 1 ep172 ep62 ep172 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz44 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz45 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63077101) qz44)

noncomputable def ep174 := @Enclosure.Real.IsNear.cos_image qz43 qz328 Bool.false 63077101 262144 407 524288 Bool.true 298040 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 2167312692731048181 9007199254740992 20900000008450079 26954000000000000000 63077101 262144 407 524288 (ep171 rfl) rfl) (Enclosure.sfrac_false_div 63077101 262144) (BSN.cos_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10888141607884933824512) qz45) 226375608064910080 72057594037927936 Bool.false 298040 1048576 38 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 63077101 262144 226375608064910080 72057594037927936 38 10888141607884933824512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298040 1048576 10888141607884933824512 37778931862957161709568 618919194 2147483648 269804 269540 (ep173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep175 := BSN.cos_dyadic_bound_f 618919194 2147483648 2 1 1048576 269804 ep172 ep57 ep172 ep172 ep58 ep172 1005327 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 618919194) qz286 0 1 ep172 ep57 ep172 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 618919194) qz287 0 1 ep172 ep58 ep172 rfl rfl rfl rfl) rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.sin_image qz43 qz328 Bool.false 63077101 262144 407 524288 Bool.false 1005327 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 2167312692731048181 9007199254740992 20900000008450079 26954000000000000000 63077101 262144 407 524288 (ep171 rfl) rfl) (Enclosure.sfrac_false_div 63077101 262144) (BSN.sin_reduce1 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10888141607884933824512) qz45) 226375608064910080 72057594037927936 Bool.false 1005327 1048576 38 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 63077101 262144 226375608064910080 72057594037927936 38 10888141607884933824512 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1005327 1048576 10888141607884933824512 37778931862957161709568 618919194 2147483648 269804 269540 (ep175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep169 rfl rfl) rfl)

noncomputable def ep177 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.true 12353348195 137438953472 919105224671 3704529551884288 Bool.true 333355374603 1099511627776 3685953005583 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz43) 331589 1048576 1 1048576 37255 131072 27687839 35329146880 12353348195 137438953472 919105224671 3704529551884288 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.true 298040 1048576 55375678 70658293760 37255 131072 27687839 35329146880 (ep174 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 331589 1048576 1 1048576 1005327 1048576 27687839 35329146880 333355374603 1099511627776 3685953005583 14818118207537152 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.false 1005327 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.false 1005327 1048576 55375678 70658293760 1005327 1048576 27687839 35329146880 (ep176 rfl rfl) rfl)) rfl)

noncomputable def ep178 := @ep154 12353348195 137438953472 919105224671 3704529551884288 Bool.true 333355374603 1099511627776 3685953005583 14818118207537152 Bool.true 7068596680764478717952 51430809841 549755813888 14606520644867 4630661939855360 Bool.true 16236318663087505801216 118134766403 1099511627776 233754336254677 74090591037685760 (ep155 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep167 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep168 ep177) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz553 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz283 qz553)

noncomputable def ep179 := @Enclosure.Complex.IsNear.of_eq qz38 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 121570270425 549755813888 8779643019687 37045295518842880 Bool.false 225353864187 1099511627776 17555495026659 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 11 qz14 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep180 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep181 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 134770 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep182 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz553 104500 1000 0 1 10799156221662949 4503599627370496 100000000040431 13477000000000000000 2257023650327556341 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000404310 134770000000000000000 10799156221662949 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep181 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep183 := nat_lit 9773465727412957759480206610922244241

noncomputable def ep184 := BSN.sin_dyadic_bound_f 1768121677 2147483648 2 1 1048576 269804 ep183 ep61 ep183 ep183 ep62 ep183 769050 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1768121677) qz291 0 1 ep183 ep61 ep183 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1768121677) qz292 0 1 ep183 ep62 ep183 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz48 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131376067) qz48)

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep185 := @Enclosure.Real.IsNear.cos_image qz47 qz332 Bool.false 131376067 524288 407 524288 Bool.false 769050 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 2257023650327556341 9007199254740992 20900000008450079 26954000000000000000 131376067 524288 407 524288 (ep182 rfl) rfl) (Enclosure.sfrac_false_div 131376067 524288) (BSN.cos_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62210250990685534552064) qz333) 226375608064910080 72057594037927936 Bool.false 769050 1048576 39 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 131376067 524288 226375608064910080 72057594037927936 39 62210250990685534552064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 769050 1048576 62210250990685534552064 75557863725914323419136 1768121677 2147483648 269804 269540 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep186 := nat_lit 349298015960523963388357832952099921522667364611590047957576436350787511280161

noncomputable def ep187 := nat_lit 95520632324915695547127551404569668075710724613201459499975800460057666081

noncomputable def ep188 := nat_lit 1047703006616922058773979243753490625231850672385543740953729357451442418508321

noncomputable def ep189 := BSN.cos_dyadic_bound_f 1768121677 2147483648 3 2 1048576 269804 ep186 ep122 ep187 ep188 ep125 ep187 712791 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1768121677) qz286 0 2 ep186 ep122 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1768121677) qz287 0 2 ep188 ep125 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable def ep190 := @Enclosure.Real.IsNear.sin_image qz47 qz332 Bool.false 131376067 524288 407 524288 Bool.true 712791 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 2257023650327556341 9007199254740992 20900000008450079 26954000000000000000 131376067 524288 407 524288 (ep182 rfl) rfl) (Enclosure.sfrac_false_div 131376067 524288) (BSN.sin_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 62210250990685534552064) qz333) 226375608064910080 72057594037927936 Bool.false 712791 1048576 39 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 131376067 524288 226375608064910080 72057594037927936 39 62210250990685534552064 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 712791 1048576 62210250990685534552064 75557863725914323419136 1768121677 2147483648 269804 269540 (ep189 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep180 rfl rfl) rfl)

noncomputable def ep191 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 121570270425 549755813888 8779643019687 37045295518842880 Bool.false 225353864187 1099511627776 17555495026659 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 316157 1048576 1 1048576 384525 524288 27687839 35329146880 121570270425 549755813888 8779643019687 37045295518842880 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 769050 1048576 55375678 70658293760 384525 524288 27687839 35329146880 (ep185 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 316157 1048576 1 1048576 712791 1048576 27687839 35329146880 225353864187 1099511627776 17555495026659 74090591037685760 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.true 712791 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.true 712791 1048576 55375678 70658293760 712791 1048576 27687839 35329146880 (ep190 rfl rfl) rfl)) rfl)

noncomputable def ep192 := @ep152 121570270425 549755813888 8779643019687 37045295518842880 Bool.false 225353864187 1099511627776 17555495026659 74090591037685760 Bool.false 38559576239022215790592 8767432573 68719476736 125631808178623 37045295518842880 Bool.false 117888644733159954448384 13402387223 137438953472 31413728910167 9261323879710720 (ep153 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep178 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep179 ep191) rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz283 qz554)

noncomputable def ep193 := @Enclosure.Complex.IsNear.of_eq qz37 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 149727557565 1099511627776 16795438632569 74090591037685760 Bool.true 139932888039 549755813888 8412204699117 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 12 qz14 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep194 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz335) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz335) (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep195 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 134770 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 104500 1000 0 1 11191020447815397 4503599627370496 100000000040431 13477000000000000000 2338923273593417973 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000404310 134770000000000000000 11191020447815397 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep197 := nat_lit 1238622355315931870007235564961529856

noncomputable def ep198 := BSN.sin_dyadic_bound_f 1054956928 2147483648 2 1 1048576 269804 ep197 ep61 ep197 ep197 ep62 ep197 494645 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1054956928) qz291 0 1 ep197 ep61 ep197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1054956928) qz292 0 1 ep197 ep62 ep197 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 272286505) qz20)

noncomputable def ep199 := @Enclosure.Real.IsNear.cos_image qz50 qz337 Bool.false 272286505 1048576 407 524288 Bool.true 494645 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 2338923273593417973 9007199254740992 20900000008450079 26954000000000000000 272286505 1048576 407 524288 (ep196 rfl) rfl) (Enclosure.sfrac_false_div 272286505 1048576) (BSN.cos_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74235994217730183004160) qz21) 226375608064910080 72057594037927936 Bool.false 494645 1048576 41 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 272286505 1048576 226375608064910080 72057594037927936 41 74235994217730183004160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 494645 1048576 74235994217730183004160 151115727451828646838272 1054956928 2147483648 269804 269540 (ep198 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep200 := BSN.cos_dyadic_bound_f 1054956928 2147483648 2 1 1048576 269804 ep197 ep57 ep197 ep197 ep58 ep197 924574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1054956928) qz286 0 1 ep197 ep57 ep197 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1054956928) qz287 0 1 ep197 ep58 ep197 rfl rfl rfl rfl) rfl rfl

noncomputable def ep201 := @Enclosure.Real.IsNear.sin_image qz50 qz337 Bool.false 272286505 1048576 407 524288 Bool.false 924574 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 2338923273593417973 9007199254740992 20900000008450079 26954000000000000000 272286505 1048576 407 524288 (ep196 rfl) rfl) (Enclosure.sfrac_false_div 272286505 1048576) (BSN.sin_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74235994217730183004160) qz21) 226375608064910080 72057594037927936 Bool.false 924574 1048576 41 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 272286505 1048576 226375608064910080 72057594037927936 41 74235994217730183004160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 924574 1048576 74235994217730183004160 151115727451828646838272 1054956928 2147483648 269804 269540 (ep200 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep194 rfl rfl) rfl)

noncomputable def ep202 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 149727557565 1099511627776 16795438632569 74090591037685760 Bool.true 139932888039 549755813888 8412204699117 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 302697 1048576 1 1048576 494645 1048576 27687839 35329146880 149727557565 1099511627776 16795438632569 74090591037685760 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 494645 1048576 55375678 70658293760 494645 1048576 27687839 35329146880 (ep199 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 302697 1048576 1 1048576 462287 524288 27687839 35329146880 139932888039 549755813888 8412204699117 37045295518842880 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 462287 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 924574 1048576 55375678 70658293760 462287 524288 27687839 35329146880 (ep201 rfl rfl) rfl)) rfl)

noncomputable def ep203 := @ep150 149727557565 1099511627776 16795438632569 74090591037685760 Bool.true 139932888039 549755813888 8412204699117 37045295518842880 Bool.true 649305349070564360192 9448636397 1099511627776 53611810997963 14818118207537152 Bool.true 11864189392572209168384 86323339147 549755813888 26813424067957 7409059103768576 (ep151 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep192 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep193 ep202) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz555 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz283 qz555)

noncomputable def ep204 := @Enclosure.Complex.IsNear.of_eq qz36 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 164342041539 1099511627776 16142654970477 74090591037685760 Bool.false 128438778897 549755813888 8082047933351 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 13 qz14 rfl)

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep205 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz340) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz340) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep206 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 134770 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep207 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz555 104500 1000 0 1 11551497052968677 4503599627370496 100000000040431 13477000000000000000 2414262884070453493 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 48450490295254733815808 18889465931478580854784 1000000000404310 134770000000000000000 11551497052968677 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep206 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep208 := nat_lit 765365424066595709718638356022733952961827556041886583791803635518599450264161

noncomputable def ep209 := nat_lit 458310610057424285075676880674245040015340335468923099067486356526368490081

noncomputable def ep210 := nat_lit 2295179650979672280585763714306853368805451987454721905177275933842745613812321

noncomputable def ep211 := BSN.cos_dyadic_bound_f 2151022677 2147483648 3 2 1048576 269804 ep208 ep122 ep209 ep210 ep125 ep209 565093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151022677) qz286 0 2 ep208 ep122 ep209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151022677) qz287 0 2 ep210 ep125 ep209 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 140528595) qz48)

noncomputable def ep212 := @Enclosure.Real.IsNear.cos_image qz52 qz341 Bool.false 140528595 524288 407 524288 Bool.true 565093 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 2414262884070453493 9007199254740992 20900000008450079 26954000000000000000 140528595 524288 407 524288 (ep207 rfl) rfl) (Enclosure.sfrac_false_div 140528595 524288) (BSN.cos_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75682382267731190743040) qz333) 226375608064910080 72057594037927936 Bool.false 565093 1048576 42 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 140528595 524288 226375608064910080 72057594037927936 42 75682382267731190743040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 565093 1048576 75682382267731190743040 75557863725914323419136 2151022677 2147483648 269804 269540 (ep211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep213 := nat_lit 1377291114831826338065488499336381719299277328607020712345992554848257915683425

noncomputable def ep214 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep215 := nat_lit 3606448988333737912757585449978955725242844357237152180650537903834870896853601

noncomputable def ep216 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep217 := BSN.sin_dyadic_bound_f 2151022677 2147483648 3 2 1048576 269804 ep213 ep214 ep209 ep215 ep216 ep209 883278 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151022677) qz291 0 2 ep213 ep214 ep209 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151022677) qz292 0 2 ep215 ep216 ep209 rfl rfl rfl rfl) rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.sin_image qz52 qz341 Bool.false 140528595 524288 407 524288 Bool.true 883278 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 2414262884070453493 9007199254740992 20900000008450079 26954000000000000000 140528595 524288 407 524288 (ep207 rfl) rfl) (Enclosure.sfrac_false_div 140528595 524288) (BSN.sin_reduce2 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75682382267731190743040) qz333) 226375608064910080 72057594037927936 Bool.false 883278 1048576 42 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 140528595 524288 226375608064910080 72057594037927936 42 75682382267731190743040 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883278 1048576 75682382267731190743040 75557863725914323419136 2151022677 2147483648 269804 269540 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep205 rfl rfl) rfl)

noncomputable def ep219 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 164342041539 1099511627776 16142654970477 74090591037685760 Bool.false 128438778897 549755813888 8082047933351 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 290823 1048576 1 1048576 565093 1048576 27687839 35329146880 164342041539 1099511627776 16142654970477 74090591037685760 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 565093 1048576 55375678 70658293760 565093 1048576 27687839 35329146880 (ep212 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 290823 1048576 1 1048576 441639 524288 27687839 35329146880 128438778897 549755813888 8082047933351 37045295518842880 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 441639 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 883278 1048576 55375678 70658293760 441639 524288 27687839 35329146880 (ep218 rfl rfl) rfl)) rfl)

noncomputable def ep220 := @ep148 164342041539 1099511627776 16142654970477 74090591037685760 Bool.false 128438778897 549755813888 8082047933351 37045295518842880 Bool.true 191084871189705927950336 10861917371 68719476736 71050427490073 18522647759421440 Bool.false 23153207857012277248000 21057719875 274877906944 8884323017071 2315330969927680 (ep149 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep203 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep204 ep219) rfl rfl

noncomputable abbrev qz343 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz343))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz267 qz283 qz556)

noncomputable def ep221 := @Enclosure.Complex.IsNear.of_eq qz35 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 114355117851 549755813888 7786847673661 37045295518842880 Bool.false 184507227069 1099511627776 15563066643887 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 14 qz14 rfl)

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep222 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz343) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz343) (Real.sqrt qz344) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep223 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 134770 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 104500 1000 0 1 11885250371606245 4503599627370496 100000000040431 13477000000000000000 2484017327665705205 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 49850353174629559828480 18889465931478580854784 1000000000404310 134770000000000000000 11885250371606245 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep225 := nat_lit 865971155964583677629589620458566609720556651776162278515503699495441650390625

noncomputable def ep226 := nat_lit 181226858105191355169983283702904740341494350823338228282988071441650390625

noncomputable def ep227 := nat_lit 2267726279279834560169126175884536417783762144750520562790051517991441650390625

noncomputable def ep228 := BSN.sin_dyadic_bound_f 1915480875 2147483648 3 2 1048576 269804 ep225 ep214 ep226 ep227 ep216 ep226 816114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1915480875) qz291 0 2 ep225 ep214 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1915480875) qz292 0 2 ep227 ep216 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72294419) qz44)

noncomputable def ep229 := @Enclosure.Real.IsNear.cos_image qz54 qz345 Bool.false 72294419 262144 407 524288 Bool.false 816114 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 2484017327665705205 9007199254740992 20900000008450079 26954000000000000000 72294419 262144 407 524288 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 72294419 262144) (BSN.cos_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33697495920365291962368) qz45) 226375608064910080 72057594037927936 Bool.false 816114 1048576 43 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 72294419 262144 226375608064910080 72057594037927936 43 33697495920365291962368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816114 1048576 33697495920365291962368 37778931862957161709568 1915480875 2147483648 269804 269540 (ep228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep230 := nat_lit 481175631917259905952069781714182740840461026253789416165627827751441650390625

noncomputable def ep231 := nat_lit 1443164442035569335145869378575142413040700090059721572040317507111441650390625

noncomputable def ep232 := BSN.cos_dyadic_bound_f 1915480875 2147483648 3 2 1048576 269804 ep230 ep122 ep226 ep231 ep125 ep226 658383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1915480875) qz286 0 2 ep230 ep122 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1915480875) qz287 0 2 ep231 ep125 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep233 := @Enclosure.Real.IsNear.sin_image qz54 qz345 Bool.false 72294419 262144 407 524288 Bool.true 658383 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 2484017327665705205 9007199254740992 20900000008450079 26954000000000000000 72294419 262144 407 524288 (ep224 rfl) rfl) (Enclosure.sfrac_false_div 72294419 262144) (BSN.sin_reduce3 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33697495920365291962368) qz45) 226375608064910080 72057594037927936 Bool.false 658383 1048576 43 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 72294419 262144 226375608064910080 72057594037927936 43 33697495920365291962368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 658383 1048576 33697495920365291962368 37778931862957161709568 1915480875 2147483648 269804 269540 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep222 rfl rfl) rfl)

noncomputable def ep234 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 114355117851 549755813888 7786847673661 37045295518842880 Bool.false 184507227069 1099511627776 15563066643887 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 280243 1048576 1 1048576 408057 524288 27687839 35329146880 114355117851 549755813888 7786847673661 37045295518842880 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 816114 1048576 55375678 70658293760 408057 524288 27687839 35329146880 (ep229 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 280243 1048576 1 1048576 658383 1048576 27687839 35329146880 184507227069 1099511627776 15563066643887 74090591037685760 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 658383 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 658383 1048576 55375678 70658293760 658383 1048576 27687839 35329146880 (ep233 rfl rfl) rfl)) rfl)

noncomputable def ep235 := @ep146 114355117851 549755813888 7786847673661 37045295518842880 Bool.false 184507227069 1099511627776 15563066643887 74090591037685760 Bool.false 1887021636126022565888 27459778883 549755813888 149887702653807 37045295518842880 Bool.false 73870168249780337115136 268738106569 1099511627776 299861403190159 74090591037685760 (ep147 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep220 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep221 ep234) rfl rfl

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz347))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz267 qz283 qz557)

noncomputable def ep236 := @Enclosure.Complex.IsNear.of_eq qz34 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 275226907629 1099511627776 15061023315141 74090591037685760 Bool.true 8700803517 137438953472 3752461556759 18522647759421440 (BSN.cpow_neg_s_mk qz13 104500 1000 15 qz14 rfl)

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep237 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz347) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz347) (Real.sqrt qz348) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz348) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep238 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 134770 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 104500 1000 0 1 12195965485668069 4503599627370496 100000000040431 13477000000000000000 2548956786504626421 9007199254740992 20900000008450079 26954000000000000000 qz16 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 51153586820399524478976 18889465931478580854784 1000000000404310 134770000000000000000 12195965485668069 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep240 := nat_lit 80076839215710262406026080620118016

noncomputable def ep241 := BSN.cos_dyadic_bound_f 531957248 2147483648 2 1 1048576 269804 ep240 ep57 ep240 ep240 ep58 ep240 1016569 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 531957248) qz286 0 1 ep240 ep57 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 531957248) qz287 0 1 ep240 ep58 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37092203) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz558 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep242 := @Enclosure.Real.IsNear.cos_image qz56 qz349 Bool.false 37092203 131072 407 524288 Bool.false 1016569 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 2548956786504626421 9007199254740992 20900000008450079 26954000000000000000 37092203 131072 407 524288 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 37092203 131072) (BSN.cos_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4679145441724481929216) qz558) 226375608064910080 72057594037927936 Bool.false 1016569 1048576 45 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 37092203 131072 226375608064910080 72057594037927936 45 4679145441724481929216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016569 1048576 4679145441724481929216 18889465931478580854784 531957248 2147483648 269804 269540 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep243 := BSN.sin_dyadic_bound_f 531957248 2147483648 2 1 1048576 269804 ep240 ep61 ep240 ep240 ep62 ep240 257096 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 531957248) qz291 0 1 ep240 ep61 ep240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 531957248) qz292 0 1 ep240 ep62 ep240 rfl rfl rfl rfl) rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.sin_image qz56 qz349 Bool.false 37092203 131072 407 524288 Bool.false 257096 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 2548956786504626421 9007199254740992 20900000008450079 26954000000000000000 37092203 131072 407 524288 (ep239 rfl) rfl) (Enclosure.sfrac_false_div 37092203 131072) (BSN.sin_reduce0 qz349 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4679145441724481929216) qz558) 226375608064910080 72057594037927936 Bool.false 257096 1048576 45 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 37092203 131072 226375608064910080 72057594037927936 45 4679145441724481929216 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257096 1048576 4679145441724481929216 18889465931478580854784 531957248 2147483648 269804 269540 (ep243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz350 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep237 rfl rfl) rfl)

noncomputable def ep245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 275226907629 1099511627776 15061023315141 74090591037685760 Bool.true 8700803517 137438953472 3752461556759 18522647759421440 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 270741 1048576 1 1048576 1016569 1048576 27687839 35329146880 275226907629 1099511627776 15061023315141 74090591037685760 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 1016569 1048576 55375678 70658293760 1016569 1048576 27687839 35329146880 (ep242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 270741 1048576 1 1048576 32137 131072 27687839 35329146880 8700803517 137438953472 3752461556759 18522647759421440 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.false 32137 131072 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.false 257096 1048576 55375678 70658293760 32137 131072 27687839 35329146880 (ep244 rfl rfl) rfl)) rfl)

noncomputable def ep246 := @ep144 275226907629 1099511627776 15061023315141 74090591037685760 Bool.true 8700803517 137438953472 3752461556759 18522647759421440 Bool.false 181499938785474652405760 330146465395 1099511627776 62967285724551 14818118207537152 Bool.false 27368449486954352869376 199131678433 1099511627776 62974249883439 14818118207537152 (ep145 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep235 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep236 ep245) rfl rfl

noncomputable abbrev qz351 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz351))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz283 qz559)

noncomputable def ep247 := @Enclosure.Complex.IsNear.of_eq qz33 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 208635681555 1099511627776 14570032444357 74090591037685760 Bool.true 178964763957 1099511627776 14562405405747 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 16 qz14 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep248 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz351) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz351) (Real.sqrt qz352) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep249 := BSN.log_dyadic_bound 0 32 1 0 1 524288 134770 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 104500 1000 0 1 3121657384082679 1125899906842624 25000000013477 3369250000000000000 652426393273279911 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 52372720210750067441664 18889465931478580854784 1000000000539080 134770000000000000000 3121657384082679 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep251 := nat_lit 192039942807991725837655791415596550197905619588557631386480390108667993480001

noncomputable def ep252 := nat_lit 28879855475434888877964650306793313983472534062081175439307454463179840321

noncomputable def ep253 := nat_lit 576062068713024307735211444946176063965749913697548731808562555417077620759361

noncomputable def ep254 := BSN.cos_dyadic_bound_f 1522559863 2147483648 3 2 1048576 269804 ep251 ep122 ep252 ep253 ep125 ep252 795885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1522559863) qz286 0 2 ep251 ep122 ep252 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1522559863) qz287 0 2 ep253 ep125 ep252 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151904857) qz48)

noncomputable def ep255 := @Enclosure.Real.IsNear.cos_image qz58 qz353 Bool.false 151904857 524288 407 524288 Bool.false 795885 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 652426393273279911 2251799813685248 5225000002816693 6738500000000000000 151904857 524288 407 524288 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 151904857 524288) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53570312782045400530944) qz333) 226375608064910080 72057594037927936 Bool.false 795885 1048576 46 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 151904857 524288 226375608064910080 72057594037927936 46 53570312782045400530944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 795885 1048576 53570312782045400530944 75557863725914323419136 1522559863 2147483648 269804 269540 (ep254 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep256 := nat_lit 5373998090382512303592792553857555361

noncomputable def ep257 := BSN.sin_dyadic_bound_f 1522559863 2147483648 2 1 1048576 269804 ep256 ep61 ep256 ep256 ep62 ep256 682699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1522559863) qz291 0 1 ep256 ep61 ep256 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1522559863) qz292 0 1 ep256 ep62 ep256 rfl rfl rfl rfl) rfl rfl

noncomputable def ep258 := @Enclosure.Real.IsNear.sin_image qz58 qz353 Bool.false 151904857 524288 407 524288 Bool.false 682699 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 652426393273279911 2251799813685248 5225000002816693 6738500000000000000 151904857 524288 407 524288 (ep250 rfl) rfl) (Enclosure.sfrac_false_div 151904857 524288) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53570312782045400530944) qz333) 226375608064910080 72057594037927936 Bool.false 682699 1048576 46 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 151904857 524288 226375608064910080 72057594037927936 46 53570312782045400530944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 682699 1048576 53570312782045400530944 75557863725914323419136 1522559863 2147483648 269804 269540 (ep257 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep248 rfl rfl) rfl)

noncomputable def ep259 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 208635681555 1099511627776 14570032444357 74090591037685760 Bool.true 178964763957 1099511627776 14562405405747 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 262143 1048576 1 1048576 795885 1048576 27687839 35329146880 208635681555 1099511627776 14570032444357 74090591037685760 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 795885 1048576 55375678 70658293760 795885 1048576 27687839 35329146880 (ep255 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 262143 1048576 1 1048576 682699 1048576 27687839 35329146880 178964763957 1099511627776 14562405405747 74090591037685760 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 682699 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 682699 1048576 55375678 70658293760 682699 1048576 27687839 35329146880 (ep258 rfl rfl) rfl)) rfl)

noncomputable def ep260 := @ep142 208635681555 1099511627776 14570032444357 74090591037685760 Bool.true 178964763957 1099511627776 14562405405747 74090591037685760 Bool.false 592397235409642533683200 269391073475 549755813888 41175807633389 9261323879710720 Bool.false 22173756962726138085376 5041728619 274877906944 164716827411471 37045295518842880 (ep143 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep247 ep259) rfl rfl

theorem EMRow32.d7 : Enclosure.Complex.IsNear qz32 Bool.false 269391073475 549755813888 41175807633389 9261323879710720 Bool.false 5041728619 274877906944 164716827411471 37045295518842880 := ep141 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep260 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz59 := (BSN.headSumC qz271 25)

noncomputable abbrev qz560 := (@Nat.cast Complex Complex.instNatCast 24)

noncomputable abbrev qz60 := (@HPow.hPow Complex Complex Complex qz273 qz560 qz274)

noncomputable def ep261 := @Enclosure.Complex.IsNear.of_eq qz59 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz60) Bool.false 621872755945 549755813888 6764782973387 1157665484963840 Bool.false 8653240819 274877906944 216465532758679 37045295518842880

noncomputable def ep262 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz60 Bool.false 1104637499049 1099511627776 421049705385833 74090591037685760 Bool.true 70756654327 549755813888 52627875787911 9261323879710720 Bool.false

noncomputable def ep263 := nat_lit 1367512652317268262256640

noncomputable abbrev qz355 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep264 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7)) Bool.false 1104637499049 1099511627776 421049705385833 74090591037685760 Bool.true 70756654327 549755813888 52627875787911 9261323879710720

noncomputable def ep265 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) Bool.false 242046311277 274877906944 204450045771353 37045295518842880 Bool.false 10680460609 274877906944 204429332970053 37045295518842880 Bool.false

noncomputable abbrev qz356 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep266 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7)) Bool.false 242046311277 274877906944 204450045771353 37045295518842880 Bool.false 10680460609 274877906944 204429332970053 37045295518842880

noncomputable def ep267 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) Bool.false 1165515208539 1099511627776 396460936126427 74090591037685760 Bool.false 84630011345 549755813888 6194388261333 1157665484963840 Bool.true

noncomputable abbrev qz357 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz7)) Bool.false 1165515208539 1099511627776 396460936126427 74090591037685760 Bool.false 84630011345 549755813888 6194388261333 1157665484963840

noncomputable def ep269 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) Bool.false 1323574674309 1099511627776 383696779087417 74090591037685760 Bool.true 5626562301 549755813888 95915866710243 18522647759421440 Bool.true

noncomputable abbrev qz358 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep270 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz7)) Bool.false 1323574674309 1099511627776 383696779087417 74090591037685760 Bool.true 5626562301 549755813888 95915866710243 18522647759421440

noncomputable def ep271 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz7) Bool.false 151653228179 137438953472 92670282565513 18522647759421440 Bool.true 230956439327 1099511627776 370616390190687 74090591037685760 Bool.false

noncomputable abbrev qz359 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep272 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz7)) Bool.false 151653228179 137438953472 92670282565513 18522647759421440 Bool.true 230956439327 1099511627776 370616390190687 74090591037685760

noncomputable def ep273 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz7) Bool.false 965157295129 1099511627776 357290468604827 74090591037685760 Bool.true 34583041655 137438953472 2791268855229 578832742481920 Bool.false

noncomputable def ep274 := nat_lit 1333955902180619538399232

noncomputable abbrev qz360 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz7)) Bool.false 965157295129 1099511627776 357290468604827 74090591037685760 Bool.true 34583041655 137438953472 2791268855229 578832742481920

noncomputable def ep276 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz7) Bool.false 731903101557 1099511627776 343540662959551 74090591037685760 Bool.true 163728436639 1099511627776 343565412257121 74090591037685760 Bool.false

noncomputable abbrev qz361 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep277 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz32 (@HPow.hPow Complex Complex Complex qz6 qz361 qz7)) Bool.false 731903101557 1099511627776 343540662959551 74090591037685760 Bool.true 163728436639 1099511627776 343565412257121 74090591037685760

noncomputable def ep278 := @Enclosure.Complex.IsNear.addLitP qz32 (@HPow.hPow Complex Complex Complex qz6 qz361 qz7) Bool.false 269391073475 549755813888 41175807633389 9261323879710720 Bool.false 5041728619 274877906944 164716827411471 37045295518842880 Bool.false

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz362))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz283 qz561)

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz361 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 193120954607 1099511627776 14134201892439 74090591037685760 Bool.true 183895351115 1099511627776 14131757434179 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 17 qz14 rfl)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep280 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz362) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz362) (Real.sqrt qz363) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz363) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep281 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 134770 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep282 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 104500 1000 0 1 3189913004350711 1125899906842624 25000000013477 3369250000000000000 666691817909298599 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 53517859495200818200576 18889465931478580854784 1000000000539080 134770000000000000000 3189913004350711 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep281 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep283 := nat_lit 254812435360317829887506958548702284286493120601768628128748982973051441779841

noncomputable def ep284 := nat_lit 50840572179261023167098916191732593563015716688776555018843178839545746561

noncomputable def ep285 := nat_lit 764335624936594967616186677813723387672353330371928331276209262561475233846401

noncomputable def ep286 := BSN.cos_dyadic_bound_f 1634091247 2147483648 3 2 1048576 269804 ep283 ep122 ep284 ep285 ep125 ep284 759371 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1634091247) qz286 0 2 ep283 ep122 ep284 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1634091247) qz287 0 2 ep285 ep125 ep284 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 155226285) qz48)

noncomputable def ep287 := @Enclosure.Real.IsNear.cos_image qz62 qz364 Bool.false 155226285 524288 407 524288 Bool.false 759371 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 666691817909298599 2251799813685248 5225000002816693 6738500000000000000 155226285 524288 407 524288 (ep282 rfl) rfl) (Enclosure.sfrac_false_div 155226285 524288) (BSN.cos_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57494474477916913664000) qz333) 226375608064910080 72057594037927936 Bool.false 759371 1048576 47 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 155226285 524288 226375608064910080 72057594037927936 47 57494474477916913664000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759371 1048576 57494474477916913664000 75557863725914323419136 1634091247 2147483648 269804 269540 (ep286 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep288 := nat_lit 7130257511426990752895165323621270081

noncomputable def ep289 := BSN.sin_dyadic_bound_f 1634091247 2147483648 2 1 1048576 269804 ep288 ep61 ep288 ep288 ep62 ep288 723095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1634091247) qz291 0 1 ep288 ep61 ep288 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1634091247) qz292 0 1 ep288 ep62 ep288 rfl rfl rfl rfl) rfl rfl

noncomputable def ep290 := @Enclosure.Real.IsNear.sin_image qz62 qz364 Bool.false 155226285 524288 407 524288 Bool.false 723095 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 666691817909298599 2251799813685248 5225000002816693 6738500000000000000 155226285 524288 407 524288 (ep282 rfl) rfl) (Enclosure.sfrac_false_div 155226285 524288) (BSN.sin_reduce0 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57494474477916913664000) qz333) 226375608064910080 72057594037927936 Bool.false 723095 1048576 47 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 155226285 524288 226375608064910080 72057594037927936 47 57494474477916913664000 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723095 1048576 57494474477916913664000 75557863725914323419136 1634091247 2147483648 269804 269540 (ep289 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep280 rfl rfl) rfl)

noncomputable def ep291 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 193120954607 1099511627776 14134201892439 74090591037685760 Bool.true 183895351115 1099511627776 14131757434179 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 254317 1048576 1 1048576 759371 1048576 27687839 35329146880 193120954607 1099511627776 14134201892439 74090591037685760 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 759371 1048576 55375678 70658293760 759371 1048576 27687839 35329146880 (ep287 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 254317 1048576 1 1048576 723095 1048576 27687839 35329146880 183895351115 1099511627776 14131757434179 74090591037685760 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 723095 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 723095 1048576 55375678 70658293760 723095 1048576 27687839 35329146880 (ep290 rfl rfl) rfl)) rfl)

noncomputable def ep292 := @ep278 193120954607 1099511627776 14134201892439 74090591037685760 Bool.true 183895351115 1099511627776 14131757434179 74090591037685760 Bool.false 402367985283620055023616 731903101557 1099511627776 343540662959551 74090591037685760 Bool.true 45005329970541642121216 163728436639 1099511627776 343565412257121 74090591037685760 EMRow32.d7 (ep279 ep291) rfl rfl

noncomputable abbrev qz366 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz366))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz283 qz562)

noncomputable def ep293 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz360 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 58313548393 274877906944 3437451411319 18522647759421440 Bool.true 112935896601 1099511627776 13717001212191 74090591037685760 (BSN.cpow_neg_s_mk qz13 104500 1000 18 qz14 rfl)

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep294 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz366) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz366) (Real.sqrt qz367) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz367) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep295 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 134770 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep296 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 104500 1000 0 1 3254268794313975 1125899906842624 25000000013477 3369250000000000000 680142178011620775 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 54597570484265130393600 18889465931478580854784 1000000000539080 134770000000000000000 3254268794313975 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep297 := nat_lit 879162916920202411387850955241416976

noncomputable def ep298 := BSN.cos_dyadic_bound_f 968316518 2147483648 2 1 1048576 269804 ep297 ep57 ep297 ep297 ep58 ep297 943772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 968316518) qz286 0 1 ep297 ep57 ep297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 968316518) qz287 0 1 ep297 ep58 ep297 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 158357941) qz48)

noncomputable def ep299 := @Enclosure.Real.IsNear.cos_image qz64 qz368 Bool.false 158357941 524288 407 524288 Bool.false 943772 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 680142178011620775 2251799813685248 5225000002816693 6738500000000000000 158357941 524288 407 524288 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 158357941 524288) (BSN.cos_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34069608702257106255872) qz333) 226375608064910080 72057594037927936 Bool.false 943772 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 158357941 524288 226375608064910080 72057594037927936 48 34069608702257106255872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943772 1048576 34069608702257106255872 75557863725914323419136 968316518 2147483648 269804 269540 (ep298 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep300 := BSN.sin_dyadic_bound_f 968316518 2147483648 2 1 1048576 269804 ep297 ep61 ep297 ep297 ep62 ep297 456951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 968316518) qz291 0 1 ep297 ep61 ep297 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 968316518) qz292 0 1 ep297 ep62 ep297 rfl rfl rfl rfl) rfl rfl

noncomputable def ep301 := @Enclosure.Real.IsNear.sin_image qz64 qz368 Bool.false 158357941 524288 407 524288 Bool.false 456951 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 680142178011620775 2251799813685248 5225000002816693 6738500000000000000 158357941 524288 407 524288 (ep296 rfl) rfl) (Enclosure.sfrac_false_div 158357941 524288) (BSN.sin_reduce0 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34069608702257106255872) qz333) 226375608064910080 72057594037927936 Bool.false 456951 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 158357941 524288 226375608064910080 72057594037927936 48 34069608702257106255872 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 456951 1048576 34069608702257106255872 75557863725914323419136 968316518 2147483648 269804 269540 (ep300 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep294 rfl rfl) rfl)

noncomputable def ep302 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 58313548393 274877906944 3437451411319 18522647759421440 Bool.true 112935896601 1099511627776 13717001212191 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 247151 1048576 1 1048576 235943 262144 27687839 35329146880 58313548393 274877906944 3437451411319 18522647759421440 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 943772 1048576 55375678 70658293760 235943 262144 27687839 35329146880 (ep299 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 247151 1048576 1 1048576 456951 1048576 27687839 35329146880 112935896601 1099511627776 13717001212191 74090591037685760 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 456951 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 456951 1048576 55375678 70658293760 456951 1048576 27687839 35329146880 (ep301 rfl rfl) rfl)) rfl)

noncomputable def ep303 := @ep276 58313548393 274877906944 3437451411319 18522647759421440 Bool.true 112935896601 1099511627776 13717001212191 74090591037685760 Bool.false 265300417156792006475776 965157295129 1099511627776 357290468604827 74090591037685760 Bool.true 304195651388274104074240 34583041655 137438953472 2791268855229 578832742481920 (ep277 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep292 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep293 ep302) rfl rfl

noncomputable abbrev qz370 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz65 := (@Inv.inv Real Real.instInv (Real.sqrt qz370))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 qz283 qz563)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz359 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 248068530303 1099511627776 2678132331445 14818118207537152 Bool.false 45707893913 1099511627776 2666795344275 14818118207537152 (BSN.cpow_neg_s_mk qz13 104500 1000 19 qz14 rfl)

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep305 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz370) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz370) (Real.sqrt qz371) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz371) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep306 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 134770 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep307 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 104500 1000 0 1 3315143513283831 1125899906842624 25000000013477 3369250000000000000 692864994276320679 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 55618878793361701994496 18889465931478580854784 1000000000539080 134770000000000000000 3315143513283831 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep306 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep308 := nat_lit 5091466570537913523749542562633764454650096999971826576638724923962588586311680

noncomputable def ep309 := nat_lit 6251958321998609382241715571546524371077416877538946781273453210552097570816

noncomputable def ep310 := nat_lit 13324671180792251956534696315020212532244700134505435120217455876608742901415936

noncomputable def ep311 := BSN.sin_dyadic_bound_f 2981961344 2147483648 3 2 1048576 269804 ep308 ep214 ep309 ep310 ep216 ep309 1031217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2981961344) qz291 0 2 ep308 ep214 ep309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2981961344) qz292 0 2 ep310 ep216 ep309 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz372 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 322640405) qz20)

noncomputable def ep312 := @Enclosure.Real.IsNear.cos_image qz66 qz372 Bool.false 322640405 1048576 407 524288 Bool.false 1031217 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 692864994276320679 2251799813685248 5225000002816693 6738500000000000000 322640405 1048576 407 524288 (ep307 rfl) rfl) (Enclosure.sfrac_false_div 322640405 1048576) (BSN.cos_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209836875002434614722560) qz21) 226375608064910080 72057594037927936 Bool.false 1031217 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 322640405 1048576 226375608064910080 72057594037927936 48 209836875002434614722560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031217 1048576 209836875002434614722560 151115727451828646838272 2981961344 2147483648 269804 269540 (ep311 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep313 := nat_lit 2831371187330840228475186630606112041192754963041032074479857603628350146871296

noncomputable def ep314 := nat_lit 8481609645348523466661076460675243074836110055368018329877025904463946245472256

noncomputable def ep315 := BSN.cos_dyadic_bound_f 2981961344 2147483648 3 2 1048576 269804 ep313 ep122 ep309 ep314 ep125 ep309 190007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2981961344) qz286 0 2 ep313 ep122 ep309 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2981961344) qz287 0 2 ep314 ep125 ep309 rfl rfl rfl rfl) rfl rfl

noncomputable def ep316 := @Enclosure.Real.IsNear.sin_image qz66 qz372 Bool.false 322640405 1048576 407 524288 Bool.true 190007 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 692864994276320679 2251799813685248 5225000002816693 6738500000000000000 322640405 1048576 407 524288 (ep307 rfl) rfl) (Enclosure.sfrac_false_div 322640405 1048576) (BSN.sin_reduce3 qz372 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209836875002434614722560) qz21) 226375608064910080 72057594037927936 Bool.false 190007 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 322640405 1048576 226375608064910080 72057594037927936 48 209836875002434614722560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 190007 1048576 209836875002434614722560 151115727451828646838272 2981961344 2147483648 269804 269540 (ep315 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz373 := (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep305 rfl rfl) rfl)

noncomputable def ep317 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 248068530303 1099511627776 2678132331445 14818118207537152 Bool.false 45707893913 1099511627776 2666795344275 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz66) 240559 1048576 1 1048576 1031217 1048576 27687839 35329146880 248068530303 1099511627776 2678132331445 14818118207537152 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 1031217 1048576 55375678 70658293760 1031217 1048576 27687839 35329146880 (ep312 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz65 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 240559 1048576 1 1048576 190007 1048576 27687839 35329146880 45707893913 1099511627776 2666795344275 14818118207537152 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.true 190007 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.true 190007 1048576 55375678 70658293760 190007 1048576 27687839 35329146880 (ep316 rfl rfl) rfl)) rfl)

noncomputable def ep318 := @ep273 248068530303 1099511627776 2678132331445 14818118207537152 Bool.false 45707893913 1099511627776 2666795344275 14818118207537152 Bool.false ep274 151653228179 137438953472 92670282565513 18522647759421440 Bool.true 31742411318722343993344 230956439327 1099511627776 370616390190687 74090591037685760 (ep275 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep303 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep304 ep317) rfl rfl

noncomputable abbrev qz374 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz67 := (@Inv.inv Real Real.instInv (Real.sqrt qz374))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz267 qz283 qz564)

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz358 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.false 110348848877 1099511627776 2603129765073 14818118207537152 Bool.false 219703314725 1099511627776 2609415330057 14818118207537152 (BSN.cpow_neg_s_mk qz13 104500 1000 20 qz14 rfl)

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep320 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz374) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz374) (Real.sqrt qz375) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz375) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep321 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 134770 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep322 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 104500 1000 0 1 3372893643545847 1125899906842624 25000000013477 3369250000000000000 704934771501082023 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 56587765202795681021952 18889465931478580854784 1000000000539080 134770000000000000000 3372893643545847 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep323 := nat_lit 998241896288411844369130182819188736

noncomputable def ep324 := BSN.sin_dyadic_bound_f 999560184 2147483648 2 1 1048576 269804 ep323 ep61 ep323 ep323 ep62 ep323 470633 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 999560184) qz291 0 1 ep323 ep61 ep323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 999560184) qz292 0 1 ep323 ep62 ep323 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz376 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328260833) qz20)

noncomputable def ep325 := @Enclosure.Real.IsNear.cos_image qz68 qz376 Bool.false 328260833 1048576 407 524288 Bool.false 470633 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 704934771501082023 2251799813685248 5225000002816693 6738500000000000000 328260833 1048576 407 524288 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 328260833 1048576) (BSN.cos_reduce3 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70337794880156473491456) qz21) 226375608064910080 72057594037927936 Bool.false 470633 1048576 49 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 328260833 1048576 226375608064910080 72057594037927936 49 70337794880156473491456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 470633 1048576 70337794880156473491456 151115727451828646838272 999560184 2147483648 269804 269540 (ep324 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep326 := BSN.cos_dyadic_bound_f 999560184 2147483648 2 1 1048576 269804 ep323 ep57 ep323 ep323 ep58 ep323 937025 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 999560184) qz286 0 1 ep323 ep57 ep323 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 999560184) qz287 0 1 ep323 ep58 ep323 rfl rfl rfl rfl) rfl rfl

noncomputable def ep327 := @Enclosure.Real.IsNear.sin_image qz68 qz376 Bool.false 328260833 1048576 407 524288 Bool.true 937025 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 704934771501082023 2251799813685248 5225000002816693 6738500000000000000 328260833 1048576 407 524288 (ep322 rfl) rfl) (Enclosure.sfrac_false_div 328260833 1048576) (BSN.sin_reduce3 qz376 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70337794880156473491456) qz21) 226375608064910080 72057594037927936 Bool.false 937025 1048576 49 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 328260833 1048576 226375608064910080 72057594037927936 49 70337794880156473491456 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937025 1048576 70337794880156473491456 151115727451828646838272 999560184 2147483648 269804 269540 (ep326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz377 := (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep320 rfl rfl) rfl)

noncomputable def ep328 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.false 110348848877 1099511627776 2603129765073 14818118207537152 Bool.false 219703314725 1099511627776 2609415330057 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz68) 234469 1048576 1 1048576 470633 1048576 27687839 35329146880 110348848877 1099511627776 2603129765073 14818118207537152 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 470633 1048576 55375678 70658293760 470633 1048576 27687839 35329146880 (ep325 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz67 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 234469 1048576 1 1048576 937025 1048576 27687839 35329146880 219703314725 1099511627776 2609415330057 14818118207537152 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.true 937025 1048576 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.true 937025 1048576 55375678 70658293760 937025 1048576 27687839 35329146880 (ep327 rfl rfl) rfl)) rfl)

noncomputable def ep329 := @ep271 110348848877 1099511627776 2603129765073 14818118207537152 Bool.false 219703314725 1099511627776 2609415330057 14818118207537152 Bool.false 181910718079072204750848 1323574674309 1099511627776 383696779087417 74090591037685760 Bool.true 12372941348711172145152 5626562301 549755813888 95915866710243 18522647759421440 (ep272 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep318 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep319 ep328) rfl rfl

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz378))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz283 qz565)

noncomputable def ep330 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.true 79029732885 549755813888 1276415703901 7409059103768576 Bool.false 45128286823 274877906944 638869094217 3704529551884288 (BSN.cpow_neg_s_mk qz13 104500 1000 21 qz14 rfl)

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep331 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz378) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz378) (Real.sqrt qz379) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz379) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep332 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 134770 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep333 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 104500 1000 0 1 3427826275261687 1125899906842624 25000000013477 3369250000000000000 716415691529692583 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 57509381830540779323392 18889465931478580854784 1000000000539080 134770000000000000000 3427826275261687 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep334 := nat_lit 399823196760115237509521029567661586323113066920025272196494981127784499690625

noncomputable def ep335 := nat_lit 125143004921185950439534560822766246245001717392777808931214513929062890625

noncomputable def ep336 := nat_lit 1199219304270503340627684019581339226476849197325290260971622514355495373290625

noncomputable def ep337 := BSN.cos_dyadic_bound_f 1828840465 2147483648 3 2 1048576 269804 ep334 ep122 ep335 ep336 ep125 ep335 690765 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1828840465) qz286 0 2 ep334 ep122 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1828840465) qz287 0 2 ep336 ep125 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 333607053) qz20)

noncomputable def ep338 := @Enclosure.Real.IsNear.cos_image qz70 qz380 Bool.false 333607053 1048576 407 524288 Bool.true 690765 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 716415691529692583 2251799813685248 5225000002816693 6738500000000000000 333607053 1048576 407 524288 (ep333 rfl) rfl) (Enclosure.sfrac_false_div 333607053 1048576) (BSN.cos_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128693206868245197357056) qz21) 226375608064910080 72057594037927936 Bool.false 690765 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 333607053 1048576 226375608064910080 72057594037927936 50 128693206868245197357056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 690765 1048576 128693206868245197357056 151115727451828646838272 1828840465 2147483648 269804 269540 (ep337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep339 := nat_lit 11186733433902228745800514334693250625

noncomputable def ep340 := BSN.sin_dyadic_bound_f 1828840465 2147483648 2 1 1048576 269804 ep339 ep61 ep339 ep339 ep62 ep339 788894 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1828840465) qz291 0 1 ep339 ep61 ep339 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1828840465) qz292 0 1 ep339 ep62 ep339 rfl rfl rfl rfl) rfl rfl

noncomputable def ep341 := @Enclosure.Real.IsNear.sin_image qz70 qz380 Bool.false 333607053 1048576 407 524288 Bool.true 788894 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 716415691529692583 2251799813685248 5225000002816693 6738500000000000000 333607053 1048576 407 524288 (ep333 rfl) rfl) (Enclosure.sfrac_false_div 333607053 1048576) (BSN.sin_reduce2 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128693206868245197357056) qz21) 226375608064910080 72057594037927936 Bool.false 788894 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 333607053 1048576 226375608064910080 72057594037927936 50 128693206868245197357056 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 788894 1048576 128693206868245197357056 151115727451828646838272 1828840465 2147483648 269804 269540 (ep340 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep331 rfl rfl) rfl)

noncomputable def ep342 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.true 79029732885 549755813888 1276415703901 7409059103768576 Bool.false 45128286823 274877906944 638869094217 3704529551884288 (@Enclosure.Real.IsNear.mulLit_ft qz69 (Real.cos qz70) 114409 524288 1 524288 690765 1048576 27687839 35329146880 79029732885 549755813888 1276415703901 7409059103768576 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.true 690765 1048576 55375678 70658293760 690765 1048576 27687839 35329146880 (ep338 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 114409 524288 1 524288 394447 524288 27687839 35329146880 45128286823 274877906944 638869094217 3704529551884288 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 394447 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 788894 1048576 55375678 70658293760 394447 524288 27687839 35329146880 (ep341 rfl rfl) rfl)) rfl)

noncomputable def ep343 := @ep269 79029732885 549755813888 1276415703901 7409059103768576 Bool.false 45128286823 274877906944 638869094217 3704529551884288 Bool.false 640748762069199992389632 1165515208539 1099511627776 396460936126427 74090591037685760 Bool.false 23262920383160574279680 84630011345 549755813888 6194388261333 1157665484963840 (ep270 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep329 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep330 ep342) rfl rfl

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz71 := (@Inv.inv Real Real.instInv (Real.sqrt qz382))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz267 qz283 qz566)

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.true 197329963431 1099511627776 12439155416279 74090591037685760 Bool.true 63269090127 549755813888 6208908607397 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 22 qz14 rfl)

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep345 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz382) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz382) (Real.sqrt qz383) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz383) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep346 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 134770 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 104500 1000 0 1 3480203401436407 1125899906842624 25000000013477 3369250000000000000 727362510900209063 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz383) Bool.false 58388124189833310502912 18889465931478580854784 1000000000539080 134770000000000000000 3480203401436407 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep348 := nat_lit 1371510014762568416731311238729442179942843883677755554046493019994081593323105

noncomputable def ep349 := nat_lit 454472489222695381826231016628733142261645241553531932784532732645068435041

noncomputable def ep350 := nat_lit 3591314226062271013201906013121616331905691317336368351754401999369740728856161

noncomputable def ep351 := BSN.sin_dyadic_bound_f 2148762667 2147483648 3 2 1048576 269804 ep348 ep214 ep349 ep350 ep216 ep349 882683 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2148762667) qz291 0 2 ep348 ep214 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2148762667) qz292 0 2 ep350 ep216 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 338704563) qz20)

noncomputable def ep352 := @Enclosure.Real.IsNear.cos_image qz72 qz384 Bool.false 338704563 1048576 407 524288 Bool.true 882683 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 727362510900209063 2251799813685248 5225000002816693 6738500000000000000 338704563 1048576 407 524288 (ep347 rfl) rfl) (Enclosure.sfrac_false_div 338704563 1048576) (BSN.cos_reduce1 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151205730429987807297536) qz21) 226375608064910080 72057594037927936 Bool.false 882683 1048576 51 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 338704563 1048576 226375608064910080 72057594037927936 51 151205730429987807297536 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 882683 1048576 151205730429987807297536 151115727451828646838272 2148762667 2147483648 269804 269540 (ep351 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep353 := nat_lit 762151995974414762798206790857080648031473999928332433107067025655665360039521

noncomputable def ep354 := nat_lit 2285547042944798897630967910537984477809898709301890235455632011501705943248481

noncomputable def ep355 := BSN.cos_dyadic_bound_f 2148762667 2147483648 3 2 1048576 269804 ep353 ep122 ep349 ep354 ep125 ep349 566022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2148762667) qz286 0 2 ep353 ep122 ep349 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2148762667) qz287 0 2 ep354 ep125 ep349 rfl rfl rfl rfl) rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.sin_image qz72 qz384 Bool.false 338704563 1048576 407 524288 Bool.false 566022 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 727362510900209063 2251799813685248 5225000002816693 6738500000000000000 338704563 1048576 407 524288 (ep347 rfl) rfl) (Enclosure.sfrac_false_div 338704563 1048576) (BSN.sin_reduce1 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151205730429987807297536) qz21) 226375608064910080 72057594037927936 Bool.false 566022 1048576 51 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 338704563 1048576 226375608064910080 72057594037927936 51 151205730429987807297536 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 566022 1048576 151205730429987807297536 151115727451828646838272 2148762667 2147483648 269804 269540 (ep355 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz385 := (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep345 rfl rfl) rfl)

noncomputable def ep357 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.true 197329963431 1099511627776 12439155416279 74090591037685760 Bool.true 63269090127 549755813888 6208908607397 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz71 (Real.cos qz72) 223557 1048576 1 1048576 882683 1048576 27687839 35329146880 197329963431 1099511627776 12439155416279 74090591037685760 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.true 882683 1048576 55375678 70658293760 882683 1048576 27687839 35329146880 (ep352 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz71 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 223557 1048576 1 1048576 283011 524288 27687839 35329146880 63269090127 549755813888 6208908607397 37045295518842880 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.false 283011 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.false 566022 1048576 55375678 70658293760 283011 524288 27687839 35329146880 (ep356 rfl rfl) rfl)) rfl)

noncomputable def ep358 := @ep267 197329963431 1099511627776 12439155416279 74090591037685760 Bool.true 63269090127 549755813888 6208908607397 37045295518842880 Bool.false 1064530934837402620919808 242046311277 274877906944 204450045771353 37045295518842880 Bool.false 11743290629599038275584 10680460609 274877906944 204429332970053 37045295518842880 (ep268 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep344 ep357) rfl rfl

noncomputable abbrev qz386 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz73 := (@Inv.inv Real Real.instInv (Real.sqrt qz386))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz267 qz283 qz567)

noncomputable def ep359 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74)))) Bool.false 136452253941 1099511627776 12149613843127 74090591037685760 Bool.true 92117575545 549755813888 6082170181591 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 23 qz14 rfl)

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep360 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz386) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz386) (Real.sqrt qz387) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz387) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep361 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 134770 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz567 104500 1000 0 1 3530250507853047 1125899906842624 25000000013477 3369250000000000000 737822356141286823 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz387) Bool.false 59227775304360265777152 18889465931478580854784 1000000000539080 134770000000000000000 3530250507853047 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep363 := nat_lit 576832708538908534240561654223498674502294143035957253374887040581871285108736

noncomputable def ep364 := nat_lit 260405447076544535496673082248498819576656787297206844006493281994271686656

noncomputable def ep365 := nat_lit 1729977314722572513650691616505999025867729115533277346436648135181625311952896

noncomputable def ep366 := BSN.cos_dyadic_bound_f 2004270148 2147483648 3 2 1048576 269804 ep363 ep122 ep364 ep365 ep125 ep364 624087 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2004270148) qz286 0 2 ep363 ep122 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2004270148) qz287 0 2 ep365 ep125 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85893827) qz44)

noncomputable def ep367 := @Enclosure.Real.IsNear.cos_image qz74 qz388 Bool.false 85893827 262144 407 524288 Bool.false 624087 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 737822356141286823 2251799813685248 5225000002816693 6738500000000000000 85893827 262144 407 524288 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 85893827 262144) (BSN.cos_reduce0 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35259493341927240105984) qz45) 226375608064910080 72057594037927936 Bool.false 624087 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 85893827 262144 226375608064910080 72057594037927936 52 35259493341927240105984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 624087 1048576 35259493341927240105984 37778931862957161709568 2004270148 2147483648 269804 269540 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep368 := nat_lit 1038090551012374126004613639136498815048468132034885290599591478421772895846400

noncomputable def ep369 := nat_lit 2718386977165713067430803012748142184180959091959551711918157644838557334962176

noncomputable def ep370 := BSN.sin_dyadic_bound_f 2004270148 2147483648 3 2 1048576 269804 ep368 ep214 ep364 ep369 ep216 ep364 842630 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2004270148) qz291 0 2 ep368 ep214 ep364 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2004270148) qz292 0 2 ep369 ep216 ep364 rfl rfl rfl rfl) rfl rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.sin_image qz74 qz388 Bool.false 85893827 262144 407 524288 Bool.false 842630 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 737822356141286823 2251799813685248 5225000002816693 6738500000000000000 85893827 262144 407 524288 (ep362 rfl) rfl) (Enclosure.sfrac_false_div 85893827 262144) (BSN.sin_reduce0 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35259493341927240105984) qz45) 226375608064910080 72057594037927936 Bool.false 842630 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 85893827 262144 226375608064910080 72057594037927936 52 35259493341927240105984 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 842630 1048576 35259493341927240105984 37778931862957161709568 2004270148 2147483648 269804 269540 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz389 := (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep360 rfl rfl) rfl)

noncomputable def ep372 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74))) Bool.false 136452253941 1099511627776 12149613843127 74090591037685760 Bool.true 92117575545 549755813888 6082170181591 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ff qz73 (Real.cos qz74) 218643 1048576 1 1048576 624087 1048576 27687839 35329146880 136452253941 1099511627776 12149613843127 74090591037685760 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz74) Bool.false 624087 1048576 55375678 70658293760 624087 1048576 27687839 35329146880 (ep367 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz73 (@Neg.neg Real Real.instNeg (Real.sin qz74)) 218643 1048576 1 1048576 421315 524288 27687839 35329146880 92117575545 549755813888 6082170181591 37045295518842880 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz74) Bool.false 421315 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz74) Bool.false 842630 1048576 55375678 70658293760 421315 524288 27687839 35329146880 (ep371 rfl rfl) rfl)) rfl)

noncomputable def ep373 := @ep265 136452253941 1099511627776 12149613843127 74090591037685760 Bool.true 92117575545 549755813888 6082170181591 37045295518842880 Bool.false 303640443670443910496256 1104637499049 1099511627776 421049705385833 74090591037685760 Bool.true 19449441043765880946688 70756654327 549755813888 52627875787911 9261323879710720 (ep266 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep359 ep372) rfl rfl

noncomputable abbrev qz390 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz75 := (@Inv.inv Real Real.instInv (Real.sqrt qz390))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz267 qz283 qz568)

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq qz60 (Complex.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76)))) Bool.false 139108012841 1099511627776 2379280982187 14818118207537152 Bool.false 88063135965 549755813888 1190805921407 7409059103768576 (BSN.cpow_neg_s_mk qz13 104500 1000 24 qz14 rfl)

noncomputable abbrev qz391 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep375 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz390) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz390) (Real.sqrt qz391) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz391) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep376 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 134770 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz568 104500 1000 0 1 3578169457974519 1125899906842624 25000000013477 3369250000000000000 747837416716674471 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 60031721881041427759104 18889465931478580854784 1000000000539080 134770000000000000000 3578169457974519 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep378 := nat_lit 4247479380724033402832231468628956176

noncomputable def ep379 := BSN.sin_dyadic_bound_f 1435597918 2147483648 2 1 1048576 269804 ep378 ep61 ep378 ep378 ep62 ep378 649919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1435597918) qz291 0 1 ep378 ep61 ep378 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1435597918) qz292 0 1 ep378 ep62 ep378 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz392 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174119467) qz48)

noncomputable def ep380 := @Enclosure.Real.IsNear.cos_image qz76 qz392 Bool.false 174119467 524288 407 524288 Bool.false 649919 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 747837416716674471 2251799813685248 5225000002816693 6738500000000000000 174119467 524288 407 524288 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 174119467 524288) (BSN.cos_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50510611333173460598784) qz333) 226375608064910080 72057594037927936 Bool.false 649919 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 174119467 524288 226375608064910080 72057594037927936 52 50510611333173460598784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 649919 1048576 50510611333173460598784 75557863725914323419136 1435597918 2147483648 269804 269540 (ep379 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep381 := nat_lit 151778986478758557273088153321551294893906903720133950936694194201998469529856

noncomputable def ep382 := nat_lit 18041081089675818298446497893194036824625669809012690771715878607328542976

noncomputable def ep383 := nat_lit 455300877274096320182667566968867496608071459820783827428539150848780751503616

noncomputable def ep384 := BSN.cos_dyadic_bound_f 1435597918 2147483648 3 2 1048576 269804 ep381 ep122 ep382 ep383 ep125 ep382 822870 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1435597918) qz286 0 2 ep381 ep122 ep382 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1435597918) qz287 0 2 ep383 ep125 ep382 rfl rfl rfl rfl) rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.sin_image qz76 qz392 Bool.false 174119467 524288 407 524288 Bool.true 822870 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 747837416716674471 2251799813685248 5225000002816693 6738500000000000000 174119467 524288 407 524288 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 174119467 524288) (BSN.sin_reduce3 qz392 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50510611333173460598784) qz333) 226375608064910080 72057594037927936 Bool.false 822870 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 174119467 524288 226375608064910080 72057594037927936 52 50510611333173460598784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 822870 1048576 50510611333173460598784 75557863725914323419136 1435597918 2147483648 269804 269540 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz393 := (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep375 rfl rfl) rfl)

noncomputable def ep386 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76))) Bool.false 139108012841 1099511627776 2379280982187 14818118207537152 Bool.false 88063135965 549755813888 1190805921407 7409059103768576 (@Enclosure.Real.IsNear.mulLit_ff qz75 (Real.cos qz76) 214039 1048576 1 1048576 649919 1048576 27687839 35329146880 139108012841 1099511627776 2379280982187 14818118207537152 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.false 649919 1048576 55375678 70658293760 649919 1048576 27687839 35329146880 (ep380 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz75 (@Neg.neg Real Real.instNeg (Real.sin qz76)) 214039 1048576 1 1048576 411435 524288 27687839 35329146880 88063135965 549755813888 1190805921407 7409059103768576 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz76) Bool.true 411435 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz76) Bool.true 822870 1048576 55375678 70658293760 411435 524288 27687839 35329146880 (ep385 rfl rfl) rfl)) rfl)

noncomputable def ep387 := @ep262 139108012841 1099511627776 2379280982187 14818118207537152 Bool.false 88063135965 549755813888 1190805921407 7409059103768576 Bool.false ep263 621872755945 549755813888 6764782973387 1157665484963840 Bool.false 9514338898436417388544 8653240819 274877906944 216465532758679 37045295518842880 (ep264 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep373 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep374 ep386) rfl rfl

theorem EMRow32.d8 : Enclosure.Complex.IsNear qz59 Bool.false 621872755945 549755813888 6764782973387 1157665484963840 Bool.false 8653240819 274877906944 216465532758679 37045295518842880 := ep261 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow32.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow32.d10 : @Eq Nat (Nat.pow 27 1) 27 := @Eq.refl Nat 27

noncomputable def ep388 := nat_lit 81294415349391658323863847309559

noncomputable def ep389 := nat_lit 12348735247004291449801023474892800

noncomputable abbrev qz602 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz569 := qz602

noncomputable abbrev qz394 := qz569

noncomputable abbrev qz77 := qz394

noncomputable abbrev qz570 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz395 := qz570

noncomputable abbrev qz78 := qz395

noncomputable abbrev qz603 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz604 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz571 := (@HAdd.hAdd Complex Complex Complex qz600 (@HAdd.hAdd Complex Complex Complex qz600 qz603 (@HMul.hMul Complex Complex Complex qz602 Complex.I (@HDiv.hDiv Complex Complex Complex qz604 (↑qz601) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz396 := qz571

noncomputable abbrev qz79 := (Complex.Stirling.logGammaStirling 1 qz396)

noncomputable abbrev qz572 := (@HAdd.hAdd Complex Complex Complex qz600 qz603 (@HMul.hMul Complex Complex Complex qz602 Complex.I (@HDiv.hDiv Complex Complex Complex qz604 (↑qz601) (2 : Complex))))

noncomputable abbrev qz397 := qz572

noncomputable abbrev qz80 := qz397

noncomputable abbrev qz81 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz283 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz398 := (@instHSub Real Real.instSub)

noncomputable def ep390 := Complex.re (@HMul.hMul Complex Complex Complex qz77 (Complex.exp (@HMul.hMul Complex Complex Complex qz77 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81))) (zetaApproximant qz5 1 27))

noncomputable def ep391 := @Enclosure.Real.IsNear.of_eq ep390 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.im (zetaApproximant qz5 1 27))))

noncomputable def ep392 := nat_lit 5646221437141467243651425

noncomputable def ep393 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.im (zetaApproximant qz5 1 27))) ep392

noncomputable def ep394 := nat_lit 5439087053737519277408256

noncomputable def ep395 := nat_lit 162336740050855971991821573741299

noncomputable def ep396 := nat_lit 24697470494008582899602046949785600

noncomputable def ep397 := nat_lit 84030215975781551968706959273

noncomputable def ep398 := nat_lit 8232490164669527633200682316595200

noncomputable def ep399 := nat_lit 1137427456253857854762297703911731426587391819776

noncomputable def ep400 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.re (zetaApproximant qz5 1 27)) 1048575 1048576 11245899

noncomputable def ep401 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) Bool.false 1048575 1048576 22491798

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 98826671) qz20)

noncomputable def ep402 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81) qz399 Bool.false 98826671 1048576 163

noncomputable def ep403 := nat_lit 42394976256000000000000000

noncomputable def ep404 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81) Bool.false 3395658585273451517 36028797018963968 13149096170911428522673 ep403

noncomputable def ep405 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81 5550617400513840125 36028797018963968 4699017170911428522673 ep403 15679389 262144

noncomputable def ep406 := nat_lit 14131658752000000000000000

noncomputable def ep407 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 2959556084171399117 36028797018963968 2878141034516856218531 ep406 Bool.false 5550617400513840125 36028797018963968

noncomputable def ep408 := @Enclosure.Complex.IsNear.subLitP qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 2674482664355916517 36028797018963968 2825712234361407972259 ep406 Bool.false 5662771079500633469 36028797018963968 4384444370869033546417

noncomputable def ep409 := nat_lit 13328655677856397358350496046252032

noncomputable def ep410 := nat_lit 1562359903539395096231775567872000

noncomputable abbrev qz605 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz573 := qz605

noncomputable abbrev qz400 := (@HSub.hSub Complex Complex Complex qz570 qz571 qz573)

noncomputable abbrev qz401 := (Complex.log qz571)

noncomputable abbrev qz82 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz400 qz401) qz396)

noncomputable abbrev qz402 := qz573

noncomputable abbrev qz83 := (@HMul.hMul Complex Complex Complex qz394 qz402 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz574 := qz604

noncomputable abbrev qz403 := qz574

noncomputable abbrev qz84 := qz403

noncomputable abbrev qz85 := (@instHMul Nat instMulNat)

noncomputable abbrev qz575 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz404 := qz575

noncomputable abbrev qz86 := qz404

noncomputable abbrev qz87 := qz396

noncomputable abbrev qz405 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz88 := qz405

noncomputable abbrev qz406 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz89 := qz406

noncomputable abbrev qz407 := (@instHSub Int Int.instSub)

noncomputable abbrev qz408 := (@instHMul Int Int.instMul)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq qz79 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz82 qz83) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k)))))) Bool.true 2674482664355916517

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz82 qz83) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) Bool.true 2674485134227401445 36028797018963968

noncomputable def ep413 := nat_lit 91894524617020850756969824256

noncomputable def ep414 := nat_lit 194571332729518694085104238592

noncomputable def ep415 := @ep412 86233856216589563 431264000000000000000 Bool.false 5662828435405116797 36028797018963968 5575000015538981 53908000000000000000 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104 Bool.true ep413 2674482664355916517 36028797018963968 2825712234361407972259 ep406 Bool.false ep414

noncomputable def ep416 := @Enclosure.Complex.IsNear.addLitP qz82 qz83 Bool.true 2707593353485085413 36028797018963968 10625000001927211 53908000000000000000

noncomputable def ep417 := @ep416 Bool.false 5662828435405116797 36028797018963968 5575000015538981 53908000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true 350550115513453962199040 2674485134227401445 36028797018963968 86233856216589563 431264000000000000000 Bool.false 5662828435405116797 5662828435405116797 36028797018963968

noncomputable abbrev qz90 := (@HMul.hMul Complex Complex Complex qz394 qz400 qz401)

noncomputable def ep418 := @Enclosure.Complex.IsNear.subLitP qz90 qz87 Bool.true 2626528560192416485 36028797018963968 10625000001927211 53908000000000000000 Bool.false 7545333079645984125

noncomputable def ep419 := @ep418 36028797018963968 5575000015538981 53908000000000000000 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 Bool.true 10830373413940341652000 2707593353485085413 36028797018963968 10625000001927211 53908000000000000000 Bool.false 22651313741620467188000 5662828435405116797 36028797018963968 5575000015538981 53908000000000000000

noncomputable abbrev qz91 := qz400

noncomputable abbrev qz92 := qz401

noncomputable def ep420 := @Enclosure.Complex.IsNear.mul qz91 qz92 Bool.true 2626528560192416485 36028797018963968 10625000001927211 53908000000000000000 Bool.false 7545333079645984125 36028797018963968 5575000015538981

noncomputable abbrev qz93 := (Complex.re qz400)

noncomputable abbrev qz94 := (Complex.re qz401)

noncomputable abbrev qz95 := (Complex.im qz400)

noncomputable abbrev qz96 := (Complex.im qz401)

noncomputable def ep421 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz93 qz94) (@HMul.hMul Real Real Real qz0 qz95 qz96) 249488277980165707 36028797018963968 350000001037729 107816000000000000000 179751052385786387 2251799813685248

noncomputable def ep422 := nat_lit 5914416522480266127755850316513280

noncomputable def ep423 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz94 7000 4000 0 1 35641182568595101 9007199254740992 50000000148247 26954000000000000000

noncomputable def ep424 := @Enclosure.Complex.IsNear.re_isNear qz91 Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable abbrev qz97 := (Enclosure.sfrac Bool.false 209000 4000)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq qz91 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz97) Bool.false 7000 4000 0 1 Bool.false 209000 4000 0

noncomputable abbrev qz409 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz98 := qz409

noncomputable abbrev qz410 := (Complex.log (Complex.mk qz98 qz97))

noncomputable def ep426 := @Enclosure.Complex.IsNear.of_eq qz92 qz410 Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000

noncomputable def ep427 := nat_lit 21095002396047264010402545000000000000000000000000000000000000000000

noncomputable def ep428 := nat_lit 146936325170627687889839394240000000000000000000000000000000000000

noncomputable def ep429 := nat_lit 26486565965886475902459840000000000000000000000000000000000000

noncomputable def ep430 := BSN.log_dyadic_bound 10994000000 76530000000 4 3 ep427 1048576 269540 ep428 ep429 303367 87524000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10994000000) (BSN.artanhQ 76530000000) 0 3 ep428 ep427 ep429 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz99 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz411 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz412 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz576 := (Real.log (Enclosure.sfrac Bool.false 43762000000 16000000))

noncomputable def ep431 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz576 1 2 0 1 35641182568595101 4503599627370496 50000000148247 13477000000000000000 35641182568595101 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 43762000000 16000000 35641182568595101 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43762000000) qz412)) Bool.false 298979909224377413009408 37778931862957161709568 1000000002964940 269540000000000000000 35641182568595101 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 43762000000 16000000 11 87524000000 65536000000 303367 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep430 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep432 := BSN.arctan_dyadic_bound_f 9000 209000 1 0 1048576 269540 0 1 1 0 1 1 45126 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz100 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz101 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz411 BSN.pi_near_15 rfl)

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 209000)))

noncomputable def ep433 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz413 884279719003555 562949953421312 1 2000000000000000 45126 1048576 1 269540 901830811035781562368 860052882228643 562949953421312 100000000013477 26954000000000000000 qz101 (ep432 rfl) rfl rfl

noncomputable abbrev qz414 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 209000) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep434 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (ep426 (@congrArg Complex Complex qz87 (Complex.mk qz98 qz97) Complex.log (BSN.w_shift_mk qz13 Bool.false 104500 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz410 Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz410) (@HMul.hMul Real Real Real qz0 qz99 qz576) Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 9000 209000 4000 43762000000 16000000 rfl rfl rfl) (ep431 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz410) qz414 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 9000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz414 (@HSub.hSub Real Real Real qz398 qz100 qz413) Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 209000 9000 rfl rfl) ep433))))

noncomputable def ep435 := @Enclosure.Real.IsNear.mulLit_ff qz95 qz96 209000 4000 0 1 860052882228643 562949953421312 100000000013477 26954000000000000000

noncomputable def ep436 := @Enclosure.Complex.IsNear.im_isNear qz91 Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable def ep437 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (ep426 (@congrArg Complex Complex qz87 (Complex.mk qz98 qz97) Complex.log (BSN.w_shift_mk qz13 Bool.false 104500 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz410 Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz410) (@HMul.hMul Real Real Real qz0 qz99 qz576) Bool.false 35641182568595101 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 9000 209000 4000 43762000000 16000000 rfl rfl rfl) (ep431 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz410) qz414 Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 9000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz414 (@HSub.hSub Real Real Real qz398 qz100 qz413) Bool.false 860052882228643 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 209000 9000 rfl rfl) ep433))))

noncomputable abbrev qz102 := (@ep425 1 (BSN.w_sub_half_mk qz283 Bool.false 104500 1000 2 qz285 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 209000 4000) Bool.false 7000 4000 0 1 Bool.false 209000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 209000 4000)))

noncomputable def ep438 := @ep421 20900000002816693 107816000000000000000 ep422 2626528560192416485 36028797018963968 10625000001927211 53908000000000000000 (@ep423 249488277980165707 36028797018963968 350000001037729 107816000000000000000 (ep424 qz102) ep434 rfl) (@ep435 179751052385786387 2251799813685248 20900000002816693 107816000000000000000 (ep436 qz102) ep437 rfl) rfl

noncomputable def ep439 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz93 qz96) (@HMul.hMul Real Real Real qz0 qz95 qz94) 6020370175600501 2251799813685248 700000000094339 107816000000000000000 7449007156836376109 36028797018963968

noncomputable def ep440 := nat_lit 16990579622939965561037219954688000

noncomputable def ep441 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz96 7000 4000 0 1 860052882228643 562949953421312 100000000013477 26954000000000000000

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff qz95 qz94 209000 4000 0 1 35641182568595101 9007199254740992 50000000148247 26954000000000000000

noncomputable def ep443 := @ep439 10450000030983623 107816000000000000000 ep440 7545333079645984125 36028797018963968 5575000015538981 53908000000000000000 (@ep441 6020370175600501 2251799813685248 700000000094339 107816000000000000000 (ep424 qz102) ep437 rfl) (@ep442 7449007156836376109 36028797018963968 10450000030983623 107816000000000000000 (ep436 qz102) ep434 rfl) rfl

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq qz87 (Complex.mk qz98 qz97) Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 104500 1000 2 qz14 rfl)

noncomputable abbrev qz415 := (ep444 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 209000 4000) Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 209000 4000)))

noncomputable abbrev qz103 := qz415

noncomputable def ep445 := ep419 (@ep420 53908000000000000000 (ep438 rfl) (ep443 rfl)) qz103 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz104 := qz402

noncomputable def ep446 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz104) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz104) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz104) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.of_eq qz402 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz282) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz282 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz411 qz294))

noncomputable def ep448 := ep447 (@Enclosure.Complex.IsNear.re_isNear qz104 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz105) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow32.d4)

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz104) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep450 := ep449 (@Enclosure.Complex.IsNear.im_isNear qz104 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz105) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz17)

noncomputable def ep451 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz104) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz104) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep452 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz104) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep453 := ep452 (@Enclosure.Complex.IsNear.re_isNear qz104 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz105) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz17)

noncomputable def ep454 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz104) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep455 := ep454 (@Enclosure.Complex.IsNear.im_isNear qz104 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz105) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow32.d4)

noncomputable def ep456 := @ep417 5575000015538981 53908000000000000000 (ep445 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz104 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep446 131072 3 1048576 (ep448 rfl) (ep450 rfl) rfl rfl) (@ep451 1 0 1 (ep453 rfl) (ep455 rfl) rfl rfl))

noncomputable abbrev qz106 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz416 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz107 := (@HMul.hMul Complex Complex Complex qz394 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz416) (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 (2 : Complex) qz416) (1 : Complex)))

noncomputable abbrev qz417 := (@HPow.hPow Complex Int Complex qz575 qz571 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz108 := qz417

noncomputable def ep457 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz108)) Bool.false 2355453 34359738368 3 34359738368

noncomputable def ep458 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz108) Bool.false 0 1 0 1 Bool.false

noncomputable def ep459 := @ep458 0 1 0 1 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104 Bool.false 2355453 2355453 34359738368 3 34359738368 Bool.true 54698853 54698853 34359738368 209

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz87 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep461 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz108 Bool.false 2355453 34359738368 3 34359738368 Bool.true 54698853 34359738368 209 103079215104

noncomputable abbrev qz109 := (Complex.re qz417)

noncomputable abbrev qz110 := (Complex.im qz417)

noncomputable def ep462 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz109) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz110) 2355453 34359738368 3 34359738368 0 1 0

noncomputable def ep463 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz109 1 12 0 1 7066359 8589934592 9 8589934592 2355453

noncomputable def ep464 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz418 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz17)

noncomputable def ep465 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep464 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz418)

noncomputable def ep466 := @Enclosure.Complex.IsNear.re_isNear qz108 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209 8589934592

noncomputable abbrev qz577 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz419 := (@HPow.hPow Complex Nat Complex qz577 qz571 1)

noncomputable abbrev qz111 := (@Inv.inv Complex Complex.instInv qz419)

noncomputable def ep467 := @Enclosure.Complex.IsNear.of_eq qz108 qz111 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_parts qz111 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209

noncomputable abbrev qz112 := (Complex.re qz419)

noncomputable abbrev qz113 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz114 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz115 := qz419

noncomputable def ep469 := @Enclosure.Real.IsNear.mulLit_ff qz112 (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115)) 9000 4000 0 1 785151 2147483648 1 2147483648

noncomputable def ep470 := @Enclosure.Complex.IsNear.re_isNear qz115 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable def ep471 := @Enclosure.Complex.IsNear.of_eq qz115 qz87 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0

noncomputable def ep472 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115)) Bool.false 785151 2147483648 1 2147483648 785151 2147483648 1

noncomputable abbrev qz116 := (Complex.im qz419)

noncomputable abbrev qz420 := (@instHAdd Real Real.instAdd)

noncomputable def ep473 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 qz112 qz112) (@HMul.hMul Real Real Real qz0 qz116 qz116)) Bool.false 21881 8 0 1

noncomputable def ep474 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz112 qz112) (@HMul.hMul Real Real Real qz0 qz116 qz116) 81 16 0 1 43681 16

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz112 qz112 9000 4000 0 1 9000 4000 0 1

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff qz116 qz116 209000 4000 0 1 209000 4000 0 1

noncomputable def ep477 := @Enclosure.Complex.IsNear.im_isNear qz115 Bool.false 9000 4000 0 1 Bool.false 209000 4000 0 1

noncomputable abbrev qz117 := (ep470 (@ep471 1 (BSN.pow_one_c qz396) qz415))

noncomputable abbrev qz118 := (ep477 (@ep471 1 (BSN.pow_one_c qz396) qz415))

noncomputable def ep478 := @ep474 0 1 700192 21881 8 0 1 (@ep475 81 16 0 1 qz117 qz117 rfl) (@ep476 43681 16 0 1 qz118 qz118 rfl)

noncomputable def ep479 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115) 21881 8 0 1 392575 392576 1073741824 (ep473 (Enclosure.Complex.normSq_eq_mul_add_mul qz115) (ep478 rfl rfl)) rfl

noncomputable def ep480 := @Enclosure.Real.IsNear.of_eq (Complex.re qz111) (@HMul.hMul Real Real Real qz0 qz112 (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115))) Bool.false 7066359 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz115) (@ep469 7066359 8589934592 9 8589934592 qz117 (@ep472 2147483648 (ep479 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep481 := @Enclosure.Real.IsNear.of_eq (Complex.im qz111) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz116) (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115))) Bool.true 164096559 8589934592 209 8589934592 (Enclosure.Complex.inv_im_eq_mul qz115)

noncomputable def ep482 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz116) (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz115)) 209000 4000 0 1 785151 2147483648 1

noncomputable def ep483 := @ep482 2147483648 164096559 8589934592 209 8589934592 (@Enclosure.Real.IsNear.neg qz116 Bool.false 209000 4000 0 1 qz118) (@ep472 2147483648 (ep479 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz110 0 1 0 1 164096559 8589934592 209 8589934592 0

noncomputable def ep485 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep464 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz418)

noncomputable def ep486 := @Enclosure.Complex.IsNear.im_isNear qz108 Bool.false 7066359 8589934592 9 8589934592 Bool.true 164096559 8589934592 209 8589934592

noncomputable abbrev qz119 := (@ep467 8589934592 (BSN.zpow_one_sub_two_mul qz396 1 1 rfl rfl) (@ep468 8589934592 ep480 (ep481 ep483)))

noncomputable def ep487 := @ep462 1 2355453 2355453 34359738368 3 34359738368 (@ep463 34359738368 3 34359738368 ep465 (ep466 qz119) rfl) (@ep484 1 0 1 ep485 (ep486 qz119) rfl) rfl

noncomputable def ep488 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz110) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz109) 54698853 34359738368 209 103079215104 0 1 0

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz110 1 12 0 1 164096559 8589934592 209 8589934592 54698853

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz109 0 1 0 1 7066359 8589934592 9 8589934592 0

noncomputable def ep491 := @ep488 1 54698853 54698853 34359738368 209 103079215104 (@ep489 34359738368 209 103079215104 ep465 (ep486 qz119) rfl) (@ep490 1 0 1 ep485 (ep466 qz119) rfl) rfl

noncomputable abbrev qz120 := (@Enclosure.Complex.IsNear.mk qz282 qz282 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz294 qz294)

noncomputable def ep492 := @ep459 103079215104 (@ep460 0 1 0 1 (BSN.stirling_sum_base qz87) qz120) (ep461 (ep487 rfl) (ep491 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep493 := @ep415 5662771079500633469 36028797018963968 4384444370869033546417 ep403 (ep456 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep457 Bool.true 54698853 34359738368 209 103079215104 (BSN.stirling_sum_succ qz87 0 1 rfl) (ep492 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep494 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 35634177476935325 4503599627370496 50000000148247 13477000000000000000 Bool.false 876200617084323 281474976710656

noncomputable abbrev qz121 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz397 qz416))

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz121) Bool.false 35634177476935325 4503599627370496 50000000148247 13477000000000000000 Bool.false 876200617084323 281474976710656 100000000013477 13477000000000000000

noncomputable def ep496 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz121 Bool.false 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000 Bool.false

noncomputable def ep497 := nat_lit 641928273627120203966473620684800

noncomputable def ep498 := nat_lit 986514193150688928543698583552

noncomputable abbrev qz122 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz397 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz122) Bool.false 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000

noncomputable def ep500 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz122 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz421 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz97))

noncomputable def ep501 := @Enclosure.Complex.IsNear.of_eq qz122 qz421 Bool.false 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000

noncomputable def ep502 := nat_lit 20963038771055250057890625000000000000000000000000000000000000000000

noncomputable def ep503 := nat_lit 144178573144358318142607727040000000000000000000000000000000000000

noncomputable def ep504 := nat_lit 25350991855517756634287040000000000000000000000000000000000000

noncomputable def ep505 := BSN.log_dyadic_bound 10914000000 76450000000 4 3 ep502 1048576 269540 ep503 ep504 301448 87364000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10914000000) (BSN.artanhQ 76450000000) 0 3 ep503 ep502 ep504 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Real.log (Enclosure.sfrac Bool.false 43682000000 16000000)) 1 2 0 1 35632940526354077 4503599627370496 50000000148247 13477000000000000000 35632940526354077 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 43682000000 16000000 35632940526354077 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43682000000) qz412)) Bool.false 298910769962898021154816 37778931862957161709568 1000000002964940 269540000000000000000 35632940526354077 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 43682000000 16000000 11 87364000000 65536000000 301448 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep505 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep507 := BSN.arctan_dyadic_bound_f 1000 209000 1 0 1048576 269540 0 1 1 0 1 1 5017 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz422 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 209000)

noncomputable def ep508 := @Enclosure.Real.IsNear.subLit_ff_p qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz423)) 884279719003555 562949953421312 1 2000000000000000 5017 1048576 1 269540 924410170717556965376 881586237638051 562949953421312 100000000013477 26954000000000000000 qz101 (ep507 rfl) rfl rfl

noncomputable abbrev qz123 := (@HAdd.hAdd Complex Complex Complex qz272 qz397 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz424 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz97)

noncomputable def ep509 := @ep500 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000 Bool.false 35632940526354077 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 881586237638051 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz120) (ep501 (@congrArg Complex Complex qz123 qz424 Complex.log (BSN.w_shift_mk qz13 Bool.false 104500 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz421 Bool.false 35632940526354077 9007199254740992 50000000148247 26954000000000000000 Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz421) (@HMul.hMul Real Real Real qz0 qz99 (Real.log (Enclosure.sfrac Bool.false 43682000000 16000000))) Bool.false 35632940526354077 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 1000 209000 4000 43682000000 16000000 rfl rfl rfl) (ep506 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz421) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz422)) Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 1000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz422)) (@HSub.hSub Real Real Real qz398 qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz423))) Bool.false 881586237638051 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 209000 1000 rfl rfl) ep508)))) rfl rfl

noncomputable abbrev qz425 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz97))

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz121 qz425 Bool.false 35635414427516573 9007199254740992 50000000148247 26954000000000000000 Bool.false 870814996530595 562949953421312 100000000013477 26954000000000000000

noncomputable def ep511 := nat_lit 21002555418715730998288219836480000000000000000000000000000000000000

noncomputable def ep512 := nat_lit 145002101392198585388360350656000000000000000000000000000000000000

noncomputable def ep513 := nat_lit 25687318657909228099853760000000000000000000000000000000000000

noncomputable def ep514 := BSN.log_dyadic_bound 10938000000 76474000000 4 3 ep511 1048576 269540 ep512 ep513 302024 87412000000 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 10938000000) (BSN.artanhQ 76474000000) 0 3 ep512 ep511 ep513 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep515 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Real.log (Enclosure.sfrac Bool.false 43706000000 16000000)) 1 2 0 1 35635414427516573 4503599627370496 50000000148247 13477000000000000000 35635414427516573 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 43706000000 16000000 35635414427516573 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43706000000) qz412)) Bool.false 298931522549980944400384 37778931862957161709568 1000000002964940 269540000000000000000 35635414427516573 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 43706000000 16000000 11 87412000000 65536000000 302024 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep514 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep516 := BSN.arctan_dyadic_bound_f 5000 209000 1 0 1048576 269540 0 1 1 0 1 1 25080 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 209000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 209000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz426 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep517 := @Enclosure.Real.IsNear.subLit_ff_p qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz423)) 884279719003555 562949953421312 1 2000000000000000 25080 1048576 1 269540 913115705802065182720 870814996530595 562949953421312 100000000013477 26954000000000000000 qz101 (ep516 rfl) rfl rfl

noncomputable abbrev qz124 := (@HAdd.hAdd Complex Complex Complex qz272 qz397 qz416)

noncomputable abbrev qz427 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz97)

noncomputable def ep518 := @ep496 35635414427516573 9007199254740992 50000000148247 26954000000000000000 Bool.false 870814996530595 562949953421312 100000000013477 26954000000000000000 Bool.false ep497 35634177476935325 4503599627370496 50000000148247 13477000000000000000 Bool.false ep498 876200617084323 281474976710656 100000000013477 13477000000000000000 (ep499 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep510 (@congrArg Complex Complex qz124 qz427 Complex.log (BSN.w_shift_mk qz13 Bool.false 104500 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz425 Bool.false 35635414427516573 9007199254740992 50000000148247 26954000000000000000 Bool.false 870814996530595 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz425) (@HMul.hMul Real Real Real qz0 qz99 (Real.log (Enclosure.sfrac Bool.false 43706000000 16000000))) Bool.false 35635414427516573 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 5000 209000 4000 43706000000 16000000 rfl rfl rfl) (ep515 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz425) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz426)) Bool.false 870814996530595 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 5000 209000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz426)) (@HSub.hSub Real Real Real qz398 qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz423))) Bool.false 870814996530595 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 209000 5000 rfl rfl) ep517)))) rfl rfl

noncomputable def ep519 := @ep408 ep403 Bool.false 35634177476935325 4503599627370496 50000000148247 13477000000000000000 Bool.false 876200617084323 281474976710656 100000000013477 13477000000000000000 Bool.true ep409 2959556084171399117 36028797018963968 2878141034516856218531 ep406 Bool.false ep410 5550617400513840125 36028797018963968 4699017170911428522673 ep403 (@ep411 36028797018963968 2825712234361407972259 ep406 Bool.false 5662771079500633469 36028797018963968 4384444370869033546417 ep403 (BSN.logGammaStirling_unfold 1 qz87) (ep493 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep494 100000000013477 13477000000000000000 (BSN.log_sum_c_eq qz13 2) (ep495 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep518 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz125 := (@HDiv.hDiv Real Real Real qz270 qz283 (2 : Real))

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_ff qz125 (Real.log Real.pi) 104500 2000 0 1 75021 65536 1 262144 15679389 262144 209 1048576 (@Enclosure.Real.IsNear.of_eq qz125 (Enclosure.sfrac Bool.false 104500 2000) Bool.false 104500 2000 0 1 (BSN.t_half_eq qz13 Bool.false 104500 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 104500 2000)) EMRow32.d5 rfl

noncomputable def ep521 := @ep405 209 1048576 890151524177923674472448 3395658585273451517 36028797018963968 13149096170911428522673 ep403 (@ep407 4699017170911428522673 ep403 (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep520 rfl rfl

noncomputable def ep522 := BSN.cos_dyadic_bound_f 1456640 2147483648 1 0 1048576 269804 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1456640) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1456640) qz287 0 0 rfl) rfl rfl

noncomputable def ep523 := @ep402 524288 Bool.false 1048575 1048576 1 134770 (@ep404 98826671 1048576 163 524288 ep521 rfl) (Enclosure.sfrac_false_div 98826671 1048576) (BSN.cos_reduce0 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102501939462182797312) qz21) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 98826671 1048576 226375608064910080 72057594037927936 15 102501939462182797312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 102501939462182797312 151115727451828646838272 1456640 2147483648 269804 269540 (ep522 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz578 := (@Nat.cast Complex Complex.instNatCast 27)

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz536 qz578 qz537)

noncomputable abbrev qz126 := qz428

noncomputable abbrev qz429 := qz578

noncomputable abbrev qz127 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz403 qz429 (@HSub.hSub Complex Complex Complex qz395 qz271 (1 : Complex))) qz402)

noncomputable abbrev qz128 := (@instHSub Nat instSubNat)

noncomputable abbrev qz430 := qz577

noncomputable abbrev qz129 := qz430

noncomputable abbrev qz130 := qz429

noncomputable def ep524 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 27) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz77 qz126 (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) Bool.false 16153984513672747997 15561352883541639168 727099262928565955791

noncomputable def ep525 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz77 qz126 (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) Bool.false 1111595412131 1099511627776 456042864957063 74090591037685760

noncomputable def ep526 := nat_lit 17761493807696618878352513564672

noncomputable def ep527 := nat_lit 1985467480259166863519383552

noncomputable def ep528 := @ep525 Bool.true 29067754757 274877906944 228006380118309 37045295518842880 Bool.false 421610216835893189 15561352883541639168 1989628710921324203 23302261423498963451904 Bool.false 53724319222820519 576346403094134784 5983947063969418573 69906784270496890355712 Bool.false ep526 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 Bool.true ep527 7223088615352633 576346403094134784

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 27) Bool.false 1111595412131 1099511627776 456042864957063 74090591037685760 Bool.true 29067754757 274877906944 228006380118309

noncomputable abbrev qz431 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable def ep530 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz431 qz7)) Bool.false 1111595412131 1099511627776 456042864957063 74090591037685760 Bool.true 29067754757 274877906944 228006380118309 37045295518842880

noncomputable def ep531 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) (@HPow.hPow Complex Complex Complex qz6 qz431 qz7) Bool.false 128654500945 137438953472 222314100770043 37045295518842880 Bool.false 41506544063 549755813888 111139945747239 18522647759421440 Bool.false

noncomputable abbrev qz432 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep532 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz59 (@HPow.hPow Complex Complex Complex qz6 qz432 qz7)) Bool.false 128654500945 137438953472 222314100770043 37045295518842880 Bool.false 41506544063 549755813888 111139945747239 18522647759421440

noncomputable def ep533 := @Enclosure.Complex.IsNear.addLitP qz59 (@HPow.hPow Complex Complex Complex qz6 qz432 qz7) Bool.false 621872755945 549755813888 6764782973387 1157665484963840 Bool.false 8653240819 274877906944 216465532758679 37045295518842880 Bool.true

noncomputable abbrev qz433 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz433))

noncomputable abbrev qz579 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz267 qz283 qz579)

noncomputable def ep534 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz432 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.true 107254752165 549755813888 5841045621659 37045295518842880 Bool.false 24200062425 549755813888 5814358735799 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 25 qz14 rfl)

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep535 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz433) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz433) (Real.sqrt qz434) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz434) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep536 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 134770 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep537 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz579 104500 1000 0 1 3624129903009015 1125899906842624 25000000013477 3369250000000000000 757443149728884135 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz434) Bool.false 60802810194841294602240 18889465931478580854784 1000000000539080 134770000000000000000 3624129903009015 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep536 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep538 := nat_lit 51578913024702645438012681883488256

noncomputable def ep539 := BSN.cos_dyadic_bound_f 476560504 2147483648 2 1 1048576 269804 ep538 ep57 ep538 ep538 ep58 ep538 1022862 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 476560504) qz286 0 1 ep538 ep57 ep538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 476560504) qz287 0 1 ep538 ep58 ep538 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22044497) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep540 := @Enclosure.Real.IsNear.cos_image qz132 qz435 Bool.false 22044497 65536 407 524288 Bool.true 1022862 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 757443149728884135 2251799813685248 5225000002816693 6738500000000000000 22044497 65536 407 524288 (ep537 rfl) rfl) (Enclosure.sfrac_false_div 22044497 65536) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2095935262263884120064) qz290) 226375608064910080 72057594037927936 Bool.false 1022862 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 22044497 65536 226375608064910080 72057594037927936 53 2095935262263884120064 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022862 1048576 2095935262263884120064 9444732965739290427392 476560504 2147483648 269804 269540 (ep539 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep541 := BSN.sin_dyadic_bound_f 476560504 2147483648 2 1 1048576 269804 ep538 ep61 ep538 ep538 ep62 ep538 230790 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 476560504) qz291 0 1 ep538 ep61 ep538 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 476560504) qz292 0 1 ep538 ep62 ep538 rfl rfl rfl rfl) rfl rfl

noncomputable def ep542 := @Enclosure.Real.IsNear.sin_image qz132 qz435 Bool.false 22044497 65536 407 524288 Bool.true 230790 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 757443149728884135 2251799813685248 5225000002816693 6738500000000000000 22044497 65536 407 524288 (ep537 rfl) rfl) (Enclosure.sfrac_false_div 22044497 65536) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2095935262263884120064) qz290) 226375608064910080 72057594037927936 Bool.false 230790 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 22044497 65536 226375608064910080 72057594037927936 53 2095935262263884120064 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230790 1048576 2095935262263884120064 9444732965739290427392 476560504 2147483648 269804 269540 (ep541 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz436 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep535 rfl rfl) rfl)

noncomputable def ep543 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.true 107254752165 549755813888 5841045621659 37045295518842880 Bool.false 24200062425 549755813888 5814358735799 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz131 (Real.cos qz132) 209715 1048576 1 1048576 511431 524288 27687839 35329146880 107254752165 549755813888 5841045621659 37045295518842880 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.true 1022862 1048576 55375678 70658293760 511431 524288 27687839 35329146880 (ep540 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 209715 1048576 1 1048576 115395 524288 27687839 35329146880 24200062425 549755813888 5814358735799 37045295518842880 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 115395 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 230790 1048576 55375678 70658293760 115395 524288 27687839 35329146880 (ep542 rfl rfl) rfl)) rfl)

noncomputable def ep544 := @ep533 107254752165 549755813888 5841045621659 37045295518842880 Bool.false 24200062425 549755813888 5814358735799 37045295518842880 Bool.false 282914239509491760496640 128654500945 137438953472 222314100770043 37045295518842880 Bool.false 11409231956516349673472 41506544063 549755813888 111139945747239 18522647759421440 EMRow32.d8 (ep534 ep543) rfl rfl

noncomputable abbrev qz437 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz437))

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz134 := (@HMul.hMul Real Real Real qz267 qz283 qz580)

noncomputable def ep545 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz431 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)))) Bool.false 82359404571 1099511627776 11414663416977 74090591037685760 Bool.true 99642053577 549755813888 5726488623831 37045295518842880 (BSN.cpow_neg_s_mk qz13 104500 1000 26 qz14 rfl)

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep546 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz437) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz437) (Real.sqrt qz438) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz438) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep547 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 134770 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep548 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz580 104500 1000 0 1 3668288609262839 1125899906842624 25000000013477 3369250000000000000 766672319335933351 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz438) Bool.false 61543670347942250676224 18889465931478580854784 1000000000539080 134770000000000000000 3668288609262839 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep547 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep549 := nat_lit 1469439850686578641613916720625900456943751856371924321443587355539055312383521

noncomputable def ep550 := nat_lit 1687516668223566505774422680123140649172351701993203882485036277528023019041

noncomputable def ep551 := nat_lit 4404944518723288791830201316517455089532910865711786556565791994062109891112481

noncomputable def ep552 := BSN.cos_dyadic_bound_f 2531663667 2147483648 3 2 1048576 269804 ep549 ep122 ep550 ep551 ep125 ep550 400497 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2531663667) qz286 0 2 ep549 ep122 ep550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2531663667) qz287 0 2 ep551 ep125 ep550 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 357009619) qz20)

noncomputable def ep553 := @Enclosure.Real.IsNear.cos_image qz134 qz439 Bool.false 357009619 1048576 407 524288 Bool.false 400497 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 766672319335933351 2251799813685248 5225000002816693 6738500000000000000 357009619 1048576 407 524288 (ep548 rfl) rfl) (Enclosure.sfrac_false_div 357009619 1048576) (BSN.cos_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 178149992984079119679488) qz21) 226375608064910080 72057594037927936 Bool.false 400497 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 357009619 1048576 226375608064910080 72057594037927936 54 178149992984079119679488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400497 1048576 178149992984079119679488 151115727451828646838272 2531663667 2147483648 269804 269540 (ep552 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep554 := nat_lit 2643641717901262701700430558982522309979415460107869215492469210948277143875105

noncomputable def ep555 := nat_lit 6921091377040468920587016684424501917466475730860239900956253112796156672880161

noncomputable def ep556 := BSN.sin_dyadic_bound_f 2531663667 2147483648 3 2 1048576 269804 ep554 ep214 ep550 ep555 ep216 ep550 969078 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2531663667) qz291 0 2 ep554 ep214 ep550 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2531663667) qz292 0 2 ep555 ep216 ep550 rfl rfl rfl rfl) rfl rfl

noncomputable def ep557 := @Enclosure.Real.IsNear.sin_image qz134 qz439 Bool.false 357009619 1048576 407 524288 Bool.false 969078 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 766672319335933351 2251799813685248 5225000002816693 6738500000000000000 357009619 1048576 407 524288 (ep548 rfl) rfl) (Enclosure.sfrac_false_div 357009619 1048576) (BSN.sin_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 178149992984079119679488) qz21) 226375608064910080 72057594037927936 Bool.false 969078 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 357009619 1048576 226375608064910080 72057594037927936 54 178149992984079119679488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 969078 1048576 178149992984079119679488 151115727451828646838272 2531663667 2147483648 269804 269540 (ep556 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz440 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep546 rfl rfl) rfl)

noncomputable def ep558 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz134)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134))) Bool.false 82359404571 1099511627776 11414663416977 74090591037685760 Bool.true 99642053577 549755813888 5726488623831 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ff qz133 (Real.cos qz134) 205643 1048576 1 1048576 400497 1048576 27687839 35329146880 82359404571 1099511627776 11414663416977 74090591037685760 qz440 (@Enclosure.Real.IsNear.recentre' (Real.cos qz134) Bool.false 400497 1048576 55375678 70658293760 400497 1048576 27687839 35329146880 (ep553 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz133 (@Neg.neg Real Real.instNeg (Real.sin qz134)) 205643 1048576 1 1048576 484539 524288 27687839 35329146880 99642053577 549755813888 5726488623831 37045295518842880 qz440 (@Enclosure.Real.IsNear.neg (Real.sin qz134) Bool.false 484539 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz134) Bool.false 969078 1048576 55375678 70658293760 484539 524288 27687839 35329146880 (ep557 rfl rfl) rfl)) rfl)

noncomputable def ep559 := @ep531 82359404571 1099511627776 11414663416977 74090591037685760 Bool.true 99642053577 549755813888 5726488623831 37045295518842880 Bool.false 152776510127561173368832 1111595412131 1099511627776 456042864957063 74090591037685760 Bool.true 31960334348662637330432 29067754757 274877906944 228006380118309 37045295518842880 (ep532 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep544 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep545 ep558) rfl rfl

noncomputable def ep560 := @Enclosure.Complex.IsNear.mul qz126 (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 421610216835893189 15561352883541639168 1989628710921324203 23302261423498963451904 Bool.false

noncomputable abbrev qz135 := (Complex.re qz428)

noncomputable abbrev qz136 := (Complex.im qz428)

noncomputable def ep561 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) 597809226007073899 15561352883541639168 15865310577497884097

noncomputable def ep562 := nat_lit 3280412681744921110796253333213413376

noncomputable def ep563 := @Enclosure.Real.IsNear.mulLit_ff qz135 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 84426445831 1099511627776 2240600723093 14818118207537152 7080829

noncomputable abbrev qz441 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz137 := (@Inv.inv Real Real.instInv (Real.sqrt qz441))

noncomputable abbrev qz442 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz541 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable abbrev qz138 := (Real.cos qz442)

noncomputable abbrev qz139 := (Real.sin qz442)

noncomputable abbrev qz581 := (@Neg.neg Real Real.instNeg qz139)

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq qz126 (Complex.mk (@HMul.hMul Real Real Real qz0 qz137 qz138) (@HMul.hMul Real Real Real qz0 qz137 qz581)) Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (BSN.cpow_neg_s_mk qz13 104500 1000 27 qz14 rfl)

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15)

noncomputable def ep565 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz441) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz441) (Real.sqrt qz443) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz443) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep566 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 134770 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz444 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz140 := qz444

noncomputable abbrev qz445 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz15))

noncomputable def ep567 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz140 104500 1000 0 1 3710780868205815 1125899906842624 25000000013477 3369250000000000000 775553201455015335 2251799813685248 5225000002816693 6738500000000000000 qz16 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz445 Bool.false 62256572154556490711040 18889465931478580854784 1000000000539080 134770000000000000000 3710780868205815 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep566 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep568 := nat_lit 603396308568751817675415595136004241

noncomputable def ep569 := BSN.sin_dyadic_bound_f 881354573 2147483648 2 1 1048576 269804 ep568 ep61 ep568 ep568 ep62 ep568 418369 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 881354573) qz291 0 1 ep568 ep61 ep568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 881354573) qz292 0 1 ep568 ep62 ep568 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz141 := qz442

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180572551) qz48)

noncomputable def ep570 := @Enclosure.Real.IsNear.cos_image qz141 qz446 Bool.false 180572551 524288 407 524288 Bool.false 418369 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 775553201455015335 2251799813685248 5225000002816693 6738500000000000000 180572551 524288 407 524288 (ep567 rfl) rfl) (Enclosure.sfrac_false_div 180572551 524288) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31009907253385166323712) qz333) 226375608064910080 72057594037927936 Bool.false 418369 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 180572551 524288 226375608064910080 72057594037927936 54 31009907253385166323712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 418369 1048576 31009907253385166323712 75557863725914323419136 881354573 2147483648 269804 269540 (ep569 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep571 := BSN.cos_dyadic_bound_f 881354573 2147483648 2 1 1048576 269804 ep568 ep57 ep568 ep568 ep58 ep568 961498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 881354573) qz286 0 1 ep568 ep57 ep568 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 881354573) qz287 0 1 ep568 ep58 ep568 rfl rfl rfl rfl) rfl rfl

noncomputable def ep572 := @Enclosure.Real.IsNear.sin_image qz141 qz446 Bool.false 180572551 524288 407 524288 Bool.true 961498 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 775553201455015335 2251799813685248 5225000002816693 6738500000000000000 180572551 524288 407 524288 (ep567 rfl) rfl) (Enclosure.sfrac_false_div 180572551 524288) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31009907253385166323712) qz333) 226375608064910080 72057594037927936 Bool.false 961498 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 180572551 524288 226375608064910080 72057594037927936 54 31009907253385166323712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 961498 1048576 31009907253385166323712 75557863725914323419136 881354573 2147483648 269804 269540 (ep571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz447 := (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep565 rfl rfl) rfl)

noncomputable def ep573 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz137 qz138) (@HMul.hMul Real Real Real qz0 qz137 qz581) Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz138 201799 1048576 1 1048576 418369 1048576 27687839 35329146880 84426445831 1099511627776 2240600723093 14818118207537152 qz447 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 418369 1048576 55375678 70658293760 418369 1048576 27687839 35329146880 (ep570 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz137 qz581 201799 1048576 1 1048576 480749 524288 27687839 35329146880 97014667451 549755813888 1123960236313 7409059103768576 qz447 (@Enclosure.Real.IsNear.neg qz139 Bool.true 480749 524288 27687839 35329146880 (@Enclosure.Real.IsNear.recentre' qz139 Bool.true 961498 1048576 55375678 70658293760 480749 524288 27687839 35329146880 (ep572 rfl rfl) rfl)) rfl)

noncomputable def ep574 := @ep563 14152968 0 1 597809226007073899 15561352883541639168 15865310577497884097 209720352811490671067136 (@Enclosure.Complex.IsNear.re_isNear qz126 Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (ep564 ep573))

noncomputable def ep575 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 7080829 14152968 0 1 Bool.false

noncomputable def ep576 := @Enclosure.Complex.IsNear.addLitP qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) Bool.false 21787 43682 0 1 Bool.true 5643

noncomputable def ep577 := @ep576 21841 0 1 Bool.false 1 648 0 1 Bool.false 209 648 0 1 Bool.false 14161658 7080829 14152968 0 1 Bool.false 908105 908105 14152968 0 1

noncomputable abbrev qz142 := (@HDiv.hDiv Complex Complex Complex qz403 qz429 (@HSub.hSub Complex Complex Complex qz395 qz271 (1 : Complex)))

noncomputable def ep578 := @Enclosure.Complex.IsNear.addLitP qz142 qz104 Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1

noncomputable def ep579 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (Enclosure.sfrac Bool.true 54000000 43682000000) (Enclosure.sfrac Bool.true 11286000000 43682000000)) Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1

noncomputable def ep580 := @ep578 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 43574000000 21787 43682 0 1 Bool.true 11286000000 5643 21841 0 1 (ep579 (BSN.N_div_s_sub_one_mk qz13 104500 1000 27 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 54000000 43682000000) (Enclosure.sfrac Bool.true 11286000000 43682000000) Bool.true 54000000 43682000000 0 1 Bool.true 11286000000 43682000000 0 1 (Enclosure.Real.IsNear.const Bool.true 54000000 43682000000) (Enclosure.Real.IsNear.const Bool.true 11286000000 43682000000))) qz105 rfl

noncomputable abbrev qz143 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz448 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz577 qz578 1))

noncomputable abbrev qz144 := qz448

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz144)) Bool.false 1 648 0 1

noncomputable def ep582 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz144) Bool.false 0 1 0 1 Bool.false

noncomputable def ep583 := @ep582 0 1 0 1 Bool.false 1 648 0 1 Bool.false 209 648 0 1 Bool.false 1 1 648 0 1 Bool.false 209 209 648 0

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep585 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz144 Bool.false 1 648 0 1 Bool.false 209 648 0 1

noncomputable abbrev qz145 := (Complex.re qz448)

noncomputable abbrev qz146 := (Complex.im qz448)

noncomputable def ep586 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) 1 648 0 1 0 1 0

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 1 27 0 1 1

noncomputable def ep588 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow32.d9 rfl) qz418

noncomputable def ep591 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep592 := ep591 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz99 qz13) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 104500 1000 qz14) (@Enclosure.Complex.IsNear.mk qz99 qz13 Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 qz411 qz16))

noncomputable def ep593 := @ep589 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 104500 1000 0 1 0 1 0

noncomputable def ep595 := @ep594 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep596 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 209 24 0 1 0 1 0 1 209

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 104500 1000 0 1 209 24 0

noncomputable def ep598 := @ep597 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep600 := @ep599 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep601 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 209 24 0 1 (@ep588 1 24 0 1 (ep593 rfl) (ep595 rfl) rfl rfl) (@ep596 209 24 0 1 (ep598 rfl) (ep600 rfl) rfl rfl)

noncomputable def ep602 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 209 24 0 1 ep601

noncomputable abbrev qz147 := (@Enclosure.Complex.IsNear.re_isNear qz448 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz448 (Complex.mk (Enclosure.sfrac Bool.false 1 27) qz282) Bool.false 1 27 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 27 1 27 EMRow32.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 27) qz282 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 27) qz294)))

noncomputable def ep603 := @ep587 648 0 1 ep602 qz147

noncomputable def ep604 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 209 24 0 1 0 1 0 1 0

noncomputable def ep605 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 209 24 0 1 ep601

noncomputable abbrev qz148 := (@Enclosure.Complex.IsNear.im_isNear qz448 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz448 (Complex.mk (Enclosure.sfrac Bool.false 1 27) qz282) Bool.false 1 27 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 27 1 27 EMRow32.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 27) qz282 Bool.false 1 27 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 27) qz294)))

noncomputable def ep606 := @ep604 1 0 1 ep605 qz148

noncomputable def ep607 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 0 1 0 1 209 648 0

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 1 24 0 1 0 1 0 1 0

noncomputable def ep609 := @ep608 1 0 1 ep602 qz148

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 209 24 0 1 1 27 0 1 209

noncomputable def ep611 := @ep610 648 0 1 ep605 qz147

noncomputable def ep612 := @ep583 1 (@ep584 0 1 0 1 (BSN.bern_sum_base qz5 27) qz120) (ep585 (@ep586 1 1 1 648 0 1 (ep603 rfl) (ep606 rfl) rfl rfl) (@ep607 1 209 209 648 0 1 (ep609 rfl) (ep611 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep613 := ep577 (ep580 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep581 Bool.false 209 648 0 1 (BSN.bern_sum_succ qz5 27 0 1 1 rfl rfl) (ep612 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep614 := @Enclosure.Real.IsNear.mulLit_ff qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 97014667451 549755813888 1123960236313 7409059103768576 908105

noncomputable def ep615 := @ep614 14152968 0 1 88099504585590355 7780676441770819584 1020673910397016865 104860176405745335533568 (@Enclosure.Complex.IsNear.im_isNear qz126 Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (ep564 ep573))

noncomputable def ep616 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 7080829 14152968 0 1 Bool.false

noncomputable def ep617 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) 76668077591360255 15561352883541639168 2034700719644368765

noncomputable def ep618 := nat_lit 11286311713033719577015186058580590592

noncomputable def ep619 := @Enclosure.Real.IsNear.mulLit_ff qz135 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 84426445831 1099511627776 2240600723093 14818118207537152 908105

noncomputable def ep620 := @ep619 14152968 0 1 76668077591360255 15561352883541639168 2034700719644368765 209720352811490671067136 (@Enclosure.Complex.IsNear.re_isNear qz126 Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (ep564 ep573))

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz127 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 97014667451 549755813888 1123960236313 7409059103768576 7080829

noncomputable def ep622 := @ep621 14152968 0 1 686944270712396879 7780676441770819584 7958570236131943477 104860176405745335533568 (@Enclosure.Complex.IsNear.im_isNear qz126 Bool.false 84426445831 1099511627776 2240600723093 14818118207537152 Bool.false 97014667451 549755813888 1123960236313 7409059103768576 (ep564 ep573))

noncomputable abbrev qz449 := (ep613 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep623 := @ep560 53724319222820519 576346403094134784 5983947063969418573 69906784270496890355712 (@ep561 209720352811490671067136 88099504585590355 7780676441770819584 1020673910397016865 104860176405745335533568 ep562 421610216835893189 15561352883541639168 1989628710921324203 23302261423498963451904 (ep574 (@ep575 908105 14152968 0 1 qz449) rfl) (ep615 (@ep616 908105 14152968 0 1 qz449) rfl) rfl rfl) (@ep617 209720352811490671067136 686944270712396879 7780676441770819584 7958570236131943477 104860176405745335533568 ep618 53724319222820519 576346403094134784 5983947063969418573 69906784270496890355712 (ep620 (@ep616 908105 14152968 0 1 qz449) rfl) (ep622 (@ep575 908105 14152968 0 1 qz449) rfl) rfl rfl)

noncomputable def ep624 := @ep528 2181231069726689420273 349533921352484451778560 (@ep529 37045295518842880 (BSN.head_sum_c_eq qz5 27) (ep530 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep559 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep623 rfl rfl rfl

noncomputable def ep625 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 27) Bool.false 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 Bool.true 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 (@ep524 116511307117494817259520 Bool.true 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 (BSN.zetaApproximant_eq_folded' qz5 1 27 rfl) (ep624 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) (Complex.im (zetaApproximant qz5 1 27)) 711 1048576 11245899

noncomputable def ep627 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81)) Bool.false 711 1048576 22491798

noncomputable def ep628 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81) qz399 Bool.false 98826671 1048576 163

noncomputable def ep629 := BSN.sin_dyadic_bound_f 1456640 2147483648 1 0 1048576 269804 0 1 1 0 1 1 711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1456640) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1456640) qz292 0 0 rfl) rfl rfl

noncomputable def ep630 := @ep628 524288 Bool.false 711 1048576 1 134770 (@ep404 98826671 1048576 163 524288 ep521 rfl) (Enclosure.sfrac_false_div 98826671 1048576) (BSN.sin_reduce0 qz399 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102501939462182797312) qz21) 226375608064910080 72057594037927936 Bool.false 711 1048576 15 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 98826671 1048576 226375608064910080 72057594037927936 15 102501939462182797312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 711 1048576 102501939462182797312 151115727451828646838272 1456640 2147483648 269804 269540 (ep629 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep631 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 27) Bool.false 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 Bool.true 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 (@ep524 116511307117494817259520 Bool.true 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 (BSN.zetaApproximant_eq_folded' qz5 1 27 rfl) (ep624 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow32.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 27 qz13) Bool.false 705783457210689610643749 679885881717189909676032 ep388 ep389 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 27 qz13) ep390 Bool.false 705783457210689610643749 679885881717189909676032 ep388 ep389 (@Eq.refl Real ep390) (@ep391 Bool.false 705783457210689610643749 679885881717189909676032 ep388 ep389 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz79 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz80 (@Nat.cast Complex Complex.instNatCast j))))) qz81) (zetaApproximant qz5 1 27)) (@ep393 ep394 ep395 ep396 1711872001838574021 201447668656945158422528 ep397 ep398 ep399 705783457210689610643749 679885881717189909676032 ep388 ep389 (@ep400 35329146880 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 ep392 ep394 ep395 ep396 (@ep401 70658293760 1048575 1048576 11245899 35329146880 (ep523 rfl rfl) rfl) ep625 rfl) (@ep626 35329146880 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 1711872001838574021 201447668656945158422528 ep397 ep398 (@ep627 70658293760 711 1048576 11245899 35329146880 (ep630 rfl rfl) rfl) ep631 rfl) rfl rfl))

noncomputable abbrev qz606 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 106726 1000)))

noncomputable abbrev qz582 := qz606

noncomputable abbrev qz450 := qz582

noncomputable abbrev qz149 := (BSN.headSumC qz450 9)

noncomputable abbrev qz150 := qz450

noncomputable abbrev qz583 := (@Neg.neg Complex Complex.instNeg qz606)

noncomputable abbrev qz451 := qz583

noncomputable abbrev qz151 := qz451

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq qz149 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz151)) Bool.true 92419032371 1099511627776 200209788572751 74090591037685760 Bool.false 384530863073 1099511627776 200220764915401 74090591037685760

noncomputable def ep633 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz151) Bool.false 2376101201 34359738368 89600094051681 37045295518842880 Bool.false 734870843889 1099511627776 179178104084697 74090591037685760 Bool.true

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz151)) Bool.false 2376101201 34359738368 89600094051681 37045295518842880 Bool.false 734870843889 1099511627776 179178104084697 74090591037685760

noncomputable def ep635 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz151) Bool.true 158293646709 549755813888 9794118497489 4630661939855360 Bool.false 871075063989 1099511627776 156727409362309 74090591037685760 Bool.false

noncomputable def ep636 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz151)) Bool.true 158293646709 549755813888 9794118497489 4630661939855360 Bool.false 871075063989 1099511627776 156727409362309 74090591037685760

noncomputable def ep637 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz151) Bool.false 95095852803 1099511627776 132416640560069 74090591037685760 Bool.false 1049971846563 1099511627776 132474797453859 74090591037685760 Bool.true

noncomputable def ep638 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz151)) Bool.false 95095852803 1099511627776 132416640560069 74090591037685760 Bool.false 1049971846563 1099511627776 132474797453859 74090591037685760

noncomputable def ep639 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz151) Bool.false 352893030679 1099511627776 21174929303983 14818118207537152 Bool.false 183586239287 137438953472 2647741987743 1852264775942144 Bool.true

noncomputable def ep640 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz151)) Bool.false 352893030679 1099511627776 21174929303983 14818118207537152 Bool.false 183586239287 137438953472 2647741987743 1852264775942144

noncomputable def ep641 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz151) Bool.false 878305150581 1099511627776 76173717947481 74090591037685760 Bool.false 81681982705 68719476736 1191491995169 1157665484963840 Bool.true

noncomputable def ep642 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz151)) Bool.false 878305150581 1099511627776 76173717947481 74090591037685760 Bool.false 81681982705 68719476736 1191491995169 1157665484963840

noncomputable def ep643 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz151) Bool.false 607557421323 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 1099511627776 41977872707503 74090591037685760 Bool.true

noncomputable def ep644 := nat_lit 1436964636223130073825280

noncomputable def ep645 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz151)) Bool.false 607557421323 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 1099511627776 41977872707503 74090591037685760

noncomputable def ep646 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz151) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz150)

noncomputable abbrev qz607 := (Enclosure.sfrac Bool.false 106726 1000)

noncomputable abbrev qz584 := qz607

noncomputable abbrev qz452 := qz584

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz452 qz284)

noncomputable abbrev qz153 := qz452

noncomputable abbrev qz453 := (@Eq.refl Real qz584)

noncomputable abbrev qz154 := qz453

noncomputable def ep648 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 57801607435 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 1099511627776 41977872707503 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 2 qz154 rfl)

noncomputable def ep649 := BSN.sin_dyadic_bound_f 320502843 2147483648 1 0 1048576 269804 0 1 1 0 1 1 155914 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 320502843) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 320502843) qz292 0 0 rfl) rfl rfl

noncomputable abbrev qz155 := (Enclosure.Real.IsNear.const Bool.false 106726 1000)

noncomputable abbrev qz454 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19392541) qz44)

noncomputable def ep650 := @Enclosure.Real.IsNear.cos_image qz152 qz454 Bool.false 19392541 262144 831 1048576 Bool.false 155914 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 1212033819 16384000 53363 67385000 19392541 262144 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz284 106726 1000 0 1 363408 524288 1 134770 1212033819 16384000 53363 67385000 qz155 qz289 rfl) rfl) (Enclosure.sfrac_false_div 19392541 262144) (BSN.cos_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5638345657060071309312) qz45) 226375608064910080 72057594037927936 Bool.false 155914 1048576 11 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 19392541 262144 226375608064910080 72057594037927936 11 5638345657060071309312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 155914 1048576 5638345657060071309312 37778931862957161709568 320502843 2147483648 269804 269540 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := nat_lit 10551824152209941314759788388857201

noncomputable def ep652 := BSN.cos_dyadic_bound_f 320502843 2147483648 2 1 1048576 269804 ep651 ep57 ep651 ep651 ep58 ep651 1036919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 320502843) qz286 0 1 ep651 ep57 ep651 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 320502843) qz287 0 1 ep651 ep58 ep651 rfl rfl rfl rfl) rfl rfl

noncomputable def ep653 := @Enclosure.Real.IsNear.sin_image qz152 qz454 Bool.false 19392541 262144 831 1048576 Bool.true 1036919 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 1212033819 16384000 53363 67385000 19392541 262144 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz284 106726 1000 0 1 363408 524288 1 134770 1212033819 16384000 53363 67385000 qz155 qz289 rfl) rfl) (Enclosure.sfrac_false_div 19392541 262144) (BSN.sin_reduce3 qz454 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5638345657060071309312) qz45) 226375608064910080 72057594037927936 Bool.false 1036919 1048576 11 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 19392541 262144 226375608064910080 72057594037927936 11 5638345657060071309312 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036919 1048576 5638345657060071309312 37778931862957161709568 320502843 2147483648 269804 269540 (ep652 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep654 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 57801607435 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 1099511627776 41977872707503 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz152) 741455 1048576 1 1048576 77957 524288 56521223 70658293760 57801607435 549755813888 20959253092789 37045295518842880 qz293 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 155914 1048576 113042446 141316587520 77957 524288 56521223 70658293760 (ep650 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 741455 1048576 1 1048576 1036919 1048576 56521223 70658293760 768828777145 1099511627776 41977872707503 74090591037685760 qz293 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.true 1036919 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.true 1036919 1048576 113042446 141316587520 1036919 1048576 56521223 70658293760 (ep653 rfl rfl) rfl)) rfl)

noncomputable def ep655 := @ep646 57801607435 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 1099511627776 41977872707503 74090591037685760 Bool.false 607557421323 607557421323 549755813888 20959253092789 37045295518842880 Bool.false 768828777145 768828777145 1099511627776 41977872707503 74090591037685760 (ep647 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz17)) (ep648 ep654) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz452 qz296)

noncomputable def ep656 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 336809692065 1099511627776 34255211761903 74090591037685760 Bool.false 538082946135 1099511627776 34277614983313 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 3 qz154 rfl)

noncomputable def ep657 := nat_lit 796000690880680567213874814482592738303871055861483198746819888950870851748096

noncomputable def ep658 := nat_lit 495710727647335133296505704122213988391734565662625715803694935527199375616

noncomputable def ep659 := nat_lit 2387010651186747031375031432039533786934829698453124344808852276981558156493056

noncomputable def ep660 := BSN.cos_dyadic_bound_f 2172218658 2147483648 3 2 1048576 269804 ep657 ep122 ep658 ep659 ep125 ep658 556347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2172218658) qz286 0 2 ep657 ep122 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2172218658) qz287 0 2 ep659 ep125 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30736501) qz44)

noncomputable def ep661 := @Enclosure.Real.IsNear.cos_image qz156 qz455 Bool.false 30736501 262144 831 1048576 Bool.true 556347 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 30736501007 262144000 53363 67385000 30736501 262144 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz296 106726 1000 0 1 575989 524288 1 134770 30736501007 262144000 53363 67385000 qz155 qz298 rfl) rfl) (Enclosure.sfrac_false_div 30736501 262144) (BSN.cos_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38214074766715772731392) qz45) 226375608064910080 72057594037927936 Bool.false 556347 1048576 18 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 30736501 262144 226375608064910080 72057594037927936 18 38214074766715772731392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 556347 1048576 38214074766715772731392 37778931862957161709568 2172218658 2147483648 269804 269540 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := nat_lit 1432404675003107152878337461505369157756254512898139657171632844163145773646080

noncomputable def ep663 := nat_lit 3750733474306232572084594247088340400047079963531673898576308609579290131988736

noncomputable def ep664 := BSN.sin_dyadic_bound_f 2172218658 2147483648 3 2 1048576 269804 ep662 ep214 ep658 ep663 ep216 ep658 888813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2172218658) qz291 0 2 ep662 ep214 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2172218658) qz292 0 2 ep663 ep216 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable def ep665 := @Enclosure.Real.IsNear.sin_image qz156 qz455 Bool.false 30736501 262144 831 1048576 Bool.true 888813 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 30736501007 262144000 53363 67385000 30736501 262144 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz296 106726 1000 0 1 575989 524288 1 134770 30736501007 262144000 53363 67385000 qz155 qz298 rfl) rfl) (Enclosure.sfrac_false_div 30736501 262144) (BSN.sin_reduce2 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38214074766715772731392) qz45) 226375608064910080 72057594037927936 Bool.false 888813 1048576 18 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 30736501 262144 226375608064910080 72057594037927936 18 38214074766715772731392 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 888813 1048576 38214074766715772731392 37778931862957161709568 2172218658 2147483648 269804 269540 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz18 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz18 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 336809692065 1099511627776 34255211761903 74090591037685760 Bool.false 538082946135 1099511627776 34277614983313 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz18 (Real.cos qz156) 605395 1048576 1 1048576 556347 1048576 56521223 70658293760 336809692065 1099511627776 34255211761903 74090591037685760 qz299 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 556347 1048576 113042446 141316587520 556347 1048576 56521223 70658293760 (ep661 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz18 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 605395 1048576 1 1048576 888813 1048576 56521223 70658293760 538082946135 1099511627776 34277614983313 74090591037685760 qz299 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 888813 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 888813 1048576 113042446 141316587520 888813 1048576 56521223 70658293760 (ep665 rfl rfl) rfl)) rfl)

noncomputable def ep667 := @ep643 336809692065 1099511627776 34255211761903 74090591037685760 Bool.false 538082946135 1099511627776 34277614983313 74090591037685760 Bool.false 482853362899680051068928 878305150581 1099511627776 76173717947481 74090591037685760 Bool.false ep644 81681982705 68719476736 1191491995169 1157665484963840 (ep645 (BSN.head_sum_c_succ qz150 2 3 rfl rfl) (ep655 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep656 ep666) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz452 qz300)

noncomputable def ep668 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 262706059951 549755813888 14850464286217 37045295518842880 Bool.false 20222273877 137438953472 3706773977363 9261323879710720 (BSN.cpow_neg_s_mk qz153 106726 1000 4 qz154 rfl)

noncomputable def ep669 := nat_lit 169291392603310122849858389851129761

noncomputable def ep670 := BSN.cos_dyadic_bound_f 641443959 2147483648 2 1 1048576 269804 ep669 ep57 ep669 ep669 ep58 ep669 1002146 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 641443959) qz286 0 1 ep669 ep57 ep669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 641443959) qz287 0 1 ep669 ep58 ep669 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77570271) qz48)

noncomputable def ep671 := @Enclosure.Real.IsNear.cos_image qz157 qz456 Bool.false 77570271 524288 831 1048576 Bool.true 1002146 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 38785135571 262144000 53363 67385000 77570271 524288 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz300 106726 1000 0 1 726817 524288 1 134770 38785135571 262144000 53363 67385000 qz155 qz302 rfl) rfl) (Enclosure.sfrac_false_div 77570271 524288) (BSN.cos_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22568802953364401815552) qz333) 226375608064910080 72057594037927936 Bool.false 1002146 1048576 23 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 77570271 524288 226375608064910080 72057594037927936 23 22568802953364401815552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002146 1048576 22568802953364401815552 75557863725914323419136 641443959 2147483648 269804 269540 (ep670 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep672 := BSN.sin_dyadic_bound_f 641443959 2147483648 2 1 1048576 269804 ep669 ep61 ep669 ep669 ep62 ep669 308568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 641443959) qz291 0 1 ep669 ep61 ep669 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 641443959) qz292 0 1 ep669 ep62 ep669 rfl rfl rfl rfl) rfl rfl

noncomputable def ep673 := @Enclosure.Real.IsNear.sin_image qz157 qz456 Bool.false 77570271 524288 831 1048576 Bool.true 308568 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 38785135571 262144000 53363 67385000 77570271 524288 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz300 106726 1000 0 1 726817 524288 1 134770 38785135571 262144000 53363 67385000 qz155 qz302 rfl) rfl) (Enclosure.sfrac_false_div 77570271 524288) (BSN.sin_reduce2 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22568802953364401815552) qz333) 226375608064910080 72057594037927936 Bool.false 308568 1048576 23 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 77570271 524288 226375608064910080 72057594037927936 23 22568802953364401815552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 308568 1048576 22568802953364401815552 75557863725914323419136 641443959 2147483648 269804 269540 (ep672 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep674 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 262706059951 549755813888 14850464286217 37045295518842880 Bool.false 20222273877 137438953472 3706773977363 9261323879710720 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz157) 524287 1048576 1 1048576 501073 524288 56521223 70658293760 262706059951 549755813888 14850464286217 37045295518842880 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 1002146 1048576 113042446 141316587520 501073 524288 56521223 70658293760 (ep671 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 524287 1048576 1 1048576 38571 131072 56521223 70658293760 20222273877 137438953472 3706773977363 9261323879710720 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 38571 131072 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 308568 1048576 113042446 141316587520 38571 131072 56521223 70658293760 (ep673 rfl rfl) rfl)) rfl)

noncomputable def ep675 := @ep641 262706059951 549755813888 14850464286217 37045295518842880 Bool.false 20222273877 137438953472 3706773977363 9261323879710720 Bool.false 194004995296336598269952 352893030679 1099511627776 21174929303983 14818118207537152 Bool.false 12615950299732725727232 183586239287 137438953472 2647741987743 1852264775942144 (ep642 (BSN.head_sum_c_succ qz150 3 4 rfl rfl) (ep667 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep668 ep674) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz452 qz304)

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 64449294469 274877906944 13270997020077 37045295518842880 Bool.true 418718067733 1099511627776 26565117944139 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 5 qz154 rfl)

noncomputable def ep677 := nat_lit 1972731859619046091346532692899001761

noncomputable def ep678 := BSN.sin_dyadic_bound_f 1185132791 2147483648 2 1 1048576 269804 ep677 ep61 ep677 ep677 ep62 ep677 549748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1185132791) qz291 0 1 ep677 ep61 ep677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1185132791) qz292 0 1 ep677 ep62 ep677 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 180112505) qz20)

noncomputable def ep679 := @Enclosure.Real.IsNear.cos_image qz158 qz457 Bool.false 180112505 1048576 831 1048576 Bool.true 549748 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 1407128947 8192000 53363 67385000 180112505 1048576 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz304 106726 1000 0 1 843808 524288 1 134770 1407128947 8192000 53363 67385000 qz155 qz306 rfl) rfl) (Enclosure.sfrac_false_div 180112505 1048576) (BSN.cos_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83396306240975551856640) qz21) 226375608064910080 72057594037927936 Bool.false 549748 1048576 27 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 180112505 1048576 226375608064910080 72057594037927936 27 83396306240975551856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 549748 1048576 83396306240975551856640 151115727451828646838272 1185132791 2147483648 269804 269540 (ep678 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep680 := BSN.cos_dyadic_bound_f 1185132791 2147483648 2 1 1048576 269804 ep677 ep57 ep677 ep677 ep58 ep677 892909 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1185132791) qz286 0 1 ep677 ep57 ep677 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1185132791) qz287 0 1 ep677 ep58 ep677 rfl rfl rfl rfl) rfl rfl

noncomputable def ep681 := @Enclosure.Real.IsNear.sin_image qz158 qz457 Bool.false 180112505 1048576 831 1048576 Bool.false 892909 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 1407128947 8192000 53363 67385000 180112505 1048576 831 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz153 qz304 106726 1000 0 1 843808 524288 1 134770 1407128947 8192000 53363 67385000 qz155 qz306 rfl) rfl) (Enclosure.sfrac_false_div 180112505 1048576) (BSN.sin_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83396306240975551856640) qz21) 226375608064910080 72057594037927936 Bool.false 892909 1048576 27 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 180112505 1048576 226375608064910080 72057594037927936 27 83396306240975551856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892909 1048576 83396306240975551856640 151115727451828646838272 1185132791 2147483648 269804 269540 (ep680 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep682 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 64449294469 274877906944 13270997020077 37045295518842880 Bool.true 418718067733 1099511627776 26565117944139 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz158) 468937 1048576 1 1048576 137437 262144 56521223 70658293760 64449294469 274877906944 13270997020077 37045295518842880 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 549748 1048576 113042446 141316587520 137437 262144 56521223 70658293760 (ep679 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 468937 1048576 1 1048576 892909 1048576 56521223 70658293760 418718067733 1099511627776 26565117944139 74090591037685760 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 892909 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 892909 1048576 113042446 141316587520 892909 1048576 56521223 70658293760 (ep681 rfl rfl) rfl)) rfl)

noncomputable def ep683 := @ep639 64449294469 274877906944 13270997020077 37045295518842880 Bool.true 418718067733 1099511627776 26565117944139 74090591037685760 Bool.false 26139748977543355564032 95095852803 1099511627776 132416640560069 74090591037685760 Bool.false 144307031766682080116736 1049971846563 1099511627776 132474797453859 74090591037685760 (ep640 (BSN.head_sum_c_succ qz150 4 5 rfl rfl) (ep675 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep676 ep682) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz452 qz544)

noncomputable def ep684 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 411683146221 1099511627776 4857851079951 14818118207537152 Bool.true 89448391287 549755813888 2425261190845 7409059103768576 (BSN.cpow_neg_s_mk qz153 106726 1000 6 qz154 rfl)

noncomputable def ep685 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz544 106726 1000 0 1 4034681531866359 2251799813685248 50000000013477 6738500000000000000 215302710584984515317 1125899906842624000 2668150000719173151 3369250000000000000000 qz155 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 50000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 33845361775666394038272 18889465931478580854784 1000000000269540 134770000000000000000 4034681531866359 2251799813685248 50000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep105 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep686 := nat_lit 2485468741480888372975574793302561432243098416345912193951556829616694766240000

noncomputable def ep687 := nat_lit 1491738310280217047863467391111003163951877450435302761497689330192100000000

noncomputable def ep688 := nat_lit 6507145794233301577810916940016338317418859479319541446354509723413889559200000

noncomputable def ep689 := BSN.sin_dyadic_bound_f 2492938590 2147483648 3 2 1048576 269804 ep686 ep214 ep687 ep688 ep216 ep687 961699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2492938590) qz291 0 2 ep686 ep214 ep687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2492938590) qz292 0 2 ep688 ep216 ep687 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100258137) qz48)

noncomputable def ep690 := @Enclosure.Real.IsNear.cos_image qz159 qz458 Bool.false 100258137 524288 13 16384 Bool.true 961699 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 215302710584984515317 1125899906842624000 2668150000719173151 3369250000000000000000 100258137 524288 13 16384 (ep685 rfl) rfl) (Enclosure.sfrac_false_div 100258137 524288) (BSN.cos_reduce1 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87712478952519708442624) qz333) 226375608064910080 72057594037927936 Bool.false 961699 1048576 30 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 100258137 524288 226375608064910080 72057594037927936 30 87712478952519708442624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 961699 1048576 87712478952519708442624 75557863725914323419136 2492938590 2147483648 269804 269540 (ep689 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep691 := nat_lit 1381478962293951414785480870675250130430144399059033575644863878378249136800000

noncomputable def ep692 := nat_lit 4141453410261293810260715677243528384962529442276230121411596256474363210400000

noncomputable def ep693 := BSN.cos_dyadic_bound_f 2492938590 2147483648 3 2 1048576 269804 ep691 ep122 ep687 ep692 ep125 ep687 417906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2492938590) qz286 0 2 ep691 ep122 ep687 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2492938590) qz287 0 2 ep692 ep125 ep687 rfl rfl rfl rfl) rfl rfl

noncomputable def ep694 := @Enclosure.Real.IsNear.sin_image qz159 qz458 Bool.false 100258137 524288 13 16384 Bool.false 417906 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 215302710584984515317 1125899906842624000 2668150000719173151 3369250000000000000000 100258137 524288 13 16384 (ep685 rfl) rfl) (Enclosure.sfrac_false_div 100258137 524288) (BSN.sin_reduce1 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87712478952519708442624) qz333) 226375608064910080 72057594037927936 Bool.false 417906 1048576 30 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 100258137 524288 226375608064910080 72057594037927936 30 87712478952519708442624 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 417906 1048576 87712478952519708442624 75557863725914323419136 2492938590 2147483648 269804 269540 (ep693 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep695 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz26 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz26 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 411683146221 1099511627776 4857851079951 14818118207537152 Bool.true 89448391287 549755813888 2425261190845 7409059103768576 (@Enclosure.Real.IsNear.mulLit_ft qz26 (Real.cos qz159) 428079 1048576 1 1048576 961699 1048576 884197 1104035840 411683146221 1099511627776 4857851079951 14818118207537152 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 961699 1048576 1768394 2208071680 961699 1048576 884197 1104035840 (ep690 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz26 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 428079 1048576 1 1048576 208953 524288 884197 1104035840 89448391287 549755813888 2425261190845 7409059103768576 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 208953 524288 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 417906 1048576 1768394 2208071680 208953 524288 884197 1104035840 (ep694 rfl rfl) rfl)) rfl)

noncomputable def ep696 := @ep637 411683146221 1099511627776 4857851079951 14818118207537152 Bool.true 89448391287 549755813888 2425261190845 7409059103768576 Bool.true 348091410319223310778368 158293646709 549755813888 9794118497489 4630661939855360 Bool.false 478878580760814374879232 871075063989 1099511627776 156727409362309 74090591037685760 (ep638 (BSN.head_sum_c_succ qz150 5 6 rfl rfl) (ep683 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep684 ep695) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz452 qz545)

noncomputable def ep697 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 196311265925 549755813888 11247146071769 37045295518842880 Bool.true 34051055025 274877906944 5612673680597 18522647759421440 (BSN.cpow_neg_s_mk qz153 106726 1000 7 qz154 rfl)

noncomputable def ep698 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz545 106726 1000 0 1 4381796493761783 2251799813685248 50000000013477 6738500000000000000 233825806296610026229 1125899906842624000 2668150000719173151 3369250000000000000000 qz155 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 50000000013477 6738500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz314) Bool.false 36757173121942042968064 18889465931478580854784 1000000000269540 134770000000000000000 4381796493761783 2251799813685248 50000000013477 6738500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep699 := nat_lit 264414023822388810687894386436614416

noncomputable def ep700 := BSN.cos_dyadic_bound_f 717085798 2147483648 2 1 1048576 269804 ep699 ep57 ep699 ep699 ep58 ep699 990658 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 717085798) qz286 0 1 ep699 ep57 ep699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 717085798) qz287 0 1 ep699 ep58 ep699 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217767251) qz20)

noncomputable def ep701 := @Enclosure.Real.IsNear.cos_image qz160 qz459 Bool.false 217767251 1048576 13 16384 Bool.false 990658 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 233825806296610026229 1125899906842624000 2668150000719173151 3369250000000000000000 217767251 1048576 13 16384 (ep698 rfl) rfl) (Enclosure.sfrac_false_div 217767251 1048576) (BSN.cos_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50460427127320647565312) qz21) 226375608064910080 72057594037927936 Bool.false 990658 1048576 33 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 217767251 1048576 226375608064910080 72057594037927936 33 50460427127320647565312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 990658 1048576 50460427127320647565312 151115727451828646838272 717085798 2147483648 269804 269540 (ep700 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep702 := BSN.sin_dyadic_bound_f 717085798 2147483648 2 1 1048576 269804 ep699 ep61 ep699 ep699 ep62 ep699 343668 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 717085798) qz291 0 1 ep699 ep61 ep699 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 717085798) qz292 0 1 ep699 ep62 ep699 rfl rfl rfl rfl) rfl rfl

noncomputable def ep703 := @Enclosure.Real.IsNear.sin_image qz160 qz459 Bool.false 217767251 1048576 13 16384 Bool.false 343668 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 233825806296610026229 1125899906842624000 2668150000719173151 3369250000000000000000 217767251 1048576 13 16384 (ep698 rfl) rfl) (Enclosure.sfrac_false_div 217767251 1048576) (BSN.sin_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 50460427127320647565312) qz21) 226375608064910080 72057594037927936 Bool.false 343668 1048576 33 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 217767251 1048576 226375608064910080 72057594037927936 33 50460427127320647565312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 343668 1048576 50460427127320647565312 151115727451828646838272 717085798 2147483648 269804 269540 (ep702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep704 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 196311265925 549755813888 11247146071769 37045295518842880 Bool.true 34051055025 274877906944 5612673680597 18522647759421440 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz160) 396325 1048576 1 1048576 495329 524288 884197 1104035840 196311265925 549755813888 11247146071769 37045295518842880 qz316 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 990658 1048576 1768394 2208071680 495329 524288 884197 1104035840 (ep701 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 396325 1048576 1 1048576 85917 262144 884197 1104035840 34051055025 274877906944 5612673680597 18522647759421440 qz316 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 85917 262144 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 343668 1048576 1768394 2208071680 85917 262144 884197 1104035840 (ep703 rfl rfl) rfl)) rfl)

noncomputable def ep705 := @ep635 196311265925 549755813888 11247146071769 37045295518842880 Bool.true 34051055025 274877906944 5612673680597 18522647759421440 Bool.false 20900407194176148471808 2376101201 34359738368 89600094051681 37045295518842880 Bool.false 201999759442379293065216 734870843889 1099511627776 179178104084697 74090591037685760 (ep636 (BSN.head_sum_c_succ qz150 6 7 rfl rfl) (ep696 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep697 ep704) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz452 qz546)

noncomputable def ep706 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz275 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 168454270803 1099511627776 21009600469389 74090591037685760 Bool.true 21896248801 68719476736 1315166301919 4630661939855360 (BSN.cpow_neg_s_mk qz153 106726 1000 8 qz154 rfl)

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz546 106726 1000 0 1 9364972152248037 4503599627370496 100000000040431 13477000000000000000 499743008960411998431 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 39279540158062550581248 18889465931478580854784 1000000000404310 134770000000000000000 9364972152248037 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep132 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep708 := nat_lit 858198477022593477274825606479937681

noncomputable def ep709 := BSN.sin_dyadic_bound_f 962491571 2147483648 2 1 1048576 269804 ep708 ep61 ep708 ep708 ep62 ep708 454389 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 962491571) qz291 0 1 ep708 ep61 ep708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 962491571) qz292 0 1 ep708 ep62 ep708 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58177743) qz44)

noncomputable def ep710 := @Enclosure.Real.IsNear.cos_image qz161 qz460 Bool.false 58177743 262144 13 16384 Bool.true 454389 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 499743008960411998431 2251799813685248000 5336300002157519453 6738500000000000000000 58177743 262144 13 16384 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 58177743 262144) (BSN.cos_reduce1 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16932330793749316632576) qz45) 226375608064910080 72057594037927936 Bool.false 454389 1048576 35 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 58177743 262144 226375608064910080 72057594037927936 35 16932330793749316632576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 454389 1048576 16932330793749316632576 37778931862957161709568 962491571 2147483648 269804 269540 (ep709 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep711 := BSN.cos_dyadic_bound_f 962491571 2147483648 2 1 1048576 269804 ep708 ep57 ep708 ep708 ep58 ep708 945008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 962491571) qz286 0 1 ep708 ep57 ep708 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 962491571) qz287 0 1 ep708 ep58 ep708 rfl rfl rfl rfl) rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.sin_image qz161 qz460 Bool.false 58177743 262144 13 16384 Bool.false 945008 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 499743008960411998431 2251799813685248000 5336300002157519453 6738500000000000000000 58177743 262144 13 16384 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 58177743 262144) (BSN.sin_reduce1 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16932330793749316632576) qz45) 226375608064910080 72057594037927936 Bool.false 945008 1048576 35 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 58177743 262144 226375608064910080 72057594037927936 35 16932330793749316632576 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945008 1048576 16932330793749316632576 37778931862957161709568 962491571 2147483648 269804 269540 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 168454270803 1099511627776 21009600469389 74090591037685760 Bool.true 21896248801 68719476736 1315166301919 4630661939855360 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz161) 370727 1048576 1 1048576 454389 1048576 884197 1104035840 168454270803 1099511627776 21009600469389 74090591037685760 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 454389 1048576 1768394 2208071680 454389 1048576 884197 1104035840 (ep710 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz30 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 370727 1048576 1 1048576 59063 65536 884197 1104035840 21896248801 68719476736 1315166301919 4630661939855360 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.false 59063 65536 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.false 945008 1048576 1768394 2208071680 59063 65536 884197 1104035840 (ep712 rfl rfl) rfl)) rfl)

noncomputable def ep714 := @ep633 168454270803 1099511627776 21009600469389 74090591037685760 Bool.true 21896248801 68719476736 1315166301919 4630661939855360 Bool.true 3175493772491282710528 92419032371 1099511627776 200209788572751 74090591037685760 Bool.false 26424759699219024969728 384530863073 1099511627776 200220764915401 74090591037685760 (ep634 (BSN.head_sum_c_succ qz150 7 8 rfl rfl) (ep705 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep706 ep713) rfl rfl

theorem EMRow32.d12 : Enclosure.Complex.IsNear qz149 Bool.true 92419032371 1099511627776 200209788572751 74090591037685760 Bool.false 384530863073 1099511627776 200220764915401 74090591037685760 := ep632 (BSN.head_sum_c_succ qz150 8 9 rfl rfl) (ep714 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz162 := (BSN.headSumC qz450 17)

noncomputable abbrev qz461 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz151)

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz162 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 16) qz461) Bool.false 13270483097 34359738368 168242312158527 37045295518842880 Bool.false 87085072289 1099511627776 336537466084199 74090591037685760

noncomputable def ep716 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 16) qz461 Bool.false 3084645685 17179869184 160804756141231 37045295518842880 Bool.false 241745772287 1099511627776 321681010395477 74090591037685760 Bool.false

noncomputable abbrev qz462 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz151)

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 15) qz462) Bool.false 3084645685 17179869184 160804756141231 37045295518842880 Bool.false 241745772287 1099511627776 321681010395477 74090591037685760

noncomputable def ep718 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 15) qz462 Bool.true 86467339487 1099511627776 306217943035731 74090591037685760 Bool.false 7489281421 34359738368 153179788806533 37045295518842880 Bool.false

noncomputable abbrev qz463 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz151)

noncomputable def ep719 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 14) qz463) Bool.true 86467339487 1099511627776 306217943035731 74090591037685760 Bool.false 7489281421 34359738368 153179788806533 37045295518842880

noncomputable def ep720 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 14) qz463 Bool.true 223028071929 1099511627776 290345373111129 74090591037685760 Bool.true 20539932495 1099511627776 290457279111089 74090591037685760 Bool.false

noncomputable abbrev qz585 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz151)

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 13) qz585) Bool.true 223028071929 1099511627776 290345373111129 74090591037685760 Bool.true 20539932495 1099511627776 290457279111089 74090591037685760

noncomputable def ep722 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 13) qz585 Bool.false 54410090319 1099511627776 273843361280617 74090591037685760 Bool.true 147120061599 1099511627776 273990221766857 74090591037685760 Bool.true

noncomputable abbrev qz586 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz151)

noncomputable def ep723 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 12) qz586) Bool.false 54410090319 1099511627776 273843361280617 74090591037685760 Bool.true 147120061599 1099511627776 273990221766857 74090591037685760

noncomputable def ep724 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 12) qz586 Bool.true 6837622065 274877906944 2005596085631 578832742481920 Bool.false 79784604567 549755813888 128406543433219 37045295518842880 Bool.false

noncomputable abbrev qz587 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz151)

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 11) qz587) Bool.true 6837622065 274877906944 2005596085631 578832742481920 Bool.false 79784604567 549755813888 128406543433219 37045295518842880

noncomputable def ep726 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 11) qz587 Bool.false 1629425865 137438953472 119419027189817 37045295518842880 Bool.true 21184530891 137438953472 119436659014147 37045295518842880 Bool.true

noncomputable abbrev qz588 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz151)

noncomputable def ep727 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 10) qz588) Bool.false 1629425865 137438953472 119419027189817 37045295518842880 Bool.true 21184530891 137438953472 119436659014147 37045295518842880

noncomputable def ep728 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 10) qz588 Bool.true 252590261721 1099511627776 220019857818349 74090591037685760 Bool.false 54879854573 1099511627776 220063508204109 74090591037685760 Bool.false

noncomputable def ep729 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 10) (@HAdd.hAdd Complex Complex Complex qz4 qz149 (@HPow.hPow Complex Complex Complex qz6 qz321 qz151)) Bool.true 252590261721 1099511627776 220019857818349 74090591037685760 Bool.false 54879854573 1099511627776 220063508204109 74090591037685760

noncomputable def ep730 := @Enclosure.Complex.IsNear.addLitP qz149 (@HPow.hPow Complex Complex Complex qz6 qz321 qz151) Bool.true 92419032371 1099511627776 200209788572751 74090591037685760 Bool.false 384530863073 1099511627776 200220764915401 74090591037685760 Bool.true

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz452 qz551)

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz321 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.true 80085614675 549755813888 9905034622799 37045295518842880 Bool.true 82412752125 274877906944 4960685822177 18522647759421440 (BSN.cpow_neg_s_mk qz153 106726 1000 9 qz154 rfl)

noncomputable def ep732 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz551 106726 1000 0 1 9895417793173221 4503599627370496 100000000040431 13477000000000000000 528049179697102592223 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz323) Bool.false 41504390431577613533184 18889465931478580854784 1000000000404310 134770000000000000000 9895417793173221 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep159 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep733 := nat_lit 889991028838130341708660967709824016

noncomputable def ep734 := BSN.sin_dyadic_bound_f 971284386 2147483648 2 1 1048576 269804 ep733 ep61 ep733 ep733 ep62 ep733 458254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 971284386) qz291 0 1 ep733 ep61 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 971284386) qz292 0 1 ep733 ep62 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61473015) qz44)

noncomputable def ep735 := @Enclosure.Real.IsNear.cos_image qz163 qz464 Bool.false 61473015 262144 13 16384 Bool.true 458254 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 528049179697102592223 2251799813685248000 5336300002157519453 6738500000000000000000 61473015 262144 13 16384 (ep732 rfl) rfl) (Enclosure.sfrac_false_div 61473015 262144) (BSN.cos_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17087015630308743577600) qz45) 226375608064910080 72057594037927936 Bool.false 458254 1048576 37 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 61473015 262144 226375608064910080 72057594037927936 37 17087015630308743577600 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 458254 1048576 17087015630308743577600 37778931862957161709568 971284386 2147483648 269804 269540 (ep734 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep736 := BSN.cos_dyadic_bound_f 971284386 2147483648 2 1 1048576 269804 ep733 ep57 ep733 ep733 ep58 ep733 943140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 971284386) qz286 0 1 ep733 ep57 ep733 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 971284386) qz287 0 1 ep733 ep58 ep733 rfl rfl rfl rfl) rfl rfl

noncomputable def ep737 := @Enclosure.Real.IsNear.sin_image qz163 qz464 Bool.false 61473015 262144 13 16384 Bool.false 943140 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 528049179697102592223 2251799813685248000 5336300002157519453 6738500000000000000000 61473015 262144 13 16384 (ep732 rfl) rfl) (Enclosure.sfrac_false_div 61473015 262144) (BSN.sin_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17087015630308743577600) qz45) 226375608064910080 72057594037927936 Bool.false 943140 1048576 37 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 61473015 262144 226375608064910080 72057594037927936 37 17087015630308743577600 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 943140 1048576 17087015630308743577600 37778931862957161709568 971284386 2147483648 269804 269540 (ep736 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep738 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.true 80085614675 549755813888 9905034622799 37045295518842880 Bool.true 82412752125 274877906944 4960685822177 18522647759421440 (@Enclosure.Real.IsNear.mulLit_ft qz40 (Real.cos qz163) 349525 1048576 1 1048576 229127 524288 884197 1104035840 80085614675 549755813888 9905034622799 37045295518842880 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.true 458254 1048576 1768394 2208071680 229127 524288 884197 1104035840 (ep735 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 349525 1048576 1 1048576 235785 262144 884197 1104035840 82412752125 274877906944 4960685822177 18522647759421440 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 235785 262144 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 943140 1048576 1768394 2208071680 235785 262144 884197 1104035840 (ep737 rfl rfl) rfl)) rfl)

noncomputable def ep739 := @ep730 80085614675 549755813888 9905034622799 37045295518842880 Bool.true 82412752125 274877906944 4960685822177 18522647759421440 Bool.true 138862964912611286581248 252590261721 1099511627776 220019857818349 74090591037685760 Bool.false 15085259558417346854912 54879854573 1099511627776 220063508204109 74090591037685760 EMRow32.d12 (ep731 ep738) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz452 qz552)

noncomputable def ep740 := @Enclosure.Complex.IsNear.of_eq qz588 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 265625668641 1099511627776 3763639312257 14818118207537152 Bool.true 224356101701 1099511627776 3761961964837 14818118207537152 (BSN.cpow_neg_s_mk qz153 106726 1000 10 qz154 rfl)

noncomputable def ep741 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz552 106726 1000 0 1 10369917190100709 4503599627370496 100000000040431 13477000000000000000 553369891015344134367 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000404310 134770000000000000000 10369917190100709 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep170 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep742 := nat_lit 183907425781742105538496844842392940470439765184326692764060964523396871454241

noncomputable def ep743 := nat_lit 26485973572080483592591124642955194674967141751859018250877257255238204961

noncomputable def ep744 := nat_lit 551669305398082155648305352277892911021969361269476360255681139055680137952801

noncomputable def ep745 := BSN.cos_dyadic_bound_f 1506180403 2147483648 3 2 1048576 269804 ep742 ep122 ep743 ep744 ep125 ep743 801069 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1506180403) qz286 0 2 ep742 ep122 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1506180403) qz287 0 2 ep744 ep125 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 257682935) qz20)

noncomputable def ep746 := @Enclosure.Real.IsNear.cos_image qz164 qz465 Bool.false 257682935 1048576 13 16384 Bool.false 801069 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 553369891015344134367 2251799813685248000 5336300002157519453 6738500000000000000000 257682935 1048576 13 16384 (ep741 rfl) rfl) (Enclosure.sfrac_false_div 257682935 1048576) (BSN.cos_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105988023509244014755840) qz21) 226375608064910080 72057594037927936 Bool.false 801069 1048576 39 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 257682935 1048576 226375608064910080 72057594037927936 39 105988023509244014755840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 801069 1048576 105988023509244014755840 151115727451828646838272 1506180403 2147483648 269804 269540 (ep745 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep747 := nat_lit 5146452523057070191647803882420123281

noncomputable def ep748 := BSN.sin_dyadic_bound_f 1506180403 2147483648 2 1 1048576 269804 ep747 ep61 ep747 ep747 ep62 ep747 676609 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1506180403) qz291 0 1 ep747 ep61 ep747 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1506180403) qz292 0 1 ep747 ep62 ep747 rfl rfl rfl rfl) rfl rfl

noncomputable def ep749 := @Enclosure.Real.IsNear.sin_image qz164 qz465 Bool.false 257682935 1048576 13 16384 Bool.false 676609 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 553369891015344134367 2251799813685248000 5336300002157519453 6738500000000000000000 257682935 1048576 13 16384 (ep741 rfl) rfl) (Enclosure.sfrac_false_div 257682935 1048576) (BSN.sin_reduce0 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105988023509244014755840) qz21) 226375608064910080 72057594037927936 Bool.false 676609 1048576 39 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 257682935 1048576 226375608064910080 72057594037927936 39 105988023509244014755840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 676609 1048576 105988023509244014755840 151115727451828646838272 1506180403 2147483648 269804 269540 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 265625668641 1099511627776 3763639312257 14818118207537152 Bool.true 224356101701 1099511627776 3761961964837 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz164) 331589 1048576 1 1048576 801069 1048576 884197 1104035840 265625668641 1099511627776 3763639312257 14818118207537152 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 801069 1048576 1768394 2208071680 801069 1048576 884197 1104035840 (ep746 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 331589 1048576 1 1048576 676609 1048576 884197 1104035840 224356101701 1099511627776 3761961964837 14818118207537152 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 676609 1048576 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 676609 1048576 1768394 2208071680 676609 1048576 884197 1104035840 (ep749 rfl rfl) rfl)) rfl)

noncomputable def ep751 := @ep728 265625668641 1099511627776 3763639312257 14818118207537152 Bool.true 224356101701 1099511627776 3761961964837 14818118207537152 Bool.false 14332581481331734609920 1629425865 137438953472 119419027189817 37045295518842880 Bool.true 186341104349074925027328 21184530891 137438953472 119436659014147 37045295518842880 (ep729 (BSN.head_sum_c_succ qz150 9 10 rfl rfl) (ep739 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep740 ep750) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz452 qz553)

noncomputable def ep752 := @Enclosure.Complex.IsNear.of_eq qz587 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 10096473795 274877906944 8939122290567 37045295518842880 Bool.false 164522728131 549755813888 8759652753 36177046405120 (BSN.cpow_neg_s_mk qz153 106726 1000 11 qz154 rfl)

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz553 106726 1000 0 1 10799156221662949 4503599627370496 100000000040431 13477000000000000000 576275373456599947487 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000404310 134770000000000000000 10799156221662949 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep181 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep754 := nat_lit 3355546238302087006318591873788684533210104177526973347202484852796755611361536

noncomputable def ep755 := nat_lit 8773943676240816566901232444165836300131740225924782127600166364153628467456

noncomputable def ep756 := nat_lit 10049090827553779385821973156477721927030049052129070477352254225661959577149696

noncomputable def ep757 := BSN.cos_dyadic_bound_f 3110995302 2147483648 3 2 1048576 269804 ep754 ep122 ep755 ep756 ep125 ep755 127740 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3110995302) qz286 0 2 ep754 ep122 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3110995302) qz287 0 2 ep756 ep125 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67087283) qz44)

noncomputable def ep758 := @Enclosure.Real.IsNear.cos_image qz165 qz466 Bool.false 67087283 262144 831 1048576 Bool.true 127740 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 576275373456599947487 2251799813685248000 5336300002157519453 6738500000000000000000 67087283 262144 831 1048576 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 67087283 262144) (BSN.cos_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54729208151186694209536) qz45) 226375608064910080 72057594037927936 Bool.false 127740 1048576 40 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 67087283 262144 226375608064910080 72057594037927936 40 54729208151186694209536 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 127740 1048576 54729208151186694209536 37778931862957161709568 3110995302 2147483648 269804 269540 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := nat_lit 6032964074002763958119944386864299490738082127367812199262392601942837197676800

noncomputable def ep760 := nat_lit 15786414761198087139682014255925468264590001801788010874623485116689277262110976

noncomputable def ep761 := BSN.sin_dyadic_bound_f 3110995302 2147483648 3 2 1048576 269804 ep759 ep214 ep755 ep760 ep216 ep755 1040766 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3110995302) qz291 0 2 ep759 ep214 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3110995302) qz292 0 2 ep760 ep216 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable def ep762 := @Enclosure.Real.IsNear.sin_image qz165 qz466 Bool.false 67087283 262144 831 1048576 Bool.true 1040766 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 576275373456599947487 2251799813685248000 5336300002157519453 6738500000000000000000 67087283 262144 831 1048576 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 67087283 262144) (BSN.sin_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54729208151186694209536) qz45) 226375608064910080 72057594037927936 Bool.false 1040766 1048576 40 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 67087283 262144 226375608064910080 72057594037927936 40 54729208151186694209536 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040766 1048576 54729208151186694209536 37778931862957161709568 3110995302 2147483648 269804 269540 (ep761 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep763 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 10096473795 274877906944 8939122290567 37045295518842880 Bool.false 164522728131 549755813888 8759652753 36177046405120 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz165) 316157 1048576 1 1048576 31935 262144 56521223 70658293760 10096473795 274877906944 8939122290567 37045295518842880 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 127740 1048576 113042446 141316587520 31935 262144 56521223 70658293760 (ep758 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 316157 1048576 1 1048576 520383 524288 56521223 70658293760 164522728131 549755813888 8759652753 36177046405120 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 520383 524288 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 1040766 1048576 113042446 141316587520 520383 524288 56521223 70658293760 (ep762 rfl rfl) rfl)) rfl)

noncomputable def ep764 := @ep726 10096473795 274877906944 8939122290567 37045295518842880 Bool.false 164522728131 549755813888 8759652753 36177046405120 Bool.true 939755620850655559680 6837622065 274877906944 2005596085631 578832742481920 Bool.false 10965512554865831706624 79784604567 549755813888 128406543433219 37045295518842880 (ep727 (BSN.head_sum_c_succ qz150 10 11 rfl rfl) (ep751 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep752 ep763) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz452 qz554)

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq qz586 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 81760578579 1099511627776 17127062319849 74090591037685760 Bool.true 306689270733 1099511627776 17177134900419 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 12 qz154 rfl)

noncomputable def ep766 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz554 106726 1000 0 1 11191020447815397 4503599627370496 100000000040431 13477000000000000000 597186424156773030111 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000404310 134770000000000000000 11191020447815397 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep195 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep767 := nat_lit 2243598267198112108887076110021845817636509937157222964720563964108761045278976

noncomputable def ep768 := nat_lit 3929254817735021794123413455939867911289074304007840875062454943054739415296

noncomputable def ep769 := nat_lit 6722936291958866283072981503153657717086951662863653212411566982440173657006336

noncomputable def ep770 := BSN.cos_dyadic_bound_f 2813771162 2147483648 3 2 1048576 269804 ep767 ep122 ep768 ep769 ep125 ep768 270107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2813771162) qz286 0 2 ep767 ep122 ep768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2813771162) qz287 0 2 ep769 ep125 ep768 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 278086599) qz20)

noncomputable def ep771 := @Enclosure.Real.IsNear.cos_image qz166 qz467 Bool.false 278086599 1048576 831 1048576 Bool.false 270107 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 597186424156773030111 2251799813685248000 5336300002157519453 6738500000000000000000 278086599 1048576 831 1048576 (ep766 rfl) rfl) (Enclosure.sfrac_false_div 278086599 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198001543078559914917888) qz21) 226375608064910080 72057594037927936 Bool.false 270107 1048576 42 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 278086599 1048576 226375608064910080 72057594037927936 42 198001543078559914917888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270107 1048576 198001543078559914917888 151115727451828646838272 2813771162 2147483648 269804 269540 (ep770 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep772 := nat_lit 4035333477102413778561438267274570577416686627439795063796965171441326089969920

noncomputable def ep773 := nat_lit 10562368884610941289518043268695210773758758856326307710432426712438527324201216

noncomputable def ep774 := BSN.sin_dyadic_bound_f 2813771162 2147483648 3 2 1048576 269804 ep772 ep214 ep768 ep773 ep216 ep768 1013189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2813771162) qz291 0 2 ep772 ep214 ep768 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2813771162) qz292 0 2 ep773 ep216 ep768 rfl rfl rfl rfl) rfl rfl

noncomputable def ep775 := @Enclosure.Real.IsNear.sin_image qz166 qz467 Bool.false 278086599 1048576 831 1048576 Bool.false 1013189 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 597186424156773030111 2251799813685248000 5336300002157519453 6738500000000000000000 278086599 1048576 831 1048576 (ep766 rfl) rfl) (Enclosure.sfrac_false_div 278086599 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198001543078559914917888) qz21) 226375608064910080 72057594037927936 Bool.false 1013189 1048576 42 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 278086599 1048576 226375608064910080 72057594037927936 42 198001543078559914917888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1013189 1048576 198001543078559914917888 151115727451828646838272 2813771162 2147483648 269804 269540 (ep774 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep776 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 81760578579 1099511627776 17127062319849 74090591037685760 Bool.true 306689270733 1099511627776 17177134900419 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz166) 302697 1048576 1 1048576 270107 1048576 56521223 70658293760 81760578579 1099511627776 17127062319849 74090591037685760 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 270107 1048576 113042446 141316587520 270107 1048576 56521223 70658293760 (ep771 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 302697 1048576 1 1048576 1013189 1048576 56521223 70658293760 306689270733 1099511627776 17177134900419 74090591037685760 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 1013189 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 1013189 1048576 113042446 141316587520 1013189 1048576 56521223 70658293760 (ep775 rfl rfl) rfl)) rfl)

noncomputable def ep777 := @ep724 81760578579 1099511627776 17127062319849 74090591037685760 Bool.true 306689270733 1099511627776 17177134900419 74090591037685760 Bool.false 14956131743520717275136 54410090319 1099511627776 273843361280617 74090591037685760 Bool.true 80880109203610939686912 147120061599 1099511627776 273990221766857 74090591037685760 (ep725 (BSN.head_sum_c_succ qz150 11 12 rfl rfl) (ep764 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep765 ep776) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz452 qz555)

noncomputable def ep778 := @Enclosure.Complex.IsNear.of_eq qz585 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 34679770281 137438953472 1031375739407 4630661939855360 Bool.false 7911258069 68719476736 2058382168029 9261323879710720 (BSN.cpow_neg_s_mk qz153 106726 1000 13 qz154 rfl)

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz555 106726 1000 0 1 11551497052968677 4503599627370496 100000000040431 13477000000000000000 616422537237567510751 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz340) Bool.false 48450490295254733815808 18889465931478580854784 1000000000404310 134770000000000000000 11551497052968677 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep206 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep780 := nat_lit 713908224752630241392945178587214481

noncomputable def ep781 := BSN.cos_dyadic_bound_f 919201229 2147483648 2 1 1048576 269804 ep780 ep57 ep780 ep780 ep58 ep780 953976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 919201229) qz286 0 1 ep780 ep57 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 919201229) qz287 0 1 ep780 ep58 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17940257) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep782 := @Enclosure.Real.IsNear.cos_image qz167 qz468 Bool.false 17940257 65536 831 1048576 Bool.true 953976 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 616422537237567510751 2251799813685248000 5336300002157519453 6738500000000000000000 17940257 65536 831 1048576 (ep779 rfl) rfl) (Enclosure.sfrac_false_div 17940257 65536) (BSN.cos_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4042689759491060137984) qz290) 226375608064910080 72057594037927936 Bool.false 953976 1048576 43 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 17940257 65536 226375608064910080 72057594037927936 43 4042689759491060137984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953976 1048576 4042689759491060137984 9444732965739290427392 919201229 2147483648 269804 269540 (ep781 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep783 := BSN.sin_dyadic_bound_f 919201229 2147483648 2 1 1048576 269804 ep780 ep61 ep780 ep780 ep62 ep780 435248 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 919201229) qz291 0 1 ep780 ep61 ep780 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 919201229) qz292 0 1 ep780 ep62 ep780 rfl rfl rfl rfl) rfl rfl

noncomputable def ep784 := @Enclosure.Real.IsNear.sin_image qz167 qz468 Bool.false 17940257 65536 831 1048576 Bool.true 435248 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 616422537237567510751 2251799813685248000 5336300002157519453 6738500000000000000000 17940257 65536 831 1048576 (ep779 rfl) rfl) (Enclosure.sfrac_false_div 17940257 65536) (BSN.sin_reduce2 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4042689759491060137984) qz290) 226375608064910080 72057594037927936 Bool.false 435248 1048576 43 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 17940257 65536 226375608064910080 72057594037927936 43 4042689759491060137984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 435248 1048576 4042689759491060137984 9444732965739290427392 919201229 2147483648 269804 269540 (ep783 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep785 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 34679770281 137438953472 1031375739407 4630661939855360 Bool.false 7911258069 68719476736 2058382168029 9261323879710720 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz167) 290823 1048576 1 1048576 119247 131072 56521223 70658293760 34679770281 137438953472 1031375739407 4630661939855360 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 953976 1048576 113042446 141316587520 119247 131072 56521223 70658293760 (ep782 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 290823 1048576 1 1048576 27203 65536 56521223 70658293760 7911258069 68719476736 2058382168029 9261323879710720 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 27203 65536 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 435248 1048576 113042446 141316587520 27203 65536 56521223 70658293760 (ep784 rfl rfl) rfl)) rfl)

noncomputable def ep786 := @ep722 34679770281 137438953472 1031375739407 4630661939855360 Bool.false 7911258069 68719476736 2058382168029 9261323879710720 Bool.true 30652744800799700287488 223028071929 1099511627776 290345373111129 74090591037685760 Bool.true 1411493413249162936320 20539932495 1099511627776 290457279111089 74090591037685760 (ep723 (BSN.head_sum_c_succ qz150 12 13 rfl rfl) (ep777 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep778 ep785) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz452 qz556)

noncomputable def ep787 := @Enclosure.Complex.IsNear.of_eq qz463 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 68280366221 549755813888 7936284962301 37045295518842880 Bool.false 260196937967 1099511627776 15902298501977 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 14 qz154 rfl)

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz556 106726 1000 0 1 11885250371606245 4503599627370496 100000000040431 13477000000000000000 126846523116004810387 450359962737049600 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 49850353174629559828480 18889465931478580854784 1000000000404310 134770000000000000000 11885250371606245 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep223 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep789 := nat_lit 1160520440529306110862284314157610000

noncomputable def ep790 := BSN.sin_dyadic_bound_f 1037918370 2147483648 2 1 1048576 269804 ep789 ep61 ep789 ep789 ep62 ep789 487294 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1037918370) qz291 0 1 ep789 ep61 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1037918370) qz292 0 1 ep789 ep62 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36917197) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep791 := @Enclosure.Real.IsNear.cos_image qz168 qz469 Bool.false 36917197 131072 831 1048576 Bool.false 487294 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 126846523116004810387 450359962737049600 5336300002157519453 6738500000000000000000 36917197 131072 831 1048576 (ep788 rfl) rfl) (Enclosure.sfrac_false_div 36917197 131072) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9129626537605143199744) qz558) 226375608064910080 72057594037927936 Bool.false 487294 1048576 44 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 36917197 131072 226375608064910080 72057594037927936 44 9129626537605143199744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 487294 1048576 9129626537605143199744 18889465931478580854784 1037918370 2147483648 269804 269540 (ep790 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep792 := BSN.cos_dyadic_bound_f 1037918370 2147483648 2 1 1048576 269804 ep789 ep57 ep789 ep789 ep58 ep789 928469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1037918370) qz286 0 1 ep789 ep57 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1037918370) qz287 0 1 ep789 ep58 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable def ep793 := @Enclosure.Real.IsNear.sin_image qz168 qz469 Bool.false 36917197 131072 831 1048576 Bool.true 928469 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 126846523116004810387 450359962737049600 5336300002157519453 6738500000000000000000 36917197 131072 831 1048576 (ep788 rfl) rfl) (Enclosure.sfrac_false_div 36917197 131072) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9129626537605143199744) qz558) 226375608064910080 72057594037927936 Bool.false 928469 1048576 44 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 36917197 131072 226375608064910080 72057594037927936 44 9129626537605143199744 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 928469 1048576 9129626537605143199744 18889465931478580854784 1037918370 2147483648 269804 269540 (ep792 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep794 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 68280366221 549755813888 7936284962301 37045295518842880 Bool.false 260196937967 1099511627776 15902298501977 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz168) 280243 1048576 1 1048576 243647 524288 56521223 70658293760 68280366221 549755813888 7936284962301 37045295518842880 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 487294 1048576 113042446 141316587520 243647 524288 56521223 70658293760 (ep791 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 280243 1048576 1 1048576 928469 1048576 56521223 70658293760 260196937967 1099511627776 15902298501977 74090591037685760 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 928469 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 928469 1048576 113042446 141316587520 928469 1048576 56521223 70658293760 (ep793 rfl rfl) rfl)) rfl)

noncomputable def ep795 := @ep720 68280366221 549755813888 7936284962301 37045295518842880 Bool.false 260196937967 1099511627776 15902298501977 74090591037685760 Bool.true 47535922594405685395456 86467339487 1099511627776 306217943035731 74090591037685760 Bool.false 263505664194440459190272 7489281421 34359738368 153179788806533 37045295518842880 (ep721 (BSN.head_sum_c_succ qz150 13 14 rfl rfl) (ep786 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep787 ep794) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz452 qz557)

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq qz462 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 283884663327 1099511627776 15391569246731 74090591037685760 Bool.false 2088766815 1099511627776 15321432782411 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 15 qz154 rfl)

noncomputable def ep797 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz557 106726 1000 0 1 12195965485668069 4503599627370496 100000000040431 13477000000000000000 650813306211705166047 2251799813685248000 5336300002157519453 6738500000000000000000 qz155 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 100000000040431 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz348) Bool.false 51153586820399524478976 18889465931478580854784 1000000000404310 134770000000000000000 12195965485668069 4503599627370496 100000000040431 13477000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep238 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep798 := nat_lit 8188433082938416913129302244519628419144480462925726696128739298443298240733440

noncomputable def ep799 := nat_lit 16146732586669937737911614748193417425710649583027930264025190419366307963136

noncomputable def ep800 := nat_lit 21419753840650769159001077549863856517165345875004381840862085949529664227123456

noncomputable def ep801 := BSN.sin_dyadic_bound_f 3357457946 2147483648 3 2 1048576 269804 ep798 ep214 ep799 ep800 ep216 ep799 1048547 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3357457946) qz291 0 2 ep798 ep214 ep799 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3357457946) qz292 0 2 ep800 ep216 ep799 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303058561) qz20)

noncomputable def ep802 := @Enclosure.Real.IsNear.cos_image qz169 qz470 Bool.false 303058561 1048576 13 16384 Bool.false 1048547 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 650813306211705166047 2251799813685248000 5336300002157519453 6738500000000000000000 303058561 1048576 13 16384 (ep797 rfl) rfl) (Enclosure.sfrac_false_div 303058561 1048576) (BSN.cos_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236260099297618587287552) qz21) 226375608064910080 72057594037927936 Bool.false 1048547 1048576 45 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 303058561 1048576 226375608064910080 72057594037927936 45 236260099297618587287552 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048547 1048576 236260099297618587287552 151115727451828646838272 3357457946 2147483648 269804 269540 (ep801 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep803 := nat_lit 4556305816115418257399795297954546196158360545884527244633310805988217381724416

noncomputable def ep804 := nat_lit 13636623983172914896723562664367251753623660338487525873371882037125919529246976

noncomputable def ep805 := BSN.cos_dyadic_bound_f 3357457946 2147483648 3 2 1048576 269804 ep803 ep122 ep799 ep804 ep125 ep799 7715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3357457946) qz286 0 2 ep803 ep122 ep799 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3357457946) qz287 0 2 ep804 ep125 ep799 rfl rfl rfl rfl) rfl rfl

noncomputable def ep806 := @Enclosure.Real.IsNear.sin_image qz169 qz470 Bool.false 303058561 1048576 13 16384 Bool.true 7715 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 650813306211705166047 2251799813685248000 5336300002157519453 6738500000000000000000 303058561 1048576 13 16384 (ep797 rfl) rfl) (Enclosure.sfrac_false_div 303058561 1048576) (BSN.sin_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236260099297618587287552) qz21) 226375608064910080 72057594037927936 Bool.false 7715 1048576 45 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 303058561 1048576 226375608064910080 72057594037927936 45 236260099297618587287552 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7715 1048576 236260099297618587287552 151115727451828646838272 3357457946 2147483648 269804 269540 (ep805 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep807 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 283884663327 1099511627776 15391569246731 74090591037685760 Bool.false 2088766815 1099511627776 15321432782411 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz169) 270741 1048576 1 1048576 1048547 1048576 884197 1104035840 283884663327 1099511627776 15391569246731 74090591037685760 qz350 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 1048547 1048576 1768394 2208071680 1048547 1048576 884197 1104035840 (ep802 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 270741 1048576 1 1048576 7715 1048576 884197 1104035840 2088766815 1099511627776 15321432782411 74090591037685760 qz350 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 7715 1048576 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 7715 1048576 1768394 2208071680 7715 1048576 884197 1104035840 (ep806 rfl rfl) rfl)) rfl)

noncomputable def ep808 := @ep718 283884663327 1099511627776 15391569246731 74090591037685760 Bool.false 2088766815 1099511627776 15321432782411 74090591037685760 Bool.false 217062643086500130979840 3084645685 17179869184 160804756141231 37045295518842880 Bool.false 8306321487351425007616 241745772287 1099511627776 321681010395477 74090591037685760 (ep719 (BSN.head_sum_c_succ qz150 14 15 rfl rfl) (ep795 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep796 ep807) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz452 qz559)

noncomputable def ep809 := @Enclosure.Complex.IsNear.of_eq qz461 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 7101191727 34359738368 464847251081 2315330969927680 Bool.true 77330349999 549755813888 7428227844361 37045295518842880 (BSN.cpow_neg_s_mk qz153 106726 1000 16 qz154 rfl)

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz559 106726 1000 0 1 3121657384082679 1125899906842624 25000000013477 3369250000000000000 166581002986803999477 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 52372720210750067441664 18889465931478580854784 1000000000539080 134770000000000000000 3121657384082679 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep249 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep811 := nat_lit 2712348305949790252937981369858433601

noncomputable def ep812 := BSN.cos_dyadic_bound_f 1283324143 2147483648 2 1 1048576 269804 ep811 ep57 ep811 ep811 ep58 ep811 866848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1283324143) qz286 0 1 ep811 ep57 ep811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1283324143) qz287 0 1 ep811 ep58 ep811 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 310281297) qz20)

noncomputable def ep813 := @Enclosure.Real.IsNear.cos_image qz170 qz471 Bool.false 310281297 1048576 831 1048576 Bool.false 866848 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 166581002986803999477 562949953421312000 1334075000719173151 1684625000000000000000 310281297 1048576 831 1048576 (ep810 rfl) rfl) (Enclosure.sfrac_false_div 310281297 1048576) (BSN.cos_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90305908348517764562944) qz21) 226375608064910080 72057594037927936 Bool.false 866848 1048576 47 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 310281297 1048576 226375608064910080 72057594037927936 47 90305908348517764562944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 866848 1048576 90305908348517764562944 151115727451828646838272 1283324143 2147483648 269804 269540 (ep812 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep814 := BSN.sin_dyadic_bound_f 1283324143 2147483648 2 1 1048576 269804 ep811 ep61 ep811 ep811 ep62 ep811 589986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1283324143) qz291 0 1 ep811 ep61 ep811 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1283324143) qz292 0 1 ep811 ep62 ep811 rfl rfl rfl rfl) rfl rfl

noncomputable def ep815 := @Enclosure.Real.IsNear.sin_image qz170 qz471 Bool.false 310281297 1048576 831 1048576 Bool.false 589986 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 166581002986803999477 562949953421312000 1334075000719173151 1684625000000000000000 310281297 1048576 831 1048576 (ep810 rfl) rfl) (Enclosure.sfrac_false_div 310281297 1048576) (BSN.sin_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90305908348517764562944) qz21) 226375608064910080 72057594037927936 Bool.false 589986 1048576 47 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 310281297 1048576 226375608064910080 72057594037927936 47 90305908348517764562944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 589986 1048576 90305908348517764562944 151115727451828646838272 1283324143 2147483648 269804 269540 (ep814 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep816 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 7101191727 34359738368 464847251081 2315330969927680 Bool.true 77330349999 549755813888 7428227844361 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz170) 262143 1048576 1 1048576 27089 32768 56521223 70658293760 7101191727 34359738368 464847251081 2315330969927680 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 866848 1048576 113042446 141316587520 27089 32768 56521223 70658293760 (ep813 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 262143 1048576 1 1048576 294993 524288 56521223 70658293760 77330349999 549755813888 7428227844361 37045295518842880 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 294993 524288 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 589986 1048576 113042446 141316587520 294993 524288 56521223 70658293760 (ep815 rfl rfl) rfl)) rfl)

noncomputable def ep817 := @ep716 7101191727 34359738368 464847251081 2315330969927680 Bool.true 77330349999 549755813888 7428227844361 37045295518842880 Bool.false 227985163614943182848 13270483097 34359738368 168242312158527 37045295518842880 Bool.false 47875524793734510149632 87085072289 1099511627776 336537466084199 74090591037685760 (ep717 (BSN.head_sum_c_succ qz150 15 16 rfl rfl) (ep808 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep809 ep816) rfl rfl

theorem EMRow32.d13 : Enclosure.Complex.IsNear qz162 Bool.false 13270483097 34359738368 168242312158527 37045295518842880 Bool.false 87085072289 1099511627776 336537466084199 74090591037685760 := ep715 (BSN.head_sum_c_succ qz150 16 17 rfl rfl) (ep817 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz171 := (BSN.headSumC qz450 25)

noncomputable abbrev qz589 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz151)

noncomputable def ep818 := @Enclosure.Complex.IsNear.of_eq qz171 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 24) qz589) Bool.false 592372970183 549755813888 22106346642483 3704529551884288 Bool.true 71988472939 1099511627776 88426452263707 14818118207537152

noncomputable def ep819 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 24) qz589 Bool.false 961694400193 1099511627776 85991781579709 14818118207537152 Bool.true 96879496327 1099511627776 86005324482239 14818118207537152 Bool.false

noncomputable def ep820 := nat_lit 1302641937392828485206016

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz151)) Bool.false 961694400193 1099511627776 85991781579709 14818118207537152 Bool.true 96879496327 1099511627776 86005324482239 14818118207537152

noncomputable def ep822 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 23) (@HPow.hPow Complex Complex Complex qz6 qz355 qz151) Bool.false 975198229159 1099511627776 417596719784563 74090591037685760 Bool.false 131985938495 1099511627776 417598060611293 74090591037685760 Bool.true

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz151)) Bool.false 975198229159 1099511627776 417596719784563 74090591037685760 Bool.false 131985938495 1099511627776 417598060611293 74090591037685760

noncomputable def ep824 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 22) (@HPow.hPow Complex Complex Complex qz6 qz356 qz151) Bool.false 1209527546761 1099511627776 404890316199519 74090591037685760 Bool.false 62796886597 549755813888 202480181150277 37045295518842880 Bool.true

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz151)) Bool.false 1209527546761 1099511627776 404890316199519 74090591037685760 Bool.false 62796886597 549755813888 202480181150277 37045295518842880

noncomputable def ep826 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 21) (@HPow.hPow Complex Complex Complex qz6 qz357 qz151) Bool.false 1263118095269 1099511627776 391925566010039 74090591037685760 Bool.true 6767354521 68719476736 97972357414561 18522647759421440 Bool.true

noncomputable def ep827 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz151)) Bool.false 1263118095269 1099511627776 391925566010039 74090591037685760 Bool.true 6767354521 68719476736 97972357414561 18522647759421440

noncomputable def ep828 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 20) (@HPow.hPow Complex Complex Complex qz6 qz358 qz151) Bool.false 1078284775755 1099511627776 378619914853419 74090591037685760 Bool.true 67599494955 274877906944 189295153043287 37045295518842880 Bool.false

noncomputable def ep829 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz151)) Bool.false 1078284775755 1099511627776 378619914853419 74090591037685760 Bool.true 67599494955 274877906944 189295153043287 37045295518842880

noncomputable def ep830 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 19) (@HPow.hPow Complex Complex Complex qz6 qz359 qz151) Bool.false 206759254427 274877906944 182468290097617 37045295518842880 Bool.true 247997366299 1099511627776 364971075722279 74090591037685760 Bool.false

noncomputable def ep831 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz151)) Bool.false 206759254427 274877906944 182468290097617 37045295518842880 Bool.true 247997366299 1099511627776 364971075722279 74090591037685760

noncomputable def ep832 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 18) (@HPow.hPow Complex Complex Complex qz6 qz360 qz151) Bool.false 613393514533 1099511627776 350908997609713 74090591037685760 Bool.true 50652793059 549755813888 87740436832237 18522647759421440 Bool.false

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 18) (@HAdd.hAdd Complex Complex Complex qz4 qz162 (@HPow.hPow Complex Complex Complex qz6 qz361 qz151)) Bool.false 613393514533 1099511627776 350908997609713 74090591037685760 Bool.true 50652793059 549755813888 87740436832237 18522647759421440

noncomputable def ep834 := @Enclosure.Complex.IsNear.addLitP qz162 (@HPow.hPow Complex Complex Complex qz6 qz361 qz151) Bool.false 13270483097 34359738368 168242312158527 37045295518842880 Bool.false 87085072289 1099511627776 336537466084199 74090591037685760 Bool.false

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz452 qz561)

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz361 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 188738055429 1099511627776 14424373292659 74090591037685760 Bool.true 188390658407 1099511627776 14424281244749 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 17 qz154 rfl)

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz561 106726 1000 0 1 3189913004350711 1125899906842624 25000000013477 3369250000000000000 170223327651166991093 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz363) Bool.false 53517859495200818200576 18889465931478580854784 1000000000539080 134770000000000000000 3189913004350711 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep281 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep837 := nat_lit 287850543501415114850366475292648196155812174690571667158373641809422938153216

noncomputable def ep838 := nat_lit 64875517559277741731095300924348252006677057826687263035672421206521159936

noncomputable def ep839 := nat_lit 863421879469126789067637235276095891963423169956061626949049580585855772139776

noncomputable def ep840 := BSN.cos_dyadic_bound_f 1684651622 2147483648 3 2 1048576 269804 ep837 ep122 ep838 ep839 ep125 ep838 742137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1684651622) qz286 0 2 ep837 ep122 ep838 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1684651622) qz287 0 2 ep839 ep125 ep838 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 317065655) qz20)

noncomputable def ep841 := @Enclosure.Real.IsNear.cos_image qz172 qz472 Bool.false 317065655 1048576 831 1048576 Bool.false 742137 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 170223327651166991093 562949953421312000 1334075000719173151 1684625000000000000000 317065655 1048576 831 1048576 (ep836 rfl) rfl) (Enclosure.sfrac_false_div 317065655 1048576) (BSN.cos_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118546819083370548428800) qz21) 226375608064910080 72057594037927936 Bool.false 742137 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 317065655 1048576 226375608064910080 72057594037927936 48 118546819083370548428800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742137 1048576 118546819083370548428800 151115727451828646838272 1684651622 2147483648 269804 269540 (ep840 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep842 := nat_lit 8054533975300975892649624985683421456

noncomputable def ep843 := BSN.sin_dyadic_bound_f 1684651622 2147483648 2 1 1048576 269804 ep842 ep61 ep842 ep842 ep62 ep842 740771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1684651622) qz291 0 1 ep842 ep61 ep842 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1684651622) qz292 0 1 ep842 ep62 ep842 rfl rfl rfl rfl) rfl rfl

noncomputable def ep844 := @Enclosure.Real.IsNear.sin_image qz172 qz472 Bool.false 317065655 1048576 831 1048576 Bool.false 740771 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 170223327651166991093 562949953421312000 1334075000719173151 1684625000000000000000 317065655 1048576 831 1048576 (ep836 rfl) rfl) (Enclosure.sfrac_false_div 317065655 1048576) (BSN.sin_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118546819083370548428800) qz21) 226375608064910080 72057594037927936 Bool.false 740771 1048576 48 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 317065655 1048576 226375608064910080 72057594037927936 48 118546819083370548428800 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 740771 1048576 118546819083370548428800 151115727451828646838272 1684651622 2147483648 269804 269540 (ep843 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep845 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 188738055429 1099511627776 14424373292659 74090591037685760 Bool.true 188390658407 1099511627776 14424281244749 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz172) 254317 1048576 1 1048576 742137 1048576 56521223 70658293760 188738055429 1099511627776 14424373292659 74090591037685760 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 742137 1048576 113042446 141316587520 742137 1048576 56521223 70658293760 (ep841 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 254317 1048576 1 1048576 740771 1048576 56521223 70658293760 188390658407 1099511627776 14424281244749 74090591037685760 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 740771 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 740771 1048576 113042446 141316587520 740771 1048576 56521223 70658293760 (ep844 rfl rfl) rfl)) rfl)

noncomputable def ep846 := @ep834 188738055429 1099511627776 14424373292659 74090591037685760 Bool.true 188390658407 1099511627776 14424281244749 74090591037685760 Bool.false 21076040675981885702144 613393514533 1099511627776 350908997609713 74090591037685760 Bool.true 111386669895403928813568 50652793059 549755813888 87740436832237 18522647759421440 EMRow32.d13 (ep835 ep845) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz452 qz562)

noncomputable def ep847 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz360 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 213643503175 1099511627776 14027582585521 74090591037685760 Bool.true 146691780181 1099511627776 14009328393331 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 18 qz154 rfl)

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz562 106726 1000 0 1 3254268794313975 1125899906842624 25000000013477 3369250000000000000 6946301826839065917 22517998136852480 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz367) Bool.false 54597570484265130393600 18889465931478580854784 1000000000539080 134770000000000000000 3254268794313975 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep295 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep849 := nat_lit 2787451406878599512402675530921927696

noncomputable def ep850 := BSN.cos_dyadic_bound_f 1292116958 2147483648 2 1 1048576 269804 ep849 ep57 ep849 ep849 ep58 ep849 864425 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1292116958) qz286 0 1 ep849 ep57 ep849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1292116958) qz287 0 1 ep849 ep58 ep849 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 323462385) qz20)

noncomputable def ep851 := @Enclosure.Real.IsNear.cos_image qz173 qz473 Bool.false 323462385 1048576 831 1048576 Bool.false 864425 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 6946301826839065917 22517998136852480 1334075000719173151 1684625000000000000000 323462385 1048576 831 1048576 (ep848 rfl) rfl) (Enclosure.sfrac_false_div 323462385 1048576) (BSN.cos_reduce0 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90924647694755472343040) qz21) 226375608064910080 72057594037927936 Bool.false 864425 1048576 49 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 323462385 1048576 226375608064910080 72057594037927936 49 90924647694755472343040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 864425 1048576 90924647694755472343040 151115727451828646838272 1292116958 2147483648 269804 269540 (ep850 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep852 := BSN.sin_dyadic_bound_f 1292116958 2147483648 2 1 1048576 269804 ep849 ep61 ep849 ep849 ep62 ep849 593531 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1292116958) qz291 0 1 ep849 ep61 ep849 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1292116958) qz292 0 1 ep849 ep62 ep849 rfl rfl rfl rfl) rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.sin_image qz173 qz473 Bool.false 323462385 1048576 831 1048576 Bool.false 593531 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 6946301826839065917 22517998136852480 1334075000719173151 1684625000000000000000 323462385 1048576 831 1048576 (ep848 rfl) rfl) (Enclosure.sfrac_false_div 323462385 1048576) (BSN.sin_reduce0 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90924647694755472343040) qz21) 226375608064910080 72057594037927936 Bool.false 593531 1048576 49 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 323462385 1048576 226375608064910080 72057594037927936 49 90924647694755472343040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 593531 1048576 90924647694755472343040 151115727451828646838272 1292116958 2147483648 269804 269540 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 213643503175 1099511627776 14027582585521 74090591037685760 Bool.true 146691780181 1099511627776 14009328393331 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz173) 247151 1048576 1 1048576 864425 1048576 56521223 70658293760 213643503175 1099511627776 14027582585521 74090591037685760 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 864425 1048576 113042446 141316587520 864425 1048576 56521223 70658293760 (ep851 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 247151 1048576 1 1048576 593531 1048576 56521223 70658293760 146691780181 1099511627776 14009328393331 74090591037685760 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 593531 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 593531 1048576 113042446 141316587520 593531 1048576 56521223 70658293760 (ep853 rfl rfl) rfl)) rfl)

noncomputable def ep855 := @ep832 213643503175 1099511627776 14027582585521 74090591037685760 Bool.true 146691780181 1099511627776 14009328393331 74090591037685760 Bool.false 909336817571131616657408 206759254427 274877906944 182468290097617 37045295518842880 Bool.true 136337993951787207360512 247997366299 1099511627776 364971075722279 74090591037685760 (ep833 (BSN.head_sum_c_succ qz150 17 18 rfl rfl) (ep846 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep847 ep854) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz452 qz563)

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz359 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 251247758047 1099511627776 2736666931637 14818118207537152 Bool.true 22400613521 1099511627776 2723846072859 14818118207537152 (BSN.cpow_neg_s_mk qz153 106726 1000 19 qz154 rfl)

noncomputable def ep857 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz563 106726 1000 0 1 3315143513283831 1125899906842624 25000000013477 3369250000000000000 176906003299365073653 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz371) Bool.false 55618878793361701994496 18889465931478580854784 1000000000539080 134770000000000000000 3315143513283831 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep306 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep858 := nat_lit 1329747654088109272062699776538801

noncomputable def ep859 := BSN.cos_dyadic_bound_f 190959957 2147483648 2 1 1048576 269804 ep858 ep57 ep858 ep858 ep58 ep858 1044433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 190959957) qz286 0 1 ep858 ep57 ep858 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 190959957) qz287 0 1 ep858 ep58 ep858 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82378277) qz44)

noncomputable def ep860 := @Enclosure.Real.IsNear.cos_image qz174 qz474 Bool.false 82378277 262144 13 16384 Bool.false 1044433 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 176906003299365073653 562949953421312000 1334075000719173151 1684625000000000000000 82378277 262144 13 16384 (ep857 rfl) rfl) (Enclosure.sfrac_false_div 82378277 262144) (BSN.cos_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3359403106394433388544) qz45) 226375608064910080 72057594037927936 Bool.false 1044433 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 82378277 262144 226375608064910080 72057594037927936 50 3359403106394433388544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1044433 1048576 3359403106394433388544 37778931862957161709568 190959957 2147483648 269804 269540 (ep859 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep861 := BSN.sin_dyadic_bound_f 190959957 2147483648 1 0 1048576 269804 0 1 1 0 1 1 93119 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 190959957) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 190959957) qz292 0 0 rfl) rfl rfl

noncomputable def ep862 := @Enclosure.Real.IsNear.sin_image qz174 qz474 Bool.false 82378277 262144 13 16384 Bool.false 93119 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 176906003299365073653 562949953421312000 1334075000719173151 1684625000000000000000 82378277 262144 13 16384 (ep857 rfl) rfl) (Enclosure.sfrac_false_div 82378277 262144) (BSN.sin_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3359403106394433388544) qz45) 226375608064910080 72057594037927936 Bool.false 93119 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q0 82378277 262144 226375608064910080 72057594037927936 50 3359403106394433388544 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 93119 1048576 3359403106394433388544 37778931862957161709568 190959957 2147483648 269804 269540 (ep861 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep863 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz65 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz65 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 251247758047 1099511627776 2736666931637 14818118207537152 Bool.true 22400613521 1099511627776 2723846072859 14818118207537152 (@Enclosure.Real.IsNear.mulLit_ff qz65 (Real.cos qz174) 240559 1048576 1 1048576 1044433 1048576 884197 1104035840 251247758047 1099511627776 2736666931637 14818118207537152 qz373 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 1044433 1048576 1768394 2208071680 1044433 1048576 884197 1104035840 (ep860 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz65 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 240559 1048576 1 1048576 93119 1048576 884197 1104035840 22400613521 1099511627776 2723846072859 14818118207537152 qz373 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 93119 1048576 884197 1104035840 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 93119 1048576 1768394 2208071680 93119 1048576 884197 1104035840 (ep862 rfl rfl) rfl)) rfl)

noncomputable def ep864 := @ep830 251247758047 1099511627776 2736666931637 14818118207537152 Bool.true 22400613521 1099511627776 2723846072859 14818118207537152 Bool.false 296396662249114797342720 1078284775755 1099511627776 378619914853419 74090591037685760 Bool.true 297305722939230199480320 67599494955 274877906944 189295153043287 37045295518842880 (ep831 (BSN.head_sum_c_succ qz150 18 19 rfl rfl) (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep856 ep863) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz452 qz564)

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz358 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 92416659757 549755813888 665282557831 3704529551884288 Bool.false 40530076871 274877906944 1329912357167 7409059103768576 (BSN.cpow_neg_s_mk qz153 106726 1000 20 qz154 rfl)

noncomputable def ep866 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz564 106726 1000 0 1 3372893643545847 1125899906842624 25000000013477 3369250000000000000 179987723500537033461 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz375) Bool.false 56587765202795681021952 18889465931478580854784 1000000000539080 134770000000000000000 3372893643545847 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep321 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep867 := nat_lit 11142086519179758263387210245437890625

noncomputable def ep868 := BSN.sin_dyadic_bound_f 1827012975 2147483648 2 1 1048576 269804 ep867 ep61 ep867 ep867 ep62 ep867 788306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1827012975) qz291 0 1 ep867 ep61 ep867 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1827012975) qz292 0 1 ep867 ep62 ep867 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83813315) qz44)

noncomputable def ep869 := @Enclosure.Real.IsNear.cos_image qz175 qz475 Bool.false 83813315 262144 831 1048576 Bool.false 788306 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 179987723500537033461 562949953421312000 1334075000719173151 1684625000000000000000 83813315 262144 831 1048576 (ep866 rfl) rfl) (Enclosure.sfrac_false_div 83813315 262144) (BSN.cos_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32141152170691128197120) qz45) 226375608064910080 72057594037927936 Bool.false 788306 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 83813315 262144 226375608064910080 72057594037927936 50 32141152170691128197120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 788306 1048576 32141152170691128197120 37778931862957161709568 1827012975 2147483648 269804 269540 (ep868 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep870 := nat_lit 398226981276359586093505315386192322110325011967984711384531770991857462890625

noncomputable def ep871 := nat_lit 124146092000887301607363286138680390420639338310440040247570654449462890625

noncomputable def ep872 := nat_lit 1194432651645076983677301219586299605550133757227333254073100171666673462890625

noncomputable def ep873 := BSN.cos_dyadic_bound_f 1827012975 2147483648 3 2 1048576 269804 ep870 ep122 ep871 ep872 ep125 ep871 691436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1827012975) qz286 0 2 ep870 ep122 ep871 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1827012975) qz287 0 2 ep872 ep125 ep871 rfl rfl rfl rfl) rfl rfl

noncomputable def ep874 := @Enclosure.Real.IsNear.sin_image qz175 qz475 Bool.false 83813315 262144 831 1048576 Bool.true 691436 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 179987723500537033461 562949953421312000 1334075000719173151 1684625000000000000000 83813315 262144 831 1048576 (ep866 rfl) rfl) (Enclosure.sfrac_false_div 83813315 262144) (BSN.sin_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32141152170691128197120) qz45) 226375608064910080 72057594037927936 Bool.false 691436 1048576 50 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 83813315 262144 226375608064910080 72057594037927936 50 32141152170691128197120 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 691436 1048576 32141152170691128197120 37778931862957161709568 1827012975 2147483648 269804 269540 (ep873 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep875 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz67 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz67 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 92416659757 549755813888 665282557831 3704529551884288 Bool.false 40530076871 274877906944 1329912357167 7409059103768576 (@Enclosure.Real.IsNear.mulLit_ff qz67 (Real.cos qz175) 234469 1048576 1 1048576 394153 524288 56521223 70658293760 92416659757 549755813888 665282557831 3704529551884288 qz377 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 788306 1048576 113042446 141316587520 394153 524288 56521223 70658293760 (ep869 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz67 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 234469 1048576 1 1048576 172859 262144 56521223 70658293760 40530076871 274877906944 1329912357167 7409059103768576 qz377 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 172859 262144 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 691436 1048576 113042446 141316587520 172859 262144 56521223 70658293760 (ep874 rfl rfl) rfl)) rfl)

noncomputable def ep876 := @ep828 92416659757 549755813888 665282557831 3704529551884288 Bool.false 40530076871 274877906944 1329912357167 7409059103768576 Bool.false 694406516501269417295872 1263118095269 1099511627776 391925566010039 74090591037685760 Bool.true 7440784985121982775296 6767354521 68719476736 97972357414561 18522647759421440 (ep829 (BSN.head_sum_c_succ qz150 19 20 rfl rfl) (ep864 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep865 ep875) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz452 qz565)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz357 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 13397637127 274877906944 324118754737 1852264775942144 Bool.false 116935722765 549755813888 1307093264231 7409059103768576 (BSN.cpow_neg_s_mk qz153 106726 1000 21 qz154 rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz565 106726 1000 0 1 3427826275261687 1125899906842624 25000000013477 3369250000000000000 182919093526789403381 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz379) Bool.false 57509381830540779323392 18889465931478580854784 1000000000539080 134770000000000000000 3427826275261687 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep332 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := nat_lit 2495630262892189393373119932215993772970512085586210874695991434701342286185281

noncomputable def ep880 := nat_lit 4859705578882430930552465766392530599267925750042098805741412099382217966401

noncomputable def ep881 := nat_lit 7477171377518803318258254865115196257713000405258548426476491479905262422623041

noncomputable def ep882 := BSN.cos_dyadic_bound_f 2889523593 2147483648 3 2 1048576 269804 ep879 ep122 ep880 ep881 ep125 ep880 234206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2889523593) qz286 0 2 ep879 ep122 ep880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2889523593) qz287 0 2 ep881 ep125 ep880 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 170356681) qz48)

noncomputable def ep883 := @Enclosure.Real.IsNear.cos_image qz176 qz476 Bool.false 170356681 524288 831 1048576 Bool.true 234206 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 182919093526789403381 562949953421312000 1334075000719173151 1684625000000000000000 170356681 524288 831 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 170356681 524288) (BSN.cos_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101666073259653927534592) qz333) 226375608064910080 72057594037927936 Bool.false 234206 1048576 51 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 170356681 524288 226375608064910080 72057594037927936 51 101666073259653927534592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 234206 1048576 101666073259653927534592 75557863725914323419136 2889523593 2147483648 269804 269540 (ep882 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep884 := nat_lit 4488246708742834963327173905375674766867507413455145895408191452782910340760385

noncomputable def ep885 := nat_lit 11747063761484472396731227664743084101777990393549123470859777232937193968141121

noncomputable def ep886 := BSN.sin_dyadic_bound_f 2889523593 2147483648 3 2 1048576 269804 ep884 ep214 ep880 ep885 ep216 ep880 1022085 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2889523593) qz291 0 2 ep884 ep214 ep880 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2889523593) qz292 0 2 ep885 ep216 ep880 rfl rfl rfl rfl) rfl rfl

noncomputable def ep887 := @Enclosure.Real.IsNear.sin_image qz176 qz476 Bool.false 170356681 524288 831 1048576 Bool.true 1022085 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 182919093526789403381 562949953421312000 1334075000719173151 1684625000000000000000 170356681 524288 831 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 170356681 524288) (BSN.sin_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101666073259653927534592) qz333) 226375608064910080 72057594037927936 Bool.false 1022085 1048576 51 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 170356681 524288 226375608064910080 72057594037927936 51 101666073259653927534592 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1022085 1048576 101666073259653927534592 75557863725914323419136 2889523593 2147483648 269804 269540 (ep886 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep888 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 13397637127 274877906944 324118754737 1852264775942144 Bool.false 116935722765 549755813888 1307093264231 7409059103768576 (@Enclosure.Real.IsNear.mulLit_ft qz69 (Real.cos qz176) 114409 524288 1 524288 117103 524288 56521223 70658293760 13397637127 274877906944 324118754737 1852264775942144 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 234206 1048576 113042446 141316587520 117103 524288 56521223 70658293760 (ep883 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 114409 524288 1 524288 1022085 1048576 56521223 70658293760 116935722765 549755813888 1307093264231 7409059103768576 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 1022085 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 1022085 1048576 113042446 141316587520 1022085 1048576 56521223 70658293760 (ep887 rfl rfl) rfl)) rfl)

noncomputable def ep889 := @ep826 13397637127 274877906944 324118754737 1852264775942144 Bool.false 116935722765 549755813888 1307093264231 7409059103768576 Bool.false 332472400444774766608384 1209527546761 1099511627776 404890316199519 74090591037685760 Bool.false 4315369187595771707392 62796886597 549755813888 202480181150277 37045295518842880 (ep827 (BSN.head_sum_c_succ qz150 20 21 rfl rfl) (ep876 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep877 ep888) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz452 qz566)

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 117164658801 549755813888 3176600896261 18522647759421440 Bool.false 6392165301 1099511627776 12637698310739 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 22 qz154 rfl)

noncomputable def ep891 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz566 106726 1000 0 1 3480203401436407 1125899906842624 25000000013477 3369250000000000000 185714094110850986741 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz383) Bool.false 58388124189833310502912 18889465931478580854784 1000000000539080 134770000000000000000 3480203401436407 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep892 := BSN.cos_dyadic_bound_f 58566400 2147483648 1 0 1048576 269804 0 1 1 0 1 1 1048186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 58566400) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 58566400) qz287 0 0 rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10809983) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep893 := @Enclosure.Real.IsNear.cos_image qz177 qz477 Bool.false 10809983 32768 831 1048576 Bool.true 1048186 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 185714094110850986741 562949953421312000 1334075000719173151 1684625000000000000000 10809983 32768 831 1048576 (ep891 rfl) rfl) (Enclosure.sfrac_false_div 10809983 32768) (BSN.cos_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128788876900251467776) qz307) 226375608064910080 72057594037927936 Bool.false 1048186 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 10809983 32768 226375608064910080 72057594037927936 52 128788876900251467776 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048186 1048576 128788876900251467776 4722366482869645213696 58566400 2147483648 269804 269540 (ep892 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep894 := BSN.sin_dyadic_bound_f 58566400 2147483648 1 0 1048576 269804 0 1 1 0 1 1 28593 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 58566400) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 58566400) qz292 0 0 rfl) rfl rfl

noncomputable def ep895 := @Enclosure.Real.IsNear.sin_image qz177 qz477 Bool.false 10809983 32768 831 1048576 Bool.true 28593 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 185714094110850986741 562949953421312000 1334075000719173151 1684625000000000000000 10809983 32768 831 1048576 (ep891 rfl) rfl) (Enclosure.sfrac_false_div 10809983 32768) (BSN.sin_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128788876900251467776) qz307) 226375608064910080 72057594037927936 Bool.false 28593 1048576 52 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 10809983 32768 226375608064910080 72057594037927936 52 128788876900251467776 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 28593 1048576 128788876900251467776 4722366482869645213696 58566400 2147483648 269804 269540 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz71 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz71 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 117164658801 549755813888 3176600896261 18522647759421440 Bool.false 6392165301 1099511627776 12637698310739 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz71 (Real.cos qz177) 223557 1048576 1 1048576 524093 524288 56521223 70658293760 117164658801 549755813888 3176600896261 18522647759421440 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 1048186 1048576 113042446 141316587520 524093 524288 56521223 70658293760 (ep893 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz71 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 223557 1048576 1 1048576 28593 1048576 56521223 70658293760 6392165301 1099511627776 12637698310739 74090591037685760 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.true 28593 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.true 28593 1048576 113042446 141316587520 28593 1048576 56521223 70658293760 (ep895 rfl rfl) rfl)) rfl)

noncomputable def ep897 := @ep824 117164658801 549755813888 3176600896261 18522647759421440 Bool.false 6392165301 1099511627776 12637698310739 74090591037685760 Bool.false 536120896173442378760192 975198229159 1099511627776 417596719784563 74090591037685760 Bool.false 72560037039090234818560 131985938495 1099511627776 417598060611293 74090591037685760 (ep825 (BSN.head_sum_c_succ qz150 21 22 rfl rfl) (ep889 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep890 ep896) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz452 qz567)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.true 6751914483 549755813888 6181094056991 37045295518842880 Bool.true 114432717411 549755813888 6214280899951 37045295518842880 (BSN.cpow_neg_s_mk qz153 106726 1000 23 qz154 rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz567 106726 1000 0 1 3530250507853047 1125899906842624 25000000013477 3369250000000000000 188384757850562147061 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz387) Bool.false 59227775304360265777152 18889465931478580854784 1000000000539080 134770000000000000000 3530250507853047 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep361 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep900 := BSN.sin_dyadic_bound_f 126562074 2147483648 1 0 1048576 269804 0 1 1 0 1 1 61762 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 126562074) qz291 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 126562074) qz292 0 0 rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350893955) qz20)

noncomputable def ep901 := @Enclosure.Real.IsNear.cos_image qz178 qz478 Bool.false 350893955 1048576 831 1048576 Bool.true 61762 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 188384757850562147061 562949953421312000 1334075000719173151 1684625000000000000000 350893955 1048576 831 1048576 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 350893955 1048576) (BSN.cos_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8906014222151550238720) qz21) 226375608064910080 72057594037927936 Bool.false 61762 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 350893955 1048576 226375608064910080 72057594037927936 53 8906014222151550238720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 61762 1048576 8906014222151550238720 151115727451828646838272 126562074 2147483648 269804 269540 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := BSN.cos_dyadic_bound_f 126562074 2147483648 1 0 1048576 269804 0 1 1 0 1 1 1046754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 126562074) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 126562074) qz287 0 0 rfl) rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.sin_image qz178 qz478 Bool.false 350893955 1048576 831 1048576 Bool.false 1046754 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 188384757850562147061 562949953421312000 1334075000719173151 1684625000000000000000 350893955 1048576 831 1048576 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 350893955 1048576) (BSN.sin_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8906014222151550238720) qz21) 226375608064910080 72057594037927936 Bool.false 1046754 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 350893955 1048576 226375608064910080 72057594037927936 53 8906014222151550238720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046754 1048576 8906014222151550238720 151115727451828646838272 126562074 2147483648 269804 269540 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz73 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz73 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.true 6751914483 549755813888 6181094056991 37045295518842880 Bool.true 114432717411 549755813888 6214280899951 37045295518842880 (@Enclosure.Real.IsNear.mulLit_ft qz73 (Real.cos qz178) 218643 1048576 1 1048576 30881 524288 56521223 70658293760 6751914483 549755813888 6181094056991 37045295518842880 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.true 61762 1048576 113042446 141316587520 30881 524288 56521223 70658293760 (ep901 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz73 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 218643 1048576 1 1048576 523377 524288 56521223 70658293760 114432717411 549755813888 6214280899951 37045295518842880 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 523377 524288 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 1046754 1048576 113042446 141316587520 523377 524288 56521223 70658293760 (ep903 rfl rfl) rfl)) rfl)

noncomputable def ep905 := @ep822 6751914483 549755813888 6181094056991 37045295518842880 Bool.true 114432717411 549755813888 6214280899951 37045295518842880 Bool.false 528697087689634699280384 961694400193 1099511627776 85991781579709 14818118207537152 Bool.true 53260066352309391589376 96879496327 1099511627776 86005324482239 14818118207537152 (ep823 (BSN.head_sum_c_succ qz150 22 23 rfl rfl) (ep897 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep898 ep904) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz452 qz568)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq qz589 (Complex.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 223051540173 1099511627776 2433604990223 14818118207537152 Bool.false 6222755847 274877906944 605281945367 3704529551884288 (BSN.cpow_neg_s_mk qz153 106726 1000 24 qz154 rfl)

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz568 106726 1000 0 1 3578169457974519 1125899906842624 25000000013477 3369250000000000000 190941856785894257397 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz391) Bool.false 60031721881041427759104 18889465931478580854784 1000000000539080 134770000000000000000 3578169457974519 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep908 := nat_lit 6218450168908709664099914220979764711068365844575640318181579221965162371030625

noncomputable def ep909 := nat_lit 9320922600876867844374381149122138956063404362664271040320188119583250390625

noncomputable def ep910 := nat_lit 16271326091502343715180312056896043161154950747777601537362665276762766661590625

noncomputable def ep911 := BSN.sin_dyadic_bound_f 3134601685 2147483648 3 2 1048576 269804 ep908 ep214 ep909 ep910 ep216 ep909 1042107 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3134601685) qz291 0 2 ep908 ep214 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3134601685) qz292 0 2 ep910 ep216 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 355656923) qz20)

noncomputable def ep912 := @Enclosure.Real.IsNear.cos_image qz179 qz479 Bool.false 355656923 1048576 831 1048576 Bool.false 1042107 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 190941856785894257397 562949953421312000 1334075000719173151 1684625000000000000000 355656923 1048576 831 1048576 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 355656923 1048576) (BSN.cos_reduce3 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220577984136892337094656) qz21) 226375608064910080 72057594037927936 Bool.false 1042107 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 355656923 1048576 226375608064910080 72057594037927936 53 220577984136892337094656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1042107 1048576 220577984136892337094656 151115727451828646838272 3134601685 2147483648 269804 269540 (ep911 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep913 := nat_lit 3458837170549672865764118736610590234574009204480984297229908540256016095190625

noncomputable def ep914 := nat_lit 10357869666447264861603607447533526425809900804717624349609085244528881784790625

noncomputable def ep915 := BSN.cos_dyadic_bound_f 3134601685 2147483648 3 2 1048576 269804 ep913 ep122 ep909 ep914 ep125 ep909 116292 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3134601685) qz286 0 2 ep913 ep122 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3134601685) qz287 0 2 ep914 ep125 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable def ep916 := @Enclosure.Real.IsNear.sin_image qz179 qz479 Bool.false 355656923 1048576 831 1048576 Bool.true 116292 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 190941856785894257397 562949953421312000 1334075000719173151 1684625000000000000000 355656923 1048576 831 1048576 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 355656923 1048576) (BSN.sin_reduce3 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220577984136892337094656) qz21) 226375608064910080 72057594037927936 Bool.false 116292 1048576 53 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 355656923 1048576 226375608064910080 72057594037927936 53 220577984136892337094656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 116292 1048576 220577984136892337094656 151115727451828646838272 3134601685 2147483648 269804 269540 (ep915 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep917 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz75 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz75 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 223051540173 1099511627776 2433604990223 14818118207537152 Bool.false 6222755847 274877906944 605281945367 3704529551884288 (@Enclosure.Real.IsNear.mulLit_ff qz75 (Real.cos qz179) 214039 1048576 1 1048576 1042107 1048576 56521223 70658293760 223051540173 1099511627776 2433604990223 14818118207537152 qz393 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 1042107 1048576 113042446 141316587520 1042107 1048576 56521223 70658293760 (ep912 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz75 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 214039 1048576 1 1048576 29073 262144 56521223 70658293760 6222755847 274877906944 605281945367 3704529551884288 qz393 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 29073 262144 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 116292 1048576 113042446 141316587520 29073 262144 56521223 70658293760 (ep916 rfl rfl) rfl)) rfl)

noncomputable def ep918 := @ep819 223051540173 1099511627776 2433604990223 14818118207537152 Bool.false 6222755847 274877906944 605281945367 3704529551884288 Bool.false ep820 592372970183 549755813888 22106346642483 3704529551884288 Bool.true 19788040765567104188416 71988472939 1099511627776 88426452263707 14818118207537152 (ep821 (BSN.head_sum_c_succ qz150 23 24 rfl rfl) (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep906 ep917) rfl rfl

theorem EMRow32.d14 : Enclosure.Complex.IsNear qz171 Bool.false 592372970183 549755813888 22106346642483 3704529551884288 Bool.true 71988472939 1099511627776 88426452263707 14818118207537152 := ep818 (BSN.head_sum_c_succ qz150 24 25 rfl rfl) (ep918 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep919 := nat_lit 3322873430957300566153362385691

noncomputable def ep920 := nat_lit 3409417312272007491892543488000

noncomputable def ep921 := nat_lit 404822619805726563103772254937372715509

noncomputable def ep922 := nat_lit 60376958907760037462099114252902072320000

noncomputable abbrev qz590 := (@HAdd.hAdd Complex Complex Complex qz600 (@HAdd.hAdd Complex Complex Complex qz600 qz603 (@HMul.hMul Complex Complex Complex qz602 Complex.I (@HDiv.hDiv Complex Complex Complex qz604 (↑qz607) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz480 := qz590

noncomputable abbrev qz180 := (Complex.Stirling.logGammaStirling 1 qz480)

noncomputable abbrev qz591 := (@HAdd.hAdd Complex Complex Complex qz600 qz603 (@HMul.hMul Complex Complex Complex qz602 Complex.I (@HDiv.hDiv Complex Complex Complex qz604 (↑qz607) (2 : Complex))))

noncomputable abbrev qz481 := qz591

noncomputable abbrev qz181 := qz481

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz452 (2 : Real)) (Real.log Real.pi))

noncomputable def ep923 := Complex.re (@HMul.hMul Complex Complex Complex qz77 (Complex.exp (@HMul.hMul Complex Complex Complex qz77 Complex.I ↑(@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182))) (zetaApproximant qz150 1 27))

noncomputable def ep924 := @Enclosure.Real.IsNear.of_eq ep923 (@HSub.hSub Real Real Real qz398 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz150 1 27))))

noncomputable def ep925 := nat_lit 44305170511235285957290068853

noncomputable def ep926 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz150 1 27))) ep925

noncomputable def ep927 := nat_lit 45458897496960099891900579840

noncomputable def ep928 := nat_lit 808240245411829381162601570899368339499

noncomputable def ep929 := nat_lit 120753917815520074924198228505804144640000

noncomputable def ep930 := nat_lit 3589346336470160848194571

noncomputable def ep931 := nat_lit 852354328068001872973135872000

noncomputable def ep932 := nat_lit 468331399874581681647646325125697173

noncomputable def ep933 := nat_lit 40251305938506691641399409501934714880000

noncomputable def ep934 := nat_lit 37763540673315012502872470207219761109054933393112154767360

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz150 1 27)) 1048575 1048576 22963493

noncomputable def ep936 := nat_lit 3168955762194069519869113

noncomputable def ep937 := nat_lit 3251473724624640933888000

noncomputable def ep938 := nat_lit 10893873777380869520975240879

noncomputable def ep939 := nat_lit 1708984344083885148774334464000

noncomputable def ep940 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) Bool.true 1048575 1048576 45926986

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102119989) qz20)

noncomputable def ep941 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) qz482 Bool.false 102119989 1048576 333

noncomputable def ep942 := nat_lit 3354156673953387977221651

noncomputable def ep943 := nat_lit 10598744064000000000000000000

noncomputable def ep944 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) Bool.false 2631612085005407934709 27021597764222976000 ep942 ep943

noncomputable def ep945 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182 4282258983440903493877 27021597764222976000 1196637220953387977221651 ep943 4003345623 65536000

noncomputable def ep946 := nat_lit 172465329602914414409089024000

noncomputable def ep947 := nat_lit 1766457344000000000000000000

noncomputable def ep948 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 377841851024385660017 4503599627370496000 367061786115590060828311 ep947 Bool.false 4282258983440903493877 27021597764222976000

noncomputable def ep949 := @Enclosure.Complex.IsNear.subLitP qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 342017878942640095017 4503599627370496000 360508186096159030044311 ep947 Bool.false 4366390426117769829877 27021597764222976000 1117994020942789233157651

noncomputable def ep950 := nat_lit 1701648419478401720793840803152658432

noncomputable def ep951 := nat_lit 1205348747633025748493523435296653312

noncomputable abbrev qz483 := (@HSub.hSub Complex Complex Complex qz570 qz590 qz573)

noncomputable abbrev qz484 := (Complex.log qz590)

noncomputable abbrev qz183 := (@HSub.hSub Complex Complex Complex qz395 (@HMul.hMul Complex Complex Complex qz394 qz483 qz484) qz480)

noncomputable abbrev qz184 := qz480

noncomputable def ep952 := @Enclosure.Complex.IsNear.of_eq qz180 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz183 qz83) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k)))))) Bool.true 342017878942640095017

noncomputable def ep953 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz183 qz83) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) Bool.true 342018174954465247017 4503599627370496000

noncomputable def ep954 := nat_lit 11751644837647410143970780512256

noncomputable def ep955 := nat_lit 37507008163486651327554397405184000

noncomputable def ep956 := @ep953 11001832027103695177 53908000000000000000000 Bool.false 1455477516331723797671 9007199254740992000 2843150007934489411 26954000000000000000000 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000 Bool.true ep954 342017878942640095017 4503599627370496000 360508186096159030044311 ep947 Bool.false ep955

noncomputable def ep957 := @Enclosure.Complex.IsNear.addLitP qz183 qz83 Bool.true 346156702361675743017 4503599627370496000 5423800000978605401 26954000000000000000000

noncomputable def ep958 := nat_lit 44829006227631668857012224

noncomputable def ep959 := @ep957 Bool.false 1455477516331723797671 9007199254740992000 2843150007934489411 26954000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep958 342018174954465247017 4503599627370496000 11001832027103695177 53908000000000000000000 Bool.false 1455477516331723797671 1455477516331723797671 9007199254740992000

noncomputable abbrev qz185 := (@HMul.hMul Complex Complex Complex qz394 qz483 qz484)

noncomputable def ep960 := @Enclosure.Complex.IsNear.subLitP qz185 qz184 Bool.true 336023603200092127017 4503599627370496000 5423800000978605401 26954000000000000000000 Bool.false 1936128690162467353767

noncomputable def ep961 := nat_lit 1384626809446702972068000

noncomputable def ep962 := nat_lit 5821910065326895190684000

noncomputable def ep963 := @ep960 9007199254740992000 2843150007934489411 26954000000000000000000 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 Bool.true ep961 346156702361675743017 4503599627370496000 5423800000978605401 26954000000000000000000 Bool.false ep962 1455477516331723797671 9007199254740992000 2843150007934489411 26954000000000000000000

noncomputable abbrev qz186 := qz483

noncomputable abbrev qz187 := qz484

noncomputable def ep964 := @Enclosure.Complex.IsNear.mul qz186 qz187 Bool.true 336023603200092127017 4503599627370496000 5423800000978605401 26954000000000000000000 Bool.false 1936128690162467353767 9007199254740992000 2843150007934489411

noncomputable abbrev qz188 := (Complex.re qz483)

noncomputable abbrev qz189 := (Complex.re qz484)

noncomputable abbrev qz190 := (Complex.im qz483)

noncomputable abbrev qz191 := (Complex.im qz484)

noncomputable def ep965 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz188 qz189) (@HMul.hMul Real Real Real qz0 qz190 qz191) 250814825874175563 36028797018963968 350000001037729 107816000000000000000 45921932054295509049 562949953421312000

noncomputable def ep966 := nat_lit 1513315774159626310490619155350290432

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz189 7000 4000 0 1 35830689410596509 9007199254740992 50000000148247 26954000000000000000

noncomputable def ep968 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable abbrev qz192 := (Enclosure.sfrac Bool.false 213452 4000)

noncomputable def ep969 := @Enclosure.Complex.IsNear.of_eq qz186 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz192) Bool.false 7000 4000 0 1 Bool.false 213452 4000 0

noncomputable abbrev qz485 := (Complex.log (Complex.mk qz98 qz192))

noncomputable def ep970 := @Enclosure.Complex.IsNear.of_eq qz187 qz485 Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000

noncomputable def ep971 := nat_lit 24402996409641953613677199845903352498658332606506319734426912686080

noncomputable def ep972 := nat_lit 222920910227148403312037039370225847429488788738701915759382102016

noncomputable def ep973 := nat_lit 68316461444509836467290154302843316542439436702588046084669440

noncomputable def ep974 := BSN.log_dyadic_bound 12874756304 78410756304 4 3 ep971 1048576 269540 ep972 ep973 347490 91285512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12874756304) (BSN.artanhQ 78410756304) 0 3 ep972 ep971 ep973 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz592 := (Real.log (Enclosure.sfrac Bool.false 45642756304 16000000))

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff qz99 qz592 1 2 0 1 35830689410596509 4503599627370496 50000000148247 13477000000000000000 35830689410596509 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 45642756304 16000000 35830689410596509 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45642756304) qz412)) Bool.false 300569607835245160169472 37778931862957161709568 1000000002964940 269540000000000000000 35830689410596509 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 45642756304 16000000 11 91285512608 65536000000 347490 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep974 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep976 := BSN.arctan_dyadic_bound_f 9000 213452 1 0 1048576 269540 0 1 1 0 1 1 44186 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz486 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 213452)))

noncomputable def ep977 := @Enclosure.Real.IsNear.subLit_ff_p qz100 qz486 884279719003555 562949953421312 1 2000000000000000 44186 1048576 1 269540 902359983991997595648 860557540885923 562949953421312 100000000013477 26954000000000000000 qz101 (ep976 rfl) rfl rfl

noncomputable abbrev qz487 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 213452) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep978 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (ep970 (@congrArg Complex Complex qz184 (Complex.mk qz98 qz192) Complex.log (BSN.w_shift_mk qz153 Bool.false 106726 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz99 qz592) Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 9000 213452 4000 45642756304 16000000 rfl rfl rfl) (ep975 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) qz487 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 9000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz487 (@HSub.hSub Real Real Real qz398 qz100 qz486) Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 213452 9000 rfl rfl) ep977))))

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 213452 4000 0 1 860557540885923 562949953421312 100000000013477 26954000000000000000

noncomputable def ep980 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable def ep981 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (ep970 (@congrArg Complex Complex qz184 (Complex.mk qz98 qz192) Complex.log (BSN.w_shift_mk qz153 Bool.false 106726 1000 2 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz485 Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz485) (@HMul.hMul Real Real Real qz0 qz99 qz592) Bool.false 35830689410596509 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 9000 213452 4000 45642756304 16000000 rfl rfl rfl) (ep975 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz485) qz487 Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 9000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz487 (@HSub.hSub Real Real Real qz398 qz100 qz486) Bool.false 860557540885923 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 213452 9000 rfl rfl) ep977))))

noncomputable abbrev qz193 := (@ep969 1 (BSN.w_sub_half_mk qz452 Bool.false 106726 1000 2 qz453 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 213452 4000) Bool.false 7000 4000 0 1 Bool.false 213452 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 213452 4000)))

noncomputable def ep982 := @ep965 5336300000719173151 26954000000000000000000 ep966 336023603200092127017 4503599627370496000 5423800000978605401 26954000000000000000000 (@ep967 250814825874175563 36028797018963968 350000001037729 107816000000000000000 (ep968 qz193) ep978 rfl) (@ep979 45921932054295509049 562949953421312000 5336300000719173151 26954000000000000000000 (ep980 qz193) ep981 rfl) rfl

noncomputable def ep983 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz188 qz191) (@HMul.hMul Real Real Real qz0 qz190 qz189) 6023902786201461 2251799813685248 700000000094339 107816000000000000000 1912033079017661509767 9007199254740992000

noncomputable def ep984 := nat_lit 4359774223778507239507585874805129216

noncomputable def ep985 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz191 7000 4000 0 1 860557540885923 562949953421312 100000000013477 26954000000000000000

noncomputable def ep986 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz189 213452 4000 0 1 35830689410596509 9007199254740992 50000000148247 26954000000000000000

noncomputable def ep987 := @ep983 2668150007910904661 26954000000000000000000 ep984 1936128690162467353767 9007199254740992000 2843150007934489411 26954000000000000000000 (@ep985 6023902786201461 2251799813685248 700000000094339 107816000000000000000 (ep968 qz193) ep981 rfl) (@ep986 1912033079017661509767 9007199254740992000 2668150007910904661 26954000000000000000000 (ep980 qz193) ep978 rfl) rfl

noncomputable def ep988 := @Enclosure.Complex.IsNear.of_eq qz184 (Complex.mk qz98 qz192) Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 (BSN.w_shift_mk qz153 Bool.false 106726 1000 2 qz154 rfl)

noncomputable abbrev qz488 := (ep988 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 213452 4000) Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 213452 4000)))

noncomputable abbrev qz194 := qz488

noncomputable def ep989 := ep963 (@ep964 26954000000000000000000 (ep982 rfl) (ep987 rfl)) qz194 rfl rfl rfl rfl rfl rfl

noncomputable def ep990 := @ep959 2843150007934489411 26954000000000000000000 (ep989 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz104 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep446 131072 3 1048576 (ep448 rfl) (ep450 rfl) rfl rfl) (@ep451 1 0 1 (ep453 rfl) (ep455 rfl) rfl rfl))

noncomputable abbrev qz489 := (@HPow.hPow Complex Int Complex qz575 qz590 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz195 := qz489

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz195)) Bool.false 2258391 34359738368 3 34359738368

noncomputable def ep992 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz195) Bool.false 0 1 0 1 Bool.false

noncomputable def ep993 := @ep992 0 1 0 1 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000 Bool.false 2258391 2258391 34359738368 3 34359738368 Bool.true 40171506311 40171506311 25769803776000 53363

noncomputable def ep994 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz77 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz86 qz184 (@HSub.hSub Int Int Int qz407 qz88 (@HMul.hMul Int Int Int qz408 qz89 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep995 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107) qz195 Bool.false 2258391 34359738368 3 34359738368 Bool.true 40171506311 25769803776000 53363 25769803776000

noncomputable abbrev qz196 := (Complex.re qz489)

noncomputable abbrev qz197 := (Complex.im qz489)

noncomputable def ep996 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz197) 2258391 34359738368 3 34359738368 0 1 0

noncomputable def ep997 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz196 1 12 0 1 6775173 8589934592 9 8589934592 2258391

noncomputable def ep998 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363 2147483648000

noncomputable abbrev qz490 := (@HPow.hPow Complex Nat Complex qz577 qz590 1)

noncomputable abbrev qz198 := (@Inv.inv Complex Complex.instInv qz490)

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq qz195 qz198 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_parts qz198 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363

noncomputable abbrev qz199 := (Complex.re qz490)

noncomputable abbrev qz200 := qz490

noncomputable def ep1001 := @Enclosure.Real.IsNear.mulLit_ff qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200)) 9000 4000 0 1 752797 2147483648 1 2147483648

noncomputable def ep1002 := @Enclosure.Complex.IsNear.re_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable def ep1003 := @Enclosure.Complex.IsNear.of_eq qz200 qz184 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0

noncomputable def ep1004 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200)) Bool.false 752797 2147483648 1 2147483648 752797 2147483648 1

noncomputable abbrev qz201 := (Complex.im qz490)

noncomputable def ep1005 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201)) Bool.false 2852672269 1000000 0 1

noncomputable def ep1006 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz199 qz199) (@HMul.hMul Real Real Real qz0 qz201 qz201) 81 16 0 1 2847609769 1000000

noncomputable def ep1007 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1008 := @Enclosure.Real.IsNear.mulLit_ff qz201 qz201 213452 4000 0 1 213452 4000 0 1

noncomputable def ep1009 := @Enclosure.Complex.IsNear.im_isNear qz200 Bool.false 9000 4000 0 1 Bool.false 213452 4000 0 1

noncomputable abbrev qz202 := (ep1002 (@ep1003 1 (BSN.pow_one_c qz480) qz488))

noncomputable abbrev qz203 := (ep1009 (@ep1003 1 (BSN.pow_one_c qz480) qz488))

noncomputable def ep1010 := @ep1006 0 1 45642756304 2852672269 1000000 0 1 (@ep1007 81 16 0 1 qz202 qz202 rfl) (@ep1008 2847609769 1000000 0 1 qz203 qz203 rfl)

noncomputable def ep1011 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200) 2852672269 1000000 0 1 376398 376399 1073741824 (ep1005 (Enclosure.Complex.normSq_eq_mul_add_mul qz200) (ep1010 rfl rfl)) rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.of_eq (Complex.re qz198) (@HMul.hMul Real Real Real qz0 qz199 (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200))) Bool.false 6775173 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz200) (@ep1001 6775173 8589934592 9 8589934592 qz202 (@ep1004 2147483648 (ep1011 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1013 := @Enclosure.Real.IsNear.of_eq (Complex.im qz198) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200))) Bool.true 40171506311 2147483648000 53363 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz200)

noncomputable def ep1014 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz201) (@Inv.inv Real Real.instInv (@DFunLike.coe qz113 Complex (fun (x : Complex) => Real) qz114 Complex.normSq qz200)) 213452 4000 0 1 752797 2147483648 1

noncomputable def ep1015 := @ep1014 2147483648 40171506311 2147483648000 53363 2147483648000 (@Enclosure.Real.IsNear.neg qz201 Bool.false 213452 4000 0 1 qz203) (@ep1004 2147483648 (ep1011 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz197 0 1 0 1 40171506311 2147483648000 53363 2147483648000 0

noncomputable def ep1017 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 6775173 8589934592 9 8589934592 Bool.true 40171506311 2147483648000 53363 2147483648000

noncomputable abbrev qz204 := (@ep999 2147483648000 (BSN.zpow_one_sub_two_mul qz480 1 1 rfl rfl) (@ep1000 2147483648000 ep1012 (ep1013 ep1015)))

noncomputable def ep1018 := @ep996 1 2258391 2258391 34359738368 3 34359738368 (@ep997 34359738368 3 34359738368 ep465 (ep998 qz204) rfl) (@ep1016 1 0 1 ep485 (ep1017 qz204) rfl) rfl

noncomputable def ep1019 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz196) 40171506311 25769803776000 53363 25769803776000 0 1 0

noncomputable def ep1020 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz197 1 12 0 1 40171506311 2147483648000 53363 2147483648000 40171506311

noncomputable def ep1021 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 (@Rat.cast Complex Complex.instRatCast (bernoulli qz106)) qz107)) qz196 0 1 0 1 6775173 8589934592 9 8589934592 0

noncomputable def ep1022 := @ep1019 1 40171506311 40171506311 25769803776000 53363 25769803776000 (@ep1020 25769803776000 53363 25769803776000 ep465 (ep1017 qz204) rfl) (@ep1021 1 0 1 ep485 (ep998 qz204) rfl) rfl

noncomputable def ep1023 := @ep993 25769803776000 (@ep994 0 1 0 1 (BSN.stirling_sum_base qz184) qz120) (ep995 (ep1018 rfl) (ep1022 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1024 := @ep956 4366390426117769829877 27021597764222976000 1117994020942789233157651 ep943 (ep990 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep991 Bool.true 40171506311 25769803776000 53363 25769803776000 (BSN.stirling_sum_succ qz184 0 1 rfl) (ep1023 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1025 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz153 2) Bool.false 35823972081745565 4503599627370496 50000000148247 13477000000000000000 Bool.false 876369194550691 281474976710656

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz481 qz416))

noncomputable def ep1026 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz153 1) qz205) Bool.false 35823972081745565 4503599627370496 50000000148247 13477000000000000000 Bool.false 876369194550691 281474976710656 100000000013477 13477000000000000000

noncomputable def ep1027 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 1) qz205 Bool.false 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000 Bool.false

noncomputable def ep1028 := nat_lit 645347309273121513613210639400960

noncomputable def ep1029 := nat_lit 986703994504368425324127453184

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz481 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz153 0) qz206) Bool.false 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000

noncomputable def ep1031 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz153 0) qz206 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz491 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz192))

noncomputable def ep1032 := @Enclosure.Complex.IsNear.of_eq qz206 qz491 Bool.false 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000

noncomputable def ep1033 := nat_lit 24253991320049509080459243425099566787237795652800840617217312686080

noncomputable def ep1034 := nat_lit 219224501782567177376899845015713782770565380952215731741462102016

noncomputable def ep1035 := nat_lit 65808708827878383520961946849508374790261087352999873284669440

noncomputable def ep1036 := BSN.log_dyadic_bound 12794756304 78330756304 4 3 ep1033 1048576 269540 ep1034 ep1035 345650 91125512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12794756304) (BSN.artanhQ 78330756304) 0 3 ep1034 ep1033 ep1035 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1037 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Real.log (Enclosure.sfrac Bool.false 45562756304 16000000)) 1 2 0 1 35822786670771869 4503599627370496 50000000148247 13477000000000000000 35822786670771869 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 45562756304 16000000 35822786670771869 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45562756304) qz412)) Bool.false 300503314848730266468352 37778931862957161709568 1000000002964940 269540000000000000000 35822786670771869 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 45562756304 16000000 11 91125512608 65536000000 345650 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep1036 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1038 := BSN.arctan_dyadic_bound_f 1000 213452 1 0 1048576 269540 0 1 1 0 1 1 4912 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz492 := (@Nat.cast Real Real.instNatCast 213452)

noncomputable def ep1039 := @Enclosure.Real.IsNear.subLit_ff_p qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz492)) 884279719003555 562949953421312 1 2000000000000000 4912 1048576 1 269540 924469280462666203136 881642609083811 562949953421312 100000000013477 26954000000000000000 qz101 (ep1038 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz272 qz481 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz493 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz192)

noncomputable def ep1040 := @ep1031 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000 Bool.false 35822786670771869 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 881642609083811 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz153 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz153) qz120) (ep1032 (@congrArg Complex Complex qz207 qz493 Complex.log (BSN.w_shift_mk qz153 Bool.false 106726 1000 0 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz491 Bool.false 35822786670771869 9007199254740992 50000000148247 26954000000000000000 Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz491) (@HMul.hMul Real Real Real qz0 qz99 (Real.log (Enclosure.sfrac Bool.false 45562756304 16000000))) Bool.false 35822786670771869 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 1000 213452 4000 45562756304 16000000 rfl rfl rfl) (ep1037 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz491) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz492 qz422)) Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 1000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz492 qz422)) (@HSub.hSub Real Real Real qz398 qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz422 qz492))) Bool.false 881642609083811 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 213452 1000 rfl rfl) ep1039)))) rfl rfl

noncomputable abbrev qz494 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz192))

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz205 qz494 Bool.false 35825157492719261 9007199254740992 50000000148247 26954000000000000000 Bool.false 871095780017571 562949953421312 100000000013477 26954000000000000000

noncomputable def ep1042 := nat_lit 24298613014768343096698677332879476041102375110763543552380192686080

noncomputable def ep1043 := nat_lit 220328824009716418907945241739111284061088143217925426946838102016

noncomputable def ep1044 := nat_lit 66552842145329312981681278960219164711811828023476325124669440

noncomputable def ep1045 := BSN.log_dyadic_bound 12818756304 78354756304 4 3 ep1042 1048576 269540 ep1043 ep1044 346202 91173512608 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 12818756304) (BSN.artanhQ 78354756304) 0 3 ep1043 ep1042 ep1044 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1046 := @Enclosure.Real.IsNear.mulLit_ff qz99 (Real.log (Enclosure.sfrac Bool.false 45586756304 16000000)) 1 2 0 1 35825157492719261 4503599627370496 50000000148247 13477000000000000000 35825157492719261 9007199254740992 50000000148247 26954000000000000000 qz411 (BSN.isNear_log_sfrac 45586756304 16000000 35825157492719261 4503599627370496 50000000148247 13477000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45586756304) qz412)) Bool.false 300523202744684734578688 37778931862957161709568 1000000002964940 269540000000000000000 35825157492719261 4503599627370496 50000000148247 13477000000000000000 (BSN.log_rat_reduce_isNear 45586756304 16000000 11 91173512608 65536000000 346202 1048576 24973259072661432 36028797018963968 269540 1000000000000000 rfl rfl rfl rfl (ep1045 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1047 := BSN.arctan_dyadic_bound_f 5000 213452 1 0 1048576 269540 0 1 1 0 1 1 24557 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 213452) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 213452) 0 0 rfl) rfl rfl rfl

noncomputable def ep1048 := @Enclosure.Real.IsNear.subLit_ff_p qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz492)) 884279719003555 562949953421312 1 2000000000000000 24557 1048576 1 269540 913410128627704528896 871095780017571 562949953421312 100000000013477 26954000000000000000 qz101 (ep1047 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz272 qz481 qz416)

noncomputable abbrev qz495 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz192)

noncomputable def ep1049 := @ep1027 35825157492719261 9007199254740992 50000000148247 26954000000000000000 Bool.false 871095780017571 562949953421312 100000000013477 26954000000000000000 Bool.false ep1028 35823972081745565 4503599627370496 50000000148247 13477000000000000000 Bool.false ep1029 876369194550691 281474976710656 100000000013477 13477000000000000000 (ep1030 (BSN.log_sum_c_succ qz153 0 1 rfl) (ep1040 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1041 (@congrArg Complex Complex qz208 qz495 Complex.log (BSN.w_shift_mk qz153 Bool.false 106726 1000 1 qz154 rfl)) (@Enclosure.Complex.IsNear.of_parts qz494 Bool.false 35825157492719261 9007199254740992 50000000148247 26954000000000000000 Bool.false 871095780017571 562949953421312 100000000013477 26954000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz494) (@HMul.hMul Real Real Real qz0 qz99 (Real.log (Enclosure.sfrac Bool.false 45586756304 16000000))) Bool.false 35825157492719261 9007199254740992 50000000148247 26954000000000000000 (Enclosure.clog_re_eq 5000 213452 4000 45586756304 16000000 rfl rfl rfl) (ep1046 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz494) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz492 qz426)) Bool.false 871095780017571 562949953421312 100000000013477 26954000000000000000 (Enclosure.clog_im_eq 5000 213452 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz492 qz426)) (@HSub.hSub Real Real Real qz398 qz100 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz492))) Bool.false 871095780017571 562949953421312 100000000013477 26954000000000000000 (BSN.arctan_recip 213452 5000 rfl rfl) ep1048)))) rfl rfl

noncomputable def ep1050 := @ep949 ep943 Bool.false 35823972081745565 4503599627370496 50000000148247 13477000000000000000 Bool.false 876369194550691 281474976710656 100000000013477 13477000000000000000 Bool.true ep950 377841851024385660017 4503599627370496000 367061786115590060828311 ep947 Bool.false ep951 4282258983440903493877 27021597764222976000 1196637220953387977221651 ep943 (@ep952 4503599627370496000 360508186096159030044311 ep947 Bool.false 4366390426117769829877 27021597764222976000 1117994020942789233157651 ep943 (BSN.logGammaStirling_unfold 1 qz184) (ep1024 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1025 100000000013477 13477000000000000000 (BSN.log_sum_c_eq qz153 2) (ep1026 (BSN.log_sum_c_succ qz153 1 2 rfl) (ep1049 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz209 := (@HDiv.hDiv Real Real Real qz270 qz452 (2 : Real))

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff qz209 (Real.log Real.pi) 106726 2000 0 1 75021 65536 1 262144 4003345623 65536000 53363 262144000 (@Enclosure.Real.IsNear.of_eq qz209 (Enclosure.sfrac Bool.false 106726 2000) Bool.false 106726 2000 0 1 (BSN.t_half_eq qz153 Bool.false 106726 1000 qz154) (Enclosure.Real.IsNear.const Bool.false 106726 2000)) EMRow32.d5 rfl

noncomputable def ep1052 := @ep945 53363 262144000 ep946 2631612085005407934709 27021597764222976000 ep942 ep943 (@ep948 1196637220953387977221651 ep943 (ep1050 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1051 rfl rfl

noncomputable def ep1053 := nat_lit 8340549090404258201570429233130167710065379754293396848459645601106378188816640

noncomputable def ep1054 := nat_lit 16750993742024682954251798260363317184310964955969750305151036966975605473536

noncomputable def ep1055 := nat_lit 21817174580238350565044240318157470060444253032268278816900255847808268085657856

noncomputable def ep1056 := BSN.sin_dyadic_bound_f 3372912478 2147483648 3 2 1048576 269804 ep1053 ep214 ep1054 ep1055 ep216 ep1054 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372912478) qz291 0 2 ep1053 ep214 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372912478) qz292 0 2 ep1055 ep216 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1057 := @ep941 1048576 Bool.true 1048575 1048576 1 134770 (@ep944 102119989 1048576 333 1048576 ep1052 rfl) (Enclosure.sfrac_false_div 102119989 1048576) (BSN.cos_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237347615300792539414528) qz21) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 15 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 102119989 1048576 226375608064910080 72057594037927936 15 237347615300792539414528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237347615300792539414528 151115727451828646838272 3372912478 2147483648 269804 269540 (ep1056 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1058 := nat_lit 19508842347747845603328000

noncomputable def ep1059 := nat_lit 21789162544017884198678643233

noncomputable def ep1060 := nat_lit 3417968688167770297548668928000

noncomputable abbrev qz496 := (@HPow.hPow Complex Complex Complex qz536 qz578 qz583)

noncomputable abbrev qz210 := qz496

noncomputable abbrev qz211 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz403 qz429 (@HSub.hSub Complex Complex Complex qz395 qz450 (1 : Complex))) qz402)

noncomputable def ep1061 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz150 1 27) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz151) (@HMul.hMul Complex Complex Complex qz77 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) Bool.false ep936 ep937 ep938

noncomputable def ep1062 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz151) (@HMul.hMul Complex Complex Complex qz77 qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) Bool.false 484032317605 549755813888 11641849008669 1852264775942144

noncomputable def ep1063 := nat_lit 152570508854389505387876879

noncomputable def ep1064 := nat_lit 303914686517051099618640233

noncomputable def ep1065 := nat_lit 1742151854220068069502497604547641344

noncomputable def ep1066 := nat_lit 563789719009161249750136798710857728

noncomputable def ep1067 := @ep1062 Bool.true 56289009829 1099511627776 93146243139327 14818118207537152 Bool.false 306196837588216221014113 ep937 ep1063 ep939 Bool.false 485982763762539132066347 ep1058 ep1064 ep1060 Bool.false ep1065 ep936 ep937 ep938 ep939 Bool.true ep1066 512763762352880121170653 ep1058

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 27, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz151) (BSN.headSumC qz150 27) Bool.false 484032317605 549755813888 11641849008669 1852264775942144 Bool.true 56289009829 1099511627776 93146243139327

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz150 26) (@HPow.hPow Complex Complex Complex qz6 qz431 qz151)) Bool.false 484032317605 549755813888 11641849008669 1852264775942144 Bool.true 56289009829 1099511627776 93146243139327 14818118207537152

noncomputable def ep1070 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz150 26) (@HPow.hPow Complex Complex Complex qz6 qz431 qz151) Bool.false 542886521633 549755813888 113503034832307 18522647759421440 Bool.false 62190866233 549755813888 227024381605749 37045295518842880 Bool.true

noncomputable def ep1071 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz150 26) (@HAdd.hAdd Complex Complex Complex qz4 qz171 (@HPow.hPow Complex Complex Complex qz6 qz432 qz151)) Bool.false 542886521633 549755813888 113503034832307 18522647759421440 Bool.false 62190866233 549755813888 227024381605749 37045295518842880

noncomputable def ep1072 := @Enclosure.Complex.IsNear.addLitP qz171 (@HPow.hPow Complex Complex Complex qz6 qz432 qz151) Bool.false 592372970183 549755813888 22106346642483 3704529551884288 Bool.true 71988472939 1099511627776 88426452263707 14818118207537152 Bool.true

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz452 qz579)

noncomputable def ep1073 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz432 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.true 24743224275 274877906944 742825404973 4630661939855360 Bool.false 196370205405 1099511627776 11916501892963 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 25 qz154 rfl)

noncomputable def ep1074 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz579 106726 1000 0 1 3624129903009015 1125899906842624 25000000013477 3369250000000000000 38678888802854013489 112589990684262400 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz434) Bool.false 60802810194841294602240 18889465931478580854784 1000000000539080 134770000000000000000 3624129903009015 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep536 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1075 := nat_lit 1129588434978006098895563968106948556482251715388985327136819087288401873226881

noncomputable def ep1076 := nat_lit 997735548037403921711116411993918993028334993794651573025161580041286864001

noncomputable def ep1077 := nat_lit 3386769833837943488843269671496857831460698476179366678264406938705123045952641

noncomputable def ep1078 := BSN.cos_dyadic_bound_f 2370701807 2147483648 3 2 1048576 269804 ep1075 ep122 ep1076 ep1077 ep125 ep1076 471940 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2370701807) qz286 0 2 ep1075 ep122 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2370701807) qz287 0 2 ep1077 ep125 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz497 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 360225223) qz20)

noncomputable def ep1079 := @Enclosure.Real.IsNear.cos_image qz212 qz497 Bool.false 360225223 1048576 831 1048576 Bool.true 471940 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 38678888802854013489 112589990684262400 1334075000719173151 1684625000000000000000 360225223 1048576 831 1048576 (ep1074 rfl) rfl) (Enclosure.sfrac_false_div 360225223 1048576) (BSN.cos_reduce2 qz497 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166823309017011261014016) qz21) 226375608064910080 72057594037927936 Bool.false 471940 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 360225223 1048576 226375608064910080 72057594037927936 54 166823309017011261014016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 471940 1048576 166823309017011261014016 151115727451828646838272 2370701807 2147483648 269804 269540 (ep1078 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1080 := nat_lit 2032460994521981054874646249462912266473630419705137867587854227855090342317185

noncomputable def ep1081 := nat_lit 5321496747146461251655588845831065781442224271142550693516625097062312622574721

noncomputable def ep1082 := BSN.sin_dyadic_bound_f 2370701807 2147483648 3 2 1048576 269804 ep1080 ep214 ep1076 ep1081 ep216 ep1076 936367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2370701807) qz291 0 2 ep1080 ep214 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2370701807) qz292 0 2 ep1081 ep216 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1083 := @Enclosure.Real.IsNear.sin_image qz212 qz497 Bool.false 360225223 1048576 831 1048576 Bool.true 936367 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 38678888802854013489 112589990684262400 1334075000719173151 1684625000000000000000 360225223 1048576 831 1048576 (ep1074 rfl) rfl) (Enclosure.sfrac_false_div 360225223 1048576) (BSN.sin_reduce2 qz497 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166823309017011261014016) qz21) 226375608064910080 72057594037927936 Bool.false 936367 1048576 54 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q2 360225223 1048576 226375608064910080 72057594037927936 54 166823309017011261014016 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 936367 1048576 166823309017011261014016 151115727451828646838272 2370701807 2147483648 269804 269540 (ep1082 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.true 24743224275 274877906944 742825404973 4630661939855360 Bool.false 196370205405 1099511627776 11916501892963 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz131 (Real.cos qz212) 209715 1048576 1 1048576 117985 262144 56521223 70658293760 24743224275 274877906944 742825404973 4630661939855360 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.true 471940 1048576 113042446 141316587520 117985 262144 56521223 70658293760 (ep1079 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 209715 1048576 1 1048576 936367 1048576 56521223 70658293760 196370205405 1099511627776 11916501892963 74090591037685760 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 936367 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 936367 1048576 113042446 141316587520 936367 1048576 56521223 70658293760 (ep1083 rfl rfl) rfl)) rfl)

noncomputable def ep1085 := @ep1072 24743224275 274877906944 742825404973 4630661939855360 Bool.false 196370205405 1099511627776 11916501892963 74090591037685760 Bool.false 149227510774587616919552 542886521633 549755813888 113503034832307 18522647759421440 Bool.false 136759161129290606575616 62190866233 549755813888 227024381605749 37045295518842880 EMRow32.d14 (ep1073 ep1084) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz452 qz580)

noncomputable def ep1086 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz431 qz151) (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 14713551007 137438953472 2915455254383 18522647759421440 Bool.true 180670742295 1099511627776 11682452485137 74090591037685760 (BSN.cpow_neg_s_mk qz153 106726 1000 26 qz154 rfl)

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz580 106726 1000 0 1 3668288609262839 1125899906842624 25000000013477 3369250000000000000 195750885056092877557 562949953421312000 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz438) Bool.false 61543670347942250676224 18889465931478580854784 1000000000539080 134770000000000000000 3668288609262839 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep547 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1088 := nat_lit 2364455933429385755533636224077554081

noncomputable def ep1089 := BSN.sin_dyadic_bound_f 1240031753 2147483648 2 1 1048576 269804 ep1088 ep61 ep1088 ep1088 ep62 ep1088 572392 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1240031753) qz291 0 1 ep1088 ep61 ep1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1240031753) qz292 0 1 ep1088 ep62 ep1088 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz498 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91153609) qz44)

noncomputable def ep1090 := @Enclosure.Real.IsNear.cos_image qz213 qz498 Bool.false 91153609 262144 831 1048576 Bool.true 572392 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 195750885056092877557 562949953421312000 1334075000719173151 1684625000000000000000 91153609 262144 831 1048576 (ep1087 rfl) rfl) (Enclosure.sfrac_false_div 91153609 262144) (BSN.cos_reduce1 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21814869302547346096128) qz45) 226375608064910080 72057594037927936 Bool.false 572392 1048576 55 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 91153609 262144 226375608064910080 72057594037927936 55 21814869302547346096128 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 572392 1048576 21814869302547346096128 37778931862957161709568 1240031753 2147483648 269804 269540 (ep1089 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1091 := BSN.cos_dyadic_bound_f 1240031753 2147483648 2 1 1048576 269804 ep1088 ep57 ep1088 ep1088 ep58 ep1088 878565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1240031753) qz286 0 1 ep1088 ep57 ep1088 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1240031753) qz287 0 1 ep1088 ep58 ep1088 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1092 := @Enclosure.Real.IsNear.sin_image qz213 qz498 Bool.false 91153609 262144 831 1048576 Bool.false 878565 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 195750885056092877557 562949953421312000 1334075000719173151 1684625000000000000000 91153609 262144 831 1048576 (ep1087 rfl) rfl) (Enclosure.sfrac_false_div 91153609 262144) (BSN.sin_reduce1 qz498 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21814869302547346096128) qz45) 226375608064910080 72057594037927936 Bool.false 878565 1048576 55 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 91153609 262144 226375608064910080 72057594037927936 55 21814869302547346096128 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 878565 1048576 21814869302547346096128 37778931862957161709568 1240031753 2147483648 269804 269540 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 14713551007 137438953472 2915455254383 18522647759421440 Bool.true 180670742295 1099511627776 11682452485137 74090591037685760 (@Enclosure.Real.IsNear.mulLit_ft qz133 (Real.cos qz213) 205643 1048576 1 1048576 71549 131072 56521223 70658293760 14713551007 137438953472 2915455254383 18522647759421440 qz440 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 572392 1048576 113042446 141316587520 71549 131072 56521223 70658293760 (ep1090 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz133 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 205643 1048576 1 1048576 878565 1048576 56521223 70658293760 180670742295 1099511627776 11682452485137 74090591037685760 qz440 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.false 878565 1048576 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.false 878565 1048576 113042446 141316587520 878565 1048576 56521223 70658293760 (ep1092 rfl rfl) rfl)) rfl)

noncomputable def ep1094 := @ep1070 14713551007 137438953472 2915455254383 18522647759421440 Bool.true 180670742295 1099511627776 11682452485137 74090591037685760 Bool.false 66524895178257921474560 484032317605 549755813888 11641849008669 1852264775942144 Bool.true 30945210411491526705152 56289009829 1099511627776 93146243139327 14818118207537152 (ep1071 (BSN.head_sum_c_succ qz150 25 26 rfl rfl) (ep1085 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1086 ep1093) rfl rfl

noncomputable def ep1095 := @Enclosure.Complex.IsNear.mul qz210 (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 306196837588216221014113 ep937 ep1063 ep939 Bool.false

noncomputable abbrev qz214 := (Complex.re qz496)

noncomputable abbrev qz215 := (Complex.im qz496)

noncomputable def ep1096 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) 7471338944494834879925 78035369390991382413312 1059608375052963865634575

noncomputable def ep1097 := nat_lit 13671874752671081190194675712

noncomputable def ep1098 := nat_lit 4877210586936961400832000

noncomputable def ep1099 := nat_lit 15823929111887825451614208000

noncomputable def ep1100 := nat_lit 35841274991324771516734345003624959170926608384

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 105195195313 549755813888 1147623665039 7409059103768576 923306487425

noncomputable abbrev qz499 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz584 (Real.log (Enclosure.sfrac Bool.false 27 1)))

noncomputable abbrev qz216 := (Real.cos qz499)

noncomputable abbrev qz217 := (Real.sin qz499)

noncomputable abbrev qz593 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1102 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz137 qz216) (@HMul.hMul Real Real Real qz0 qz137 qz593)) Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (BSN.cpow_neg_s_mk qz153 106726 1000 27 qz154 rfl)

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz140 106726 1000 0 1 3710780868205815 1125899906842624 25000000013477 3369250000000000000 39603679894013381169 112589990684262400 1334075000719173151 1684625000000000000000 qz155 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 25000000013477 3369250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz445 Bool.false 62256572154556490711040 18889465931478580854784 1000000000539080 134770000000000000000 3710780868205815 1125899906842624 25000000013477 3369250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 134770 1000000000000000 rfl rfl rfl rfl (ep566 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1104 := nat_lit 6288623557494842303072777726250020707364078221111565834271003034384000000000000

noncomputable def ep1105 := nat_lit 9532155348727260520091353208627673805469089346762251878906250000000000000000

noncomputable def ep1106 := nat_lit 16454771541921885705300936615936085618839921577302200205762969256720000000000000

noncomputable def ep1107 := BSN.sin_dyadic_bound_f 3143394500 2147483648 3 2 1048576 269804 ep1104 ep214 ep1105 ep1106 ep216 ep1105 1042574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3143394500) qz291 0 2 ep1104 ep214 ep1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3143394500) qz292 0 2 ep1106 ep216 ep1105 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz499

noncomputable abbrev qz500 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 368838011) qz20)

noncomputable def ep1108 := @Enclosure.Real.IsNear.cos_image qz218 qz500 Bool.false 368838011 1048576 831 1048576 Bool.false 1042574 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 39603679894013381169 112589990684262400 1334075000719173151 1684625000000000000000 368838011 1048576 831 1048576 (ep1103 rfl) rfl) (Enclosure.sfrac_false_div 368838011 1048576) (BSN.cos_reduce3 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 221196723483130044874752) qz21) 226375608064910080 72057594037927936 Bool.false 1042574 1048576 55 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 368838011 1048576 226375608064910080 72057594037927936 55 221196723483130044874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1042574 1048576 221196723483130044874752 151115727451828646838272 3143394500 2147483648 269804 269540 (ep1107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1109 := nat_lit 3497916267652124506382694893787179359115807495882764242096737796880000000000000

noncomputable def ep1110 := nat_lit 10474684492258918998107901974944282729736484308954768222532400890640000000000000

noncomputable def ep1111 := BSN.cos_dyadic_bound_f 3143394500 2147483648 3 2 1048576 269804 ep1109 ep122 ep1105 ep1110 ep125 ep1105 112024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3143394500) qz286 0 2 ep1109 ep122 ep1105 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3143394500) qz287 0 2 ep1110 ep125 ep1105 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1112 := @Enclosure.Real.IsNear.sin_image qz218 qz500 Bool.false 368838011 1048576 831 1048576 Bool.true 112024 1048576 1 134770 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 39603679894013381169 112589990684262400 1334075000719173151 1684625000000000000000 368838011 1048576 831 1048576 (ep1103 rfl) rfl) (Enclosure.sfrac_false_div 368838011 1048576) (BSN.sin_reduce3 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 221196723483130044874752) qz21) 226375608064910080 72057594037927936 Bool.false 112024 1048576 55 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q3 368838011 1048576 226375608064910080 72057594037927936 55 221196723483130044874752 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 112024 1048576 221196723483130044874752 151115727451828646838272 3143394500 2147483648 269804 269540 (ep1111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1113 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz137 qz216) (@HMul.hMul Real Real Real qz0 qz137 qz593) Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (@Enclosure.Real.IsNear.mulLit_ff qz137 qz216 201799 1048576 1 1048576 521287 524288 56521223 70658293760 105195195313 549755813888 1147623665039 7409059103768576 qz447 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 1042574 1048576 113042446 141316587520 521287 524288 56521223 70658293760 (ep1108 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz137 qz593 201799 1048576 1 1048576 14003 131072 56521223 70658293760 2825791397 137438953472 142669144233 926132387971072 qz447 (@Enclosure.Real.IsNear.neg qz217 Bool.true 14003 131072 56521223 70658293760 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 112024 1048576 113042446 141316587520 14003 131072 56521223 70658293760 (ep1112 rfl rfl) rfl)) rfl)

noncomputable def ep1114 := @ep1101 1845291630312 0 1 7471338944494834879925 78035369390991382413312 1059608375052963865634575 ep1097 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (ep1102 ep1113))

noncomputable def ep1115 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 923306487425 1845291630312 0 1 Bool.false

noncomputable def ep1116 := @Enclosure.Complex.IsNear.addLitP qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) Bool.false 2840922269 5695344538 0 1 Bool.true 720400500

noncomputable def ep1117 := @ep1116 2847672269 0 1 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1 Bool.false 1846612974850 923306487425 1845291630312 0 1 Bool.false 35255454290647 35255454290647 461322907578000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz403 qz429 (@HSub.hSub Complex Complex Complex qz395 qz450 (1 : Complex)))

noncomputable def ep1118 := @Enclosure.Complex.IsNear.addLitP qz219 qz104 Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1

noncomputable def ep1119 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 54000000 45562756304) (Enclosure.sfrac Bool.true 11526408000 45562756304)) Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1

noncomputable def ep1120 := @ep1118 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 45454756304 2840922269 5695344538 0 1 Bool.true 11526408000 720400500 2847672269 0 1 (ep1119 (BSN.N_div_s_sub_one_mk qz153 106726 1000 27 qz154 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 54000000 45562756304) (Enclosure.sfrac Bool.true 11526408000 45562756304) Bool.true 54000000 45562756304 0 1 Bool.true 11526408000 45562756304 0 1 (Enclosure.Real.IsNear.const Bool.true 54000000 45562756304) (Enclosure.Real.IsNear.const Bool.true 11526408000 45562756304))) qz105 rfl

noncomputable def ep1121 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz144)) Bool.false 1 648 0 1

noncomputable def ep1122 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz144) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1123 := @ep1122 0 1 0 1 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1 Bool.false 1 1 648 0 1 Bool.false 53363 53363 162000 0

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1125 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz144 Bool.false 1 648 0 1 Bool.false 53363 162000 0 1

noncomputable def ep1126 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) 1 648 0 1 0 1 0

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 1 24 0 1 1 27 0 1 1

noncomputable def ep1128 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1130 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) qz150 Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 (BSN.ascPochhammer_one_eval qz150)

noncomputable def ep1131 := ep1130 (@Enclosure.Complex.IsNear.of_eq qz150 (Complex.mk qz99 qz153) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_crit_mk qz153 Bool.false 106726 1000 qz154) (@Enclosure.Complex.IsNear.mk qz99 qz153 Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 qz411 qz155))

noncomputable def ep1132 := @ep1129 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1133 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 106726 1000 0 1 0 1 0

noncomputable def ep1134 := @ep1133 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1135 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) 53363 6000 0 1 0 1 0 1 53363

noncomputable def ep1136 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 106726 1000 0 1 53363 6000 0

noncomputable def ep1137 := @ep1136 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1139 := @ep1138 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep590) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1140 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 (@ep1128 1 24 0 1 (ep1132 rfl) (ep1134 rfl) rfl rfl) (@ep1135 53363 6000 0 1 (ep1137 rfl) (ep1139 rfl) rfl rfl)

noncomputable def ep1141 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 ep1140

noncomputable def ep1142 := @ep1127 648 0 1 ep1141 qz147

noncomputable def ep1143 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 53363 6000 0 1 0 1 0 1 0

noncomputable def ep1144 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 53363 6000 0 1 ep1140

noncomputable def ep1145 := @ep1143 1 0 1 ep1144 qz148

noncomputable def ep1146 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145) 0 1 0 1 53363 162000 0

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 1 24 0 1 0 1 0 1 0

noncomputable def ep1148 := @ep1147 1 0 1 ep1141 qz148

noncomputable def ep1149 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz106)) ↑qz143) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)))) qz145 53363 6000 0 1 1 27 0 1 53363

noncomputable def ep1150 := @ep1149 162000 0 1 ep1144 qz147

noncomputable def ep1151 := @ep1123 1 (@ep1124 0 1 0 1 (BSN.bern_sum_base qz150 27) qz120) (ep1125 (@ep1126 1 1 1 648 0 1 (ep1142 rfl) (ep1145 rfl) rfl rfl) (@ep1146 1 53363 53363 162000 0 1 (ep1148 rfl) (ep1150 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1152 := ep1117 (ep1120 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1121 Bool.false 53363 162000 0 1 (BSN.bern_sum_succ qz150 27 0 1 1 rfl rfl) (ep1151 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 2825791397 137438953472 142669144233 926132387971072 35255454290647

noncomputable def ep1154 := @ep1153 461322907578000 0 1 7663427648602848474143 ep1098 186291314562676131329213 ep1099 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (ep1102 ep1113))

noncomputable def ep1155 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))) Bool.false 923306487425 1845291630312 0 1 Bool.false

noncomputable def ep1156 := nat_lit 40459993665647248078590233

noncomputable def ep1157 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1))))))) 285284953842550387241347 ep1058 ep1156

noncomputable def ep1158 := nat_lit 63295716447551301806456832

noncomputable def ep1159 := nat_lit 9480961121966160545073580939741775743540002816

noncomputable def ep1160 := @Enclosure.Real.IsNear.mulLit_ff qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 105195195313 549755813888 1147623665039 7409059103768576 35255454290647

noncomputable def ep1161 := @ep1160 461322907578000 0 1 285284953842550387241347 ep1058 ep1156 ep1060 (@Enclosure.Complex.IsNear.re_isNear qz210 Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (ep1102 ep1113))

noncomputable def ep1162 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz211 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz85 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz85 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz129 qz130 (@HSub.hSub Nat Nat Nat qz128 (@HMul.hMul Nat Nat Nat qz85 2 k) 1)))))) 2825791397 137438953472 142669144233 926132387971072 923306487425

noncomputable def ep1163 := @ep1162 1845291630312 0 1 200697809919988744825 19508842347747845603328 4878790608359330584075 ep1158 (@Enclosure.Complex.IsNear.im_isNear qz210 Bool.false 105195195313 549755813888 1147623665039 7409059103768576 Bool.false 2825791397 137438953472 142669144233 926132387971072 (ep1102 ep1113))

noncomputable abbrev qz501 := (ep1152 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1164 := @ep1095 485982763762539132066347 ep1058 ep1064 ep1060 (@ep1096 ep1097 7663427648602848474143 ep1098 186291314562676131329213 ep1099 ep1100 306196837588216221014113 ep937 ep1063 ep939 (ep1114 (@ep1115 35255454290647 461322907578000 0 1 qz501) rfl) (ep1154 (@ep1155 35255454290647 461322907578000 0 1 qz501) rfl) rfl rfl) (@ep1157 ep1060 200697809919988744825 19508842347747845603328 4878790608359330584075 ep1158 ep1159 485982763762539132066347 ep1058 ep1064 ep1060 (ep1161 (@ep1155 35255454290647 461322907578000 0 1 qz501) rfl) (ep1163 (@ep1115 35255454290647 461322907578000 0 1 qz501) rfl) rfl rfl)

noncomputable def ep1165 := @ep1067 ep1059 ep1060 (@ep1068 14818118207537152 (BSN.head_sum_c_eq qz150 27) (ep1069 (BSN.head_sum_c_succ qz150 26 27 rfl rfl) (ep1094 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1164 rfl rfl rfl

noncomputable def ep1166 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz150 1 27) Bool.false ep936 ep937 ep938 ep939 Bool.true 512763762352880121170653 ep1058 ep1059 ep1060 (@ep1061 ep939 Bool.true 512763762352880121170653 ep1058 ep1059 ep1060 (BSN.zetaApproximant_eq_folded' qz150 1 27 rfl) (ep1165 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1167 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz150 1 27)) 21 131072 22963493

noncomputable def ep1168 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) Bool.false 168 1048576 45926986

noncomputable def ep1169 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) qz482 Bool.false 102119989 1048576 333

noncomputable def ep1170 := nat_lit 4641083269665487748852128150965810202118238070143429249279870239266643707330816

noncomputable def ep1171 := nat_lit 13889747821512413880647880856376703971986092280518348247229308643865979911045376

noncomputable def ep1172 := BSN.cos_dyadic_bound_f 3372912478 2147483648 3 2 1048576 269804 ep1170 ep122 ep1054 ep1171 ep125 ep1054 168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372912478) qz286 0 2 ep1170 ep122 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372912478) qz287 0 2 ep1171 ep125 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1173 := @ep1169 1048576 Bool.false 168 1048576 1 134770 (@ep944 102119989 1048576 333 1048576 ep1052 rfl) (Enclosure.sfrac_false_div 102119989 1048576) (BSN.sin_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237347615300792539414528) qz21) 226375608064910080 72057594037927936 Bool.false 168 1048576 15 1000000000000000 269540 134770 (BSN.sin_reduce_arg_pos_rat_q1 102119989 1048576 226375608064910080 72057594037927936 15 237347615300792539414528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 168 1048576 237347615300792539414528 151115727451828646838272 3372912478 2147483648 269804 269540 (ep1172 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1174 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz150 1 27) Bool.false ep936 ep937 ep938 ep939 Bool.true 512763762352880121170653 ep1058 ep1059 ep1060 (@ep1061 ep939 Bool.true 512763762352880121170653 ep1058 ep1059 ep1060 (BSN.zetaApproximant_eq_folded' qz150 1 27 rfl) (ep1165 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow32.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 1 27 qz153) Bool.true ep919 ep920 ep921 ep922 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 27 qz153) ep923 Bool.true ep919 ep920 ep921 ep922 (@Eq.refl Real ep923) (@ep924 Bool.true ep919 ep920 ep921 ep922 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz398 (Complex.im (@HSub.hSub Complex Complex Complex qz78 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) (zetaApproximant qz150 1 27)) (@ep926 ep927 ep928 ep929 ep930 ep931 ep932 ep933 ep934 ep919 ep920 ep921 ep922 (@ep935 70658293760 ep936 ep937 ep938 ep939 ep925 ep927 ep928 ep929 (@ep940 141316587520 1048575 1048576 22963493 70658293760 (ep1057 rfl rfl) rfl) ep1166 rfl) (@ep1167 70658293760 512763762352880121170653 ep1058 ep1059 ep1060 ep930 ep931 ep932 ep933 (@ep1168 141316587520 21 131072 22963493 70658293760 (ep1173 rfl rfl) rfl) ep1174 rfl) rfl rfl))

theorem EMRow32.d16 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow32.d17 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow32.d18 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow32.d19 : @Eq Nat (Nat.pow 27 (Nat.succ (Nat.mul 2 3))) 10460353203 := @Eq.refl Nat 10460353203

noncomputable abbrev qz594 := (@HAdd.hAdd Complex Complex Complex qz600 qz599 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz502 := qz594

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz502) (@HAdd.hAdd Real Real Real qz420 (Complex.re qz271) qz295))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz503 := (@HPow.hPow Complex Complex Complex qz536 qz578 (@HSub.hSub Complex Complex Complex qz570 qz537 qz538))

noncomputable abbrev qz223 := qz503

noncomputable def ep1175 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 28913481209 1855425871872 178071175 1855425871872 133489957140568585 288230376151711744 189753904105

noncomputable def ep1176 := nat_lit 256014463678420898128766959616

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27)) 26561 1769472 1 1769472 1088569 1048576 6663 1048576 28913481209 1855425871872

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz595 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz504 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz595 qz224 2))

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz504 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1179 := nat_lit 781950621441006189802102638025

noncomputable def ep1180 := nat_lit 19807040628566084398385987584

noncomputable def ep1181 := nat_lit 26986075409044041160201671

noncomputable def ep1182 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz505 := (@HPow.hPow Real Nat Real qz595 qz224 1)

noncomputable def ep1183 := @Enclosure.Real.IsNear.mulLit_ff qz505 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1179 ep1180 ep1181 ep1182

noncomputable def ep1184 := ep1183 (@Enclosure.Real.IsNear.of_eq qz505 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz506 := (@HPow.hPow Real Nat Real qz595 qz224 2)

noncomputable def ep1185 := @Enclosure.Real.IsNear.inv_image qz506 ep1179 ep1180 ep1181 ep1182 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz506 (@HMul.hMul Real Real Real qz0 qz505 qz224) Bool.false ep1179 ep1180 ep1181 ep1182 (BSN.pow_succ_r qz224 1 2 rfl) ep1184) rfl rfl rfl

noncomputable def ep1186 := ep1178 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz504 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1185 rfl rfl rfl) rfl)

noncomputable def ep1187 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))))) Bool.false 1088569 1048576 6663 1048576

noncomputable def ep1188 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))))) Bool.false 1088569 1048576 6663 1048576

noncomputable def ep1189 := nat_lit 5974755043076000326414873135496345

noncomputable def ep1190 := nat_lit 5543603854358996569440465539039232

noncomputable def ep1191 := nat_lit 268595603231664508258127838497764907221352803

noncomputable def ep1192 := nat_lit 20362327029340797694606048302191998324545945600

noncomputable def ep1193 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27)))) ep1189 ep1190 ep1191 ep1192 540953 547616

noncomputable def ep1194 := nat_lit 260951215667978968618832130789467512009

noncomputable def ep1195 := nat_lit 242155703566109688146298415676311732224

noncomputable def ep1196 := nat_lit 1587705864978588408920674372113760092648421919

noncomputable def ep1197 := nat_lit 122173962176044786167636289813151989947275673600

noncomputable def ep1198 := nat_lit 52173009145236817040270940032689

noncomputable def ep1199 := nat_lit 332175176359546897320025261558726656

noncomputable def ep1200 := nat_lit 23867754411398640628092658872829350679694899

noncomputable def ep1201 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27))) ep1194 ep1195 ep1196 ep1197 ep1198 ep1199 ep1200

noncomputable def ep1202 := nat_lit 86694150077485797307038374614374398403575880009580257965162414079203082240

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 27)) (Complex.re (zetaApproximant qz5 1 27)) 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 16153984513672747997 15561352883541639168 727099262928565955791 116511307117494817259520 ep1194

noncomputable def ep1204 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 27)) (Complex.im (zetaApproximant qz5 1 27)) 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 7223088615352633 576346403094134784 2181231069726689420273 349533921352484451778560 ep1198

noncomputable def ep1205 := @ep1175 2017612633061982208 ep1176 3725500772684185331 7782220156096217088 5233315846521235 54475541092673519616 (@ep1177 178071175 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz504) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow32.d16 EMRow32.d17 rfl) (ep1186 rfl)) (ep1187 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 27)) (@ep1188 1088569 1048576 6663 1048576 (@ep1193 524288 (@ep1201 ep1197 ep1202 ep1189 ep1190 ep1191 ep1192 (@ep1203 ep1195 ep1196 ep1197 ep625 ep625 rfl) (@ep1204 ep1199 ep1200 ep1197 ep631 ep631 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz502)

noncomputable abbrev qz596 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1206 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz596) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 133489957140568585 288230376151711744 189753904105 2017612633061982208 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz596) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 109637635 3670016 1 3670016 8522891797 549755813888 1653 549755813888

noncomputable def ep1208 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz596 109637635 1048576 1 1048576 2 7 0 1 109637635 3670016

noncomputable abbrev qz507 := (Complex.re qz594)

noncomputable abbrev qz508 := (Complex.im qz594)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz267 qz507 qz507) (@HMul.hMul Real Real Real qz267 qz508 qz508))

noncomputable abbrev qz227 := qz502

noncomputable def ep1209 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 109637635 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1210 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 109637635 1048576 1 1048576 109637635

noncomputable def ep1211 := @Enclosure.Real.IsNear.sqrt_image qz226 21865 2 0 1 54818817 54818818 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz507 qz507)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz508 qz508)

noncomputable def ep1212 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 43681 4 0 1

noncomputable abbrev qz230 := qz507

noncomputable def ep1213 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz509 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1214 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz509 qz13) Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 104500 1000 3 qz14)

noncomputable abbrev qz510 := (ep1214 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz16))

noncomputable def ep1215 := @ep1213 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz510)

noncomputable def ep1216 := ep1215 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz510)

noncomputable abbrev qz231 := qz508

noncomputable def ep1217 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 104500 1000 0 1 104500 1000 0 1 43681 4

noncomputable def ep1218 := @ep1217 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz510)

noncomputable def ep1219 := ep1218 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 104500 1000 0 1 qz510)

noncomputable def ep1220 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 8522891797 549755813888

noncomputable def ep1221 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 8522891797 549755813888

noncomputable def ep1222 := nat_lit 3641904746674779549487445227951857230492464395625

noncomputable def ep1223 := nat_lit 15152848975846801455935804345602422347792708605575168

noncomputable def ep1224 := nat_lit 5029607267528138569401712621522630808198242256946809013007466641

noncomputable def ep1225 := nat_lit 53979439744233250473734652436885623235665569704262979483672400657121280000

noncomputable def ep1226 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1222 ep1223 ep1224 ep1225

noncomputable def ep1227 := nat_lit 5885072639612909255438108139335687528575538265625

noncomputable def ep1228 := nat_lit 30305697951693602911871608691204844695585417211150336

noncomputable def ep1229 := nat_lit 8170294579557951226024735055404157404734213340269287251288173271

noncomputable def ep1230 := nat_lit 107958879488466500947469304873771246471331139408525958967344801314242560000

noncomputable def ep1231 := nat_lit 1398736853736649843536782316568026932409390525625

noncomputable def ep1232 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1227 ep1228 ep1229 ep1230 ep1231

noncomputable def ep1233 := nat_lit 1888919955498325912778690187641104211662271173624330774726760011

noncomputable def ep1234 := nat_lit 220740930443130152786662064881030008479732965511017631016757315667776332027459231061963806458511360000

noncomputable def ep1235 := nat_lit 2425916865767025672549125

noncomputable def ep1236 := nat_lit 174085318024506601157689344

noncomputable def ep1237 := nat_lit 28214004058961370169965307289

noncomputable def ep1238 := nat_lit 10390326245526003739654116363101798400

noncomputable def ep1239 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1235 ep1236 ep1237 ep1238 ep1235 ep1236 ep1237

noncomputable def ep1240 := nat_lit 13379764520928402120843825569

noncomputable def ep1241 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1235 ep1236 ep1237 ep1238 Bool.false 1182682059446514916794475 ep1236 ep1240

noncomputable def ep1242 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep1235 ep1236 ep1237 ep1238 Bool.false 1182682059446514916794475 ep1236 ep1240 ep1238

noncomputable def ep1243 := nat_lit 58028439341502200385896448

noncomputable def ep1244 := nat_lit 175016118156009625294880897

noncomputable def ep1245 := nat_lit 3463442081842001246551372121033932800

noncomputable def ep1246 := nat_lit 43521329506126650289422336

noncomputable def ep1247 := nat_lit 13844477852246670647040332299

noncomputable abbrev qz232 := (Complex.re qz503)

noncomputable abbrev qz233 := (Complex.im qz503)

noncomputable def ep1248 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) 15454937979896776150045 ep1243 ep1244 ep1245 618070419926679000249815 ep1246 ep1247

noncomputable def ep1249 := nat_lit 5195163122763001869827058181550899200

noncomputable def ep1250 := nat_lit 35193042423172246265911882710167199534129610752000

noncomputable def ep1251 := nat_lit 3607752168585417965157679292743680

noncomputable def ep1252 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 65519 960 0 1 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 15454937979896776150045

noncomputable def ep1253 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 65519 960 0 1 0 1 0 1 65519

noncomputable def ep1254 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 196557 4 0 1 65519 960 0

noncomputable def ep1255 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow32.d18 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz17)

noncomputable abbrev qz511 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 qz539)

noncomputable abbrev qz234 := qz511

noncomputable def ep1256 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz77 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1

noncomputable abbrev qz235 := (Complex.re qz511)

noncomputable abbrev qz236 := (Complex.im qz511)

noncomputable def ep1257 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 109195 4 0 1 43681 2 0 1

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 21839 2 0 1 5 2 0 1 109195 4

noncomputable abbrev qz512 := (@HAdd.hAdd Complex Complex Complex qz535 qz534 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz512

noncomputable def ep1259 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz77 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 21839 2 0 1 Bool.false 209 1 0 1

noncomputable abbrev qz238 := (Complex.re qz512)

noncomputable abbrev qz239 := (Complex.im qz512)

noncomputable def ep1260 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 43681 4 0 1

noncomputable def ep1261 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1262 := @ep1261 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable abbrev qz513 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1263 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz513 qz13) Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 104500 1000 1 qz14)

noncomputable abbrev qz514 := (ep1263 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz16))

noncomputable def ep1264 := ep1262 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz514)

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 104500 1000 0 1 104500 1000 0 1 43681 4

noncomputable def ep1266 := @ep1265 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep1267 := ep1266 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz514)

noncomputable def ep1268 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 21839 2 0 1 Bool.false 209 1 0 1 (@ep1260 174712 21839 2 0 1 (ep1264 rfl) (ep1267 rfl) rfl rfl)

noncomputable def ep1269 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 209 4 0 1 627 4 0 1

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 104500 1000 0 1 209 4

noncomputable def ep1271 := @ep1270 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep1272 := ep1271 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz514)

noncomputable def ep1273 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 104500 1000 0 1 3 2 0 1 627 4

noncomputable def ep1274 := @ep1273 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 104500 1000 0 1 ep592)

noncomputable def ep1275 := ep1274 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 104500 1000 0 1 qz514)

noncomputable abbrev qz240 := (ep1259 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1268 (@ep1269 3344 209 1 0 1 (ep1272 rfl) (ep1275 rfl) rfl rfl)))

noncomputable def ep1276 := @ep1258 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz240)

noncomputable abbrev qz515 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1277 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz515 qz13) Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 104500 1000 2 qz14)

noncomputable abbrev qz516 := (ep1277 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz16))

noncomputable def ep1278 := ep1276 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz516)

noncomputable def ep1279 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 209 1 0 1 104500 1000 0 1 43681 2

noncomputable def ep1280 := @ep1279 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz240)

noncomputable def ep1281 := ep1280 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz516)

noncomputable def ep1282 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 (@ep1257 393114 196557 4 0 1 (ep1278 rfl) (ep1281 rfl) rfl rfl)

noncomputable def ep1283 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 4564351 4 0 1 1045 2 0 1

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 21839 2 0 1 104500 1000 0 1 4564351 4

noncomputable def ep1285 := @ep1284 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz240)

noncomputable def ep1286 := ep1285 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz516)

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 209 1 0 1 5 2 0 1 1045 2

noncomputable def ep1288 := @ep1287 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 21839 2 0 1 Bool.false 209 1 0 1 qz240)

noncomputable def ep1289 := ep1288 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 104500 1000 0 1 qz516)

noncomputable abbrev qz241 := (ep1256 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1282 (@ep1283 9124522 4562261 4 0 1 (ep1286 rfl) (ep1289 rfl) rfl rfl)))

noncomputable def ep1290 := @ep1254 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz241)

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4562261 4 0 1 0 1 0

noncomputable def ep1292 := @ep1291 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz241)

noncomputable def ep1293 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 4562261 2880 0 1 0 1 0 1 4562261

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4562261 4 0 1 4562261 2880 0

noncomputable def ep1295 := @ep1294 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz241)

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 196557 4 0 1 0 1 0

noncomputable def ep1297 := @ep1296 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 196557 4 0 1 Bool.true 4562261 4 0 1 qz241)

noncomputable def ep1298 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 (@ep1253 65519 960 0 1 (ep1290 rfl) (ep1292 rfl) rfl rfl) (@ep1293 4562261 2880 0 1 (ep1295 rfl) (ep1297 rfl) rfl rfl)

noncomputable def ep1299 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 ep1298

noncomputable def ep1300 := nat_lit 1803876084292708982578839646371840

noncomputable def ep1301 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 Bool.false 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300

noncomputable abbrev qz597 := (@Nat.cast Real Real.instNatCast 10460353203)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz597))

noncomputable def ep1302 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz138) (@HMul.hMul Real Real Real qz0 qz242 qz581)) Bool.false 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 Bool.false 677372929701609575 75557863725914323419136 3034565065928203284959

noncomputable def ep1303 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz597) 56226753128282463 549755813888 1 549755813888 2687612 2687613 274877906944 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz597) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz597 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 10460353203) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz597 qz15)) Bool.false 56226753128282463 549755813888 1 549755813888 56226753128282463 549755813888 1 549755813888 (BSN.sqrt_enclosure 10460353203 1 28113376564141231 28113376564141232 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1304 := nat_lit 3581115178500000000000000

noncomputable def ep1305 := nat_lit 1790557589250000000000000

noncomputable def ep1306 := nat_lit 32640387355024858926381268992

noncomputable def ep1307 := nat_lit 9903520314283042199192993792

noncomputable def ep1308 := nat_lit 71622303570000000000000000

noncomputable def ep1309 := nat_lit 165384128016192829869617185803053619675

noncomputable def ep1310 := nat_lit 3756250787496183507247588531701759465

noncomputable def ep1311 := nat_lit 191591553670487038802158425

noncomputable def ep1312 := BSN.log_dyadic_bound 11 43 10 9 ep1309 274877906944 71622303570 ep1310 ep1311 143829354570 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 11) (BSN.artanhQ 43) 0 9 ep1310 ep1309 ep1311 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1313 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz140 104500 1000 0 1 3710782420401399 1125899906842624 25007162230357 ep1305 775553525863892391 2251799813685248 5226496906144613 ep1304 qz16 (BSN.isNear_log_sfrac 27 1 3710782420401399 1125899906842624 25007162230357 ep1305 Bool.false (@Enclosure.Real.IsNear.recentre' qz445 Bool.false ep1306 ep1307 1000286489214280 ep1308 3710782420401399 1125899906842624 25007162230357 ep1305 (BSN.log_rat_reduce_isNear 27 1 4 54 32 143829354570 274877906944 24973259072661432 36028797018963968 71622303570 1000000000000000 rfl rfl rfl rfl (ep1312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1314 := nat_lit 8131917777857095091630374912

noncomputable def ep1315 := nat_lit 221859320419280750341286229374643082974032674422290385167615156285963641121322789456087045615304753215975255707769673580800

noncomputable def ep1316 := nat_lit 937046835760177389014339949136452948956763638101868628335989667301470209077471332707205705798296416271460543045470610396282880

noncomputable def ep1317 := nat_lit 2084420601222426112097033492390917437784850938488320505007628123274765061727866515606474968218060042152727011616850176

noncomputable def ep1318 := nat_lit 581056750131428557442044348403172774875186305156860122920079206493895662840983555839202708985373429182724089105187479716096

noncomputable def ep1319 := nat_lit 17179191988936585465262899067501637397540666698534258186159810567193620499753641099632104606302100964976776622500294523931852800

noncomputable def ep1320 := BSN.sin_dyadic_bound_f 462246008388382 1125899906842624 3 2 549755813888 143384494452 ep1315 ep1316 ep1317 ep1318 ep1319 ep1317 219418561079 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 462246008388382) (BSN.sinEvenQ 1125899906842624) 0 2 ep1315 ep1316 ep1317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 462246008388382) (BSN.sinOddQ 1125899906842624) 0 2 ep1318 ep1319 ep1317 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz517 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47336030631341) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1321 := @Enclosure.Real.IsNear.cos_image qz141 qz517 Bool.false 47336030631341 137438953472 803 549755813888 Bool.false 219418561079 549755813888 1 71622303570 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 775553525863892391 2251799813685248 5226496906144613 ep1304 47336030631341 137438953472 803 549755813888 (ep1313 rfl) rfl) (Enclosure.sfrac_false_div 47336030631341 137438953472) (BSN.cos_reduce3 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1314) (@Nat.cast Real Real.instNatCast ep1180)) 226375608064910080 72057594037927936 Bool.false 219418561079 549755813888 54 1000000000000000 143244607140 71622303570 (BSN.sin_reduce_arg_pos_rat_q3 47336030631341 137438953472 226375608064910080 72057594037927936 54 ep1314 ep1180 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 219418561079 549755813888 ep1314 ep1180 462246008388382 1125899906842624 143384494452 143244607140 (ep1320 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1322 := nat_lit 123256104419867626823431059445242775393323834612800653235566201326923478296317873194055294886266293146671654382988315033856

noncomputable def ep1323 := nat_lit 104116315084464154334926661015161438772973737566874292037332185255718912119719036967467300644255157363495615893941178932920320

noncomputable def ep1324 := nat_lit 369764144418400435618068984268743544345095934136524983065688588724523885358830163849134671708862443319930657694941711401216

noncomputable def ep1325 := nat_lit 4685234178800886945071699745682264744783818190509343141679948336507351045387356663536028528991482081357302715227353051981414400

noncomputable def ep1326 := BSN.cos_dyadic_bound_f 462246008388382 1125899906842624 3 2 549755813888 143384494452 ep1322 ep1323 ep1317 ep1324 ep1325 ep1317 504070381948 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 462246008388382) (BSN.cosEvenQ 1125899906842624) 0 2 ep1322 ep1323 ep1317 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 462246008388382) (BSN.cosOddQ 1125899906842624) 0 2 ep1324 ep1325 ep1317 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1327 := @Enclosure.Real.IsNear.sin_image qz141 qz517 Bool.false 47336030631341 137438953472 803 549755813888 Bool.true 504070381948 549755813888 1 71622303570 (@Enclosure.Real.IsNear.recentre' qz141 Bool.false 775553525863892391 2251799813685248 5226496906144613 ep1304 47336030631341 137438953472 803 549755813888 (ep1313 rfl) rfl) (Enclosure.sfrac_false_div 47336030631341 137438953472) (BSN.sin_reduce3 qz517 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1314) (@Nat.cast Real Real.instNatCast ep1180)) 226375608064910080 72057594037927936 Bool.false 504070381948 549755813888 54 1000000000000000 143244607140 71622303570 (BSN.sin_reduce_arg_pos_rat_q3 47336030631341 137438953472 226375608064910080 72057594037927936 54 ep1314 ep1180 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 504070381948 549755813888 ep1314 ep1180 462246008388382 1125899906842624 143384494452 143244607140 (ep1326 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz518 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 5375225 549755813888 1 549755813888 5375225 549755813888 1 549755813888 (ep1303 rfl rfl) rfl)

noncomputable def ep1328 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz138) (@HMul.hMul Real Real Real qz0 qz242 qz581) Bool.false 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 Bool.false 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300 (@Enclosure.Real.IsNear.mulLit_ff qz242 qz138 5375225 549755813888 1 549755813888 219418561079 549755813888 29031232790299 19687388895829378990080 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 qz518 (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 219418561079 549755813888 58062465580598 39374777791658757980160 219418561079 549755813888 29031232790299 19687388895829378990080 (ep1321 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz581 5375225 549755813888 1 549755813888 126017595487 137438953472 29031232790299 19687388895829378990080 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300 qz518 (@Enclosure.Real.IsNear.neg qz139 Bool.true 126017595487 137438953472 29031232790299 19687388895829378990080 (@Enclosure.Real.IsNear.recentre' qz139 Bool.true 504070381948 549755813888 58062465580598 39374777791658757980160 126017595487 137438953472 29031232790299 19687388895829378990080 (ep1327 rfl rfl) rfl)) rfl)

noncomputable def ep1329 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 4562261 2880 0 1 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300 618070419926679000249815

noncomputable def ep1330 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 65519 960 0 1 Bool.false 4562261 2880 0 1 ep1298

noncomputable def ep1331 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 Bool.false 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300

noncomputable def ep1332 := nat_lit 14507109835375550096474112

noncomputable def ep1333 := nat_lit 198821668554549951027228721

noncomputable def ep1334 := nat_lit 1731721040921000623275686060516966400

noncomputable def ep1335 := nat_lit 12186834509601102414680453243

noncomputable def ep1336 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) 8876159396223951548885 ep1332 ep1333 ep1334 1076168146691827498207855 ep1236 ep1335

noncomputable def ep1337 := nat_lit 17157298536718747567426675086597528178750862131200

noncomputable def ep1338 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 65519 960 0 1 677372929701609575 75557863725914323419136 3034565065928203284959 ep1300 8876159396223951548885

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 4562261 2880 0 1 1179424134975867775 302231454903657293676544 2671226944184276702863 ep1251 1076168146691827498207855

noncomputable abbrev qz519 := (@ep1302 ep1300 (BSN.cpow_neg_s_sub_mk qz13 104500 1000 27 3 10460353203 qz14 rfl EMRow32.d19) ep1328)

noncomputable def ep1340 := ep1242 (@ep1248 ep1249 ep1250 ep1235 ep1236 ep1237 ep1238 (@ep1252 ep1243 ep1244 ep1245 ep1299 (ep1301 qz519) rfl) (@ep1329 ep1246 ep1247 ep1249 ep1330 (ep1331 qz519) rfl) rfl rfl) (@ep1336 ep1238 ep1337 1182682059446514916794475 ep1236 ep1240 ep1238 (@ep1338 ep1332 ep1333 ep1334 ep1299 (ep1331 qz519) rfl) (@ep1339 ep1236 ep1335 ep1238 ep1330 (ep1301 qz519) rfl) rfl rfl)

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 1182682059446514916794475 ep1236 ep1240 ep1238 1182682059446514916794475 ep1236 ep1240

noncomputable def ep1342 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1235 ep1236 ep1237 ep1238 Bool.false 1182682059446514916794475 ep1236 ep1240

noncomputable def ep1343 := @ep1207 133489957140568585 288230376151711744 189753904105 2017612633061982208 (@ep1208 1 3670016 (ep1209 (@ep1210 1048576 1 1048576 (ep1211 (@ep1212 174920 21865 2 0 1 (ep1216 rfl) (ep1219 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1220 1653 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1221 1653 549755813888 8522891797 549755813888 1653 549755813888 (@ep1226 4261445072 4261446725 274877906944 (@ep1232 ep1228 ep1233 ep1230 ep1234 ep1222 ep1223 ep1224 ep1225 (@ep1239 ep1238 ep1227 ep1228 ep1229 ep1230 (@ep1241 ep1238 ep1340) (@ep1241 ep1238 ep1340) rfl) (@ep1341 ep1238 ep1231 ep1228 ep1233 ep1230 (@ep1342 ep1238 ep1340) (@ep1342 ep1238 ep1340) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow32.d20 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 3725500772684185331 7782220156096217088 5233315846521235 54475541092673519616 := ep1205 (ep1206 ep1343) rfl rfl

noncomputable abbrev qz598 := (@HAdd.hAdd Complex Complex Complex qz600 qz606 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz520 := qz598

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz520) (@HAdd.hAdd Real Real Real qz420 (Complex.re qz450) qz295))

noncomputable abbrev qz521 := (@HPow.hPow Complex Complex Complex qz536 qz578 (@HSub.hSub Complex Complex Complex qz570 qz583 qz538))

noncomputable abbrev qz244 := qz521

noncomputable def ep1344 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 9051218531 618475290624 61495349 618475290624 508294228753738617 1008806316530991104 100498242487

noncomputable def ep1345 := nat_lit 323498347277345586791927775232

noncomputable def ep1346 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27)) 26561 1769472 1 1769472 1022313 1048576 6907 1048576 9051218531 618475290624

noncomputable def ep1347 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz150 1 27)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz150 1 27)) (Complex.im (zetaApproximant qz150 1 27))))) Bool.false 1022313 1048576 6907 1048576

noncomputable def ep1348 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz150 1 27)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz150 1 27)) (Complex.im (zetaApproximant qz150 1 27))))) Bool.false 1022313 1048576 6907 1048576

noncomputable def ep1349 := nat_lit 1651596438758413818832336127482766721761261

noncomputable def ep1350 := nat_lit 1737466119469605208519895820709920768000000

noncomputable def ep1351 := nat_lit 50008066584736653624598441347697252016179527665333066670733

noncomputable def ep1352 := nat_lit 3894169984431769530541244658901540611770500274850889728000000

noncomputable def ep1353 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz150 1 27)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz150 1 27)) (Complex.im (zetaApproximant qz150 1 27)))) ep1349 ep1350 ep1351 ep1352 507703 514610

noncomputable def ep1354 := nat_lit 10042280622742996090473261232900440045488651406769

noncomputable def ep1355 := nat_lit 10572081381924435343333482614112472786796544000000

noncomputable def ep1356 := nat_lit 36408624547415598007378856636554583887880997830558762857003

noncomputable def ep1357 := nat_lit 2920627488323827147905933494176155458827875206138167296000000

noncomputable def ep1358 := nat_lit 262926675982280921057484132470586743607148446409

noncomputable def ep1359 := nat_lit 380594929749279672360005374108049020324675584000000

noncomputable def ep1360 := nat_lit 4389701564547568844279897496873420497014591673764148584187

noncomputable def ep1361 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz150 1 27)) (Complex.re (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz150 1 27)) (Complex.im (zetaApproximant qz150 1 27))) ep1354 ep1355 ep1356 ep1357 ep1358 ep1359 ep1360

noncomputable def ep1362 := nat_lit 11682509953295308591623733976704621835311500824552669184000000

noncomputable def ep1363 := nat_lit 3824820770351386667780457848817888574147844906578157470898962547159018894810535281622717038592000000

noncomputable def ep1364 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz150 1 27)) (Complex.re (zetaApproximant qz150 1 27)) ep936 ep937 ep938 ep939 ep936 ep937 ep938 ep939 ep1354

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz150 1 27)) (Complex.im (zetaApproximant qz150 1 27)) 512763762352880121170653 ep1058 ep1059 ep1060 512763762352880121170653 ep1058 ep1059 ep1060 ep1358

noncomputable def ep1366 := @ep1344 1008806316530991104 ep1345 4707520526096713537 9079256848778919936 903660143204719 9079256848778919936 (@ep1346 61495349 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz504) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow32.d16 EMRow32.d17 rfl) (ep1186 rfl)) (ep1347 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz150 1 27)) (@ep1348 1022313 1048576 6907 1048576 (@ep1353 524288 (@ep1361 ep1362 ep1363 ep1349 ep1350 ep1351 ep1352 (@ep1364 ep1355 ep1356 ep1357 ep1166 ep1166 rfl) (@ep1365 ep1359 ep1360 ep1362 ep1174 ep1174 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz520)

noncomputable def ep1367 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz596) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 508294228753738617 1008806316530991104 100498242487 1008806316530991104 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz153 3)

noncomputable def ep1368 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz596) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 111970483 3670016 1 3670016 4539537699 274877906944 857 274877906944

noncomputable def ep1369 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz596 111970483 1048576 1 1048576 2 7 0 1 111970483 3670016

noncomputable abbrev qz522 := (Complex.re qz598)

noncomputable abbrev qz523 := (Complex.im qz598)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz267 qz522 qz522) (@HMul.hMul Real Real Real qz267 qz523 qz523))

noncomputable abbrev qz247 := qz520

noncomputable def ep1370 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 111970483 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1371 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 111970483 1048576 1 1048576 111970483

noncomputable def ep1372 := @Enclosure.Real.IsNear.sqrt_image qz246 2850672269 250000 0 1 55985241 55985242 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz522 qz522)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz523 qz523)

noncomputable def ep1373 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 2847609769 250000 0 1

noncomputable abbrev qz250 := qz522

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1375 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz509 qz153) Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 106726 1000 3 qz154)

noncomputable abbrev qz524 := (ep1375 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz153 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz155))

noncomputable def ep1376 := @ep1374 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz524)

noncomputable def ep1377 := ep1376 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz524)

noncomputable abbrev qz251 := qz523

noncomputable def ep1378 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 106726 1000 0 1 106726 1000 0 1 2847609769 250000

noncomputable def ep1379 := @ep1378 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz524)

noncomputable def ep1380 := ep1379 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 106726 1000 0 1 qz524)

noncomputable def ep1381 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 4539537699 274877906944

noncomputable def ep1382 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 9079075398 549755813888

noncomputable def ep1383 := nat_lit 322870159911115195280022433432328047844698757439280039497542713

noncomputable def ep1384 := nat_lit 1183816326238031363744984714500189245921305359810560000000000000000

noncomputable def ep1385 := nat_lit 10852608395468530254049829913207185637552956009591068658333765639963003596522787

noncomputable def ep1386 := nat_lit 105428593250455567331512993040792232882159315828638631804047657533440000000000000000000000

noncomputable def ep1387 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1383 ep1384 ep1385 ep1386

noncomputable def ep1388 := nat_lit 1042481063200450820029803794352084008922911754065417628609

noncomputable def ep1389 := nat_lit 913438523331814323877303020447676887284957839360000000000000000

noncomputable def ep1390 := nat_lit 53030115073271602925510114988898027204225829875557838188629088068971133297

noncomputable def ep1391 := nat_lit 51478805298074007486090328633199332461991853431952456935570145280000000000000000000000

noncomputable def ep1392 := nat_lit 321519104453207411017263807714847746969134663806011258250865449

noncomputable def ep1393 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1388 ep1389 ep1390 ep1391 ep1392

noncomputable def ep1394 := nat_lit 10744002719798470011258385197709922477838701510005926205723453267597750715530531

noncomputable def ep1395 := nat_lit 294922042097115819070503658200590792222153520886148522789740717122258568226328846047364192354569662525792583680000000000000000

noncomputable def ep1396 := nat_lit 32287475330233716185231215647

noncomputable def ep1397 := nat_lit 30223145490365729367654400000000

noncomputable def ep1398 := nat_lit 611517417680564463644538548147461

noncomputable def ep1399 := nat_lit 1268350371768311003375746626355200000000000

noncomputable def ep1400 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1396 ep1397 ep1398 ep1399 ep1396 ep1397 ep1398

noncomputable def ep1401 := nat_lit 17930953807681492407789776417357

noncomputable def ep1402 := nat_lit 1088033237653166257235558400000000

noncomputable def ep1403 := nat_lit 1003911983026072069527209468342374591

noncomputable def ep1404 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1396 ep1397 ep1398 ep1399 Bool.false ep1401 ep1402 ep1403

noncomputable def ep1405 := nat_lit 324697695172687616864191136346931200000000000

noncomputable def ep1406 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1396 ep1397 ep1398 ep1399 Bool.false ep1401 ep1402 ep1403 ep1405

noncomputable def ep1407 := nat_lit 1003983274036012003205200817

noncomputable def ep1408 := nat_lit 1450710983537555009647411200000

noncomputable def ep1409 := nat_lit 56193658045377120632368117200571

noncomputable def ep1410 := nat_lit 432930260230250155818921515129241600000000

noncomputable def ep1411 := nat_lit 319222761235903797512037396007

noncomputable def ep1412 := nat_lit 181338872942194376205926400000000

noncomputable def ep1413 := nat_lit 57201607696095831109362890212660883

noncomputable abbrev qz252 := (Complex.re qz521)

noncomputable abbrev qz253 := (Complex.im qz521)

noncomputable def ep1414 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1407 ep1408 ep1409 ep1410 ep1411 ep1412 ep1413

noncomputable def ep1415 := nat_lit 162348847586343808432095568173465600000000000

noncomputable def ep1416 := nat_lit 281038770553607388836724740148700615626863936534898278400000

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 8542516807 120000000 0 1 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 ep1407

noncomputable def ep1418 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) 8542516807 120000000 0 1 0 1 0 1 8542516807

noncomputable def ep1419 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 25627550421 500000 0 1 8542516807 120000000 0

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz535 qz582 qz539)

noncomputable abbrev qz254 := qz525

noncomputable def ep1420 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz77 (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1

noncomputable abbrev qz255 := (Complex.re qz525)

noncomputable abbrev qz256 := (Complex.im qz525)

noncomputable def ep1421 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 2847422269 100000 0 1 2847609769 125000 0 1

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 2847422269 250000 0 1 5 2 0 1 2847422269 100000

noncomputable abbrev qz526 := (@HAdd.hAdd Complex Complex Complex qz535 qz582 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz526

noncomputable def ep1423 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz77 (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1

noncomputable abbrev qz258 := (Complex.re qz526)

noncomputable abbrev qz259 := (Complex.im qz526)

noncomputable def ep1424 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 2847609769 250000 0 1

noncomputable def ep1425 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1426 := @ep1425 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1427 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz513 qz153) Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 106726 1000 1 qz154)

noncomputable abbrev qz527 := (ep1427 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz153 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz155))

noncomputable def ep1428 := ep1426 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz527)

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 106726 1000 0 1 106726 1000 0 1 2847609769 250000

noncomputable def ep1430 := @ep1429 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1431 := ep1430 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz527)

noncomputable def ep1432 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 (@ep1424 11389689076 2847422269 250000 0 1 (ep1428 rfl) (ep1431 rfl) rfl rfl)

noncomputable def ep1433 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 53363 1000 0 1 160089 1000 0 1

noncomputable def ep1434 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 106726 1000 0 1 53363 1000

noncomputable def ep1435 := @ep1434 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1436 := ep1435 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz527)

noncomputable def ep1437 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 106726 1000 0 1 3 2 0 1 160089 1000

noncomputable def ep1438 := @ep1437 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 106726 1000 0 1 ep1131)

noncomputable def ep1439 := ep1438 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 106726 1000 0 1 qz527)

noncomputable abbrev qz260 := (ep1423 (BSN.ascPochhammer_succ_eval_c 1 2 qz450 rfl) (ep1432 (@ep1433 213452000 53363 250 0 1 (ep1436 rfl) (ep1439 rfl) rfl rfl)))

noncomputable def ep1440 := @ep1422 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz260)

noncomputable def ep1441 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz515 qz153) Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 (BSN.s_add_nat_mk qz153 Bool.false 106726 1000 2 qz154)

noncomputable abbrev qz528 := (ep1441 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz153 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz155))

noncomputable def ep1442 := ep1440 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz528)

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 53363 250 0 1 106726 1000 0 1 2847609769 125000

noncomputable def ep1444 := @ep1443 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz260)

noncomputable def ep1445 := ep1444 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz528)

noncomputable def ep1446 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 (@ep1421 640688760525000 25627550421 500000 0 1 (ep1442 rfl) (ep1445 rfl) rfl rfl)

noncomputable def ep1447 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 151946994540647 125000000 0 1 53363 100 0 1

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 2847422269 250000 0 1 106726 1000 0 1 151946994540647 125000000

noncomputable def ep1449 := @ep1448 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz260)

noncomputable def ep1450 := ep1449 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz528)

noncomputable def ep1451 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 53363 250 0 1 5 2 0 1 53363 100

noncomputable def ep1452 := @ep1451 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2847422269 250000 0 1 Bool.false 53363 250 0 1 qz260)

noncomputable def ep1453 := ep1452 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 106726 1000 0 1 qz528)

noncomputable abbrev qz261 := (ep1420 (BSN.ascPochhammer_succ_eval_c 2 3 qz450 rfl) (ep1446 (@ep1447 15188029079064700 151880290790647 125000000 0 1 (ep1450 rfl) (ep1453 rfl) rfl rfl)))

noncomputable def ep1454 := @ep1419 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz261)

noncomputable def ep1455 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 151880290790647 125000000 0 1 0 1 0

noncomputable def ep1456 := @ep1455 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz261)

noncomputable def ep1457 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) 151880290790647 90000000000 0 1 0 1 0 1 151880290790647

noncomputable def ep1458 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 151880290790647 125000000 0 1 151880290790647 90000000000 0

noncomputable def ep1459 := @ep1458 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz261)

noncomputable def ep1460 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 25627550421 500000 0 1 0 1 0

noncomputable def ep1461 := @ep1460 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1255) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 25627550421 500000 0 1 Bool.true 151880290790647 125000000 0 1 qz261)

noncomputable def ep1462 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 (@ep1418 8542516807 120000000 0 1 (ep1454 rfl) (ep1456 rfl) rfl rfl) (@ep1457 151880290790647 90000000000 0 1 (ep1459 rfl) (ep1461 rfl) rfl rfl)

noncomputable def ep1463 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 ep1462

noncomputable def ep1464 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.false 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 Bool.false 157635378284166075 151115727451828646838272 376622979837080913989 ep1300

noncomputable def ep1465 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz593)) Bool.false 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 Bool.false 157635378284166075 151115727451828646838272 376622979837080913989

noncomputable def ep1466 := nat_lit 895278794625000000000000000

noncomputable def ep1467 := @Enclosure.Real.IsNear.mulLit_ff qz153 qz140 106726 1000 0 1 3710782420401399 1125899906842624 25007162230357 ep1305 198018482299879854837 562949953421312000 1334457198098540591 ep1466 qz155 (BSN.isNear_log_sfrac 27 1 3710782420401399 1125899906842624 25007162230357 ep1305 Bool.false (@Enclosure.Real.IsNear.recentre' qz445 Bool.false ep1306 ep1307 1000286489214280 ep1308 3710782420401399 1125899906842624 25007162230357 ep1305 (BSN.log_rat_reduce_isNear 27 1 4 54 32 143829354570 274877906944 24973259072661432 36028797018963968 71622303570 1000000000000000 rfl rfl rfl rfl (ep1312 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1468 := nat_lit 7248903906577449621307523072

noncomputable def ep1469 := nat_lit 4951760157141521099596496896

noncomputable def ep1470 := nat_lit 90906304083996292465524778785500796001788077013540563944279595817088868114933433375458673879454257378086952923322261842151706296640771130526696964091454789343083351467637988744702590396710497465705966001304603176989745382300806410736520567781299018858496

noncomputable def ep1471 := nat_lit 2371728904138043385318735560374504222700605579872037175997883585289299297944925459400262945270439995320386160994569494400873352117161187529222914467416668525224467727137180455887633346091077280717708110065332645507572399051088361938793378954328561156096000

noncomputable def ep1472 := nat_lit 2966199767040626144858737880697456790582920901167916249831692592617358012406168300955635062951099429898806811888813480781521238658078347998878712994482379961708143663844051601954044211328117782608120873589973862485042641955339950104374505701376

noncomputable def ep1473 := nat_lit 739542907029212010943066515758393944199152872690190730431978673190200681277369721849631210587909141417838186434784696084102508785571747644104286309633770769088771096550759565685175039361912431016653530978009940011261001973630617349684506039037214698045440

noncomputable def ep1474 := nat_lit 135188547535868472963167926941346740693934518052706119031879364361490059982860751185814987880415079733262011176690461180849781070678187689165706124642750105937794660446819285985595100727191405000909362273723960793931626745912036630511222600396727985897472000

noncomputable def ep1475 := BSN.sin_dyadic_bound_f 1648209924173318 1125899906842624 5 4 549755813888 143384494452 ep1470 ep1471 ep1472 ep1473 ep1474 ep1472 546618085159 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.sinEvenP 1648209924173318) (BSN.sinEvenQ 1125899906842624) 0 4 ep1470 ep1471 ep1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.sinOddP 1648209924173318) (BSN.sinOddQ 1125899906842624) 0 4 ep1473 ep1474 ep1472 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz529 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12086089007561) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1476 := @Enclosure.Real.IsNear.cos_image qz218 qz529 Bool.false 12086089007561 34359738368 205 137438953472 Bool.false 546618085159 549755813888 1 71622303570 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 198018482299879854837 562949953421312000 1334457198098540591 ep1466 12086089007561 34359738368 205 137438953472 (ep1467 rfl) rfl) (Enclosure.sfrac_false_div 12086089007561 34359738368) (BSN.cos_reduce3 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1468) (@Nat.cast Real Real.instNatCast ep1469)) 226375608064910080 72057594037927936 Bool.false 546618085159 549755813888 55 1000000000000000 143244607140 71622303570 (BSN.sin_reduce_arg_pos_rat_q3 12086089007561 34359738368 226375608064910080 72057594037927936 55 ep1468 ep1469 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 546618085159 549755813888 ep1468 ep1469 1648209924173318 1125899906842624 143384494452 143244607140 (ep1475 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1477 := nat_lit 26769600706433326612816658999530762011475463435247404023618877946537175005597851424755614620765068319306841755195330886812536197431603790873709357979885548598268361012185043590027847460273673943077869721815927997595452306305363010964935284062146705555456

noncomputable def ep1478 := nat_lit 139513464949296669724631503551441424864741504698355127999875505017017605761466203494133114427672940901199185940857029082404314830421246325248406733377451089719086336890422379758096079181828075336335771180313685029857199944181668349340786997313444773888000

noncomputable def ep1479 := nat_lit 272553430077606932851988905773857489981593436442966067560563466011158196860083243519091874261432680984544442195795859401412217740287792822664881774025371131695424358488645805617630736610589436005759950228716862547428543885761823331963746416011172894539776

noncomputable def ep1480 := nat_lit 21345560137242390467868620043370538004305450218848334583980952267603693681504329134602366507433959957883475448951125449607860169054450687763006230206750016727020209544234624102988700114819695526459372990587993809568151591459795257449140410588957050404864000

noncomputable def ep1481 := BSN.cos_dyadic_bound_f 1648209924173318 1125899906842624 5 4 549755813888 143384494452 ep1477 ep1478 ep1472 ep1479 ep1480 ep1472 58652569254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 1648209924173318) (BSN.cosEvenQ 1125899906842624) 0 4 ep1477 ep1478 ep1472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 1648209924173318) (BSN.cosOddQ 1125899906842624) 0 4 ep1479 ep1480 ep1472 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1482 := @Enclosure.Real.IsNear.sin_image qz218 qz529 Bool.false 12086089007561 34359738368 205 137438953472 Bool.true 58652569254 549755813888 1 71622303570 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 198018482299879854837 562949953421312000 1334457198098540591 ep1466 12086089007561 34359738368 205 137438953472 (ep1467 rfl) rfl) (Enclosure.sfrac_false_div 12086089007561 34359738368) (BSN.sin_reduce3 qz529 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1468) (@Nat.cast Real Real.instNatCast ep1469)) 226375608064910080 72057594037927936 Bool.false 58652569254 549755813888 55 1000000000000000 143244607140 71622303570 (BSN.sin_reduce_arg_pos_rat_q3 12086089007561 34359738368 226375608064910080 72057594037927936 55 ep1468 ep1469 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 58652569254 549755813888 ep1468 ep1469 1648209924173318 1125899906842624 143384494452 143244607140 (ep1481 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1483 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz593) Bool.false 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 Bool.false 157635378284166075 151115727451828646838272 376622979837080913989 ep1300 (@Enclosure.Real.IsNear.mulLit_ff qz242 qz216 5375225 549755813888 1 549755813888 546618085159 549755813888 7410005592661 4921847223957344747520 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 qz518 (@Enclosure.Real.IsNear.recentre' qz216 Bool.false 546618085159 549755813888 14820011185322 9843694447914689495040 546618085159 549755813888 7410005592661 4921847223957344747520 (ep1476 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz593 5375225 549755813888 1 549755813888 29326284627 274877906944 7410005592661 4921847223957344747520 157635378284166075 151115727451828646838272 376622979837080913989 ep1300 qz518 (@Enclosure.Real.IsNear.neg qz217 Bool.true 29326284627 274877906944 7410005592661 4921847223957344747520 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 58652569254 549755813888 14820011185322 9843694447914689495040 29326284627 274877906944 7410005592661 4921847223957344747520 (ep1482 rfl rfl) rfl)) rfl)

noncomputable def ep1484 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 151880290790647 90000000000 0 1 157635378284166075 151115727451828646838272 376622979837080913989 ep1300 ep1411

noncomputable def ep1485 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 8542516807 120000000 0 1 Bool.false 151880290790647 90000000000 0 1 ep1462

noncomputable def ep1486 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.false 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 Bool.false 157635378284166075 151115727451828646838272 376622979837080913989 ep1300

noncomputable def ep1487 := nat_lit 17954704911603886902222967

noncomputable def ep1488 := nat_lit 241785163922925834941235200000

noncomputable def ep1489 := nat_lit 3217308135160685829569953913123

noncomputable def ep1490 := nat_lit 216465130115125077909460757564620800000000

noncomputable def ep1491 := nat_lit 17850157635579274916729773065857

noncomputable def ep1492 := nat_lit 999086020823331040782854537472690091

noncomputable def ep1493 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1487 ep1488 ep1489 ep1490 ep1491 ep1402 ep1492

noncomputable def ep1494 := nat_lit 4335438605684680808147875440992116813598233064884299366400000

noncomputable def ep1495 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 8542516807 120000000 0 1 157635378284166075 151115727451828646838272 376622979837080913989 ep1300 ep1487

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 151880290790647 90000000000 0 1 2938195196798785775 302231454903657293676544 6578115011647424041453 ep1251 ep1491

noncomputable abbrev qz530 := (@ep1465 ep1300 (BSN.cpow_neg_s_sub_mk qz153 106726 1000 27 3 10460353203 qz154 rfl EMRow32.d19) ep1483)

noncomputable def ep1497 := ep1406 (@ep1414 ep1415 ep1416 ep1396 ep1397 ep1398 ep1399 (@ep1417 ep1408 ep1409 ep1410 ep1463 (ep1464 qz530) rfl) (@ep1484 ep1412 ep1413 ep1415 ep1485 (ep1486 qz530) rfl) rfl rfl) (@ep1493 ep1405 ep1494 ep1401 ep1402 ep1403 ep1405 (@ep1495 ep1488 ep1489 ep1490 ep1463 (ep1486 qz530) rfl) (@ep1496 ep1402 ep1492 ep1405 ep1485 (ep1464 qz530) rfl) rfl rfl)

noncomputable def ep1498 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1401 ep1402 ep1403 ep1405 ep1401 ep1402 ep1403

noncomputable def ep1499 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1396 ep1397 ep1398 ep1399 Bool.false ep1401 ep1402 ep1403

noncomputable def ep1500 := @ep1368 508294228753738617 1008806316530991104 100498242487 1008806316530991104 (@ep1369 1 3670016 (ep1370 (@ep1371 1048576 1 1048576 (ep1372 (@ep1373 11402689076 2850672269 250000 0 1 (ep1377 rfl) (ep1380 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1381 857 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1382 1714 549755813888 4539537699 274877906944 857 274877906944 (@ep1387 4539536842 4539538556 274877906944 (@ep1393 ep1384 ep1394 ep1386 ep1395 ep1383 ep1384 ep1385 ep1386 (@ep1400 ep1399 ep1388 ep1389 ep1390 ep1391 (@ep1404 ep1405 ep1497) (@ep1404 ep1405 ep1497) rfl) (@ep1498 ep1405 ep1392 ep1384 ep1394 ep1386 (@ep1499 ep1405 ep1497) (@ep1499 ep1405 ep1497) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow32.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 4707520526096713537 9079256848778919936 903660143204719 9079256848778919936 := ep1366 (ep1367 ep1500) rfl rfl

noncomputable def EMRow32.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz531 := (EMRow32.d3 qz541 qz584 (@Enclosure.dec_le_dec qz541 qz584 104500 1000 106726 1000 (@Eq.refl Real qz541) (@Eq.refl Real qz584) rfl rfl rfl) 27 27 1 1)

noncomputable abbrev qz262 := qz531

noncomputable def ep1501 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 104500 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 27 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz531)

noncomputable def ep1502 := @Enclosure.Real.IsNear.pos_val qz263 705783457210689610643749 679885881717189909676032

noncomputable def ep1503 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 27 qz13) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz531)

noncomputable def ep1504 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1502 ep388 ep389 (@ep1503 705783457210689610643749 679885881717189909676032 ep388 ep389 (@Eq.refl Real (hardyZApproximantEM 1 27 qz13)) EMRow32.d11) rfl rfl rfl)

noncomputable def ep1505 := @Enclosure.Real.IsNear.neg_val qz264 ep919 ep920

noncomputable def ep1506 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 27 qz153) Bool.true

noncomputable def ep1507 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 27 qz13)

noncomputable def ep1508 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 27 qz13) Bool.false

noncomputable def ep1509 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 27 qz13) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 3725500772684185331 7782220156096217088 5233315846521235 54475541092673519616 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 27))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1510 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 27 qz153)

noncomputable def ep1511 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 27 qz153) Bool.true

noncomputable def ep1512 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 27 qz153) (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 4707520526096713537 9079256848778919936 903660143204719 9079256848778919936 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz420 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz150 1 27))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz77 (@HMul.hMul Complex Complex Complex qz77 (@HDiv.hDiv Complex Complex Complex qz84 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz150 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1513 := @List.cons EMRow32.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1501 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 27 rfl) (ep1504 (@ep1505 ep921 ep922 (@ep1506 ep919 ep920 ep921 ep922 (@Eq.refl Real (hardyZApproximantEM 1 27 qz153)) EMRow32.d15) rfl rfl rfl)) (ep1507 (hardyZErrorBoundEM 1 27 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 27 qz13 rfl) (@ep1508 Bool.false 705783457210689610643749 679885881717189909676032 ep388 ep389 3725500772684185331 7782220156096217088 5233315846521235 54475541092673519616 (@ep1503 705783457210689610643749 679885881717189909676032 ep388 ep389 (@Eq.refl Real (hardyZApproximantEM 1 27 qz13)) EMRow32.d11) (ep1509 EMRow32.d20) rfl rfl rfl rfl rfl)) (ep1510 (hardyZErrorBoundEM 1 27 qz153) (BSN.hardyZErrorBoundEM_le_strong 1 27 qz153 rfl) (@ep1511 Bool.false ep919 ep920 ep921 ep922 4707520526096713537 9079256848778919936 903660143204719 9079256848778919936 (@ep1506 ep919 ep920 ep921 ep922 (@Eq.refl Real (hardyZApproximantEM 1 27 qz153)) EMRow32.d15) (ep1512 EMRow32.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow32.d0)

noncomputable abbrev qz532 := (@Enclosure.dec_le_dec qz541 qz584 104500 1000 106726 1000 (@Eq.refl Real qz541) (@Eq.refl Real qz584) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1513 (@List.IsChain.singleton EMRow32.d1 EMRow32.d22 (EMRow32.d2 qz283 qz452 qz532))))

noncomputable abbrev qz533 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1514 := And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz265)) (@Option.some Real qz13))

noncomputable def ep1515 := ep1514 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz265)) (@Option.some Real qz153))

noncomputable def ep1516 := @And.intro (@Eq Nat (@List.length qz533 qz265) 1) ep1515

noncomputable def ep1517 := @And.intro (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 qz265)) (@Option.some Real qz13))

noncomputable def ep1518 := @ep1517 (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 qz265)) (@Option.some Real qz153))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1513 (@List.IsChain.singleton EMRow32.d1 EMRow32.d22 (EMRow32.d2 qz283 qz452 qz532)))

theorem EMRow32.d23 : Zeta.Certificates.BatchSpec 1 104500 1000 106726 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz533 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz533 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz153)))) qz266 (ep1516 (@Eq.refl Nat 1) (ep1518 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz153))))

theorem solution : Zeta.Certificates.BatchSpec 1 104500 1000 106726 1000 := EMRow32.d23
#print axioms solution
#check solution
