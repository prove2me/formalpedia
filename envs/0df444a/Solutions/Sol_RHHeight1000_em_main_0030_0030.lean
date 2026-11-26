-- Prove2me | solution 1 for RHHeight1000.em_main_0030_0030
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T09:00:10.257201+00:00
-- url     : https://prove2.me/submissions/f3b2b261-d86e-4719-8954-daac53b72f56

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow30.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow30.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow30.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow30.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow30.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 62500000033171 16585500000000000000 4138529546116343 2251799813685248 62500000033171 16585500000000000000 963576 524288

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 265368 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 62500000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000530736 265368000000000000000 4138529546116343 2251799813685248 62500000033171 16585500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 265368 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 62500000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000530736 265368000000000000000 4138529546116343 2251799813685248 62500000033171 16585500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz272 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz272)

theorem EMRow30.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 265368 1200336 1048576 1 265368 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 265368 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 265368 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 265368 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 265368 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 265368 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 265368 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow30.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz546 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 99995 1000)))

noncomputable abbrev qz521 := qz546

noncomputable abbrev qz273 := qz521

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz547 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz522 := qz547

noncomputable abbrev qz274 := qz522

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz523 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz523

noncomputable abbrev qz524 := (@Neg.neg Complex Complex.instNeg qz546)

noncomputable abbrev qz276 := qz524

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 8) qz276)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 1650932987253 1099511627776 31322296379701 12157300068319232 Bool.true 48526812689 274877906944 15636317578935 6078650034159616

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 331905956047 274877906944 14018919788503 6078650034159616 Bool.false 10865375049 549755813888 6997845925519 3039325017079808 Bool.false

noncomputable abbrev qz7 := qz275

noncomputable abbrev qz8 := qz276

noncomputable abbrev qz277 := (@HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast 7) qz8)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz277) Bool.false 331905956047 274877906944 14018919788503 6078650034159616 Bool.false 10865375049 549755813888 6997845925519 3039325017079808

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz277 Bool.false 920135537913 1099511627776 73576613891431 36471900204957696 Bool.true 59861866627 1099511627776 73464522580915 36471900204957696 Bool.false

noncomputable def ep42 := nat_lit 1459737832007145921445888

noncomputable abbrev qz278 := (@HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast 6) qz8)

noncomputable def ep43 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz278) Bool.false 920135537913 1099511627776 73576613891431 36471900204957696 Bool.true 59861866627 1099511627776 73464522580915 36471900204957696

noncomputable def ep44 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz278 Bool.false 1366937001057 1099511627776 20732566250725 12157300068319232 Bool.true 102937744081 1099511627776 20705630447823 12157300068319232 Bool.true

noncomputable abbrev qz279 := (@HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast 5) qz8)

noncomputable def ep45 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz279) Bool.false 1366937001057 1099511627776 20732566250725 12157300068319232 Bool.true 102937744081 1099511627776 20705630447823 12157300068319232

noncomputable def ep46 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz279 Bool.false 1738443898441 1099511627776 49728817562215 36471900204957696 Bool.true 425066513239 1099511627776 49651502993467 36471900204957696 Bool.true

noncomputable abbrev qz280 := (@HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast 4) qz8)

noncomputable def ep47 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz280) Bool.false 1738443898441 1099511627776 49728817562215 36471900204957696 Bool.true 425066513239 1099511627776 49651502993467 36471900204957696

noncomputable def ep48 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz280 Bool.false 615229801353 549755813888 8946360630143 9117975051239424 Bool.true 53717735515 274877906944 8931742170443 9117975051239424 Bool.false

noncomputable abbrev qz525 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz281 := qz525

noncomputable abbrev qz9 := qz281

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz7 qz9 qz8)) Bool.false 615229801353 549755813888 8946360630143 9117975051239424 Bool.true 53717735515 274877906944 8931742170443 9117975051239424

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz7 qz9 qz8) Bool.false 1862086973451 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 1099511627776 6560085088455 12157300068319232 Bool.true

noncomputable def ep51 := nat_lit 1352904640683884314361856

noncomputable abbrev qz526 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz282 := qz526

noncomputable abbrev qz10 := qz282

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz7 qz10 qz8)) Bool.false 1862086973451 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 1099511627776 6560085088455 12157300068319232

noncomputable def ep53 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz7 qz10 qz8) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz283 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz11 := qz283

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz11) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz12 := (@Inv.inv Real Real.instInv (Real.sqrt qz284))

noncomputable abbrev qz548 := (Enclosure.sfrac Bool.false 99995 1000)

noncomputable abbrev qz527 := qz548

noncomputable abbrev qz285 := qz527

noncomputable abbrev qz286 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz13 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log qz286))

noncomputable abbrev qz14 := qz285

noncomputable abbrev qz287 := (@Eq.refl Real qz527)

noncomputable abbrev qz15 := qz287

noncomputable def ep55 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz7 qz10 qz8) (Complex.mk (@HMul.hMul Real Real Real qz0 qz12 (Real.cos qz13)) (@HMul.hMul Real Real Real qz0 qz12 (@Neg.neg Real Real.instNeg (Real.sin qz13)))) Bool.false 762575345675 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 1099511627776 6560085088455 12157300068319232 (BSN.cpow_neg_s_mk qz14 99995 1000 2 qz15 rfl)

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep56 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz284) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz284) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz16)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz16)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep57 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 132684 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep58 := nat_lit 31431558745104694503745582164010000

noncomputable def ep59 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep60 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz288 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz289 := (BSN.cosOddQ 2147483648)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 421057570 2147483648 2 1 1048576 265628 ep58 ep59 ep58 ep58 ep60 ep58 1028485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 421057570) qz288 0 1 ep58 ep59 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 421057570) qz289 0 1 ep58 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz18 := (Real.log qz286)

noncomputable abbrev qz19 := (Enclosure.Real.IsNear.const Bool.false 99995 1000)

noncomputable abbrev qz20 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz290 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72677965) qz17)

noncomputable abbrev qz291 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 132684 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 132684 rfl rfl rfl (ep57 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz13 qz290 Bool.false 72677965 1048576 99 131072 Bool.false 1028485 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz13 Bool.false 454237287 6553600 19999 26536800 72677965 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz18 99995 1000 0 1 363408 524288 1 132684 454237287 6553600 19999 26536800 qz19 qz291 rfl) rfl) (Enclosure.sfrac_false_div 72677965 1048576) (BSN.cos_reduce0 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29629292445539720232960) qz20) 226375608064910080 72057594037927936 Bool.false 1028485 1048576 11 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 72677965 1048576 226375608064910080 72057594037927936 11 29629292445539720232960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1028485 1048576 29629292445539720232960 151115727451828646838272 421057570 2147483648 265628 265368 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep64 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz292 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz293 := (BSN.sinOddQ 2147483648)

noncomputable def ep65 := BSN.sin_dyadic_bound_f 421057570 2147483648 2 1 1048576 265628 ep58 ep63 ep58 ep58 ep64 ep58 204279 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 421057570) qz292 0 1 ep58 ep63 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 421057570) qz293 0 1 ep58 ep64 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep66 := @Enclosure.Real.IsNear.sin_image qz13 qz290 Bool.false 72677965 1048576 99 131072 Bool.false 204279 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz13 Bool.false 454237287 6553600 19999 26536800 72677965 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz18 99995 1000 0 1 363408 524288 1 132684 454237287 6553600 19999 26536800 qz19 qz291 rfl) rfl) (Enclosure.sfrac_false_div 72677965 1048576) (BSN.sin_reduce0 qz290 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29629292445539720232960) qz20) 226375608064910080 72057594037927936 Bool.false 204279 1048576 11 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 72677965 1048576 226375608064910080 72057594037927936 11 29629292445539720232960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 204279 1048576 29629292445539720232960 151115727451828646838272 421057570 2147483648 265628 265368 (ep65 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep56 rfl rfl) rfl)

noncomputable def ep67 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz12 (Real.cos qz13)) (@HMul.hMul Real Real Real qz0 qz12 (@Neg.neg Real Real.instNeg (Real.sin qz13))) Bool.false 762575345675 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 1099511627776 6560085088455 12157300068319232 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.cos qz13) 741455 1048576 1 1048576 1028485 1048576 3316697 4347789312 762575345675 1099511627776 6569198334197 12157300068319232 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz13) Bool.false 1028485 1048576 13266788 17391157248 1028485 1048576 3316697 4347789312 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz12 (@Neg.neg Real Real.instNeg (Real.sin qz13)) 741455 1048576 1 1048576 204279 1048576 3316697 4347789312 151463685945 1099511627776 6560085088455 12157300068319232 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz13) Bool.false 204279 1048576 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' (Real.sin qz13) Bool.false 204279 1048576 13266788 17391157248 204279 1048576 3316697 4347789312 (ep66 rfl rfl) rfl)) rfl)

noncomputable abbrev qz295 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz295

noncomputable def ep68 := @ep53 762575345675 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 1099511627776 6560085088455 12157300068319232 Bool.false 1862086973451 1862086973451 1099511627776 6569198334197 12157300068319232 Bool.true 151463685945 151463685945 1099511627776 6560085088455 12157300068319232 (ep54 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz11 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep55 ep67) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep69 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz7 qz9 qz8) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 631627370745 1099511627776 16077847517981 36471900204957696 Bool.true 63407256115 1099511627776 16046713416407 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 3 qz15 rfl)

noncomputable def ep70 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz16)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz16)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep71 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 132684 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep72 := nat_lit 6409731802828591806083668951596874756253795097383734706914466692438088833105920

noncomputable def ep73 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep74 := nat_lit 9902259775832757625776439949299038831800324611338816257032015163866229047296

noncomputable def ep75 := nat_lit 16771360586818773122634542541883425917794167586634280434645551408024925430153216

noncomputable def ep76 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep77 := BSN.sin_dyadic_bound_f 3158397516 2147483648 3 2 1048576 265628 ep72 ep73 ep74 ep75 ep76 ep74 1043331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3158397516) qz292 0 2 ep72 ep73 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3158397516) qz293 0 2 ep75 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14399005) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 132684 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 132684 rfl rfl rfl (ep71 rfl)))

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz23 qz297 Bool.false 14399005 131072 791 1048576 Bool.true 1043331 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 11519204011 104857600 19999 26536800 14399005 131072 791 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz24 99995 1000 0 1 575989 524288 1 132684 11519204011 104857600 19999 26536800 qz19 qz298 rfl) rfl) (Enclosure.sfrac_false_div 14399005 131072) (BSN.cos_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27781558360600393809920) qz299) 226375608064910080 72057594037927936 Bool.false 1043331 1048576 17 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 14399005 131072 226375608064910080 72057594037927936 17 27781558360600393809920 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1043331 1048576 27781558360600393809920 18889465931478580854784 3158397516 2147483648 265628 265368 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 3565363117027365562324605613086841104066241865040447644400051280316212120190976

noncomputable def ep80 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep81 := nat_lit 10676284831530431171722263959361925234535124945898665300686089810620903902478336

noncomputable def ep82 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep83 := BSN.cos_dyadic_bound_f 3158397516 2147483648 3 2 1048576 265628 ep79 ep80 ep74 ep81 ep82 ep74 104737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3158397516) qz288 0 2 ep79 ep80 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3158397516) qz289 0 2 ep81 ep82 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep84 := @Enclosure.Real.IsNear.sin_image qz23 qz297 Bool.false 14399005 131072 791 1048576 Bool.false 104737 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 11519204011 104857600 19999 26536800 14399005 131072 791 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz24 99995 1000 0 1 575989 524288 1 132684 11519204011 104857600 19999 26536800 qz19 qz298 rfl) rfl) (Enclosure.sfrac_false_div 14399005 131072) (BSN.sin_reduce1 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27781558360600393809920) qz299) 226375608064910080 72057594037927936 Bool.false 104737 1048576 17 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 14399005 131072 226375608064910080 72057594037927936 17 27781558360600393809920 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 104737 1048576 27781558360600393809920 18889465931478580854784 3158397516 2147483648 265628 265368 (ep83 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep70 rfl rfl) rfl)

noncomputable def ep85 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 631627370745 1099511627776 16077847517981 36471900204957696 Bool.true 63407256115 1099511627776 16046713416407 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz23) 605395 1048576 1 1048576 1043331 1048576 26500405 34782314496 631627370745 1099511627776 16077847517981 36471900204957696 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 1043331 1048576 106001620 139129257984 1043331 1048576 26500405 34782314496 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 104737 1048576 26500405 34782314496 63407256115 1099511627776 16046713416407 36471900204957696 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 104737 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 104737 1048576 106001620 139129257984 104737 1048576 26500405 34782314496 (ep84 rfl rfl) rfl)) rfl)

noncomputable def ep86 := @ep50 631627370745 1099511627776 16077847517981 36471900204957696 Bool.true 63407256115 1099511627776 16046713416407 36471900204957696 Bool.false ep51 615229801353 549755813888 8946360630143 9117975051239424 Bool.true 236253099266153182658560 53717735515 274877906944 8931742170443 9117975051239424 (ep52 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep68 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep69 ep85) rfl rfl

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz301))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep87 := @Enclosure.Complex.IsNear.of_eq qz280 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 507984295735 1099511627776 13943375041643 36471900204957696 Bool.true 210195571179 1099511627776 13924534311695 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 4 qz15 rfl)

noncomputable def ep88 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz301) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz301) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz16)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz16)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep89 := nat_lit 318077276165597140789031982421875

noncomputable def ep90 := nat_lit 49379992292270016474244603430625

noncomputable def ep91 := nat_lit 20095619060363156210525625

noncomputable def ep92 := BSN.log_dyadic_bound 3 5 14 13 ep89 524288 132684 ep90 ep91 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep90 ep89 ep91 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep93 := nat_lit 503888993751966306973519262678139136

noncomputable def ep94 := BSN.cos_dyadic_bound_f 842526788 2147483648 2 1 1048576 265628 ep93 ep59 ep93 ep93 ep60 ep93 968905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 842526788) qz288 0 1 ep93 ep59 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 842526788) qz289 0 1 ep93 ep60 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145356131) qz17)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 132684 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 132684 rfl rfl rfl (ep92 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz26 qz302 Bool.false 145356131 1048576 99 131072 Bool.false 968905 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 14535613183 104857600 19999 26536800 145356131 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz27 99995 1000 0 1 726817 524288 1 132684 14535613183 104857600 19999 26536800 qz19 qz303 rfl) rfl) (Enclosure.sfrac_false_div 145356131 1048576) (BSN.cos_reduce0 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59287552043882687496192) qz20) 226375608064910080 72057594037927936 Bool.false 968905 1048576 22 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145356131 1048576 226375608064910080 72057594037927936 22 59287552043882687496192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968905 1048576 59287552043882687496192 151115727451828646838272 842526788 2147483648 265628 265368 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := BSN.sin_dyadic_bound_f 842526788 2147483648 2 1 1048576 265628 ep93 ep63 ep93 ep93 ep64 ep93 400917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 842526788) qz292 0 1 ep93 ep63 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 842526788) qz293 0 1 ep93 ep64 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable def ep97 := @Enclosure.Real.IsNear.sin_image qz26 qz302 Bool.false 145356131 1048576 99 131072 Bool.false 400917 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 14535613183 104857600 19999 26536800 145356131 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz27 99995 1000 0 1 726817 524288 1 132684 14535613183 104857600 19999 26536800 qz19 qz303 rfl) rfl) (Enclosure.sfrac_false_div 145356131 1048576) (BSN.sin_reduce0 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59287552043882687496192) qz20) 226375608064910080 72057594037927936 Bool.false 400917 1048576 22 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145356131 1048576 226375608064910080 72057594037927936 22 59287552043882687496192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400917 1048576 59287552043882687496192 151115727451828646838272 842526788 2147483648 265628 265368 (ep96 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep88 rfl rfl) rfl)

noncomputable def ep98 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 507984295735 1099511627776 13943375041643 36471900204957696 Bool.true 210195571179 1099511627776 13924534311695 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 524287 1048576 1 1048576 968905 1048576 3316697 4347789312 507984295735 1099511627776 13943375041643 36471900204957696 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 968905 1048576 13266788 17391157248 968905 1048576 3316697 4347789312 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 400917 1048576 3316697 4347789312 210195571179 1099511627776 13924534311695 36471900204957696 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 400917 1048576 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 400917 1048576 13266788 17391157248 400917 1048576 3316697 4347789312 (ep97 rfl rfl) rfl)) rfl)

noncomputable def ep99 := @ep48 507984295735 1099511627776 13943375041643 36471900204957696 Bool.true 210195571179 1099511627776 13924534311695 36471900204957696 Bool.false 955719640286059569348608 1738443898441 1099511627776 49728817562215 36471900204957696 Bool.true 116841393471120386031616 425066513239 1099511627776 49651502993467 36471900204957696 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep86 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep87 ep98) rfl rfl

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz305))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz285 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep100 := @Enclosure.Complex.IsNear.of_eq qz279 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 46438362173 137438953472 1558610148745 4558987525619712 Bool.false 161064384579 549755813888 6232694175001 18235950102478848 (BSN.cpow_neg_s_mk qz14 99995 1000 5 qz15 rfl)

noncomputable def ep101 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz305) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz305) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz305 qz16)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz305 qz16)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep102 := nat_lit 11734546589655452485523914939250625

noncomputable def ep103 := nat_lit 2429970938528035899633153341031900

noncomputable def ep104 := nat_lit 824199001261152424427520000

noncomputable def ep105 := BSN.log_dyadic_bound 2 3 17 16 ep102 524288 132684 ep103 ep104 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep103 ep102 ep104 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep106 := nat_lit 197884315051888319513900798529481888171960023827031692303609815330368749445376

noncomputable def ep107 := nat_lit 30664130109941367960215281206583524118460418843550092749854831168495165696

noncomputable def ep108 := nat_lit 593591616895445075805781965026032497467643150643407976725329736328769258004736

noncomputable def ep109 := BSN.cos_dyadic_bound_f 1534012262 2147483648 3 2 1048576 265628 ep106 ep80 ep107 ep108 ep82 ep107 792232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1534012262) qz288 0 2 ep106 ep80 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1534012262) qz289 0 2 ep108 ep82 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168753161) qz17)

noncomputable abbrev qz307 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 132684 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 132684 rfl rfl rfl (ep105 rfl)))

noncomputable def ep110 := @Enclosure.Real.IsNear.cos_image qz29 qz306 Bool.false 168753161 1048576 99 131072 Bool.true 792232 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 527353631 3276800 19999 26536800 168753161 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz30 99995 1000 0 1 843808 524288 1 132684 527353631 3276800 19999 26536800 qz19 qz307 rfl) rfl) (Enclosure.sfrac_false_div 168753161 1048576) (BSN.cos_reduce2 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107946516478528671711232) qz20) 226375608064910080 72057594037927936 Bool.false 792232 1048576 25 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 168753161 1048576 226375608064910080 72057594037927936 25 107946516478528671711232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 792232 1048576 107946516478528671711232 151115727451828646838272 1534012262 2147483648 265628 265368 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep111 := nat_lit 5537520213050365738611954435402942736

noncomputable def ep112 := BSN.sin_dyadic_bound_f 1534012262 2147483648 2 1 1048576 265628 ep111 ep63 ep111 ep111 ep64 ep111 686934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1534012262) qz292 0 1 ep111 ep63 ep111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1534012262) qz293 0 1 ep111 ep64 ep111 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz29 qz306 Bool.false 168753161 1048576 99 131072 Bool.true 686934 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 527353631 3276800 19999 26536800 168753161 1048576 99 131072 (@Enclosure.Real.IsNear.mulLit_ff qz14 qz30 99995 1000 0 1 843808 524288 1 132684 527353631 3276800 19999 26536800 qz19 qz307 rfl) rfl) (Enclosure.sfrac_false_div 168753161 1048576) (BSN.sin_reduce2 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107946516478528671711232) qz20) 226375608064910080 72057594037927936 Bool.false 686934 1048576 25 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 168753161 1048576 226375608064910080 72057594037927936 25 107946516478528671711232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 686934 1048576 107946516478528671711232 151115727451828646838272 1534012262 2147483648 265628 265368 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz308 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep101 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 46438362173 137438953472 1558610148745 4558987525619712 Bool.false 161064384579 549755813888 6232694175001 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz29) 468937 1048576 1 1048576 99029 131072 3316697 4347789312 46438362173 137438953472 1558610148745 4558987525619712 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 792232 1048576 13266788 17391157248 99029 131072 3316697 4347789312 (ep110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 343467 524288 3316697 4347789312 161064384579 549755813888 6232694175001 18235950102478848 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 343467 524288 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 686934 1048576 13266788 17391157248 343467 524288 3316697 4347789312 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep46 46438362173 137438953472 1558610148745 4558987525619712 Bool.false 161064384579 549755813888 6232694175001 18235950102478848 Bool.false 187870390887428237819904 1366937001057 1099511627776 20732566250725 12157300068319232 Bool.true 56590623277044809596928 102937744081 1099511627776 20705630447823 12157300068319232 (ep47 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep99 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep100 ep114) rfl rfl

noncomputable abbrev qz309 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz31 := (@Inv.inv Real Real.instInv (Real.sqrt qz309))

noncomputable abbrev qz310 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz268 qz285 qz310)

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq qz278 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 55850182893 137438953472 1422364392407 4558987525619712 Bool.false 21537938727 549755813888 5673815618723 18235950102478848 (BSN.cpow_neg_s_mk qz14 99995 1000 6 qz15 rfl)

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz16)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz309) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz309) (Real.sqrt qz311) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz311) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 132684 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep119 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz310 99995 1000 0 1 4034681531866359 2251799813685248 125000000033171 16585500000000000000 80689595955795313641 450359962737049600 2499875000663386829 3317100000000000000000 qz19 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 33845361775666394038272 18889465931478580854784 1000000000265368 132684000000000000000 4034681531866359 2251799813685248 125000000033171 16585500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep120 := nat_lit 1814858006969459208606837798775441

noncomputable def ep121 := BSN.cos_dyadic_bound_f 206400461 2147483648 2 1 1048576 265628 ep120 ep59 ep120 ep120 ep60 ep120 1043736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 206400461) qz288 0 1 ep120 ep59 ep120 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 206400461) qz289 0 1 ep120 ep60 ep120 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187870105) qz17)

noncomputable def ep122 := @Enclosure.Real.IsNear.cos_image qz32 qz312 Bool.false 187870105 1048576 791 1048576 Bool.true 1043736 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 80689595955795313641 450359962737049600 2499875000663386829 3317100000000000000000 187870105 1048576 791 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 187870105 1048576) (BSN.cos_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14524141246879304253440) qz20) 226375608064910080 72057594037927936 Bool.false 1043736 1048576 28 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 187870105 1048576 226375608064910080 72057594037927936 28 14524141246879304253440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043736 1048576 14524141246879304253440 151115727451828646838272 206400461 2147483648 265628 265368 (ep121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep123 := BSN.sin_dyadic_bound_f 206400461 2147483648 1 0 1048576 265628 0 1 1 0 1 1 100626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 206400461) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 206400461) qz293 0 0 rfl) rfl rfl

noncomputable def ep124 := @Enclosure.Real.IsNear.sin_image qz32 qz312 Bool.false 187870105 1048576 791 1048576 Bool.true 100626 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 80689595955795313641 450359962737049600 2499875000663386829 3317100000000000000000 187870105 1048576 791 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 187870105 1048576) (BSN.sin_reduce2 qz312 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14524141246879304253440) qz20) 226375608064910080 72057594037927936 Bool.false 100626 1048576 28 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 187870105 1048576 226375608064910080 72057594037927936 28 14524141246879304253440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 100626 1048576 14524141246879304253440 151115727451828646838272 206400461 2147483648 265628 265368 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz313 := (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep117 rfl rfl) rfl)

noncomputable def ep125 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 55850182893 137438953472 1422364392407 4558987525619712 Bool.false 21537938727 549755813888 5673815618723 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ft qz31 (Real.cos qz32) 428079 1048576 1 1048576 130467 131072 26500405 34782314496 55850182893 137438953472 1422364392407 4558987525619712 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 1043736 1048576 106001620 139129257984 130467 131072 26500405 34782314496 (ep122 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz31 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 428079 1048576 1 1048576 50313 524288 26500405 34782314496 21537938727 549755813888 5673815618723 18235950102478848 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 50313 524288 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 100626 1048576 106001620 139129257984 50313 524288 26500405 34782314496 (ep124 rfl rfl) rfl)) rfl)

noncomputable def ep126 := @ep44 55850182893 137438953472 1422364392407 4558987525619712 Bool.false 21537938727 549755813888 5673815618723 18235950102478848 Bool.false 126462465383158498983936 920135537913 1099511627776 73576613891431 36471900204957696 Bool.true 32909409208381290315776 59861866627 1099511627776 73464522580915 36471900204957696 (ep45 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep125) rfl rfl

noncomputable abbrev qz314 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz314))

noncomputable abbrev qz315 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz268 qz285 qz315)

noncomputable def ep127 := @Enclosure.Complex.IsNear.of_eq qz277 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 407488286275 1099511627776 10536904839587 36471900204957696 Bool.false 81592616725 1099511627776 10509628525313 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 7 qz15 rfl)

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz16)

noncomputable def ep128 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz314) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz314) (Real.sqrt qz316) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz316) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep129 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 132684 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep130 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz315 99995 1000 0 1 4381796493761783 2251799813685248 125000000033171 16585500000000000000 87631548078741898217 450359962737049600 2499875000663386829 3317100000000000000000 qz19 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 125000000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 36757173121942042968064 18889465931478580854784 1000000000265368 132684000000000000000 4381796493761783 2251799813685248 125000000033171 16585500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep131 := nat_lit 4868957669086194840032399564169294447944111499651016845540462436945412569386945

noncomputable def ep132 := nat_lit 5718061689581162077495315903939061733651801479906495864197169944428703862721

noncomputable def ep133 := nat_lit 12742774176299759842435577870884631739903903391928052649778225250185100732616641

noncomputable def ep134 := BSN.sin_dyadic_bound_f 2948873241 2147483648 3 2 1048576 265628 ep131 ep73 ep132 ep133 ep76 ep132 1028167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2948873241) qz292 0 2 ep131 ep73 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2948873241) qz293 0 2 ep133 ep76 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204033097) qz17)

noncomputable def ep135 := @Enclosure.Real.IsNear.cos_image qz34 qz317 Bool.false 204033097 1048576 791 1048576 Bool.false 1028167 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 87631548078741898217 450359962737049600 2499875000663386829 3317100000000000000000 204033097 1048576 791 1048576 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 204033097 1048576) (BSN.cos_reduce3 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207508506774992788127744) qz20) 226375608064910080 72057594037927936 Bool.false 1028167 1048576 30 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 204033097 1048576 226375608064910080 72057594037927936 30 207508506774992788127744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1028167 1048576 207508506774992788127744 151115727451828646838272 2948873241 2147483648 265628 265368 (ep134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep136 := nat_lit 2707517843576588760941331009384692054072796078241634467906566762722753073598401

noncomputable def ep137 := nat_lit 8111117407350603958669002396346198038751084631765090411991305948279401813069761

noncomputable def ep138 := BSN.cos_dyadic_bound_f 2948873241 2147483648 3 2 1048576 265628 ep136 ep80 ep132 ep137 ep82 ep132 205873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2948873241) qz288 0 2 ep136 ep80 ep132 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2948873241) qz289 0 2 ep137 ep82 ep132 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz34 qz317 Bool.false 204033097 1048576 791 1048576 Bool.true 205873 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 87631548078741898217 450359962737049600 2499875000663386829 3317100000000000000000 204033097 1048576 791 1048576 (ep130 rfl) rfl) (Enclosure.sfrac_false_div 204033097 1048576) (BSN.sin_reduce3 qz317 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207508506774992788127744) qz20) 226375608064910080 72057594037927936 Bool.false 205873 1048576 30 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 204033097 1048576 226375608064910080 72057594037927936 30 207508506774992788127744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 205873 1048576 207508506774992788127744 151115727451828646838272 2948873241 2147483648 265628 265368 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz318 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep128 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 407488286275 1099511627776 10536904839587 36471900204957696 Bool.false 81592616725 1099511627776 10509628525313 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 396325 1048576 1 1048576 1028167 1048576 26500405 34782314496 407488286275 1099511627776 10536904839587 36471900204957696 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 1028167 1048576 106001620 139129257984 1028167 1048576 26500405 34782314496 (ep135 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 396325 1048576 1 1048576 205873 1048576 26500405 34782314496 81592616725 1099511627776 10509628525313 36471900204957696 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 205873 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 205873 1048576 106001620 139129257984 205873 1048576 26500405 34782314496 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep41 407488286275 1099511627776 10536904839587 36471900204957696 Bool.false 81592616725 1099511627776 10509628525313 36471900204957696 Bool.false ep42 331905956047 274877906944 14018919788503 6078650034159616 Bool.false 23893212413045451522048 10865375049 549755813888 6997845925519 3039325017079808 (ep43 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep126 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep127 ep140) rfl rfl

noncomputable abbrev qz319 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt qz319))

noncomputable abbrev qz320 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz268 qz285 qz320)

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.false 323309163065 1099511627776 3284456802695 12157300068319232 Bool.true 107919000427 549755813888 1640625727897 6078650034159616 (BSN.cpow_neg_s_mk qz14 99995 1000 8 qz15 rfl)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz16)

noncomputable def ep143 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz319) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz319) (Real.sqrt qz321) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz321) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep144 := BSN.log_dyadic_bound 0 16 1 0 1 524288 132684 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz320 99995 1000 0 1 9364972152248037 4503599627370496 250000000099513 33171000000000000000 187290078072808491963 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 39279540158062550581248 18889465931478580854784 1000000000398052 132684000000000000000 9364972152248037 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep146 := nat_lit 2553427520094606397600749274109978896

noncomputable def ep147 := BSN.cos_dyadic_bound_f 1264098406 2147483648 2 1 1048576 265628 ep146 ep59 ep146 ep146 ep60 ep146 872095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1264098406) qz288 0 1 ep146 ep59 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1264098406) qz289 0 1 ep146 ep60 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 218034347) qz17)

noncomputable def ep148 := @Enclosure.Real.IsNear.cos_image qz36 qz322 Bool.false 218034347 1048576 791 1048576 Bool.false 872095 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 187290078072808491963 900719925474099200 4999750001990160487 6634200000000000000000 218034347 1048576 791 1048576 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 218034347 1048576) (BSN.cos_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88953017401629447553024) qz20) 226375608064910080 72057594037927936 Bool.false 872095 1048576 33 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 218034347 1048576 226375608064910080 72057594037927936 33 88953017401629447553024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 872095 1048576 88953017401629447553024 151115727451828646838272 1264098406 2147483648 265628 265368 (ep147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep149 := BSN.sin_dyadic_bound_f 1264098406 2147483648 2 1 1048576 265628 ep146 ep63 ep146 ep146 ep64 ep146 582202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1264098406) qz292 0 1 ep146 ep63 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1264098406) qz293 0 1 ep146 ep64 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep150 := @Enclosure.Real.IsNear.sin_image qz36 qz322 Bool.false 218034347 1048576 791 1048576 Bool.false 582202 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 187290078072808491963 900719925474099200 4999750001990160487 6634200000000000000000 218034347 1048576 791 1048576 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 218034347 1048576) (BSN.sin_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88953017401629447553024) qz20) 226375608064910080 72057594037927936 Bool.false 582202 1048576 33 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 218034347 1048576 226375608064910080 72057594037927936 33 88953017401629447553024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582202 1048576 88953017401629447553024 151115727451828646838272 1264098406 2147483648 265628 265368 (ep149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep143 rfl rfl) rfl)

noncomputable def ep151 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.false 323309163065 1099511627776 3284456802695 12157300068319232 Bool.true 107919000427 549755813888 1640625727897 6078650034159616 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz36) 370727 1048576 1 1048576 872095 1048576 26500405 34782314496 323309163065 1099511627776 3284456802695 12157300068319232 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.false 872095 1048576 106001620 139129257984 872095 1048576 26500405 34782314496 (ep148 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 370727 1048576 1 1048576 291101 524288 26500405 34782314496 107919000427 549755813888 1640625727897 6078650034159616 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.false 291101 524288 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.false 582202 1048576 106001620 139129257984 291101 524288 26500405 34782314496 (ep150 rfl rfl) rfl)) rfl)

noncomputable def ep152 := @ep39 323309163065 1099511627776 3284456802695 12157300068319232 Bool.true 107919000427 549755813888 1640625727897 6078650034159616 Bool.false 453805004040910072184832 1650932987253 1099511627776 31322296379701 12157300068319232 Bool.true 53355794810463441649664 48526812689 274877906944 15636317578935 6078650034159616 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep142 ep151) rfl rfl

theorem EMRow30.d6 : Enclosure.Complex.IsNear qz3 Bool.false 1650932987253 1099511627776 31322296379701 12157300068319232 Bool.true 48526812689 274877906944 15636317578935 6078650034159616 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep152 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz37 := (BSN.headSumC qz273 17)

noncomputable abbrev qz38 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz276)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq qz37 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz38) Bool.false 2518279435067 1099511627776 157890328120193 36471900204957696 Bool.true 118881239681 1099511627776 157681713113855 36471900204957696

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz38 Bool.false 580951703879 274877906944 75455051117351 18235950102478848 Bool.false 18845023153 274877906944 75350756982095 18235950102478848 Bool.false

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz276)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz39) Bool.false 580951703879 274877906944 75455051117351 18235950102478848 Bool.false 18845023153 274877906944 75350756982095 18235950102478848

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz39 Bool.false 522955191305 274877906944 5987787783909 1519662508539904 Bool.false 119508788729 549755813888 23917782093709 6078650034159616 Bool.false

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz276)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz40) Bool.false 522955191305 274877906944 5987787783909 1519662508539904 Bool.false 119508788729 549755813888 23917782093709 6078650034159616

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz40 Bool.false 898982620869 549755813888 68122772533421 18235950102478848 Bool.false 238604779519 1099511627776 136080064202551 36471900204957696 Bool.false

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz276)

noncomputable def ep159 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz41) Bool.false 898982620869 549755813888 68122772533421 18235950102478848 Bool.false 238604779519 1099511627776 136080064202551 36471900204957696

noncomputable def ep160 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz41 Bool.false 833743460571 549755813888 21420618174605 6078650034159616 Bool.true 4627658077 137438953472 10695139397453 3039325017079808 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz276)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz42) Bool.false 833743460571 549755813888 21420618174605 6078650034159616 Bool.true 4627658077 137438953472 10695139397453 3039325017079808

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz42 Bool.false 1971422254569 1099511627776 120468782752379 36471900204957696 Bool.true 128489941379 1099511627776 120310029597137 36471900204957696 Bool.true

noncomputable def ep163 := nat_lit 1833421258960030968840192

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz276)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz43) Bool.false 1971422254569 1099511627776 120468782752379 36471900204957696 Bool.true 128489941379 1099511627776 120310029597137 36471900204957696

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz43 Bool.false 1796904855197 1099511627776 112072157449073 36471900204957696 Bool.false 76685331709 549755813888 13987767738757 4558987525619712 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz276)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz44) Bool.false 1796904855197 1099511627776 112072157449073 36471900204957696 Bool.false 76685331709 549755813888 13987767738757 4558987525619712

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz44 Bool.false 1005063099139 549755813888 25815889560041 9117975051239424 Bool.true 15159153907 137438953472 25771849551155 9117975051239424 Bool.true

noncomputable abbrev qz324 := (@HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast 9) qz8)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz324) Bool.false 1005063099139 549755813888 25815889560041 9117975051239424 Bool.true 15159153907 137438953472 25771849551155 9117975051239424

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP qz3 qz324 Bool.false 1650932987253 1099511627776 31322296379701 12157300068319232 Bool.true 48526812689 274877906944 15636317578935 6078650034159616 Bool.false

noncomputable def ep170 := nat_lit 2210157128303826308169728

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz325))

noncomputable abbrev qz326 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz268 qz285 qz326)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq qz324 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.false 359193211025 1099511627776 9296669101061 36471900204957696 Bool.false 18208504875 274877906944 4634746365505 18235950102478848 (BSN.cpow_neg_s_mk qz14 99995 1000 9 qz15 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz16)

noncomputable def ep172 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz325) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz325) (Real.sqrt qz327) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep173 := BSN.log_dyadic_bound 1 17 2 1 867 524288 132684 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep174 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz326 99995 1000 0 1 9895417793173221 4503599627370496 250000000099513 33171000000000000000 197898460445671246779 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 41504390431577613533184 18889465931478580854784 1000000000398052 132684000000000000000 9895417793173221 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep175 := nat_lit 4834419857360376028867127779093146397021577759133671848238188091529194584590145

noncomputable def ep176 := nat_lit 5637321407430835819286174253175333654832167498322961707426274774148162701121

noncomputable def ep177 := nat_lit 12652448725093715865230299901215004309139165859876617664526088175799269743839041

noncomputable def ep178 := BSN.sin_dyadic_bound_f 2943635959 2147483648 3 2 1048576 265628 ep175 ep73 ep176 ep177 ep76 ep176 1027661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2943635959) qz292 0 2 ep175 ep73 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2943635959) qz293 0 2 ep177 ep76 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230384129) qz17)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image qz46 qz328 Bool.false 230384129 1048576 791 1048576 Bool.false 1027661 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 197898460445671246779 900719925474099200 4999750001990160487 6634200000000000000000 230384129 1048576 791 1048576 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 230384129 1048576) (BSN.cos_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207139965811550865850368) qz20) 226375608064910080 72057594037927936 Bool.false 1027661 1048576 34 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 230384129 1048576 226375608064910080 72057594037927936 34 207139965811550865850368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1027661 1048576 207139965811550865850368 151115727451828646838272 2943635959 2147483648 265628 265368 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep180 := nat_lit 2688294285825733720845864843608714813303024162851294565335627284082507285972801

noncomputable def ep181 := nat_lit 8053608214662339490899022182319793772599408153557237772592029302699225532516161

noncomputable def ep182 := BSN.cos_dyadic_bound_f 2943635959 2147483648 3 2 1048576 265628 ep180 ep80 ep176 ep181 ep82 ep176 208380 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2943635959) qz288 0 2 ep180 ep80 ep176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2943635959) qz289 0 2 ep181 ep82 ep176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep183 := @Enclosure.Real.IsNear.sin_image qz46 qz328 Bool.false 230384129 1048576 791 1048576 Bool.true 208380 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 197898460445671246779 900719925474099200 4999750001990160487 6634200000000000000000 230384129 1048576 791 1048576 (ep174 rfl) rfl) (Enclosure.sfrac_false_div 230384129 1048576) (BSN.sin_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207139965811550865850368) qz20) 226375608064910080 72057594037927936 Bool.false 208380 1048576 34 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 230384129 1048576 226375608064910080 72057594037927936 34 207139965811550865850368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 208380 1048576 207139965811550865850368 151115727451828646838272 2943635959 2147483648 265628 265368 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep172 rfl rfl) rfl)

noncomputable def ep184 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.false 359193211025 1099511627776 9296669101061 36471900204957696 Bool.false 18208504875 274877906944 4634746365505 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz46) 349525 1048576 1 1048576 1027661 1048576 26500405 34782314496 359193211025 1099511627776 9296669101061 36471900204957696 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.false 1027661 1048576 106001620 139129257984 1027661 1048576 26500405 34782314496 (ep179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 349525 1048576 1 1048576 52095 262144 26500405 34782314496 18208504875 274877906944 4634746365505 18235950102478848 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.true 52095 262144 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.true 208380 1048576 106001620 139129257984 52095 262144 26500405 34782314496 (ep183 rfl rfl) rfl)) rfl)

noncomputable def ep185 := @ep169 359193211025 1099511627776 9296669101061 36471900204957696 Bool.false 18208504875 274877906944 4634746365505 18235950102478848 Bool.false ep170 1005063099139 549755813888 25815889560041 9117975051239424 Bool.true 8333832993996240060416 15159153907 137438953472 25771849551155 9117975051239424 EMRow30.d6 (ep171 ep184) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz331 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz268 qz285 qz331)

noncomputable def ep186 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)))) Bool.true 213221343081 1099511627776 2936199736303 12157300068319232 Bool.false 137321947337 549755813888 734561975453 3039325017079808 (BSN.cpow_neg_s_mk qz14 99995 1000 10 qz15 rfl)

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz16)

noncomputable def ep187 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz332) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz332) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep188 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 132684 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep189 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz331 99995 1000 0 1 10369917190100709 4503599627370496 250000000099513 33171000000000000000 207387973884824079291 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 43494585150108164161536 18889465931478580854784 1000000000398052 132684000000000000000 10369917190100709 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep190 := nat_lit 522771946055104902198918468958901754998151236584797783325867420263959756800000

noncomputable def ep191 := nat_lit 213900396456072958457763137234160692888323582191947115800067840409600000000

noncomputable def ep192 := nat_lit 1567888037372402560679839880602236943608677062590009455746002125111060070400000

noncomputable def ep193 := BSN.cos_dyadic_bound_f 1955583880 2147483648 3 2 1048576 265628 ep190 ep80 ep191 ep192 ep82 ep191 643029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1955583880) qz288 0 2 ep190 ep80 ep191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1955583880) qz289 0 2 ep192 ep82 ep191 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 241431377) qz17)

noncomputable def ep194 := @Enclosure.Real.IsNear.cos_image qz48 qz333 Bool.false 241431377 1048576 791 1048576 Bool.true 643029 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 207387973884824079291 900719925474099200 4999750001990160487 6634200000000000000000 241431377 1048576 791 1048576 (ep189 rfl) rfl) (Enclosure.sfrac_false_div 241431377 1048576) (BSN.cos_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137611981836275431768064) qz20) 226375608064910080 72057594037927936 Bool.false 643029 1048576 36 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 241431377 1048576 226375608064910080 72057594037927936 36 137611981836275431768064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 643029 1048576 137611981836275431768064 151115727451828646838272 1955583880 2147483648 265628 265368 (ep193 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep195 := nat_lit 940818382582023965591287033616235830442361566986882452293921302202799882240000

noncomputable def ep196 := nat_lit 2463701829930086267949201090582238533846270627737333746391831872122860339200000

noncomputable def ep197 := BSN.sin_dyadic_bound_f 1955583880 2147483648 3 2 1048576 265628 ep195 ep73 ep191 ep196 ep76 ep191 828266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1955583880) qz292 0 2 ep195 ep73 ep191 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1955583880) qz293 0 2 ep196 ep76 ep191 rfl rfl rfl rfl) rfl rfl

noncomputable def ep198 := @Enclosure.Real.IsNear.sin_image qz48 qz333 Bool.false 241431377 1048576 791 1048576 Bool.true 828266 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 207387973884824079291 900719925474099200 4999750001990160487 6634200000000000000000 241431377 1048576 791 1048576 (ep189 rfl) rfl) (Enclosure.sfrac_false_div 241431377 1048576) (BSN.sin_reduce2 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137611981836275431768064) qz20) 226375608064910080 72057594037927936 Bool.false 828266 1048576 36 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 241431377 1048576 226375608064910080 72057594037927936 36 137611981836275431768064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 828266 1048576 137611981836275431768064 151115727451828646838272 1955583880 2147483648 265628 265368 (ep197 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep187 rfl rfl) rfl)

noncomputable def ep199 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48))) Bool.true 213221343081 1099511627776 2936199736303 12157300068319232 Bool.false 137321947337 549755813888 734561975453 3039325017079808 (@Enclosure.Real.IsNear.mulLit_ft qz47 (Real.cos qz48) 331589 1048576 1 1048576 643029 1048576 26500405 34782314496 213221343081 1099511627776 2936199736303 12157300068319232 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz48) Bool.true 643029 1048576 106001620 139129257984 643029 1048576 26500405 34782314496 (ep194 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)) 331589 1048576 1 1048576 414133 524288 26500405 34782314496 137321947337 549755813888 734561975453 3039325017079808 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz48) Bool.true 414133 524288 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz48) Bool.true 828266 1048576 106001620 139129257984 414133 524288 26500405 34782314496 (ep198 rfl rfl) rfl)) rfl)

noncomputable def ep200 := @ep167 213221343081 1099511627776 2936199736303 12157300068319232 Bool.false 137321947337 549755813888 734561975453 3039325017079808 Bool.false 987858891148125521575936 1796904855197 1099511627776 112072157449073 36471900204957696 Bool.false 10539551736738137243648 76685331709 549755813888 13987767738757 4558987525619712 (ep168 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep185 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep186 ep199) rfl rfl

noncomputable abbrev qz335 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz335))

noncomputable abbrev qz336 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz268 qz285 qz336)

noncomputable def ep201 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 43629349843 274877906944 1399437550551 6078650034159616 Bool.true 281860604797 1099511627776 2802629229027 12157300068319232 (BSN.cpow_neg_s_mk qz14 99995 1000 11 qz15 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz16)

noncomputable def ep202 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz335) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz335) (Real.sqrt qz337) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep203 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 132684 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep204 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz336 99995 1000 0 1 10799156221662949 4503599627370496 250000000099513 33171000000000000000 215972325277037317051 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 45294944137145793642496 18889465931478580854784 1000000000398052 132684000000000000000 10799156221662949 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep205 := nat_lit 811508253899012185520298137242061022568204213139343712005168840063892712390656

noncomputable def ep206 := nat_lit 515201097797425861477647637830328610713168102504974273097237187351795531776

noncomputable def ep207 := nat_lit 2433494359501441704837939116450522410483186303213021187469312045816974546108416

noncomputable def ep208 := BSN.cos_dyadic_bound_f 2182715324 2147483648 3 2 1048576 265628 ep205 ep80 ep206 ep207 ep82 ep206 551996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2182715324) qz288 0 2 ep205 ep80 ep206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2182715324) qz289 0 2 ep207 ep82 ep206 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 251424877) qz17)

noncomputable def ep209 := @Enclosure.Real.IsNear.cos_image qz50 qz338 Bool.false 251424877 1048576 791 1048576 Bool.false 551996 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 215972325277037317051 900719925474099200 4999750001990160487 6634200000000000000000 251424877 1048576 791 1048576 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 251424877 1048576) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153594936258714176323584) qz20) 226375608064910080 72057594037927936 Bool.false 551996 1048576 38 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 251424877 1048576 226375608064910080 72057594037927936 38 153594936258714176323584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 551996 1048576 153594936258714176323584 151115727451828646838272 2182715324 2147483648 265628 265368 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep210 := nat_lit 1460302696139983993247354528925445577734197049168814702190826122365125445877760

noncomputable def ep211 := nat_lit 3823768164303524149967345670057775028696028094704744737867149079319616117866496

noncomputable def ep212 := BSN.sin_dyadic_bound_f 2182715324 2147483648 3 2 1048576 265628 ep210 ep73 ep206 ep211 ep76 ep206 891521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2182715324) qz292 0 2 ep210 ep73 ep206 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2182715324) qz293 0 2 ep211 ep76 ep206 rfl rfl rfl rfl) rfl rfl

noncomputable def ep213 := @Enclosure.Real.IsNear.sin_image qz50 qz338 Bool.false 251424877 1048576 791 1048576 Bool.false 891521 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 215972325277037317051 900719925474099200 4999750001990160487 6634200000000000000000 251424877 1048576 791 1048576 (ep204 rfl) rfl) (Enclosure.sfrac_false_div 251424877 1048576) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153594936258714176323584) qz20) 226375608064910080 72057594037927936 Bool.false 891521 1048576 38 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 251424877 1048576 226375608064910080 72057594037927936 38 153594936258714176323584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 891521 1048576 153594936258714176323584 151115727451828646838272 2182715324 2147483648 265628 265368 (ep212 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep202 rfl rfl) rfl)

noncomputable def ep214 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 43629349843 274877906944 1399437550551 6078650034159616 Bool.true 281860604797 1099511627776 2802629229027 12157300068319232 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 316157 1048576 1 1048576 137999 262144 26500405 34782314496 43629349843 274877906944 1399437550551 6078650034159616 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 551996 1048576 106001620 139129257984 137999 262144 26500405 34782314496 (ep209 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 316157 1048576 1 1048576 891521 1048576 26500405 34782314496 281860604797 1099511627776 2802629229027 12157300068319232 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 891521 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 891521 1048576 106001620 139129257984 891521 1048576 26500405 34782314496 (ep213 rfl rfl) rfl)) rfl)

noncomputable def ep215 := @ep165 43629349843 274877906944 1399437550551 6078650034159616 Bool.true 281860604797 1099511627776 2802629229027 12157300068319232 Bool.false 541900423038748260827136 1971422254569 1099511627776 120468782752379 36471900204957696 Bool.true 70638092299233554071552 128489941379 1099511627776 120310029597137 36471900204957696 (ep166 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep200 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep201 ep214) rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz341 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz268 qz285 qz341)

noncomputable def ep216 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 303935333427 1099511627776 8054926295251 36471900204957696 Bool.false 91468676763 1099511627776 8031643172299 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 12 qz15 rfl)

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz16)

noncomputable def ep217 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz342) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz342) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep218 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 132684 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep219 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz341 99995 1000 0 1 11191020447815397 4503599627370496 250000000099513 33171000000000000000 223809217935860124603 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 46938541828353910898688 18889465931478580854784 1000000000398052 132684000000000000000 11191020447815397 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep220 := nat_lit 155308312606724842259553034681673281

noncomputable def ep221 := BSN.cos_dyadic_bound_f 627767279 2147483648 2 1 1048576 265628 ep220 ep59 ep220 ep220 ep60 ep220 1004091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 627767279) qz288 0 1 ep220 ep59 ep220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 627767279) qz289 0 1 ep220 ep60 ep220 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260548221) qz17)

noncomputable def ep222 := @Enclosure.Real.IsNear.cos_image qz52 qz343 Bool.false 260548221 1048576 791 1048576 Bool.true 1004091 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 223809217935860124603 900719925474099200 4999750001990160487 6634200000000000000000 260548221 1048576 791 1048576 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 260548221 1048576) (BSN.cos_reduce2 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44175195085818478723072) qz20) 226375608064910080 72057594037927936 Bool.false 1004091 1048576 39 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 260548221 1048576 226375608064910080 72057594037927936 39 44175195085818478723072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1004091 1048576 44175195085818478723072 151115727451828646838272 627767279 2147483648 265628 265368 (ep221 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep223 := BSN.sin_dyadic_bound_f 627767279 2147483648 2 1 1048576 265628 ep220 ep63 ep220 ep220 ep64 ep220 302179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 627767279) qz292 0 1 ep220 ep63 ep220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 627767279) qz293 0 1 ep220 ep64 ep220 rfl rfl rfl rfl) rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.sin_image qz52 qz343 Bool.false 260548221 1048576 791 1048576 Bool.true 302179 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 223809217935860124603 900719925474099200 4999750001990160487 6634200000000000000000 260548221 1048576 791 1048576 (ep219 rfl) rfl) (Enclosure.sfrac_false_div 260548221 1048576) (BSN.sin_reduce2 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44175195085818478723072) qz20) 226375608064910080 72057594037927936 Bool.false 302179 1048576 39 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 260548221 1048576 226375608064910080 72057594037927936 39 44175195085818478723072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 302179 1048576 44175195085818478723072 151115727451828646838272 627767279 2147483648 265628 265368 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep217 rfl rfl) rfl)

noncomputable def ep225 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 303935333427 1099511627776 8054926295251 36471900204957696 Bool.false 91468676763 1099511627776 8031643172299 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 302697 1048576 1 1048576 1004091 1048576 26500405 34782314496 303935333427 1099511627776 8054926295251 36471900204957696 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 1004091 1048576 106001620 139129257984 1004091 1048576 26500405 34782314496 (ep222 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 302697 1048576 1 1048576 302179 1048576 26500405 34782314496 91468676763 1099511627776 8031643172299 36471900204957696 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 302179 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 302179 1048576 106001620 139129257984 302179 1048576 26500405 34782314496 (ep224 rfl rfl) rfl)) rfl)

noncomputable def ep226 := @ep162 303935333427 1099511627776 8054926295251 36471900204957696 Bool.false 91468676763 1099511627776 8031643172299 36471900204957696 Bool.false ep163 833743460571 549755813888 21420618174605 6078650034159616 Bool.true 40705310920264191574016 4627658077 137438953472 10695139397453 3039325017079808 (ep164 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep215 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep216 ep225) rfl rfl

noncomputable abbrev qz345 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz345))

noncomputable abbrev qz346 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz268 qz285 qz346)

noncomputable def ep227 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 32619580149 274877906944 1930459004803 9117975051239424 Bool.false 275626044135 1099511627776 7738391433115 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 13 qz15 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz16)

noncomputable def ep228 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz345) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz345) (Real.sqrt qz347) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep229 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 132684 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz346 99995 1000 0 1 11551497052968677 4503599627370496 250000000099513 33171000000000000000 231018389562320571323 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 48450490295254733815808 18889465931478580854784 1000000000398052 132684000000000000000 11551497052968677 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep231 := nat_lit 812703789561918457414442533299732736

noncomputable def ep232 := BSN.sin_dyadic_bound_f 949473988 2147483648 2 1 1048576 265628 ep231 ep63 ep231 ep231 ep64 ep231 448652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 949473988) qz292 0 1 ep231 ep63 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 949473988) qz293 0 1 ep231 ep64 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268940801) qz17)

noncomputable def ep233 := @Enclosure.Real.IsNear.cos_image qz54 qz348 Bool.false 268940801 1048576 791 1048576 Bool.false 448652 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 231018389562320571323 900719925474099200 4999750001990160487 6634200000000000000000 268940801 1048576 791 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 268940801 1048576) (BSN.cos_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66813292216129192722432) qz20) 226375608064910080 72057594037927936 Bool.false 448652 1048576 40 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 268940801 1048576 226375608064910080 72057594037927936 40 66813292216129192722432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448652 1048576 66813292216129192722432 151115727451828646838272 949473988 2147483648 265628 265368 (ep232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep234 := BSN.cos_dyadic_bound_f 949473988 2147483648 2 1 1048576 265628 ep231 ep59 ep231 ep231 ep60 ep231 947745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 949473988) qz288 0 1 ep231 ep59 ep231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 949473988) qz289 0 1 ep231 ep60 ep231 rfl rfl rfl rfl) rfl rfl

noncomputable def ep235 := @Enclosure.Real.IsNear.sin_image qz54 qz348 Bool.false 268940801 1048576 791 1048576 Bool.true 947745 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 231018389562320571323 900719925474099200 4999750001990160487 6634200000000000000000 268940801 1048576 791 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 268940801 1048576) (BSN.sin_reduce3 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66813292216129192722432) qz20) 226375608064910080 72057594037927936 Bool.false 947745 1048576 40 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 268940801 1048576 226375608064910080 72057594037927936 40 66813292216129192722432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947745 1048576 66813292216129192722432 151115727451828646838272 949473988 2147483648 265628 265368 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep228 rfl rfl) rfl)

noncomputable def ep236 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 32619580149 274877906944 1930459004803 9117975051239424 Bool.false 275626044135 1099511627776 7738391433115 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 290823 1048576 1 1048576 112163 262144 26500405 34782314496 32619580149 274877906944 1930459004803 9117975051239424 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 448652 1048576 106001620 139129257984 112163 262144 26500405 34782314496 (ep233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 290823 1048576 1 1048576 947745 1048576 26500405 34782314496 275626044135 1099511627776 7738391433115 36471900204957696 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 947745 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 947745 1048576 106001620 139129257984 947745 1048576 26500405 34782314496 (ep235 rfl rfl) rfl)) rfl)

noncomputable def ep237 := @ep160 32619580149 274877906944 1930459004803 9117975051239424 Bool.false 275626044135 1099511627776 7738391433115 36471900204957696 Bool.false 247110461203502214414336 898982620869 549755813888 68122772533421 18235950102478848 Bool.false 32793591190508659539968 238604779519 1099511627776 136080064202551 36471900204957696 (ep161 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep227 ep236) rfl rfl

noncomputable abbrev qz350 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz350))

noncomputable abbrev qz351 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz268 qz285 qz351)

noncomputable def ep238 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 146927761741 549755813888 3730680873487 18235950102478848 Bool.false 412797939 1099511627776 7426628359703 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 14 qz15 rfl)

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz16)

noncomputable def ep239 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz350) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz350) (Real.sqrt qz352) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz352) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep240 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 132684 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep241 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz351 99995 1000 0 1 11885250371606245 4503599627370496 250000000099513 33171000000000000000 47538624436350658751 180143985094819840 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 49850353174629559828480 18889465931478580854784 1000000000398052 132684000000000000000 11885250371606245 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep240 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep242 := nat_lit 8314094175688719787814587360159960203475670858678687142007164841122144624640000

noncomputable def ep243 := nat_lit 16645110855728759939350604940994298415693987560846523638774117339161600000000

noncomputable def ep244 := nat_lit 21748059328275467166279256392419238335477538173821857666984559346294593331200000

noncomputable def ep245 := BSN.sin_dyadic_bound_f 3370240060 2147483648 3 2 1048576 265628 ep242 ep73 ep243 ep244 ep76 ep243 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3370240060) qz292 0 2 ep242 ep73 ep243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3370240060) qz293 0 2 ep244 ep76 ep243 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 276711213) qz17)

noncomputable def ep246 := @Enclosure.Real.IsNear.cos_image qz56 qz353 Bool.false 276711213 1048576 791 1048576 Bool.false 1048574 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 47538624436350658751 180143985094819840 4999750001990160487 6634200000000000000000 276711213 1048576 791 1048576 (ep241 rfl) rfl) (Enclosure.sfrac_false_div 276711213 1048576) (BSN.cos_reduce3 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237159560613931962597376) qz20) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 41 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 276711213 1048576 226375608064910080 72057594037927936 41 237159560613931962597376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048574 1048576 237159560613931962597376 151115727451828646838272 3370240060 2147483648 265628 265368 (ep245 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep247 := nat_lit 4626339035762945997647815468951530912337903360404091311621213408329707724800000

noncomputable def ep248 := nat_lit 13845726885577380473064745196972604140182322106090580887586091990310799974400000

noncomputable def ep249 := BSN.cos_dyadic_bound_f 3370240060 2147483648 3 2 1048576 265628 ep247 ep80 ep243 ep248 ep82 ep243 1473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3370240060) qz288 0 2 ep247 ep80 ep243 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3370240060) qz289 0 2 ep248 ep82 ep243 rfl rfl rfl rfl) rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.sin_image qz56 qz353 Bool.false 276711213 1048576 791 1048576 Bool.true 1473 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 47538624436350658751 180143985094819840 4999750001990160487 6634200000000000000000 276711213 1048576 791 1048576 (ep241 rfl) rfl) (Enclosure.sfrac_false_div 276711213 1048576) (BSN.sin_reduce3 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237159560613931962597376) qz20) 226375608064910080 72057594037927936 Bool.false 1473 1048576 41 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 276711213 1048576 226375608064910080 72057594037927936 41 237159560613931962597376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1473 1048576 237159560613931962597376 151115727451828646838272 3370240060 2147483648 265628 265368 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep239 rfl rfl) rfl)

noncomputable def ep251 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 146927761741 549755813888 3730680873487 18235950102478848 Bool.false 412797939 1099511627776 7426628359703 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 280243 1048576 1 1048576 524287 524288 26500405 34782314496 146927761741 549755813888 3730680873487 18235950102478848 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 1048574 1048576 106001620 139129257984 524287 524288 26500405 34782314496 (ep246 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 280243 1048576 1 1048576 1473 1048576 26500405 34782314496 412797939 1099511627776 7426628359703 36471900204957696 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.true 1473 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.true 1473 1048576 106001620 139129257984 1473 1048576 26500405 34782314496 (ep250 rfl rfl) rfl)) rfl)

noncomputable def ep252 := @ep158 146927761741 549755813888 3730680873487 18235950102478848 Bool.false 412797939 1099511627776 7426628359703 36471900204957696 Bool.false 574995313645670031687680 522955191305 274877906944 5987787783909 1519662508539904 Bool.false 262802605657921744273408 119508788729 549755813888 23917782093709 6078650034159616 (ep159 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep237 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep238 ep251) rfl rfl

noncomputable abbrev qz355 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz355))

noncomputable abbrev qz356 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz268 qz285 qz356)

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 28998256287 137438953472 3601597710443 18235950102478848 Bool.true 81818742423 549755813888 449676337621 2279493762809856 (BSN.cpow_neg_s_mk qz14 99995 1000 15 qz15 rfl)

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz16)

noncomputable def ep254 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz355) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz355) (Real.sqrt qz357) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz357) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep255 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 132684 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz356 99995 1000 0 1 12195965485668069 4503599627370496 250000000099513 33171000000000000000 243907113747875711931 900719925474099200 4999750001990160487 6634200000000000000000 qz19 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 51153586820399524478976 18889465931478580854784 1000000000398052 132684000000000000000 12195965485668069 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep257 := nat_lit 3029089018552656279309059963606422081

noncomputable def ep258 := BSN.cos_dyadic_bound_f 1319252753 2147483648 2 1 1048576 265628 ep257 ep59 ep257 ep257 ep60 ep257 856856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1319252753) qz288 0 1 ep257 ep59 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1319252753) qz289 0 1 ep257 ep60 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 283945251) qz17)

noncomputable def ep259 := @Enclosure.Real.IsNear.cos_image qz58 qz358 Bool.false 283945251 1048576 791 1048576 Bool.false 856856 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 243907113747875711931 900719925474099200 4999750001990160487 6634200000000000000000 283945251 1048576 791 1048576 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 283945251 1048576) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92834159520464462938112) qz20) 226375608064910080 72057594037927936 Bool.false 856856 1048576 43 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 283945251 1048576 226375608064910080 72057594037927936 43 92834159520464462938112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 856856 1048576 92834159520464462938112 151115727451828646838272 1319252753 2147483648 265628 265368 (ep258 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep260 := BSN.sin_dyadic_bound_f 1319252753 2147483648 2 1 1048576 265628 ep257 ep63 ep257 ep257 ep64 ep257 604406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1319252753) qz292 0 1 ep257 ep63 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1319252753) qz293 0 1 ep257 ep64 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable def ep261 := @Enclosure.Real.IsNear.sin_image qz58 qz358 Bool.false 283945251 1048576 791 1048576 Bool.false 604406 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 243907113747875711931 900719925474099200 4999750001990160487 6634200000000000000000 283945251 1048576 791 1048576 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 283945251 1048576) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92834159520464462938112) qz20) 226375608064910080 72057594037927936 Bool.false 604406 1048576 43 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 283945251 1048576 226375608064910080 72057594037927936 43 92834159520464462938112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 604406 1048576 92834159520464462938112 151115727451828646838272 1319252753 2147483648 265628 265368 (ep260 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep254 rfl rfl) rfl)

noncomputable def ep262 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 28998256287 137438953472 3601597710443 18235950102478848 Bool.true 81818742423 549755813888 449676337621 2279493762809856 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 270741 1048576 1 1048576 107107 131072 26500405 34782314496 28998256287 137438953472 3601597710443 18235950102478848 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 856856 1048576 106001620 139129257984 107107 131072 26500405 34782314496 (ep259 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 270741 1048576 1 1048576 302203 524288 26500405 34782314496 81818742423 549755813888 449676337621 2279493762809856 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 302203 524288 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 604406 1048576 106001620 139129257984 302203 524288 26500405 34782314496 (ep261 rfl rfl) rfl)) rfl)

noncomputable def ep263 := @ep156 28998256287 137438953472 3601597710443 18235950102478848 Bool.true 81818742423 549755813888 449676337621 2279493762809856 Bool.false 79845394198905002917888 580951703879 274877906944 75455051117351 18235950102478848 Bool.false 20720322082431437897728 18845023153 274877906944 75350756982095 18235950102478848 (ep157 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep252 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep253 ep262) rfl rfl

noncomputable abbrev qz360 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz360))

noncomputable abbrev qz361 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz268 qz285 qz361)

noncomputable def ep264 := @Enclosure.Complex.IsNear.of_eq qz38 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 194472619551 1099511627776 6980225885491 36471900204957696 Bool.true 194261332293 1099511627776 6980199149665 36471900204957696 (BSN.cpow_neg_s_mk qz14 99995 1000 16 qz15 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz16)

noncomputable def ep265 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz360) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz360) (Real.sqrt qz362) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep266 := BSN.log_dyadic_bound 0 32 1 0 1 524288 132684 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep267 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz361 99995 1000 0 1 3121657384082679 1125899906842624 62500000033171 8292750000000000000 62430026024269497321 225179981368524800 1249937500663386829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 52372720210750067441664 18889465931478580854784 1000000000530736 132684000000000000000 3121657384082679 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep266 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep268 := nat_lit 288405740061333826878258642133644121196920811119783993645436358011596146916161

noncomputable def ep269 := nat_lit 65125961780627615860142935727909475382866941471479678662971032265572662081

noncomputable def ep270 := nat_lit 865086968260440225403055640529476544639996699476409021578983131970257295424321

noncomputable def ep271 := BSN.cos_dyadic_bound_f 1685463177 2147483648 3 2 1048576 265628 ep268 ep80 ep269 ep270 ep82 ep269 741857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685463177) qz288 0 2 ep268 ep80 ep269 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685463177) qz289 0 2 ep270 ep82 ep269 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz61 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145356231) qz61)

noncomputable abbrev qz364 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep272 := @Enclosure.Real.IsNear.cos_image qz60 qz363 Bool.false 145356231 524288 99 131072 Bool.false 741857 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 62430026024269497321 225179981368524800 1249937500663386829 1658550000000000000000 145356231 524288 99 131072 (ep267 rfl) rfl) (Enclosure.sfrac_false_div 145356231 524288) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59301963562690273083392) qz364) 226375608064910080 72057594037927936 Bool.false 741857 1048576 44 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145356231 524288 226375608064910080 72057594037927936 44 59301963562690273083392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741857 1048576 59301963562690273083392 75557863725914323419136 1685463177 2147483648 265628 265368 (ep271 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep273 := nat_lit 8070065785396524006463579555579022241

noncomputable def ep274 := BSN.sin_dyadic_bound_f 1685463177 2147483648 2 1 1048576 265628 ep273 ep63 ep273 ep273 ep64 ep273 741051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685463177) qz292 0 1 ep273 ep63 ep273 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685463177) qz293 0 1 ep273 ep64 ep273 rfl rfl rfl rfl) rfl rfl

noncomputable def ep275 := @Enclosure.Real.IsNear.sin_image qz60 qz363 Bool.false 145356231 524288 99 131072 Bool.false 741051 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 62430026024269497321 225179981368524800 1249937500663386829 1658550000000000000000 145356231 524288 99 131072 (ep267 rfl) rfl) (Enclosure.sfrac_false_div 145356231 524288) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59301963562690273083392) qz364) 226375608064910080 72057594037927936 Bool.false 741051 1048576 44 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145356231 524288 226375608064910080 72057594037927936 44 59301963562690273083392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741051 1048576 59301963562690273083392 75557863725914323419136 1685463177 2147483648 265628 265368 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep265 rfl rfl) rfl)

noncomputable def ep276 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 194472619551 1099511627776 6980225885491 36471900204957696 Bool.true 194261332293 1099511627776 6980199149665 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 262143 1048576 1 1048576 741857 1048576 3316697 4347789312 194472619551 1099511627776 6980225885491 36471900204957696 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 741857 1048576 13266788 17391157248 741857 1048576 3316697 4347789312 (ep272 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 262143 1048576 1 1048576 741051 1048576 3316697 4347789312 194261332293 1099511627776 6980199149665 36471900204957696 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 741051 1048576 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 741051 1048576 13266788 17391157248 741051 1048576 3316697 4347789312 (ep275 rfl rfl) rfl)) rfl)

noncomputable def ep277 := @ep154 194472619551 1099511627776 6980225885491 36471900204957696 Bool.true 194261332293 1099511627776 6980199149665 36471900204957696 Bool.false 692219380211335716405248 2518279435067 1099511627776 157890328120193 36471900204957696 Bool.true 32677826338421278244864 118881239681 1099511627776 157681713113855 36471900204957696 (ep155 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep263 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep264 ep276) rfl rfl

theorem EMRow30.d7 : Enclosure.Complex.IsNear qz37 Bool.false 2518279435067 1099511627776 157890328120193 36471900204957696 Bool.true 118881239681 1099511627776 157681713113855 36471900204957696 := ep153 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep277 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow30.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow30.d9 : @Eq Nat (Nat.pow 20 1) 20 := @Eq.refl Nat 20

noncomputable def ep278 := nat_lit 5134592455540199781226977180043

noncomputable def ep279 := nat_lit 1844536061402088358390267904000

noncomputable def ep280 := nat_lit 35697486233615557820255937640225435771

noncomputable def ep281 := nat_lit 6088713422804488949896446002532974592000

noncomputable abbrev qz549 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz528 := qz549

noncomputable abbrev qz366 := qz528

noncomputable abbrev qz62 := qz366

noncomputable abbrev qz529 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz367 := qz529

noncomputable abbrev qz63 := qz367

noncomputable abbrev qz550 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz551 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz530 := (@HAdd.hAdd Complex Complex Complex qz547 (@HAdd.hAdd Complex Complex Complex qz547 qz550 (@HMul.hMul Complex Complex Complex qz549 Complex.I (@HDiv.hDiv Complex Complex Complex qz551 (↑qz548) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz368 := qz530

noncomputable abbrev qz64 := (Complex.Stirling.logGammaStirling 1 qz368)

noncomputable abbrev qz531 := (@HAdd.hAdd Complex Complex Complex qz547 qz550 (@HMul.hMul Complex Complex Complex qz549 Complex.I (@HDiv.hDiv Complex Complex Complex qz551 (↑qz548) (2 : Complex))))

noncomputable abbrev qz369 := qz531

noncomputable abbrev qz65 := qz369

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz285 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz370 := (@instHSub Real Real.instSub)

noncomputable def ep282 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66))) (zetaApproximant qz5 1 20))

noncomputable def ep283 := @Enclosure.Real.IsNear.of_eq ep282 (@HSub.hSub Real Real Real qz370 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 20))))

noncomputable def ep284 := nat_lit 51346145310881089948506293869

noncomputable def ep285 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 20))) ep284

noncomputable def ep286 := nat_lit 18445360614020883583902679040

noncomputable def ep287 := nat_lit 307187133607091885894832304619385403

noncomputable def ep288 := nat_lit 52488908817280077154279706918387712000

noncomputable def ep289 := nat_lit 22075547909213623652206857

noncomputable def ep290 := nat_lit 63778735192899056455390304376729023

noncomputable def ep291 := nat_lit 94709409448469975830686838031568044666106711717052122398720

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.re (zetaApproximant qz5 1 20)) 1048575 1048576 10711009

noncomputable def ep293 := nat_lit 3672566004640661608504849

noncomputable def ep294 := nat_lit 1319315000583235043328000

noncomputable def ep295 := nat_lit 109268885317425689025749557

noncomputable def ep296 := nat_lit 21881498942173244811116544000

noncomputable def ep297 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 1048575 1048576 42844036

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92238237) qz17)

noncomputable def ep298 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz371 Bool.false 92238237 1048576 315

noncomputable def ep299 := nat_lit 3478231449600000000000000000

noncomputable def ep300 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) Bool.false 316928171021768863811 3602879701896396800 1040209194282781208097443 ep299

noncomputable def ep301 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66 523134014782498680899 3602879701896396800 376822365282781208097443 ep299 1500344979 26214400

noncomputable def ep302 := nat_lit 8308081846433057703487078400

noncomputable def ep303 := nat_lit 869557862400000000000000000

noncomputable def ep304 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 70792050070621880393 900719925474099200 172463708962066289352797 ep303 Bool.false 523134014782498680899 3602879701896396800

noncomputable def ep305 := nat_lit 289852620800000000000000000

noncomputable def ep306 := @Enclosure.Complex.IsNear.subLitP qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 63744573974453196193 900719925474099200 56395636317500384288799 ep305 Bool.false 534344723500655314499 3602879701896396800 350607965279302976647843

noncomputable def ep307 := nat_lit 318819050318846195578918537609084928

noncomputable def ep308 := nat_lit 147249134627455787835349065996959744

noncomputable abbrev qz552 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz532 := qz552

noncomputable abbrev qz372 := (@HSub.hSub Complex Complex Complex qz529 qz530 qz532)

noncomputable abbrev qz373 := (Complex.log qz530)

noncomputable abbrev qz67 := (@HSub.hSub Complex Complex Complex qz367 (@HMul.hMul Complex Complex Complex qz366 qz372 qz373) qz368)

noncomputable abbrev qz374 := qz532

noncomputable abbrev qz68 := (@HMul.hMul Complex Complex Complex qz366 qz374 ↑(Real.log qz272))

noncomputable abbrev qz533 := qz551

noncomputable abbrev qz375 := qz533

noncomputable abbrev qz69 := qz375

noncomputable abbrev qz70 := (@instHMul Nat instMulNat)

noncomputable abbrev qz534 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz376 := qz534

noncomputable abbrev qz71 := qz376

noncomputable abbrev qz72 := qz368

noncomputable abbrev qz377 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz73 := qz377

noncomputable abbrev qz378 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz74 := qz378

noncomputable abbrev qz379 := (@instHSub Int Int.instSub)

noncomputable abbrev qz380 := (@instHMul Int Int.instMul)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq qz64 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 63744573974453196193

noncomputable def ep310 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz67 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 63744641398650213793 900719925474099200

noncomputable def ep311 := nat_lit 2190246884141833737052853633024

noncomputable def ep312 := nat_lit 1835994489780381768273439699763200

noncomputable def ep313 := @ep310 860528732452938609 4422800000000000000000 Bool.false 534350716462949336643 3602879701896396800 891625002440158273 8845600000000000000000 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400 Bool.true ep311 63744573974453196193 900719925474099200 56395636317500384288799 ep305 Bool.false ep312

noncomputable def ep314 := @Enclosure.Complex.IsNear.addLitP qz67 qz68 Bool.true 64572346880092312993 900719925474099200 1695750000306267843 8845600000000000000000

noncomputable def ep315 := nat_lit 8355137637403880822276096

noncomputable def ep316 := @ep314 Bool.false 534350716462949336643 3602879701896396800 891625002440158273 8845600000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep315 63744641398650213793 900719925474099200 860528732452938609 4422800000000000000000 Bool.false 534350716462949336643 534350716462949336643 3602879701896396800

noncomputable abbrev qz75 := (@HMul.hMul Complex Complex Complex qz366 qz372 qz373)

noncomputable def ep317 := @Enclosure.Complex.IsNear.subLitP qz75 qz72 Bool.true 62545727047775589793 900719925474099200 1695750000306267843 8845600000000000000000 Bool.false 714485694358514435651

noncomputable def ep318 := nat_lit 2137402865851797346572000

noncomputable def ep319 := @ep317 3602879701896396800 891625002440158273 8845600000000000000000 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 Bool.true 258289387520369251972000 64572346880092312993 900719925474099200 1695750000306267843 8845600000000000000000 Bool.false ep318 534350716462949336643 3602879701896396800 891625002440158273 8845600000000000000000

noncomputable abbrev qz76 := qz372

noncomputable abbrev qz77 := qz373

noncomputable def ep320 := @Enclosure.Complex.IsNear.mul qz76 qz77 Bool.true 62545727047775589793 900719925474099200 1695750000306267843 8845600000000000000000 Bool.false 714485694358514435651 3602879701896396800 891625002440158273

noncomputable abbrev qz78 := (Complex.re qz372)

noncomputable abbrev qz79 := (Complex.re qz373)

noncomputable abbrev qz80 := (Complex.im qz372)

noncomputable abbrev qz81 := (Complex.im qz373)

noncomputable def ep321 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz78 qz79) (@HMul.hMul Real Real Real qz0 qz80 qz81) 246715193690797643 36028797018963968 875000002554167 265368000000000000000 17178401722511382717 225179981368524800

noncomputable def ep322 := nat_lit 563361826051957798119504944253894656

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz79 7000 4000 0 1 35245027670113949 9007199254740992 125000000364881 66342000000000000000

noncomputable def ep324 := @Enclosure.Complex.IsNear.re_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable abbrev qz381 := (Enclosure.sfrac Bool.false 199990 4000)

noncomputable abbrev qz82 := qz381

noncomputable def ep325 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz82) Bool.false 7000 4000 0 1 Bool.false 199990 4000 0

noncomputable abbrev qz382 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz83 := qz382

noncomputable abbrev qz383 := (Complex.log (Complex.mk qz83 qz82))

noncomputable def ep326 := @Enclosure.Complex.IsNear.of_eq qz77 qz383 Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000

noncomputable def ep327 := nat_lit 422367265547601150657504626870700001500000000

noncomputable def ep328 := nat_lit 1425938744966426429816263769248000800000000

noncomputable def ep329 := nat_lit 8561564365249218170666667708000300000000

noncomputable def ep330 := BSN.log_dyadic_bound 7309000100 72845000100 3 2 ep327 1048576 265368 ep328 ep329 211130 80154000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7309000100) (BSN.artanhQ 72845000100) 0 2 ep328 ep327 ep329 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz84 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz384 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz535 := (Real.log (Enclosure.sfrac Bool.false 40077000100 16000000))

noncomputable def ep331 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz535 1 2 0 1 35245027670113949 4503599627370496 125000000364881 33171000000000000000 35245027670113949 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 40077000100 16000000 35245027670113949 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40077000100) qz385)) Bool.false 295656721073739233492992 37778931862957161709568 1000000002919048 265368000000000000000 35245027670113949 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 40077000100 16000000 11 80154000200 65536000000 211130 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep332 := BSN.arctan_dyadic_bound_f 9000 199990 1 0 1048576 265368 0 1 1 0 1 1 47156 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz85 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz86 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz384 BSN.pi_near_15 rfl)

noncomputable abbrev qz386 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 199990)))

noncomputable def ep333 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz386 884279719003555 562949953421312 1 2000000000000000 47156 1048576 1 265368 900688022630336299008 858963034277283 562949953421312 250000000033171 66342000000000000000 qz86 (ep332 rfl) rfl rfl

noncomputable abbrev qz387 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199990) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep334 := @Enclosure.Complex.IsNear.re_isNear qz77 Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (ep326 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz14 Bool.false 99995 1000 2 qz15 rfl)) (@Enclosure.Complex.IsNear.of_parts qz383 Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz383) (@HMul.hMul Real Real Real qz0 qz84 qz535) Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 9000 199990 4000 40077000100 16000000 rfl rfl rfl) (ep331 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz383) qz387 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 9000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz387 (@HSub.hSub Real Real Real qz370 qz85 qz386) Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 199990 9000 rfl rfl) ep333))))

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz81 199990 4000 0 1 858963034277283 562949953421312 250000000033171 66342000000000000000

noncomputable def ep336 := @Enclosure.Complex.IsNear.im_isNear qz76 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable def ep337 := @Enclosure.Complex.IsNear.im_isNear qz77 Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (ep326 (@congrArg Complex Complex qz72 (Complex.mk qz83 qz82) Complex.log (BSN.w_shift_mk qz14 Bool.false 99995 1000 2 qz15 rfl)) (@Enclosure.Complex.IsNear.of_parts qz383 Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz383) (@HMul.hMul Real Real Real qz0 qz84 qz535) Bool.false 35245027670113949 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 9000 199990 4000 40077000100 16000000 rfl rfl rfl) (ep331 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz383) qz387 Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 9000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz387 (@HSub.hSub Real Real Real qz370 qz85 qz386) Bool.false 858963034277283 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 199990 9000 rfl rfl) ep333))))

noncomputable abbrev qz388 := (Enclosure.Real.IsNear.const Bool.false 199990 4000)

noncomputable abbrev qz87 := (@ep325 1 (BSN.w_sub_half_mk qz285 Bool.false 99995 1000 2 qz287 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz381 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz388))

noncomputable def ep338 := @ep321 4999750000663386829 26536800000000000000000 ep322 62545727047775589793 900719925474099200 1695750000306267843 8845600000000000000000 (@ep323 246715193690797643 36028797018963968 875000002554167 265368000000000000000 (ep324 qz87) ep334 rfl) (@ep335 17178401722511382717 225179981368524800 4999750000663386829 26536800000000000000000 (ep336 qz87) ep337 rfl) rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz78 qz81) (@HMul.hMul Real Real Real qz0 qz80 qz79) 6012741239940981 2251799813685248 1750000000232197 265368000000000000000 704865308374608866051 3602879701896396800

noncomputable def ep340 := nat_lit 1608878753437277854244505633263976448

noncomputable def ep341 := @Enclosure.Real.IsNear.mulLit_ff qz78 qz81 7000 4000 0 1 858963034277283 562949953421312 250000000033171 66342000000000000000

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz80 qz79 199990 4000 0 1 35245027670113949 9007199254740992 125000000364881 66342000000000000000

noncomputable def ep343 := @ep339 2499875007297255119 26536800000000000000000 ep340 714485694358514435651 3602879701896396800 891625002440158273 8845600000000000000000 (@ep341 6012741239940981 2251799813685248 1750000000232197 265368000000000000000 (ep324 qz87) ep337 rfl) (@ep342 704865308374608866051 3602879701896396800 2499875007297255119 26536800000000000000000 (ep336 qz87) ep334 rfl) rfl

noncomputable def ep344 := @Enclosure.Complex.IsNear.of_eq qz72 (Complex.mk qz83 qz82) Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 (BSN.w_shift_mk qz14 Bool.false 99995 1000 2 qz15 rfl)

noncomputable abbrev qz389 := (ep344 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 199990 4000) Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 199990 4000)))

noncomputable abbrev qz88 := qz389

noncomputable def ep345 := ep319 (@ep320 8845600000000000000000 (ep338 rfl) (ep343 rfl)) qz88 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz89 := qz374

noncomputable def ep346 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz90 := (@Enclosure.Complex.IsNear.of_eq qz374 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz283) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz283 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz384 qz295))

noncomputable def ep348 := ep347 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow30.d4)

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep350 := ep349 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz11 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz11 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep351 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz89) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz89) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep352 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz89) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep353 := ep352 (@Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz11 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz11 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep354 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz89) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep355 := ep354 (@Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz90) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow30.d4)

noncomputable def ep356 := @ep316 891625002440158273 8845600000000000000000 (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep346 131072 3 1048576 (ep348 rfl) (ep350 rfl) rfl rfl) (@ep351 1 0 1 (ep353 rfl) (ep355 rfl) rfl rfl))

noncomputable abbrev qz91 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz390 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz92 := (@HMul.hMul Complex Complex Complex qz366 (@HMul.hMul Complex Complex Complex qz366 (2 : Complex) qz390) (@HSub.hSub Complex Complex Complex qz367 (@HMul.hMul Complex Complex Complex qz366 (2 : Complex) qz390) (1 : Complex)))

noncomputable abbrev qz391 := (@HPow.hPow Complex Int Complex qz534 qz530 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz93 := qz391

noncomputable def ep357 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93)) Bool.false 2572029 34359738368 3 34359738368

noncomputable def ep358 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93) Bool.false 0 1 0 1 Bool.false

noncomputable def ep359 := @ep358 0 1 0 1 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400 Bool.false 2572029 2572029 34359738368 3 34359738368 Bool.true 5715334219 5715334219 3435973836800 19999

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz72 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false

noncomputable def ep361 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz93 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400

noncomputable abbrev qz94 := (Complex.re qz391)

noncomputable abbrev qz95 := (Complex.im qz391)

noncomputable def ep362 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) 2572029 34359738368 3 34359738368 0 1 0

noncomputable def ep363 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 1 12 0 1 7716087 8589934592 9 8589934592 2572029

noncomputable def ep364 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz11) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz392 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz11 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep365 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep364 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz392)

noncomputable def ep366 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999 858993459200

noncomputable abbrev qz536 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz393 := (@HPow.hPow Complex Nat Complex qz536 qz530 1)

noncomputable abbrev qz96 := (@Inv.inv Complex Complex.instInv qz393)

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq qz93 qz96 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999

noncomputable def ep368 := @Enclosure.Complex.IsNear.of_parts qz96 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999

noncomputable abbrev qz97 := (Complex.re qz393)

noncomputable abbrev qz98 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz99 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz100 := qz393

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 9000 4000 0 1 857343 2147483648 1 2147483648

noncomputable def ep370 := @Enclosure.Complex.IsNear.re_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable def ep371 := @Enclosure.Complex.IsNear.of_eq qz100 qz72 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0

noncomputable def ep372 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) Bool.false 857343 2147483648 1 2147483648 857343 2147483648 1

noncomputable abbrev qz101 := (Complex.im qz393)

noncomputable abbrev qz394 := (@instHAdd Real Real.instAdd)

noncomputable def ep373 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101)) Bool.false 400770001 160000 0 1

noncomputable def ep374 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz97 qz97) (@HMul.hMul Real Real Real qz0 qz101 qz101) 81 16 0 1 399960001 160000

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff qz97 qz97 9000 4000 0 1 9000 4000 0 1

noncomputable def ep376 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 199990 4000 0 1 199990 4000 0 1

noncomputable def ep377 := @Enclosure.Complex.IsNear.im_isNear qz100 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable abbrev qz102 := (ep370 (@ep371 1 (BSN.pow_one_c qz368) qz389))

noncomputable abbrev qz103 := (ep377 (@ep371 1 (BSN.pow_one_c qz368) qz389))

noncomputable def ep378 := @ep374 0 1 6412320016 400770001 160000 0 1 (@ep375 81 16 0 1 qz102 qz102 rfl) (@ep376 399960001 160000 0 1 qz103 qz103 rfl)

noncomputable def ep379 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100) 400770001 160000 0 1 428671 428672 1073741824 (ep373 (Enclosure.Complex.normSq_eq_mul_add_mul qz100) (ep378 rfl rfl)) rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.of_eq (Complex.re qz96) (@HMul.hMul Real Real Real qz0 qz97 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.false 7716087 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz100) (@ep369 7716087 8589934592 9 8589934592 qz102 (@ep372 2147483648 (ep379 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep381 := @Enclosure.Real.IsNear.of_eq (Complex.im qz96) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100))) Bool.true 17146002657 858993459200 19999 858993459200 (Enclosure.Complex.inv_im_eq_mul qz100)

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz101) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz100)) 199990 4000 0 1 857343 2147483648 1

noncomputable def ep383 := @ep382 2147483648 17146002657 858993459200 19999 858993459200 (@Enclosure.Real.IsNear.neg qz101 Bool.false 199990 4000 0 1 qz103) (@ep372 2147483648 (ep379 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 0 1 0 1 17146002657 858993459200 19999 858993459200 0

noncomputable def ep385 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep364 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz392)

noncomputable def ep386 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999 858993459200

noncomputable abbrev qz104 := (@ep367 858993459200 (BSN.zpow_one_sub_two_mul qz368 1 1 rfl rfl) (@ep368 858993459200 ep380 (ep381 ep383)))

noncomputable def ep387 := @ep362 1 2572029 2572029 34359738368 3 34359738368 (@ep363 34359738368 3 34359738368 ep365 (ep366 qz104) rfl) (@ep384 1 0 1 ep385 (ep386 qz104) rfl) rfl

noncomputable def ep388 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94) 5715334219 3435973836800 19999 10307921510400 0 1 0

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz95 1 12 0 1 17146002657 858993459200 19999 858993459200 5715334219

noncomputable def ep390 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz94 0 1 0 1 7716087 8589934592 9 8589934592 0

noncomputable def ep391 := @ep388 1 5715334219 5715334219 3435973836800 19999 10307921510400 (@ep389 3435973836800 19999 10307921510400 ep365 (ep386 qz104) rfl) (@ep390 1 0 1 ep385 (ep366 qz104) rfl) rfl

noncomputable abbrev qz105 := (@Enclosure.Complex.IsNear.mk qz283 qz283 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz295 qz295)

noncomputable def ep392 := @ep359 10307921510400 (@ep360 0 1 0 1 (BSN.stirling_sum_base qz72) qz105) (ep361 (ep387 rfl) (ep391 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep393 := @ep313 534344723500655314499 3602879701896396800 350607965279302976647843 ep299 (ep356 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep357 Bool.true 5715334219 3435973836800 19999 10307921510400 (BSN.stirling_sum_succ qz72 0 1 rfl) (ep392 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep394 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz14 2) Bool.false 35237380480843421 4503599627370496 125000000364881 33171000000000000000 Bool.false 875836618605987 281474976710656

noncomputable abbrev qz106 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz369 qz390))

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz14 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz14 1) qz106) Bool.false 35237380480843421 4503599627370496 125000000364881 33171000000000000000 Bool.false 875836618605987 281474976710656 250000000033171 33171000000000000000

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz14 1) qz106 Bool.false 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000 Bool.false

noncomputable def ep397 := nat_lit 634780214412155279918538124427264

noncomputable def ep398 := nat_lit 986104367297839569253473189888

noncomputable abbrev qz107 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz369 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep399 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz14 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz14 0) qz107) Bool.false 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000

noncomputable def ep400 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz14 0) qz107 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz395 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82))

noncomputable def ep401 := @Enclosure.Complex.IsNear.of_eq qz107 qz395 Bool.false 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000

noncomputable def ep402 := nat_lit 420514907276537331923020706865900001500000000

noncomputable def ep403 := nat_lit 1391668531252353164837140566688000800000000

noncomputable def ep404 := nat_lit 8192834420582976393319466748000300000000

noncomputable def ep405 := BSN.log_dyadic_bound 7229000100 72765000100 3 2 ep402 1048576 265368 ep403 ep404 209035 79994000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7229000100) (BSN.artanhQ 72765000100) 0 2 ep403 ep402 ep404 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep406 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 39997000100 16000000)) 1 2 0 1 35236029713628829 4503599627370496 125000000364881 33171000000000000000 35236029713628829 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 39997000100 16000000 35236029713628829 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39997000100) qz385)) Bool.false 295581240743984503980032 37778931862957161709568 1000000002919048 265368000000000000000 35236029713628829 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 39997000100 16000000 11 79994000200 65536000000 209035 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep405 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep407 := BSN.arctan_dyadic_bound_f 1000 199990 1 0 1048576 265368 0 1 1 0 1 1 5243 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz396 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 199990)

noncomputable def ep408 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz396 qz397)) 884279719003555 562949953421312 1 2000000000000000 5243 1048576 1 265368 924282944028083748864 881464904811939 562949953421312 250000000033171 66342000000000000000 qz86 (ep407 rfl) rfl rfl

noncomputable abbrev qz108 := (@HAdd.hAdd Complex Complex Complex qz274 qz369 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz398 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz82)

noncomputable def ep409 := @ep400 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000 Bool.false 35236029713628829 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 881464904811939 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz14 0) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz14) qz105) (ep401 (@congrArg Complex Complex qz108 qz398 Complex.log (BSN.w_shift_mk qz14 Bool.false 99995 1000 0 qz15 rfl)) (@Enclosure.Complex.IsNear.of_parts qz395 Bool.false 35236029713628829 9007199254740992 125000000364881 66342000000000000000 Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz395) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 39997000100 16000000))) Bool.false 35236029713628829 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 1000 199990 4000 39997000100 16000000 rfl rfl rfl) (ep406 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz395) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz397 qz396)) Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 1000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz397 qz396)) (@HSub.hSub Real Real Real qz370 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz396 qz397))) Bool.false 881464904811939 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 199990 1000 rfl rfl) ep408)))) rfl rfl

noncomputable abbrev qz399 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82))

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq qz106 qz399 Bool.false 35238731248058013 9007199254740992 125000000364881 66342000000000000000 Bool.false 870208332400035 562949953421312 250000000033171 66342000000000000000

noncomputable def ep411 := nat_lit 421069973695044918613828673267340001500000000

noncomputable def ep412 := nat_lit 1401898135863212512445432407456000800000000

noncomputable def ep413 := nat_lit 8302177006585912401481707036000300000000

noncomputable def ep414 := BSN.log_dyadic_bound 7253000100 72789000100 3 2 ep411 1048576 265368 ep412 ep413 209664 80042000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7253000100) (BSN.artanhQ 72789000100) 0 2 ep412 ep411 ep413 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep415 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 40021000100 16000000)) 1 2 0 1 35238731248058013 4503599627370496 125000000364881 33171000000000000000 35238731248058013 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 40021000100 16000000 35238731248058013 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40021000100) qz385)) Bool.false 295603902857309432315904 37778931862957161709568 1000000002919048 265368000000000000000 35238731248058013 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 40021000100 16000000 11 80042000200 65536000000 209664 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep414 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep416 := BSN.arctan_dyadic_bound_f 5000 199990 1 0 1048576 265368 0 1 1 0 1 1 26210 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz400 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep417 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz400 qz397)) 884279719003555 562949953421312 1 2000000000000000 26210 1048576 1 265368 912479572354699100160 870208332400035 562949953421312 250000000033171 66342000000000000000 qz86 (ep416 rfl) rfl rfl

noncomputable abbrev qz109 := (@HAdd.hAdd Complex Complex Complex qz274 qz369 qz390)

noncomputable abbrev qz401 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz82)

noncomputable def ep418 := @ep396 35238731248058013 9007199254740992 125000000364881 66342000000000000000 Bool.false 870208332400035 562949953421312 250000000033171 66342000000000000000 Bool.false ep397 35237380480843421 4503599627370496 125000000364881 33171000000000000000 Bool.false ep398 875836618605987 281474976710656 250000000033171 33171000000000000000 (ep399 (BSN.log_sum_c_succ qz14 0 1 rfl) (ep409 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep410 (@congrArg Complex Complex qz109 qz401 Complex.log (BSN.w_shift_mk qz14 Bool.false 99995 1000 1 qz15 rfl)) (@Enclosure.Complex.IsNear.of_parts qz399 Bool.false 35238731248058013 9007199254740992 125000000364881 66342000000000000000 Bool.false 870208332400035 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz399) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 40021000100 16000000))) Bool.false 35238731248058013 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 5000 199990 4000 40021000100 16000000 rfl rfl rfl) (ep415 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz399) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz397 qz400)) Bool.false 870208332400035 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 5000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz397 qz400)) (@HSub.hSub Real Real Real qz370 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz400 qz397))) Bool.false 870208332400035 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 199990 5000 rfl rfl) ep417)))) rfl rfl

noncomputable def ep419 := @ep306 ep299 Bool.false 35237380480843421 4503599627370496 125000000364881 33171000000000000000 Bool.false 875836618605987 281474976710656 250000000033171 33171000000000000000 Bool.true ep307 70792050070621880393 900719925474099200 172463708962066289352797 ep303 Bool.false ep308 523134014782498680899 3602879701896396800 376822365282781208097443 ep299 (@ep309 900719925474099200 56395636317500384288799 ep305 Bool.false 534344723500655314499 3602879701896396800 350607965279302976647843 ep299 (BSN.logGammaStirling_unfold 1 qz72) (ep393 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep394 250000000033171 33171000000000000000 (BSN.log_sum_c_eq qz14 2) (ep395 (BSN.log_sum_c_succ qz14 1 2 rfl) (ep418 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz110 := (@HDiv.hDiv Real Real Real qz271 qz285 (2 : Real))

noncomputable def ep420 := @Enclosure.Real.IsNear.mulLit_ff qz110 (Real.log Real.pi) 99995 2000 0 1 75021 65536 1 262144 1500344979 26214400 19999 104857600 (@Enclosure.Real.IsNear.of_eq qz110 (Enclosure.sfrac Bool.false 99995 2000) Bool.false 99995 2000 0 1 (BSN.t_half_eq qz14 Bool.false 99995 1000 qz15) (Enclosure.Real.IsNear.const Bool.false 99995 2000)) EMRow30.d5 rfl

noncomputable def ep421 := @ep301 19999 104857600 ep302 316928171021768863811 3602879701896396800 1040209194282781208097443 ep299 (@ep304 376822365282781208097443 ep299 (ep419 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep420 rfl rfl

noncomputable def ep422 := BSN.cos_dyadic_bound_f 1381512 2147483648 1 0 1048576 265628 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1381512) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1381512) qz289 0 0 rfl) rfl rfl

noncomputable def ep423 := @ep298 1048576 Bool.false 1048575 1048576 1 132684 (@ep300 92238237 1048576 315 1048576 ep421 rfl) (Enclosure.sfrac_false_div 92238237 1048576) (BSN.cos_reduce0 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97215313183384797184) qz20) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 14 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 92238237 1048576 226375608064910080 72057594037927936 14 97215313183384797184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 97215313183384797184 151115727451828646838272 1381512 2147483648 265628 265368 (ep422 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep424 := nat_lit 3518173334888626782208000

noncomputable def ep425 := nat_lit 1745950469224058498127477643

noncomputable def ep426 := nat_lit 350103983074771916977864704000

noncomputable abbrev qz402 := (@HPow.hPow Complex Complex Complex qz523 (@Nat.cast Complex Complex.instNatCast 20) qz524)

noncomputable abbrev qz111 := qz402

noncomputable abbrev qz403 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz375 qz403 (@HSub.hSub Complex Complex Complex qz367 qz273 (1 : Complex))) qz374)

noncomputable abbrev qz113 := (@instHSub Nat instSubNat)

noncomputable abbrev qz404 := qz536

noncomputable abbrev qz114 := qz404

noncomputable abbrev qz115 := qz403

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz8) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false ep293 ep294 ep295

noncomputable def ep428 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz8) (@HMul.hMul Complex Complex Complex qz62 qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 197716330307 68719476736 29608122267523 6078650034159616

noncomputable def ep429 := nat_lit 2687639080882019828042557

noncomputable def ep430 := nat_lit 43044660038060718059109643

noncomputable def ep431 := nat_lit 252376814117328413445297310598692864

noncomputable def ep432 := nat_lit 18006173305420285467324492162269184

noncomputable def ep433 := @ep428 Bool.true 16466753761 274877906944 29566554382697 6078650034159616 Bool.true 123302835228480166231151 ep294 ep429 ep296 Bool.false 276264717466065096411961 ep424 ep430 ep426 Bool.false ep431 ep293 ep294 ep295 ep296 Bool.false ep432 65506076881939536059961 ep424

noncomputable def ep434 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz8) (BSN.headSumC qz5 20) Bool.false 197716330307 68719476736 29608122267523 6078650034159616 Bool.true 16466753761 274877906944 29566554382697

noncomputable abbrev qz116 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 19) qz276)

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz116) Bool.false 197716330307 68719476736 29608122267523 6078650034159616 Bool.true 16466753761 274877906944 29566554382697 6078650034159616

noncomputable def ep436 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz116 Bool.false 46919510949 17179869184 85621834740017 18235950102478848 Bool.true 130184053893 549755813888 21373698654953 4558987525619712 Bool.false

noncomputable abbrev qz117 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz276)

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz117) Bool.false 46919510949 17179869184 85621834740017 18235950102478848 Bool.true 130184053893 549755813888 21373698654953 4558987525619712

noncomputable def ep438 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz117 Bool.false 342961758871 137438953472 82329629667173 18235950102478848 Bool.true 261364373467 1099511627776 164439827430763 36471900204957696 Bool.false

noncomputable abbrev qz118 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz276)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz37 qz118) Bool.false 342961758871 137438953472 82329629667173 18235950102478848 Bool.true 261364373467 1099511627776 164439827430763 36471900204957696

noncomputable def ep440 := @Enclosure.Complex.IsNear.addLitP qz37 qz118 Bool.false 2518279435067 1099511627776 157890328120193 36471900204957696 Bool.true 118881239681 1099511627776 157681713113855 36471900204957696 Bool.false

noncomputable def ep441 := nat_lit 3016723534089385744007168

noncomputable abbrev qz405 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz119 := (@Inv.inv Real Real.instInv (Real.sqrt qz405))

noncomputable abbrev qz406 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz120 := (@HMul.hMul Real Real Real qz268 qz285 qz406)

noncomputable def ep442 := @Enclosure.Complex.IsNear.of_eq qz118 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)))) Bool.false 225414635901 1099511627776 6768931214153 36471900204957696 Bool.true 71241566893 549755813888 1689528579227 9117975051239424 (BSN.cpow_neg_s_mk qz14 99995 1000 17 qz15 rfl)

noncomputable abbrev qz407 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz16)

noncomputable def ep443 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz405) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz405) (Real.sqrt qz407) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz407) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep444 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 132684 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep445 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz406 99995 1000 0 1 3189913004350711 1125899906842624 62500000033171 8292750000000000000 63795070174009869289 225179981368524800 1249937500663386829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz407) Bool.false 53517859495200818200576 18889465931478580854784 1000000000530736 132684000000000000000 3189913004350711 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep446 := nat_lit 2147152973222687543807757849928400896

noncomputable def ep447 := BSN.cos_dyadic_bound_f 1210502656 2147483648 2 1 1048576 265628 ep446 ep59 ep446 ep446 ep60 ep446 886353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1210502656) qz288 0 1 ep446 ep59 ep446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1210502656) qz289 0 1 ep446 ep60 ep446 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz408 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297068945) qz17)

noncomputable def ep448 := @Enclosure.Real.IsNear.cos_image qz120 qz408 Bool.false 297068945 1048576 791 1048576 Bool.false 886353 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 63795070174009869289 225179981368524800 1249937500663386829 1658550000000000000000 297068945 1048576 791 1048576 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 297068945 1048576) (BSN.cos_reduce0 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85181551762276498800640) qz20) 226375608064910080 72057594037927936 Bool.false 886353 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 297068945 1048576 226375608064910080 72057594037927936 45 85181551762276498800640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 886353 1048576 85181551762276498800640 151115727451828646838272 1210502656 2147483648 265628 265368 (ep447 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep449 := BSN.sin_dyadic_bound_f 1210502656 2147483648 2 1 1048576 265628 ep446 ep63 ep446 ep446 ep64 ep446 560258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1210502656) qz292 0 1 ep446 ep63 ep446 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1210502656) qz293 0 1 ep446 ep64 ep446 rfl rfl rfl rfl) rfl rfl

noncomputable def ep450 := @Enclosure.Real.IsNear.sin_image qz120 qz408 Bool.false 297068945 1048576 791 1048576 Bool.false 560258 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz120 Bool.false 63795070174009869289 225179981368524800 1249937500663386829 1658550000000000000000 297068945 1048576 791 1048576 (ep445 rfl) rfl) (Enclosure.sfrac_false_div 297068945 1048576) (BSN.sin_reduce0 qz408 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85181551762276498800640) qz20) 226375608064910080 72057594037927936 Bool.false 560258 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 297068945 1048576 226375608064910080 72057594037927936 45 85181551762276498800640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 560258 1048576 85181551762276498800640 151115727451828646838272 1210502656 2147483648 265628 265368 (ep449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz409 := (@Enclosure.Real.IsNear.recentre' qz119 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep443 rfl rfl) rfl)

noncomputable def ep451 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz120)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120))) Bool.false 225414635901 1099511627776 6768931214153 36471900204957696 Bool.true 71241566893 549755813888 1689528579227 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz120) 254317 1048576 1 1048576 886353 1048576 26500405 34782314496 225414635901 1099511627776 6768931214153 36471900204957696 qz409 (@Enclosure.Real.IsNear.recentre' (Real.cos qz120) Bool.false 886353 1048576 106001620 139129257984 886353 1048576 26500405 34782314496 (ep448 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz120)) 254317 1048576 1 1048576 280129 524288 26500405 34782314496 71241566893 549755813888 1689528579227 9117975051239424 qz409 (@Enclosure.Real.IsNear.neg (Real.sin qz120) Bool.false 280129 524288 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz120) Bool.false 560258 1048576 106001620 139129257984 280129 524288 26500405 34782314496 (ep450 rfl rfl) rfl)) rfl)

noncomputable def ep452 := @ep440 225414635901 1099511627776 6768931214153 36471900204957696 Bool.true 71241566893 549755813888 1689528579227 9117975051239424 Bool.false ep441 342961758871 137438953472 82329629667173 18235950102478848 Bool.true 143686583856677777309696 261364373467 1099511627776 164439827430763 36471900204957696 EMRow30.d7 (ep442 ep451) rfl rfl

noncomputable abbrev qz410 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz121 := (@Inv.inv Real Real.instInv (Real.sqrt qz410))

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz122 := (@HMul.hMul Real Real Real qz268 qz285 qz411)

noncomputable def ep453 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)))) Bool.false 32394328721 137438953472 274350422737 1519662508539904 Bool.false 996265681 1099511627776 2183253936287 12157300068319232 (BSN.cpow_neg_s_mk qz14 99995 1000 18 qz15 rfl)

noncomputable abbrev qz412 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz16)

noncomputable def ep454 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz410) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz410) (Real.sqrt qz412) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz412) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep455 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 132684 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep456 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz411 99995 1000 0 1 3254268794313975 1125899906842624 62500000033171 8292750000000000000 2603284864699407441 9007199254740992 1249937500663386829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 54597570484265130393600 18889465931478580854784 1000000000530736 132684000000000000000 3254268794313975 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep457 := nat_lit 8262432222890305884326189225268336343980595333127261363706435008325014000247040

noncomputable def ep458 := nat_lit 16439303626513672083064287468776843422214876343003942458476342702771641262336

noncomputable def ep459 := nat_lit 21613087425507874227957915315039051725837020834587487664774558562189596867174656

noncomputable def ep460 := BSN.sin_dyadic_bound_f 3365002778 2147483648 3 2 1048576 265628 ep457 ep73 ep458 ep459 ep76 ep458 1048568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3365002778) qz292 0 2 ep457 ep73 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3365002778) qz293 0 2 ep459 ep76 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303062245) qz17)

noncomputable def ep461 := @Enclosure.Real.IsNear.cos_image qz122 qz413 Bool.false 303062245 1048576 791 1048576 Bool.false 1048568 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 2603284864699407441 9007199254740992 1249937500663386829 1658550000000000000000 303062245 1048576 791 1048576 (ep456 rfl) rfl) (Enclosure.sfrac_false_div 303062245 1048576) (BSN.cos_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236791019650490040320000) qz20) 226375608064910080 72057594037927936 Bool.false 1048568 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 303062245 1048576 226375608064910080 72057594037927936 45 236791019650490040320000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048568 1048576 236791019650490040320000 151115727451828646838272 3365002778 2147483648 265628 265368 (ep460 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep462 := nat_lit 4597546480995287123329244808468532121510204019000924732040675601381795174031616

noncomputable def ep463 := nat_lit 13759760835732834025821605850468042677686182304316766311205074118739842239570176

noncomputable def ep464 := BSN.cos_dyadic_bound_f 3365002778 2147483648 3 2 1048576 265628 ep462 ep80 ep458 ep463 ep82 ep458 4031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3365002778) qz288 0 2 ep462 ep80 ep458 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3365002778) qz289 0 2 ep463 ep82 ep458 rfl rfl rfl rfl) rfl rfl

noncomputable def ep465 := @Enclosure.Real.IsNear.sin_image qz122 qz413 Bool.false 303062245 1048576 791 1048576 Bool.true 4031 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz122 Bool.false 2603284864699407441 9007199254740992 1249937500663386829 1658550000000000000000 303062245 1048576 791 1048576 (ep456 rfl) rfl) (Enclosure.sfrac_false_div 303062245 1048576) (BSN.sin_reduce3 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236791019650490040320000) qz20) 226375608064910080 72057594037927936 Bool.false 4031 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 303062245 1048576 226375608064910080 72057594037927936 45 236791019650490040320000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4031 1048576 236791019650490040320000 151115727451828646838272 3365002778 2147483648 265628 265368 (ep464 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz121 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep454 rfl rfl) rfl)

noncomputable def ep466 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz122)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122))) Bool.false 32394328721 137438953472 274350422737 1519662508539904 Bool.false 996265681 1099511627776 2183253936287 12157300068319232 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz122) 247151 1048576 1 1048576 131071 131072 26500405 34782314496 32394328721 137438953472 274350422737 1519662508539904 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz122) Bool.false 1048568 1048576 106001620 139129257984 131071 131072 26500405 34782314496 (ep461 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz121 (@Neg.neg Real Real.instNeg (Real.sin qz122)) 247151 1048576 1 1048576 4031 1048576 26500405 34782314496 996265681 1099511627776 2183253936287 12157300068319232 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz122) Bool.true 4031 1048576 26500405 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz122) Bool.true 4031 1048576 106001620 139129257984 4031 1048576 26500405 34782314496 (ep465 rfl rfl) rfl)) rfl)

noncomputable def ep467 := @ep438 32394328721 137438953472 274350422737 1519662508539904 Bool.false 996265681 1099511627776 2183253936287 12157300068319232 Bool.false 51588547857988844519424 46919510949 17179869184 85621834740017 18235950102478848 Bool.true 286277762012741879463936 130184053893 549755813888 21373698654953 4558987525619712 (ep439 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep452 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep453 ep466) rfl rfl

noncomputable abbrev qz415 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz123 := (@Inv.inv Real Real.instInv (Real.sqrt qz415))

noncomputable abbrev qz416 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz268 qz285 qz416)

noncomputable def ep468 := @Enclosure.Complex.IsNear.of_eq qz116 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.false 10038286511 68719476736 400316507819 2279493762809856 Bool.false 97250546371 549755813888 3204868528279 18235950102478848 (BSN.cpow_neg_s_mk qz14 99995 1000 19 qz15 rfl)

noncomputable abbrev qz417 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz16)

noncomputable def ep469 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz415) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz415) (Real.sqrt qz417) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz417) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep470 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 132684 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep471 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz416 99995 1000 0 1 3315143513283831 1125899906842624 62500000033171 8292750000000000000 66299555122163336169 225179981368524800 1249937500663386829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz417) Bool.false 55618878793361701994496 18889465931478580854784 1000000000530736 132684000000000000000 3315143513283831 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep470 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep472 := nat_lit 4827936983383764795979851924016772161

noncomputable def ep473 := BSN.sin_dyadic_bound_f 1482314641 2147483648 2 1 1048576 265628 ep472 ep63 ep472 ep472 ep64 ep472 667664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1482314641) qz292 0 1 ep472 ep63 ep472 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1482314641) qz293 0 1 ep472 ep64 ep472 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz418 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 308731361) qz17)

noncomputable def ep474 := @Enclosure.Real.IsNear.cos_image qz124 qz418 Bool.false 308731361 1048576 99 131072 Bool.false 667664 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 66299555122163336169 225179981368524800 1249937500663386829 1658550000000000000000 308731361 1048576 99 131072 (ep471 rfl) rfl) (Enclosure.sfrac_false_div 308731361 1048576) (BSN.cos_reduce3 qz418 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104308619805249169784832) qz20) 226375608064910080 72057594037927936 Bool.false 667664 1048576 46 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 308731361 1048576 226375608064910080 72057594037927936 46 104308619805249169784832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 667664 1048576 104308619805249169784832 151115727451828646838272 1482314641 2147483648 265628 265368 (ep473 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep475 := nat_lit 172523800500866643710384153985766494970113194936657974033652025958461702633601

noncomputable def ep476 := nat_lit 23308975515524726791716429072282017828214874608855114234451256833384609921

noncomputable def ep477 := nat_lit 517524783551568881677569029099154920874683155060756211872487175361718338680961

noncomputable def ep478 := BSN.cos_dyadic_bound_f 1482314641 2147483648 3 2 1048576 265628 ep475 ep80 ep476 ep477 ep82 ep476 808538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1482314641) qz288 0 2 ep475 ep80 ep476 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1482314641) qz289 0 2 ep477 ep82 ep476 rfl rfl rfl rfl) rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.sin_image qz124 qz418 Bool.false 308731361 1048576 99 131072 Bool.true 808538 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 66299555122163336169 225179981368524800 1249937500663386829 1658550000000000000000 308731361 1048576 99 131072 (ep471 rfl) rfl) (Enclosure.sfrac_false_div 308731361 1048576) (BSN.sin_reduce3 qz418 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104308619805249169784832) qz20) 226375608064910080 72057594037927936 Bool.false 808538 1048576 46 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 308731361 1048576 226375608064910080 72057594037927936 46 104308619805249169784832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 808538 1048576 104308619805249169784832 151115727451828646838272 1482314641 2147483648 265628 265368 (ep478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz419 := (@Enclosure.Real.IsNear.recentre' qz123 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep469 rfl rfl) rfl)

noncomputable def ep480 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.false 10038286511 68719476736 400316507819 2279493762809856 Bool.false 97250546371 549755813888 3204868528279 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz124) 240559 1048576 1 1048576 41729 65536 3316697 4347789312 10038286511 68719476736 400316507819 2279493762809856 qz419 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.false 667664 1048576 13266788 17391157248 41729 65536 3316697 4347789312 (ep474 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 240559 1048576 1 1048576 404269 524288 3316697 4347789312 97250546371 549755813888 3204868528279 18235950102478848 qz419 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.true 404269 524288 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.true 808538 1048576 13266788 17391157248 404269 524288 3316697 4347789312 (ep479 rfl rfl) rfl)) rfl)

noncomputable def ep481 := @ep436 10038286511 68719476736 400316507819 2279493762809856 Bool.false 97250546371 549755813888 3204868528279 18235950102478848 Bool.false 3396740690214794559488 197716330307 68719476736 29608122267523 6078650034159616 Bool.true 18105387231943680065536 16466753761 274877906944 29566554382697 6078650034159616 (ep437 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep467 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep468 ep480) rfl rfl

noncomputable def ep482 := @Enclosure.Complex.IsNear.mul qz111 (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true 123302835228480166231151 ep294 ep429 ep296 Bool.false

noncomputable abbrev qz125 := (Complex.re qz402)

noncomputable abbrev qz126 := (Complex.im qz402)

noncomputable def ep483 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 5291818576774430462603 105545200046658803466240 299996900532215860298837

noncomputable def ep484 := nat_lit 3501039830747719169778647040

noncomputable def ep485 := nat_lit 2638630001166470086656000

noncomputable def ep486 := nat_lit 3250633810222682804699303

noncomputable def ep487 := nat_lit 87525995768692979244466176000

noncomputable def ep488 := nat_lit 26028044821020295193311816975426239351729684480

noncomputable def ep489 := @Enclosure.Real.IsNear.mulLit_tf qz125 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 55008068683 549755813888 3118445931157 18235950102478848 96200770241

noncomputable abbrev qz420 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz420))

noncomputable abbrev qz421 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz527 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz128 := (Real.cos qz421)

noncomputable abbrev qz129 := (Real.sin qz421)

noncomputable abbrev qz422 := (@Neg.neg Real Real.instNeg qz129)

noncomputable def ep490 := @Enclosure.Complex.IsNear.of_eq qz111 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz422)) Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (BSN.cpow_neg_s_mk qz14 99995 1000 20 qz15 rfl)

noncomputable abbrev qz423 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz16)

noncomputable def ep491 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz420) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz420) (Real.sqrt qz423) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz423) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep492 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 132684 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz424 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz130 := qz424

noncomputable abbrev qz425 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz16))

noncomputable def ep493 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz130 99995 1000 0 1 3372893643545847 1125899906842624 62500000033171 8292750000000000000 67454499977273394153 225179981368524800 1249937500663386829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz425 Bool.false 56587765202795681021952 18889465931478580854784 1000000000530736 132684000000000000000 3372893643545847 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep492 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep494 := nat_lit 1141552193233618004134629081577993187532075966817937212781666569417513806570081

noncomputable def ep495 := nat_lit 1018962962483632078497518456385335775856927891583201043967361177837803119201

noncomputable def ep496 := nat_lit 3422618653775886748246892207821208891044514044670645236257064985896865813471841

noncomputable def ep497 := BSN.cos_dyadic_bound_f 2376948651 2147483648 3 2 1048576 265628 ep494 ep80 ep495 ep496 ep82 ep495 469214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2376948651) qz288 0 2 ep494 ep80 ep495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2376948651) qz289 0 2 ep496 ep82 ep495 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz131 := qz421

noncomputable abbrev qz426 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78527373) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep498 := @Enclosure.Real.IsNear.cos_image qz131 qz426 Bool.false 78527373 262144 99 131072 Bool.true 469214 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 67454499977273394153 225179981368524800 1249937500663386829 1658550000000000000000 78527373 262144 99 131072 (ep493 rfl) rfl) (Enclosure.sfrac_false_div 78527373 262144) (BSN.cos_reduce2 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41815722890006632595456) qz427) 226375608064910080 72057594037927936 Bool.false 469214 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 78527373 262144 226375608064910080 72057594037927936 47 41815722890006632595456 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 469214 1048576 41815722890006632595456 37778931862957161709568 2376948651 2147483648 265628 265368 (ep497 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep499 := nat_lit 2053978777450525501779534332075279468937051197959020422171825936009254609330785

noncomputable def ep500 := nat_lit 5377818477097831386057403458886822351198032397115823542093120771450596105101921

noncomputable def ep501 := BSN.sin_dyadic_bound_f 2376948651 2147483648 3 2 1048576 265628 ep499 ep73 ep495 ep500 ep76 ep495 937736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2376948651) qz292 0 2 ep499 ep73 ep495 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2376948651) qz293 0 2 ep500 ep76 ep495 rfl rfl rfl rfl) rfl rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.sin_image qz131 qz426 Bool.false 78527373 262144 99 131072 Bool.true 937736 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 67454499977273394153 225179981368524800 1249937500663386829 1658550000000000000000 78527373 262144 99 131072 (ep493 rfl) rfl) (Enclosure.sfrac_false_div 78527373 262144) (BSN.sin_reduce2 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41815722890006632595456) qz427) 226375608064910080 72057594037927936 Bool.false 937736 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 78527373 262144 226375608064910080 72057594037927936 47 41815722890006632595456 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 937736 1048576 41815722890006632595456 37778931862957161709568 2376948651 2147483648 265628 265368 (ep501 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz428 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep491 rfl rfl) rfl)

noncomputable def ep503 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 qz128) (@HMul.hMul Real Real Real qz0 qz127 qz422) Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (@Enclosure.Real.IsNear.mulLit_ft qz127 qz128 234469 1048576 1 1048576 234607 524288 3316697 4347789312 55008068683 549755813888 3118445931157 18235950102478848 qz428 (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 469214 1048576 13266788 17391157248 234607 524288 3316697 4347789312 (ep498 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 qz422 234469 1048576 1 1048576 117217 131072 3316697 4347789312 27483752773 137438953472 781554150697 4558987525619712 qz428 (@Enclosure.Real.IsNear.neg qz129 Bool.true 117217 131072 3316697 4347789312 (@Enclosure.Real.IsNear.recentre' qz129 Bool.true 937736 1048576 13266788 17391157248 117217 131072 3316697 4347789312 (ep502 rfl rfl) rfl)) rfl)

noncomputable def ep504 := @ep489 191985600480 0 1 5291818576774430462603 105545200046658803466240 299996900532215860298837 ep484 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (ep490 ep503))

noncomputable def ep505 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 96200770241 191985600480 0 1 Bool.false

noncomputable def ep506 := @Enclosure.Complex.IsNear.addLitP qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 399170001 799940002 0 1 Bool.true 79996000

noncomputable def ep507 := @ep506 399970001 0 1 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1 Bool.false 192401540482 96200770241 191985600480 0 1 Bool.false 4159192049999 4159192049999 19198560048000 0 1

noncomputable abbrev qz132 := (@HDiv.hDiv Complex Complex Complex qz375 qz403 (@HSub.hSub Complex Complex Complex qz367 qz273 (1 : Complex)))

noncomputable def ep508 := @Enclosure.Complex.IsNear.addLitP qz132 qz89 Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1

noncomputable def ep509 := @Enclosure.Complex.IsNear.of_eq qz132 (Complex.mk (Enclosure.sfrac Bool.true 40000000 39997000100) (Enclosure.sfrac Bool.true 7999600000 39997000100)) Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1

noncomputable def ep510 := @ep508 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 39917000100 399170001 799940002 0 1 Bool.true 7999600000 79996000 399970001 0 1 (ep509 (BSN.N_div_s_sub_one_mk qz14 99995 1000 20 qz15 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 39997000100) (Enclosure.sfrac Bool.true 7999600000 39997000100) Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 39997000100) (Enclosure.Real.IsNear.const Bool.true 7999600000 39997000100))) qz90 rfl

noncomputable abbrev qz133 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz134 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz404 qz403 1))

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz134)) Bool.false 1 480 0 1

noncomputable def ep512 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz134) Bool.false 0 1 0 1 Bool.false

noncomputable def ep513 := @ep512 0 1 0 1 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1 Bool.false 1 1 480 0 1 Bool.false 19999 19999 48000 0

noncomputable def ep514 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false

noncomputable def ep515 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz134 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1

noncomputable def ep516 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz134)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz134)) 1 480 0 1 0 1 0

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz134) 1 24 0 1 1 20 0 1 1

noncomputable def ep518 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep520 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz11) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow30.d8 rfl) qz392

noncomputable def ep521 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep522 := ep521 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz84 qz14) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_crit_mk qz14 Bool.false 99995 1000 qz15) (@Enclosure.Complex.IsNear.mk qz84 qz14 Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 qz384 qz19))

noncomputable def ep523 := @ep519 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 99995 1000 0 1 0 1 0

noncomputable def ep525 := @ep524 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep526 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 19999 2400 0 1 0 1 0 1 19999

noncomputable def ep527 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 99995 1000 0 1 19999 2400 0

noncomputable def ep528 := @ep527 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep530 := @ep529 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep531 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 (@ep518 1 24 0 1 (ep523 rfl) (ep525 rfl) rfl rfl) (@ep526 19999 2400 0 1 (ep528 rfl) (ep530 rfl) rfl rfl)

noncomputable def ep532 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 ep531

noncomputable abbrev qz135 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz404 qz403 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz283) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow30.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz283 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz295))

noncomputable def ep533 := @ep517 480 0 1 ep532 (@Enclosure.Complex.IsNear.re_isNear qz134 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz135)

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz134) 19999 2400 0 1 0 1 0 1 0

noncomputable def ep535 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 ep531

noncomputable def ep536 := @ep534 1 0 1 ep535 (@Enclosure.Complex.IsNear.im_isNear qz134 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz135)

noncomputable def ep537 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz134)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz134)) 0 1 0 1 19999 48000 0

noncomputable def ep538 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz134) 1 24 0 1 0 1 0 1 0

noncomputable def ep539 := @ep538 1 0 1 ep532 (@Enclosure.Complex.IsNear.im_isNear qz134 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz135)

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz134) 19999 2400 0 1 1 20 0 1 19999

noncomputable def ep541 := @ep540 48000 0 1 ep535 (@Enclosure.Complex.IsNear.re_isNear qz134 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz135)

noncomputable def ep542 := @ep513 1 (@ep514 0 1 0 1 (BSN.bern_sum_base qz5 20) qz105) (ep515 (@ep516 1 1 1 480 0 1 (ep533 rfl) (ep536 rfl) rfl rfl) (@ep537 1 19999 19999 48000 0 1 (ep539 rfl) (ep541 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep543 := ep507 (ep510 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep511 Bool.false 19999 48000 0 1 (BSN.bern_sum_succ qz5 20 0 1 1 rfl rfl) (ep542 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep544 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 27483752773 137438953472 781554150697 4558987525619712 4159192049999

noncomputable def ep545 := @ep544 19198560048000 0 1 114310206037599570897227 ep485 ep486 ep487 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (ep490 ep503))

noncomputable def ep546 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 96200770241 191985600480 0 1 Bool.false

noncomputable def ep547 := nat_lit 10554520004665880346624000

noncomputable def ep548 := nat_lit 12970215525219923255918843

noncomputable def ep549 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 228789121952132562081317 ep547 ep548

noncomputable def ep550 := nat_lit 875259957686929792444661760

noncomputable def ep551 := nat_lit 21868811153092136228043868895429914270346772480

noncomputable def ep552 := @Enclosure.Real.IsNear.mulLit_tf qz125 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 55008068683 549755813888 3118445931157 18235950102478848 4159192049999

noncomputable def ep553 := @ep552 19198560048000 0 1 228789121952132562081317 ep547 ep548 ep426 (@Enclosure.Complex.IsNear.re_isNear qz111 Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (ep490 ep503))

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff qz126 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz112 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz115 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 27483752773 137438953472 781554150697 4558987525619712 96200770241

noncomputable def ep555 := @ep554 191985600480 0 1 2643958185875819628293 26386300011664700866560 75186111282101987007977 ep550 (@Enclosure.Complex.IsNear.im_isNear qz111 Bool.true 55008068683 549755813888 3118445931157 18235950102478848 Bool.false 27483752773 137438953472 781554150697 4558987525619712 (ep490 ep503))

noncomputable abbrev qz429 := (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep556 := @ep482 276264717466065096411961 ep424 ep430 ep426 (@ep483 ep484 114310206037599570897227 ep485 ep486 ep487 ep488 123302835228480166231151 ep294 ep429 ep296 (ep504 (@ep505 4159192049999 19198560048000 0 1 qz429) rfl) (ep545 (@ep546 4159192049999 19198560048000 0 1 qz429) rfl) rfl rfl) (@ep549 ep426 2643958185875819628293 26386300011664700866560 75186111282101987007977 ep550 ep551 276264717466065096411961 ep424 ep430 ep426 (ep553 (@ep546 4159192049999 19198560048000 0 1 qz429) rfl) (ep555 (@ep505 4159192049999 19198560048000 0 1 qz429) rfl) rfl rfl)

noncomputable def ep557 := @ep433 ep425 ep426 (@ep434 6078650034159616 (BSN.head_sum_c_eq qz5 20) (ep435 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep481 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep556 rfl rfl rfl

noncomputable def ep558 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 20) Bool.false ep293 ep294 ep295 ep296 Bool.false 65506076881939536059961 ep424 ep425 ep426 (@ep427 ep296 Bool.false 65506076881939536059961 ep424 ep425 ep426 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep559 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) (Complex.im (zetaApproximant qz5 1 20)) 337 524288 10711009

noncomputable def ep560 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66)) Bool.false 674 1048576 42844036

noncomputable def ep561 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) qz371 Bool.false 92238237 1048576 315

noncomputable def ep562 := BSN.sin_dyadic_bound_f 1381512 2147483648 1 0 1048576 265628 0 1 1 0 1 1 674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1381512) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1381512) qz293 0 0 rfl) rfl rfl

noncomputable def ep563 := @ep561 1048576 Bool.false 674 1048576 1 132684 (@ep300 92238237 1048576 315 1048576 ep421 rfl) (Enclosure.sfrac_false_div 92238237 1048576) (BSN.sin_reduce0 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97215313183384797184) qz20) 226375608064910080 72057594037927936 Bool.false 674 1048576 14 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 92238237 1048576 226375608064910080 72057594037927936 14 97215313183384797184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 674 1048576 97215313183384797184 151115727451828646838272 1381512 2147483648 265628 265368 (ep562 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep564 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 20) Bool.false ep293 ep294 ep295 ep296 Bool.false 65506076881939536059961 ep424 ep425 ep426 (@ep427 ep296 Bool.false 65506076881939536059961 ep424 ep425 ep426 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep557 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow30.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz14) Bool.false ep278 ep279 ep280 ep281 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz14) ep282 Bool.false ep278 ep279 ep280 ep281 (@Eq.refl Real ep282) (@ep283 Bool.false ep278 ep279 ep280 ep281 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz64 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz65 (@Nat.cast Complex Complex.instNatCast j))))) qz66) (zetaApproximant qz5 1 20)) (@ep285 ep286 ep287 ep288 ep289 ep279 ep290 ep281 ep291 ep278 ep279 ep280 ep281 (@ep292 34782314496 ep293 ep294 ep295 ep296 ep284 ep286 ep287 ep288 (@ep297 139129257984 1048575 1048576 10711009 34782314496 (ep423 rfl rfl) rfl) ep558 rfl) (@ep559 34782314496 65506076881939536059961 ep424 ep425 ep426 ep289 ep279 ep290 ep281 (@ep560 139129257984 337 524288 10711009 34782314496 (ep563 rfl rfl) rfl) ep564 rfl) rfl rfl))

noncomputable abbrev qz553 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 102256 1000)))

noncomputable abbrev qz537 := qz553

noncomputable abbrev qz430 := qz537

noncomputable abbrev qz136 := (BSN.headSumC qz430 9)

noncomputable abbrev qz137 := qz430

noncomputable abbrev qz538 := (@Neg.neg Complex Complex.instNeg qz553)

noncomputable abbrev qz431 := qz538

noncomputable abbrev qz138 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 8) qz431)

noncomputable def ep565 := @Enclosure.Complex.IsNear.of_eq qz136 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 8) qz138) Bool.false 662496782227 549755813888 3997955663011 1519662508539904 Bool.true 33937459585 137438953472 16002079468011 6078650034159616

noncomputable def ep566 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 8) qz138 Bool.false 1112650407029 1099511627776 28628713571705 12157300068319232 Bool.true 149278783103 274877906944 14322924418401 6078650034159616 Bool.false

noncomputable def ep567 := nat_lit 1456845830845541912674304

noncomputable abbrev qz139 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 7) qz431)

noncomputable def ep568 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 7) qz139) Bool.false 1112650407029 1099511627776 28628713571705 12157300068319232 Bool.true 149278783103 274877906944 14322924418401 6078650034159616

noncomputable def ep569 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 7) qz139 Bool.false 1315637767579 1099511627776 75129714343903 36471900204957696 Bool.true 59984036307 68719476736 9395969832671 4558987525619712 Bool.true

noncomputable abbrev qz140 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 6) qz431)

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 6) qz140) Bool.false 1315637767579 1099511627776 75129714343903 36471900204957696 Bool.true 59984036307 68719476736 9395969832671 4558987525619712

noncomputable def ep571 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 6) qz140 Bool.false 268815604855 274877906944 5292599800681 3039325017079808 Bool.true 580657938225 1099511627776 21179497820055 12157300068319232 Bool.false

noncomputable abbrev qz141 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 5) qz431)

noncomputable def ep572 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 5) qz141) Bool.false 268815604855 274877906944 5292599800681 3039325017079808 Bool.true 580657938225 1099511627776 21179497820055 12157300068319232

noncomputable def ep573 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 5) qz141 Bool.false 451223471279 549755813888 12697983437293 9117975051239424 Bool.true 120310926191 1099511627776 50798890603489 36471900204957696 Bool.false

noncomputable abbrev qz142 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 4) qz431)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 4) qz142) Bool.false 451223471279 549755813888 12697983437293 9117975051239424 Bool.true 120310926191 1099511627776 50798890603489 36471900204957696

noncomputable def ep575 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 4) qz142 Bool.false 1411927553391 1099511627776 36552814364279 36471900204957696 Bool.true 81713054245 274877906944 1143091806889 1139746881404928 Bool.true

noncomputable abbrev qz143 := (@HPow.hPow Complex Complex Complex qz275 qz281 qz431)

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 3) qz143) Bool.false 1411927553391 1099511627776 36552814364279 36471900204957696 Bool.true 81713054245 274877906944 1143091806889 1139746881404928

noncomputable def ep577 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 3) qz143 Bool.false 475394550483 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 274877906944 1679193848623 3039325017079808 Bool.false

noncomputable abbrev qz144 := (@HPow.hPow Complex Complex Complex qz275 qz282 qz431)

noncomputable def ep578 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 2) qz144) Bool.false 475394550483 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 274877906944 1679193848623 3039325017079808

noncomputable def ep579 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 2) qz144 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep580 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz11) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz137)

noncomputable abbrev qz554 := (Enclosure.sfrac Bool.false 102256 1000)

noncomputable abbrev qz539 := qz554

noncomputable abbrev qz432 := qz539

noncomputable abbrev qz145 := (@HMul.hMul Real Real Real qz268 qz432 (Real.log qz286))

noncomputable abbrev qz146 := qz432

noncomputable abbrev qz433 := (@Eq.refl Real qz539)

noncomputable abbrev qz147 := qz433

noncomputable def ep581 := @Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk (@HMul.hMul Real Real Real qz0 qz12 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz12 (@Neg.neg Real Real.instNeg (Real.sin qz145)))) Bool.true 74361263405 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 274877906944 1679193848623 3039325017079808 (BSN.cpow_neg_s_mk qz146 102256 1000 2 qz147 rfl)

noncomputable def ep582 := nat_lit 29189716367770463968293383701528576

noncomputable def ep583 := BSN.sin_dyadic_bound_f 413340032 2147483648 2 1 1048576 265628 ep582 ep63 ep582 ep582 ep64 ep582 200582 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 413340032) qz292 0 1 ep582 ep63 ep582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 413340032) qz293 0 1 ep582 ep64 ep582 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz148 := (Enclosure.Real.IsNear.const Bool.false 102256 1000)

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4645081) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep584 := @Enclosure.Real.IsNear.cos_image qz145 qz434 Bool.false 4645081 65536 405 524288 Bool.true 200582 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 145158783 2048000 6391 8292750 4645081 65536 405 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz18 102256 1000 0 1 363408 524288 1 132684 145158783 2048000 6391 8292750 qz148 qz291 rfl) rfl) (Enclosure.sfrac_false_div 4645081 65536) (BSN.cos_reduce1 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1817888686197054636032) qz435) 226375608064910080 72057594037927936 Bool.false 200582 1048576 11 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 4645081 65536 226375608064910080 72057594037927936 11 1817888686197054636032 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 200582 1048576 1817888686197054636032 9444732965739290427392 413340032 2147483648 265628 265368 (ep583 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep585 := BSN.cos_dyadic_bound_f 413340032 2147483648 2 1 1048576 265628 ep582 ep59 ep582 ep582 ep60 ep582 1029212 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 413340032) qz288 0 1 ep582 ep59 ep582 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 413340032) qz289 0 1 ep582 ep60 ep582 rfl rfl rfl rfl) rfl rfl

noncomputable def ep586 := @Enclosure.Real.IsNear.sin_image qz145 qz434 Bool.false 4645081 65536 405 524288 Bool.false 1029212 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz145 Bool.false 145158783 2048000 6391 8292750 4645081 65536 405 524288 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz18 102256 1000 0 1 363408 524288 1 132684 145158783 2048000 6391 8292750 qz148 qz291 rfl) rfl) (Enclosure.sfrac_false_div 4645081 65536) (BSN.sin_reduce1 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1817888686197054636032) qz435) 226375608064910080 72057594037927936 Bool.false 1029212 1048576 11 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 4645081 65536 226375608064910080 72057594037927936 11 1817888686197054636032 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1029212 1048576 1817888686197054636032 9444732965739290427392 413340032 2147483648 265628 265368 (ep585 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep587 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz12 (Real.cos qz145)) (@HMul.hMul Real Real Real qz0 qz12 (@Neg.neg Real Real.instNeg (Real.sin qz145))) Bool.true 74361263405 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 274877906944 1679193848623 3039325017079808 (@Enclosure.Real.IsNear.mulLit_ft qz12 (Real.cos qz145) 741455 1048576 1 1048576 100291 524288 13565327 17391157248 74361263405 549755813888 3353806616291 6078650034159616 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz145) Bool.true 200582 1048576 54261308 69564628992 100291 524288 13565327 17391157248 (ep584 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz12 (@Neg.neg Real Real.instNeg (Real.sin qz145)) 741455 1048576 1 1048576 257303 262144 13565327 17391157248 190778595865 274877906944 1679193848623 3039325017079808 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz145) Bool.false 257303 262144 13565327 17391157248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz145) Bool.false 1029212 1048576 54261308 69564628992 257303 262144 13565327 17391157248 (ep586 rfl rfl) rfl)) rfl)

noncomputable def ep588 := @ep579 74361263405 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 274877906944 1679193848623 3039325017079808 Bool.false 475394550483 475394550483 549755813888 3353806616291 6078650034159616 Bool.true 190778595865 190778595865 274877906944 1679193848623 3039325017079808 (ep580 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz11 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep581 ep587) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz268 qz432 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.false 461138452425 1099511627776 16429974666533 36471900204957696 Bool.false 27266385405 68719476736 4107152909243 9117975051239424 (BSN.cpow_neg_s_mk qz146 102256 1000 3 qz147 rfl)

noncomputable def ep590 := nat_lit 9296527135887191270152707341724160000

noncomputable def ep591 := BSN.sin_dyadic_bound_f 1746144520 2147483648 2 1 1048576 265628 ep590 ep63 ep590 ep590 ep64 ep590 761715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1746144520) qz292 0 1 ep590 ep63 ep590 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1746144520) qz293 0 1 ep590 ep64 ep590 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58898331) qz61)

noncomputable def ep592 := @Enclosure.Real.IsNear.cos_image qz149 qz436 Bool.false 58898331 524288 809 1048576 Bool.false 761715 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 3681145699 32768000 6391 8292750 58898331 524288 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz24 102256 1000 0 1 575989 524288 1 132684 3681145699 32768000 6391 8292750 qz148 qz298 rfl) rfl) (Enclosure.sfrac_false_div 58898331 524288) (BSN.cos_reduce3 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61436998538386359713792) qz364) 226375608064910080 72057594037927936 Bool.false 761715 1048576 17 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 58898331 524288 226375608064910080 72057594037927936 17 61436998538386359713792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 761715 1048576 61436998538386359713792 75557863725914323419136 1746144520 2147483648 265628 265368 (ep591 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep593 := nat_lit 332248072500953055813680243947781827846245124420789947129821522010623180800000

noncomputable def ep594 := nat_lit 86425416788286903659606627141939916391071682532382859377641527705600000000

noncomputable def ep595 := nat_lit 996571366669282593633721518589061603705953229897305075670709282976458342400000

noncomputable def ep596 := BSN.cos_dyadic_bound_f 1746144520 2147483648 3 2 1048576 265628 ep593 ep80 ep594 ep595 ep82 ep594 720624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1746144520) qz288 0 2 ep593 ep80 ep594 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1746144520) qz289 0 2 ep595 ep82 ep594 rfl rfl rfl rfl) rfl rfl

noncomputable def ep597 := @Enclosure.Real.IsNear.sin_image qz149 qz436 Bool.false 58898331 524288 809 1048576 Bool.true 720624 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 3681145699 32768000 6391 8292750 58898331 524288 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz24 102256 1000 0 1 575989 524288 1 132684 3681145699 32768000 6391 8292750 qz148 qz298 rfl) rfl) (Enclosure.sfrac_false_div 58898331 524288) (BSN.sin_reduce3 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61436998538386359713792) qz364) 226375608064910080 72057594037927936 Bool.false 720624 1048576 17 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 58898331 524288 226375608064910080 72057594037927936 17 61436998538386359713792 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 720624 1048576 61436998538386359713792 75557863725914323419136 1746144520 2147483648 265628 265368 (ep596 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep598 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.false 461138452425 1099511627776 16429974666533 36471900204957696 Bool.false 27266385405 68719476736 4107152909243 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz149) 605395 1048576 1 1048576 761715 1048576 27097483 34782314496 461138452425 1099511627776 16429974666533 36471900204957696 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.false 761715 1048576 108389932 139129257984 761715 1048576 27097483 34782314496 (ep592 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 605395 1048576 1 1048576 45039 65536 27097483 34782314496 27266385405 68719476736 4107152909243 9117975051239424 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 45039 65536 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 720624 1048576 108389932 139129257984 45039 65536 27097483 34782314496 (ep597 rfl rfl) rfl)) rfl)

noncomputable def ep599 := @ep577 461138452425 1099511627776 16429974666533 36471900204957696 Bool.false 27266385405 68719476736 4107152909243 9117975051239424 Bool.false 776215381265361779294208 1411927553391 1099511627776 36552814364279 36471900204957696 Bool.true 5615278330216783544320 81713054245 274877906944 1143091806889 1139746881404928 (ep578 (BSN.head_sum_c_succ qz137 2 3 rfl rfl) (ep588 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep589 ep598) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz268 qz432 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq qz142 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 509480610833 1099511627776 14239119384893 36471900204957696 Bool.false 206541290789 1099511627776 14219952783041 36471900204957696 (BSN.cpow_neg_s_mk qz146 102256 1000 4 qz147 rfl)

noncomputable def ep601 := nat_lit 467989579688398448495749397443772416

noncomputable def ep602 := BSN.cos_dyadic_bound_f 827101952 2147483648 2 1 1048576 265628 ep601 ep59 ep601 ep601 ep60 ep601 971759 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 827101952) qz288 0 1 ep601 ep59 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 827101952) qz289 0 1 ep601 ep60 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74321399) qz61)

noncomputable def ep603 := @Enclosure.Real.IsNear.cos_image qz150 qz437 Bool.false 74321399 524288 809 1048576 Bool.true 971759 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 4645087447 32768000 6391 8292750 74321399 524288 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz27 102256 1000 0 1 726817 524288 1 132684 4645087447 32768000 6391 8292750 qz148 qz303 rfl) rfl) (Enclosure.sfrac_false_div 74321399 524288) (BSN.cos_reduce2 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29101062843524687331328) qz364) 226375608064910080 72057594037927936 Bool.false 971759 1048576 22 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 74321399 524288 226375608064910080 72057594037927936 22 29101062843524687331328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 971759 1048576 29101062843524687331328 75557863725914323419136 827101952 2147483648 265628 265368 (ep602 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep604 := BSN.sin_dyadic_bound_f 827101952 2147483648 2 1 1048576 265628 ep601 ep63 ep601 ep601 ep64 ep601 393947 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 827101952) qz292 0 1 ep601 ep63 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 827101952) qz293 0 1 ep601 ep64 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable def ep605 := @Enclosure.Real.IsNear.sin_image qz150 qz437 Bool.false 74321399 524288 809 1048576 Bool.true 393947 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 4645087447 32768000 6391 8292750 74321399 524288 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz27 102256 1000 0 1 726817 524288 1 132684 4645087447 32768000 6391 8292750 qz148 qz303 rfl) rfl) (Enclosure.sfrac_false_div 74321399 524288) (BSN.sin_reduce2 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29101062843524687331328) qz364) 226375608064910080 72057594037927936 Bool.false 393947 1048576 22 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 74321399 524288 226375608064910080 72057594037927936 22 29101062843524687331328 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 393947 1048576 29101062843524687331328 75557863725914323419136 827101952 2147483648 265628 265368 (ep604 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep606 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 509480610833 1099511627776 14239119384893 36471900204957696 Bool.false 206541290789 1099511627776 14219952783041 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz150) 524287 1048576 1 1048576 971759 1048576 27097483 34782314496 509480610833 1099511627776 14239119384893 36471900204957696 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 971759 1048576 108389932 139129257984 971759 1048576 27097483 34782314496 (ep603 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 524287 1048576 1 1048576 393947 1048576 27097483 34782314496 206541290789 1099511627776 14219952783041 36471900204957696 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 393947 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 393947 1048576 108389932 139129257984 393947 1048576 27097483 34782314496 (ep605 rfl rfl) rfl)) rfl)

noncomputable def ep607 := @ep575 509480610833 1099511627776 14239119384893 36471900204957696 Bool.false 206541290789 1099511627776 14219952783041 36471900204957696 Bool.false 992250906793420949291008 451223471279 549755813888 12697983437293 9117975051239424 Bool.true 33070815573876150370304 120310926191 1099511627776 50798890603489 36471900204957696 (ep576 (BSN.head_sum_c_succ qz137 3 4 rfl rfl) (ep599 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep600 ep606) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz268 qz432 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.false 86407738431 549755813888 1589907982375 4558987525619712 Bool.true 230173506017 549755813888 3184900714169 9117975051239424 (BSN.cpow_neg_s_mk qz146 102256 1000 5 qz147 rfl)

noncomputable def ep609 := nat_lit 1640008682680863242593990498625678074972406028512140090061213848492315568800000

noncomputable def ep610 := nat_lit 2101459903646524644265829711200583960576568244468838246653242815760100000000

noncomputable def ep611 := nat_lit 4915823128235296678493439836454633056996064949047482593690335059845426506400000

noncomputable def ep612 := BSN.cos_dyadic_bound_f 2602047010 2147483648 3 2 1048576 265628 ep609 ep80 ep610 ep611 ep82 ep610 368526 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2602047010) qz288 0 2 ep609 ep80 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2602047010) qz289 0 2 ep611 ep82 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172568861) qz17)

noncomputable def ep613 := @Enclosure.Real.IsNear.cos_image qz151 qz438 Bool.false 172568861 1048576 809 1048576 Bool.false 368526 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 168524279 1024000 6391 8292750 172568861 1048576 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz30 102256 1000 0 1 843808 524288 1 132684 168524279 1024000 6391 8292750 qz148 qz307 rfl) rfl) (Enclosure.sfrac_false_div 172568861 1048576) (BSN.cos_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183102780415029618409472) qz20) 226375608064910080 72057594037927936 Bool.false 368526 1048576 26 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 172568861 1048576 226375608064910080 72057594037927936 26 183102780415029618409472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 368526 1048576 183102780415029618409472 151115727451828646838272 2602047010 2147483648 265628 265368 (ep612 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep614 := nat_lit 2950334460902636616953770233757260067781869596726277091512862333033559943840000

noncomputable def ep615 := nat_lit 7723664081567668194978682126022308755873486880934919025372438955290950167200000

noncomputable def ep616 := BSN.sin_dyadic_bound_f 2602047010 2147483648 3 2 1048576 265628 ep614 ep73 ep610 ep615 ep76 ep610 981682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2602047010) qz292 0 2 ep614 ep73 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2602047010) qz293 0 2 ep615 ep76 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.sin_image qz151 qz438 Bool.false 172568861 1048576 809 1048576 Bool.false 981682 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 168524279 1024000 6391 8292750 172568861 1048576 809 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz146 qz30 102256 1000 0 1 843808 524288 1 132684 168524279 1024000 6391 8292750 qz148 qz307 rfl) rfl) (Enclosure.sfrac_false_div 172568861 1048576) (BSN.sin_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183102780415029618409472) qz20) 226375608064910080 72057594037927936 Bool.false 981682 1048576 26 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 172568861 1048576 226375608064910080 72057594037927936 26 183102780415029618409472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 981682 1048576 183102780415029618409472 151115727451828646838272 2602047010 2147483648 265628 265368 (ep616 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep618 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.false 86407738431 549755813888 1589907982375 4558987525619712 Bool.true 230173506017 549755813888 3184900714169 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz151) 468937 1048576 1 1048576 184263 524288 27097483 34782314496 86407738431 549755813888 1589907982375 4558987525619712 qz308 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.false 368526 1048576 108389932 139129257984 184263 524288 27097483 34782314496 (ep613 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 468937 1048576 1 1048576 490841 524288 27097483 34782314496 230173506017 549755813888 3184900714169 9117975051239424 qz308 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 490841 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 981682 1048576 108389932 139129257984 490841 524288 27097483 34782314496 (ep617 rfl rfl) rfl)) rfl)

noncomputable def ep619 := @ep573 86407738431 549755813888 1589907982375 4558987525619712 Bool.true 230173506017 549755813888 3184900714169 9117975051239424 Bool.false 295565883265711058452480 268815604855 274877906944 5292599800681 3039325017079808 Bool.true 319220077419412901068800 580657938225 1099511627776 21179497820055 12157300068319232 (ep574 (BSN.head_sum_c_succ qz137 4 5 rfl rfl) (ep607 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep608 ep618) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz268 qz432 qz310)

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.false 240375348159 1099511627776 11618516735731 36471900204957696 Bool.true 379086642687 1099511627776 11629265201203 36471900204957696 (BSN.cpow_neg_s_mk qz146 102256 1000 6 qz147 rfl)

noncomputable def ep621 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz310 102256 1000 0 1 4034681531866359 2251799813685248 125000000033171 16585500000000000000 25785649670157900369 140737488355328000 798875000211995861 1036593750000000000000 qz148 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 125000000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz311) Bool.false 33845361775666394038272 18889465931478580854784 1000000000265368 132684000000000000000 4034681531866359 2251799813685248 125000000033171 16585500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep622 := nat_lit 777791500472948840047972759308484616800509043743883901227999193517354769186816

noncomputable def ep623 := nat_lit 473304006293943985054067670254318866285271788456923589867223887976423489536

noncomputable def ep624 := nat_lit 2332427893406258632173810142584945212668956587654737856504263132776111460581376

noncomputable def ep625 := BSN.cos_dyadic_bound_f 2159695496 2147483648 3 2 1048576 265628 ep622 ep80 ep623 ep624 ep82 ep623 561521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2159695496) qz288 0 2 ep622 ep80 ep623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2159695496) qz289 0 2 ep624 ep82 ep623 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 192118061) qz17)

noncomputable def ep626 := @Enclosure.Real.IsNear.cos_image qz152 qz439 Bool.false 192118061 1048576 809 1048576 Bool.false 561521 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 25785649670157900369 140737488355328000 798875000211995861 1036593750000000000000 192118061 1048576 809 1048576 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 192118061 1048576) (BSN.cos_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151975059920297406758912) qz20) 226375608064910080 72057594037927936 Bool.false 561521 1048576 29 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 192118061 1048576 226375608064910080 72057594037927936 29 151975059920297406758912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 561521 1048576 151975059920297406758912 151115727451828646838272 2159695496 2147483648 265628 265368 (ep625 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep627 := nat_lit 1399646057646272756898307712619068855147888061308225483338504769220857445744640

noncomputable def ep628 := nat_lit 3664973373063381311138813613964768580556197339578326961026775080712188624633856

noncomputable def ep629 := BSN.sin_dyadic_bound_f 2159695496 2147483648 3 2 1048576 265628 ep627 ep73 ep623 ep628 ep76 ep623 885553 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2159695496) qz292 0 2 ep627 ep73 ep623 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2159695496) qz293 0 2 ep628 ep76 ep623 rfl rfl rfl rfl) rfl rfl

noncomputable def ep630 := @Enclosure.Real.IsNear.sin_image qz152 qz439 Bool.false 192118061 1048576 809 1048576 Bool.false 885553 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 25785649670157900369 140737488355328000 798875000211995861 1036593750000000000000 192118061 1048576 809 1048576 (ep621 rfl) rfl) (Enclosure.sfrac_false_div 192118061 1048576) (BSN.sin_reduce0 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151975059920297406758912) qz20) 226375608064910080 72057594037927936 Bool.false 885553 1048576 29 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 192118061 1048576 226375608064910080 72057594037927936 29 151975059920297406758912 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 885553 1048576 151975059920297406758912 151115727451828646838272 2159695496 2147483648 265628 265368 (ep629 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep631 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz31 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz31 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.false 240375348159 1099511627776 11618516735731 36471900204957696 Bool.true 379086642687 1099511627776 11629265201203 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz31 (Real.cos qz152) 428079 1048576 1 1048576 561521 1048576 27097483 34782314496 240375348159 1099511627776 11618516735731 36471900204957696 qz313 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.false 561521 1048576 108389932 139129257984 561521 1048576 27097483 34782314496 (ep626 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz31 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 428079 1048576 1 1048576 885553 1048576 27097483 34782314496 379086642687 1099511627776 11629265201203 36471900204957696 qz313 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 885553 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 885553 1048576 108389932 139129257984 885553 1048576 27097483 34782314496 (ep630 rfl rfl) rfl)) rfl)

noncomputable def ep632 := @ep571 240375348159 1099511627776 11618516735731 36471900204957696 Bool.true 379086642687 1099511627776 11629265201203 36471900204957696 Bool.false 361639755848592262168576 1315637767579 1099511627776 75129714343903 36471900204957696 Bool.true 1055250326407748058611712 59984036307 68719476736 9395969832671 4558987525619712 (ep572 (BSN.head_sum_c_succ qz137 5 6 rfl rfl) (ep619 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep620 ep631) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz432 qz315)

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq qz139 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 101493680275 549755813888 2689106592803 9117975051239424 Bool.false 90657362125 274877906944 5384893924519 18235950102478848 (BSN.cpow_neg_s_mk qz146 102256 1000 7 qz147 rfl)

noncomputable def ep634 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz315 102256 1000 0 1 4381796493761783 2251799813685248 125000000033171 16585500000000000000 28004061391631555153 140737488355328000 798875000211995861 1036593750000000000000 qz148 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 125000000033171 16585500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz316) Bool.false 36757173121942042968064 18889465931478580854784 1000000000265368 132684000000000000000 4381796493761783 2251799813685248 125000000033171 16585500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep129 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep635 := nat_lit 961823446659465448232615308418799100826006029925618268729652187819084025390625

noncomputable def ep636 := nat_lit 723568340876383569509468763044767896911140409074176501328225561676025390625

noncomputable def ep637 := nat_lit 2884023203296643577558826987730307766684195808958706453186300112333900025390625

noncomputable def ep638 := BSN.cos_dyadic_bound_f 2277377075 2147483648 3 2 1048576 265628 ep635 ep80 ep636 ep637 ep82 ep636 512174 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2277377075) qz288 0 2 ep635 ep80 ep636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2277377075) qz289 0 2 ep637 ep82 ep636 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52161629) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep639 := @Enclosure.Real.IsNear.cos_image qz153 qz440 Bool.false 52161629 262144 809 1048576 Bool.true 512174 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 28004061391631555153 140737488355328000 798875000211995861 1036593750000000000000 52161629 262144 809 1048576 (ep634 rfl) rfl) (Enclosure.sfrac_false_div 52161629 262144) (BSN.cos_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40064041206476563283968) qz427) 226375608064910080 72057594037927936 Bool.false 512174 1048576 31 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 52161629 262144 226375608064910080 72057594037927936 31 40064041206476563283968 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 512174 1048576 40064041206476563283968 37778931862957161709568 2277377075 2147483648 265628 265368 (ep638 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep640 := nat_lit 1730703349314336699963099980143402567169281941538853542512311357625010425390625

noncomputable def ep641 := nat_lit 4531622994699939116981294141425886623134072762415639182720569761918028025390625

noncomputable def ep642 := BSN.sin_dyadic_bound_f 2277377075 2147483648 3 2 1048576 265628 ep640 ep73 ep636 ep641 ep76 ep636 914980 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2277377075) qz292 0 2 ep640 ep73 ep636 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2277377075) qz293 0 2 ep641 ep76 ep636 rfl rfl rfl rfl) rfl rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.sin_image qz153 qz440 Bool.false 52161629 262144 809 1048576 Bool.true 914980 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 28004061391631555153 140737488355328000 798875000211995861 1036593750000000000000 52161629 262144 809 1048576 (ep634 rfl) rfl) (Enclosure.sfrac_false_div 52161629 262144) (BSN.sin_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40064041206476563283968) qz427) 226375608064910080 72057594037927936 Bool.false 914980 1048576 31 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 52161629 262144 226375608064910080 72057594037927936 31 40064041206476563283968 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 914980 1048576 40064041206476563283968 37778931862957161709568 2277377075 2147483648 265628 265368 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 101493680275 549755813888 2689106592803 9117975051239424 Bool.false 90657362125 274877906944 5384893924519 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz153) 396325 1048576 1 1048576 256087 524288 27097483 34782314496 101493680275 549755813888 2689106592803 9117975051239424 qz318 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 512174 1048576 108389932 139129257984 256087 524288 27097483 34782314496 (ep639 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 396325 1048576 1 1048576 228745 262144 27097483 34782314496 90657362125 274877906944 5384893924519 18235950102478848 qz318 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.true 228745 262144 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.true 914980 1048576 108389932 139129257984 228745 262144 27097483 34782314496 (ep643 rfl rfl) rfl)) rfl)

noncomputable def ep645 := @ep569 101493680275 549755813888 2689106592803 9117975051239424 Bool.false 90657362125 274877906944 5384893924519 18235950102478848 Bool.false 611686030089042371018752 1112650407029 1099511627776 28628713571705 12157300068319232 Bool.true 10258359862624998391808 149278783103 274877906944 14322924418401 6078650034159616 (ep570 (BSN.head_sum_c_succ qz137 6 7 rfl rfl) (ep632 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep633 ep644) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz432 qz320)

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 212343157425 1099511627776 3354931732383 12157300068319232 Bool.false 81403863933 274877906944 839577524805 3039325017079808 (BSN.cpow_neg_s_mk qz146 102256 1000 8 qz147 rfl)

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz320 102256 1000 0 1 9364972152248037 4503599627370496 250000000099513 33171000000000000000 59851537025017204467 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz321) Bool.false 39279540158062550581248 18889465931478580854784 1000000000398052 132684000000000000000 9364972152248037 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep648 := nat_lit 2371591647791413824459374706353504256

noncomputable def ep649 := BSN.sin_dyadic_bound_f 1240966272 2147483648 2 1 1048576 265628 ep648 ep63 ep648 ep648 ep64 ep648 572775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1240966272) qz292 0 1 ep648 ep63 ep648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1240966272) qz293 0 1 ep648 ep64 ep648 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111482175) qz61)

noncomputable def ep650 := @Enclosure.Real.IsNear.cos_image qz154 qz441 Bool.false 111482175 524288 809 1048576 Bool.false 572775 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 59851537025017204467 281474976710656000 1597750000635987583 2073187500000000000000 111482175 524288 809 1048576 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 111482175 524288) (BSN.cos_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43662619077174833971200) qz364) 226375608064910080 72057594037927936 Bool.false 572775 1048576 33 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 111482175 524288 226375608064910080 72057594037927936 33 43662619077174833971200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 572775 1048576 43662619077174833971200 75557863725914323419136 1240966272 2147483648 265628 265368 (ep649 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep651 := BSN.cos_dyadic_bound_f 1240966272 2147483648 2 1 1048576 265628 ep648 ep59 ep648 ep648 ep60 ep648 878316 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1240966272) qz288 0 1 ep648 ep59 ep648 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1240966272) qz289 0 1 ep648 ep60 ep648 rfl rfl rfl rfl) rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.sin_image qz154 qz441 Bool.false 111482175 524288 809 1048576 Bool.true 878316 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 59851537025017204467 281474976710656000 1597750000635987583 2073187500000000000000 111482175 524288 809 1048576 (ep647 rfl) rfl) (Enclosure.sfrac_false_div 111482175 524288) (BSN.sin_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43662619077174833971200) qz364) 226375608064910080 72057594037927936 Bool.false 878316 1048576 33 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 111482175 524288 226375608064910080 72057594037927936 33 43662619077174833971200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 878316 1048576 43662619077174833971200 75557863725914323419136 1240966272 2147483648 265628 265368 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep653 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 212343157425 1099511627776 3354931732383 12157300068319232 Bool.false 81403863933 274877906944 839577524805 3039325017079808 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz154) 370727 1048576 1 1048576 572775 1048576 27097483 34782314496 212343157425 1099511627776 3354931732383 12157300068319232 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 572775 1048576 108389932 139129257984 572775 1048576 27097483 34782314496 (ep650 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 370727 1048576 1 1048576 219579 262144 27097483 34782314496 81403863933 274877906944 839577524805 3039325017079808 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 219579 262144 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 878316 1048576 108389932 139129257984 219579 262144 27097483 34782314496 (ep652 rfl rfl) rfl)) rfl)

noncomputable def ep654 := @ep566 212343157425 1099511627776 3354931732383 12157300068319232 Bool.false 81403863933 274877906944 839577524805 3039325017079808 Bool.false ep567 662496782227 549755813888 3997955663011 1519662508539904 Bool.true 18657315715442781716480 33937459585 137438953472 16002079468011 6078650034159616 (ep568 (BSN.head_sum_c_succ qz137 7 8 rfl rfl) (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep646 ep653) rfl rfl

theorem EMRow30.d11 : Enclosure.Complex.IsNear qz136 Bool.false 662496782227 549755813888 3997955663011 1519662508539904 Bool.true 33937459585 137438953472 16002079468011 6078650034159616 := ep565 (BSN.head_sum_c_succ qz137 8 9 rfl rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz155 := (BSN.headSumC qz430 17)

noncomputable abbrev qz156 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz431)

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz155 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 16) qz156) Bool.false 438285926375 274877906944 80642491141537 18235950102478848 Bool.true 49282991443 1099511627776 161296431817631 36471900204957696

noncomputable def ep656 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 16) qz156 Bool.false 1555901283011 1099511627776 154156581076189 36471900204957696 Bool.false 35541386615 274877906944 38542190939047 9117975051239424 Bool.false

noncomputable def ep657 := nat_lit 1927601889359553363968000

noncomputable abbrev qz157 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz431)

noncomputable def ep658 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 15) qz157) Bool.false 1555901283011 1099511627776 154156581076189 36471900204957696 Bool.false 35541386615 274877906944 38542190939047 9117975051239424

noncomputable def ep659 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 15) qz157 Bool.false 1300771750553 1099511627776 48929632013335 12157300068319232 Bool.false 133339936921 549755813888 3058689200095 759831254269952 Bool.false

noncomputable abbrev qz158 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz431)

noncomputable def ep660 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 14) qz158) Bool.false 1300771750553 1099511627776 48929632013335 12157300068319232 Bool.false 133339936921 549755813888 3058689200095 759831254269952

noncomputable def ep661 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 14) qz158 Bool.false 510810148519 549755813888 69580973607599 18235950102478848 Bool.false 174888240893 1099511627776 139212309649855 36471900204957696 Bool.false

noncomputable abbrev qz159 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz431)

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 13) qz159) Bool.false 510810148519 549755813888 69580973607599 18235950102478848 Bool.false 174888240893 1099511627776 139212309649855 36471900204957696

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 13) qz159 Bool.false 1034334206129 1099511627776 43759966227533 12157300068319232 Bool.true 129796546579 1099511627776 43765653063773 12157300068319232 Bool.true

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz431)

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 12) qz160) Bool.false 1034334206129 1099511627776 43759966227533 12157300068319232 Bool.true 129796546579 1099511627776 43765653063773 12157300068319232

noncomputable def ep665 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 12) qz160 Bool.false 1329969285119 1099511627776 123045147652895 36471900204957696 Bool.true 14284344409 1099511627776 123081946896875 36471900204957696 Bool.true

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz431)

noncomputable def ep666 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 11) qz161) Bool.false 1329969285119 1099511627776 123045147652895 36471900204957696 Bool.true 14284344409 1099511627776 123081946896875 36471900204957696

noncomputable def ep667 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 11) qz161 Bool.false 62651381055 68719476736 28610923892741 9117975051239424 Bool.false 4606084459 137438953472 57254748010609 18235950102478848 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz431)

noncomputable def ep668 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 10) qz162) Bool.false 62651381055 68719476736 28610923892741 9117975051239424 Bool.false 4606084459 137438953472 57254748010609 18235950102478848

noncomputable def ep669 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 10) qz162 Bool.false 1345315297479 1099511627776 105424139350433 36471900204957696 Bool.false 47219858185 549755813888 52759240213813 18235950102478848 Bool.true

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 9) qz431)

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 10) (@HAdd.hAdd Complex Complex Complex qz4 qz136 qz163) Bool.false 1345315297479 1099511627776 105424139350433 36471900204957696 Bool.false 47219858185 549755813888 52759240213813 18235950102478848

noncomputable def ep671 := @Enclosure.Complex.IsNear.addLitP qz136 qz163 Bool.false 662496782227 549755813888 3997955663011 1519662508539904 Bool.true 33937459585 137438953472 16002079468011 6078650034159616 Bool.false

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz268 qz432 qz326)

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 20321733025 1099511627776 9473203438169 36471900204957696 Bool.false 182969696525 549755813888 1188250452445 4558987525619712 (BSN.cpow_neg_s_mk qz146 102256 1000 9 qz147 rfl)

noncomputable def ep673 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz326 102256 1000 0 1 9895417793173221 4503599627370496 250000000099513 33171000000000000000 63241615116170055411 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 41504390431577613533184 18889465931478580854784 1000000000398052 132684000000000000000 9895417793173221 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep173 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep674 := BSN.sin_dyadic_bound_f 119134063 2147483648 1 0 1048576 265628 0 1 1 0 1 1 58141 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 119134063) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 119134063) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235593375) qz17)

noncomputable def ep675 := @Enclosure.Real.IsNear.cos_image qz164 qz442 Bool.false 235593375 1048576 809 1048576 Bool.false 58141 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 63241615116170055411 281474976710656000 1597750000635987583 2073187500000000000000 235593375 1048576 809 1048576 (ep673 rfl) rfl) (Enclosure.sfrac_false_div 235593375 1048576) (BSN.cos_reduce3 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383314425866155458560) qz20) 226375608064910080 72057594037927936 Bool.false 58141 1048576 35 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 235593375 1048576 226375608064910080 72057594037927936 35 8383314425866155458560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 58141 1048576 8383314425866155458560 151115727451828646838272 119134063 2147483648 265628 265368 (ep674 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep676 := BSN.cos_dyadic_bound_f 119134063 2147483648 1 0 1048576 265628 0 1 1 0 1 1 1046962 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 119134063) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 119134063) qz289 0 0 rfl) rfl rfl

noncomputable def ep677 := @Enclosure.Real.IsNear.sin_image qz164 qz442 Bool.false 235593375 1048576 809 1048576 Bool.true 1046962 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 63241615116170055411 281474976710656000 1597750000635987583 2073187500000000000000 235593375 1048576 809 1048576 (ep673 rfl) rfl) (Enclosure.sfrac_false_div 235593375 1048576) (BSN.sin_reduce3 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383314425866155458560) qz20) 226375608064910080 72057594037927936 Bool.false 1046962 1048576 35 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 235593375 1048576 226375608064910080 72057594037927936 35 8383314425866155458560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046962 1048576 8383314425866155458560 151115727451828646838272 119134063 2147483648 265628 265368 (ep676 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep678 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 20321733025 1099511627776 9473203438169 36471900204957696 Bool.false 182969696525 549755813888 1188250452445 4558987525619712 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz164) 349525 1048576 1 1048576 58141 1048576 27097483 34782314496 20321733025 1099511627776 9473203438169 36471900204957696 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 58141 1048576 108389932 139129257984 58141 1048576 27097483 34782314496 (ep675 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz45 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 349525 1048576 1 1048576 523481 524288 27097483 34782314496 182969696525 549755813888 1188250452445 4558987525619712 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.true 523481 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.true 1046962 1048576 108389932 139129257984 523481 524288 27097483 34782314496 (ep677 rfl rfl) rfl)) rfl)

noncomputable def ep679 := @ep671 20321733025 1099511627776 9473203438169 36471900204957696 Bool.false 182969696525 549755813888 1188250452445 4558987525619712 Bool.false 739594906301544479588352 1345315297479 1099511627776 105424139350433 36471900204957696 Bool.false 6489847892042653368320 47219858185 549755813888 52759240213813 18235950102478848 EMRow30.d11 (ep672 ep678) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz268 qz432 qz331)

noncomputable def ep680 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 342893200599 1099511627776 3006518740177 12157300068319232 Bool.true 28795520349 549755813888 374625649733 1519662508539904 (BSN.cpow_neg_s_mk qz146 102256 1000 10 qz147 rfl)

noncomputable def ep681 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz331 102256 1000 0 1 10369917190100709 4503599627370496 250000000099513 33171000000000000000 66274140761933631219 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz332) Bool.false 43494585150108164161536 18889465931478580854784 1000000000398052 132684000000000000000 10369917190100709 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep188 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep682 := nat_lit 5327627327613706024046405595076219545977695331958510337640292460762586196640000

noncomputable def ep683 := nat_lit 6844607526116510852589562820467981387713314624468464858352114797584100000000

noncomputable def ep684 := nat_lit 13942227922041231902550679171109341126742428121927911465001529211372589591200000

noncomputable def ep685 := BSN.sin_dyadic_bound_f 3015911330 2147483648 3 2 1048576 265628 ep682 ep73 ep683 ep684 ep76 ep683 1034091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3015911330) qz292 0 2 ep682 ep73 ep683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3015911330) qz293 0 2 ep684 ep76 ep683 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 246890413) qz17)

noncomputable def ep686 := @Enclosure.Real.IsNear.cos_image qz165 qz443 Bool.false 246890413 1048576 809 1048576 Bool.true 1034091 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 66274140761933631219 281474976710656000 1597750000635987583 2073187500000000000000 246890413 1048576 809 1048576 (ep681 rfl) rfl) (Enclosure.sfrac_false_div 246890413 1048576) (BSN.cos_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212225892882329911689216) qz20) 226375608064910080 72057594037927936 Bool.false 1034091 1048576 37 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 246890413 1048576 226375608064910080 72057594037927936 37 212225892882329911689216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1034091 1048576 212225892882329911689216 151115727451828646838272 3015911330 2147483648 265628 265368 (ep685 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep687 := nat_lit 2962835007574777351515820691851441072826592213143380616403874529222585264800000

noncomputable def ep688 := nat_lit 8874815807672099032842282949913387255704350010181204919494919358072587594400000

noncomputable def ep689 := BSN.cos_dyadic_bound_f 3015911330 2147483648 3 2 1048576 265628 ep687 ep80 ep683 ep688 ep82 ep683 173682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3015911330) qz288 0 2 ep687 ep80 ep683 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3015911330) qz289 0 2 ep688 ep82 ep683 rfl rfl rfl rfl) rfl rfl

noncomputable def ep690 := @Enclosure.Real.IsNear.sin_image qz165 qz443 Bool.false 246890413 1048576 809 1048576 Bool.false 173682 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 66274140761933631219 281474976710656000 1597750000635987583 2073187500000000000000 246890413 1048576 809 1048576 (ep681 rfl) rfl) (Enclosure.sfrac_false_div 246890413 1048576) (BSN.sin_reduce1 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212225892882329911689216) qz20) 226375608064910080 72057594037927936 Bool.false 173682 1048576 37 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 246890413 1048576 226375608064910080 72057594037927936 37 212225892882329911689216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 173682 1048576 212225892882329911689216 151115727451828646838272 3015911330 2147483648 265628 265368 (ep689 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep691 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 342893200599 1099511627776 3006518740177 12157300068319232 Bool.true 28795520349 549755813888 374625649733 1519662508539904 (@Enclosure.Real.IsNear.mulLit_ft qz47 (Real.cos qz165) 331589 1048576 1 1048576 1034091 1048576 27097483 34782314496 342893200599 1099511627776 3006518740177 12157300068319232 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 1034091 1048576 108389932 139129257984 1034091 1048576 27097483 34782314496 (ep686 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz47 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 331589 1048576 1 1048576 86841 524288 27097483 34782314496 28795520349 549755813888 374625649733 1519662508539904 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 86841 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 173682 1048576 108389932 139129257984 86841 524288 27097483 34782314496 (ep690 rfl rfl) rfl)) rfl)

noncomputable def ep692 := @ep669 342893200599 1099511627776 3006518740177 12157300068319232 Bool.true 28795520349 549755813888 374625649733 1519662508539904 Bool.false 1102174751459159970938880 62651381055 68719476736 28610923892741 9117975051239424 Bool.false 10128886842377652666368 4606084459 137438953472 57254748010609 18235950102478848 (ep670 (BSN.head_sum_c_succ qz137 9 10 rfl rfl) (ep679 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep680 ep691) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz268 qz432 qz336)

noncomputable def ep693 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 327547188239 1099511627776 2867150693977 12157300068319232 Bool.true 51133020081 1099511627776 2857483625219 12157300068319232 (BSN.cpow_neg_s_mk qz146 102256 1000 11 qz147 rfl)

noncomputable def ep694 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz336 102256 1000 0 1 10799156221662949 4503599627370496 250000000099513 33171000000000000000 69017407412647907059 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 45294944137145793642496 18889465931478580854784 1000000000398052 132684000000000000000 10799156221662949 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep203 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep695 := nat_lit 12231460200419063792426823237490321

noncomputable def ep696 := BSN.cos_dyadic_bound_f 332559667 2147483648 2 1 1048576 265628 ep695 ep59 ep695 ep695 ep60 ep695 1036027 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 332559667) qz288 0 1 ep695 ep59 ep695 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 332559667) qz289 0 1 ep695 ep60 ep695 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128554939) qz61)

noncomputable def ep697 := @Enclosure.Real.IsNear.cos_image qz166 qz444 Bool.false 128554939 524288 809 1048576 Bool.false 1036027 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 69017407412647907059 281474976710656000 1597750000635987583 2073187500000000000000 128554939 524288 809 1048576 (ep694 rfl) rfl) (Enclosure.sfrac_false_div 128554939 524288) (BSN.cos_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11700903088029138157568) qz364) 226375608064910080 72057594037927936 Bool.false 1036027 1048576 39 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 128554939 524288 226375608064910080 72057594037927936 39 11700903088029138157568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036027 1048576 11700903088029138157568 75557863725914323419136 332559667 2147483648 265628 265368 (ep696 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep698 := BSN.sin_dyadic_bound_f 332559667 2147483648 1 0 1048576 265628 0 1 1 0 1 1 161733 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 332559667) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 332559667) qz293 0 0 rfl) rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.sin_image qz166 qz444 Bool.false 128554939 524288 809 1048576 Bool.false 161733 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 69017407412647907059 281474976710656000 1597750000635987583 2073187500000000000000 128554939 524288 809 1048576 (ep694 rfl) rfl) (Enclosure.sfrac_false_div 128554939 524288) (BSN.sin_reduce0 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11700903088029138157568) qz364) 226375608064910080 72057594037927936 Bool.false 161733 1048576 39 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 128554939 524288 226375608064910080 72057594037927936 39 11700903088029138157568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161733 1048576 11700903088029138157568 75557863725914323419136 332559667 2147483648 265628 265368 (ep698 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep700 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 327547188239 1099511627776 2867150693977 12157300068319232 Bool.true 51133020081 1099511627776 2857483625219 12157300068319232 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz166) 316157 1048576 1 1048576 1036027 1048576 27097483 34782314496 327547188239 1099511627776 2867150693977 12157300068319232 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 1036027 1048576 108389932 139129257984 1036027 1048576 27097483 34782314496 (ep697 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 316157 1048576 1 1048576 161733 1048576 27097483 34782314496 51133020081 1099511627776 2857483625219 12157300068319232 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 161733 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 161733 1048576 108389932 139129257984 161733 1048576 27097483 34782314496 (ep699 rfl rfl) rfl)) rfl)

noncomputable def ep701 := @ep667 327547188239 1099511627776 2867150693977 12157300068319232 Bool.true 51133020081 1099511627776 2857483625219 12157300068319232 Bool.false 91394793348329671491584 1329969285119 1099511627776 123045147652895 36471900204957696 Bool.true 1963225346606574338048 14284344409 1099511627776 123081946896875 36471900204957696 (ep668 (BSN.head_sum_c_succ qz137 10 11 rfl rfl) (ep692 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep693 ep700) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz432 qz341)

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 147817539495 549755813888 1029343878713 4558987525619712 Bool.true 57756101085 549755813888 2053753073611 9117975051239424 (BSN.cpow_neg_s_mk qz146 102256 1000 12 qz147 rfl)

noncomputable def ep703 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz341 102256 1000 0 1 11191020447815397 4503599627370496 250000000099513 33171000000000000000 71521811681988202227 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz342) Bool.false 46938541828353910898688 18889465931478580854784 1000000000398052 132684000000000000000 11191020447815397 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep218 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep704 := nat_lit 2822236021400899672490978749235130520434163533902376606867894430830837104640000

noncomputable def ep705 := nat_lit 1923056788467146198452817687793967206796034961907229109287159601561600000000

noncomputable def ep706 := nat_lit 7388457011725790429345544543168913511373710913139327028000877631868711731200000

noncomputable def ep707 := BSN.sin_dyadic_bound_f 2573350920 2147483648 3 2 1048576 265628 ep704 ep73 ep705 ep706 ep76 ep705 976670 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2573350920) qz292 0 2 ep704 ep73 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2573350920) qz293 0 2 ep706 ep76 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 266439511) qz17)

noncomputable def ep708 := @Enclosure.Real.IsNear.cos_image qz167 qz445 Bool.false 266439511 1048576 809 1048576 Bool.true 976670 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 71521811681988202227 281474976710656000 1597750000635987583 2073187500000000000000 266439511 1048576 809 1048576 (ep703 rfl) rfl) (Enclosure.sfrac_false_div 266439511 1048576) (BSN.cos_reduce1 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181083472638413962739712) qz20) 226375608064910080 72057594037927936 Bool.false 976670 1048576 40 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 266439511 1048576 226375608064910080 72057594037927936 40 181083472638413962739712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 976670 1048576 181083472638413962739712 151115727451828646838272 2573350920 2147483648 265628 265368 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep709 := nat_lit 1568763592684262994138745001880758718999777978817723550086291199173381324800000

noncomputable def ep710 := nat_lit 4702444664475854690019329370266688222585741866529356192040299278317020774400000

noncomputable def ep711 := BSN.cos_dyadic_bound_f 2573350920 2147483648 3 2 1048576 265628 ep709 ep80 ep705 ep710 ep82 ep705 381610 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2573350920) qz288 0 2 ep709 ep80 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2573350920) qz289 0 2 ep710 ep82 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.sin_image qz167 qz445 Bool.false 266439511 1048576 809 1048576 Bool.false 381610 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 71521811681988202227 281474976710656000 1597750000635987583 2073187500000000000000 266439511 1048576 809 1048576 (ep703 rfl) rfl) (Enclosure.sfrac_false_div 266439511 1048576) (BSN.sin_reduce1 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 181083472638413962739712) qz20) 226375608064910080 72057594037927936 Bool.false 381610 1048576 40 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q1 266439511 1048576 226375608064910080 72057594037927936 40 181083472638413962739712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 381610 1048576 181083472638413962739712 151115727451828646838272 2573350920 2147483648 265628 265368 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep713 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 147817539495 549755813888 1029343878713 4558987525619712 Bool.true 57756101085 549755813888 2053753073611 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz167) 302697 1048576 1 1048576 488335 524288 27097483 34782314496 147817539495 549755813888 1029343878713 4558987525619712 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 976670 1048576 108389932 139129257984 488335 524288 27097483 34782314496 (ep708 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 302697 1048576 1 1048576 190805 524288 27097483 34782314496 57756101085 549755813888 2053753073611 9117975051239424 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 190805 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 381610 1048576 108389932 139129257984 190805 524288 27097483 34782314496 (ep712 rfl rfl) rfl)) rfl)

noncomputable def ep714 := @ep665 147817539495 549755813888 1029343878713 4558987525619712 Bool.true 57756101085 549755813888 2053753073611 9117975051239424 Bool.false 568631243322646752919552 1034334206129 1099511627776 43759966227533 12157300068319232 Bool.true 71356406104389847089152 129796546579 1099511627776 43765653063773 12157300068319232 (ep666 (BSN.head_sum_c_succ qz137 11 12 rfl rfl) (ep701 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep702 ep713) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz432 qz346)

noncomputable def ep715 := @Enclosure.Complex.IsNear.of_eq qz159 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 12713909091 1099511627776 7882048532599 36471900204957696 Bool.false 19042799217 68719476736 989418807317 4558987525619712 (BSN.cpow_neg_s_mk qz146 102256 1000 13 qz147 rfl)

noncomputable def ep716 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz346 102256 1000 0 1 11551497052968677 4503599627370496 250000000099513 33171000000000000000 73825617665522814707 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 48450490295254733815808 18889465931478580854784 1000000000398052 132684000000000000000 11551497052968677 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep717 := nat_lit 4167664112019485360395804777581893712070155206180657722003597143463166410260736

noncomputable def ep718 := nat_lit 13517802242367200352659080332336712779982149487432367265092089172652832358656

noncomputable def ep719 := nat_lit 12475956731573721680482096172081007710650501319567108431480607252044193566064896

noncomputable def ep720 := BSN.cos_dyadic_bound_f 3283698398 2147483648 3 2 1048576 265628 ep717 ep80 ep718 ep719 ep82 ep718 43717 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3283698398) qz288 0 2 ep717 ep80 ep718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3283698398) qz289 0 2 ep719 ep82 ep718 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 275021857) qz17)

noncomputable def ep721 := @Enclosure.Real.IsNear.cos_image qz168 qz446 Bool.false 275021857 1048576 809 1048576 Bool.true 43717 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 73825617665522814707 281474976710656000 1597750000635987583 2073187500000000000000 275021857 1048576 809 1048576 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 275021857 1048576) (BSN.cos_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231069732549127542145024) qz20) 226375608064910080 72057594037927936 Bool.false 43717 1048576 41 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 275021857 1048576 226375608064910080 72057594037927936 41 231069732549127542145024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 43717 1048576 231069732549127542145024 151115727451828646838272 3283698398 2147483648 265628 265368 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := nat_lit 7490981159841179888430321335381539311502293651535238005794401186895577272582400

noncomputable def ep723 := nat_lit 19597350405477352811984631653080248280862226559612637611032330202256502556754176

noncomputable def ep724 := BSN.sin_dyadic_bound_f 3283698398 2147483648 3 2 1048576 265628 ep722 ep73 ep718 ep723 ep76 ep718 1047664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3283698398) qz292 0 2 ep722 ep73 ep718 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3283698398) qz293 0 2 ep723 ep76 ep718 rfl rfl rfl rfl) rfl rfl

noncomputable def ep725 := @Enclosure.Real.IsNear.sin_image qz168 qz446 Bool.false 275021857 1048576 809 1048576 Bool.true 1047664 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 73825617665522814707 281474976710656000 1597750000635987583 2073187500000000000000 275021857 1048576 809 1048576 (ep716 rfl) rfl) (Enclosure.sfrac_false_div 275021857 1048576) (BSN.sin_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 231069732549127542145024) qz20) 226375608064910080 72057594037927936 Bool.false 1047664 1048576 41 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 275021857 1048576 226375608064910080 72057594037927936 41 231069732549127542145024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047664 1048576 231069732549127542145024 151115727451828646838272 3283698398 2147483648 265628 265368 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep726 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 12713909091 1099511627776 7882048532599 36471900204957696 Bool.false 19042799217 68719476736 989418807317 4558987525619712 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz168) 290823 1048576 1 1048576 43717 1048576 27097483 34782314496 12713909091 1099511627776 7882048532599 36471900204957696 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 43717 1048576 108389932 139129257984 43717 1048576 27097483 34782314496 (ep721 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 290823 1048576 1 1048576 65479 65536 27097483 34782314496 19042799217 68719476736 989418807317 4558987525619712 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 65479 65536 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 1047664 1048576 108389932 139129257984 65479 65536 27097483 34782314496 (ep725 rfl rfl) rfl)) rfl)

noncomputable def ep727 := @ep663 12713909091 1099511627776 7882048532599 36471900204957696 Bool.false 19042799217 68719476736 989418807317 4558987525619712 Bool.false 1123283395765252011327488 510810148519 549755813888 69580973607599 18235950102478848 Bool.false 12018228401446477365248 174888240893 1099511627776 139212309649855 36471900204957696 (ep664 (BSN.head_sum_c_succ qz137 12 13 rfl rfl) (ep714 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep715 ep726) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz432 qz351)

noncomputable def ep728 := @Enclosure.Complex.IsNear.of_eq qz158 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 279151453515 1099511627776 7626948824807 36471900204957696 Bool.false 91791632949 1099511627776 7604771954705 36471900204957696 (BSN.cpow_neg_s_mk qz146 102256 1000 14 qz147 rfl)

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz351 102256 1000 0 1 11885250371606245 4503599627370496 250000000099513 33171000000000000000 15191727024987102359 56294995342131200 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz352) Bool.false 49850353174629559828480 18889465931478580854784 1000000000398052 132684000000000000000 11885250371606245 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep240 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep730 := nat_lit 3375444739333423916618082582550530281337596435751253424975738859705549788785185

noncomputable def ep731 := nat_lit 2750119347361253976174804664269698539638369785720552949642801727628046740001

noncomputable def ep732 := nat_lit 8835997933596572989466885651509237891581909494933544741589418191669804037810721

noncomputable def ep733 := BSN.sin_dyadic_bound_f 2691032499 2147483648 3 2 1048576 265628 ep730 ep73 ep731 ep732 ep76 ep731 996105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2691032499) qz292 0 2 ep730 ep73 ep731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2691032499) qz293 0 2 ep732 ep76 ep731 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141483983) qz61)

noncomputable def ep734 := @Enclosure.Real.IsNear.cos_image qz169 qz447 Bool.false 141483983 524288 809 1048576 Bool.false 996105 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 15191727024987102359 56294995342131200 1597750000635987583 2073187500000000000000 141483983 524288 809 1048576 (ep729 rfl) rfl) (Enclosure.sfrac_false_div 141483983 524288) (BSN.cos_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94682288772011404558336) qz364) 226375608064910080 72057594037927936 Bool.false 996105 1048576 42 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 141483983 524288 226375608064910080 72057594037927936 42 94682288772011404558336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 996105 1048576 94682288772011404558336 75557863725914323419136 2691032499 2147483648 265628 265368 (ep733 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep735 := nat_lit 1876469352672951622110568014601081133427392850877683259630807278382029014542881

noncomputable def ep736 := nat_lit 5623907819324132358379354434474704003202901813061608672993136231690830950148641

noncomputable def ep737 := BSN.cos_dyadic_bound_f 2691032499 2147483648 3 2 1048576 265628 ep735 ep80 ep731 ep736 ep82 ep731 327543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2691032499) qz288 0 2 ep735 ep80 ep731 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2691032499) qz289 0 2 ep736 ep82 ep731 rfl rfl rfl rfl) rfl rfl

noncomputable def ep738 := @Enclosure.Real.IsNear.sin_image qz169 qz447 Bool.false 141483983 524288 809 1048576 Bool.true 327543 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 15191727024987102359 56294995342131200 1597750000635987583 2073187500000000000000 141483983 524288 809 1048576 (ep729 rfl) rfl) (Enclosure.sfrac_false_div 141483983 524288) (BSN.sin_reduce3 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94682288772011404558336) qz364) 226375608064910080 72057594037927936 Bool.false 327543 1048576 42 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 141483983 524288 226375608064910080 72057594037927936 42 94682288772011404558336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 327543 1048576 94682288772011404558336 75557863725914323419136 2691032499 2147483648 265628 265368 (ep737 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep739 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 279151453515 1099511627776 7626948824807 36471900204957696 Bool.false 91791632949 1099511627776 7604771954705 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz169) 280243 1048576 1 1048576 996105 1048576 27097483 34782314496 279151453515 1099511627776 7626948824807 36471900204957696 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 996105 1048576 108389932 139129257984 996105 1048576 27097483 34782314496 (ep734 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 280243 1048576 1 1048576 327543 1048576 27097483 34782314496 91791632949 1099511627776 7604771954705 36471900204957696 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 327543 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 327543 1048576 108389932 139129257984 327543 1048576 27097483 34782314496 (ep738 rfl rfl) rfl)) rfl)

noncomputable def ep740 := @ep661 279151453515 1099511627776 7626948824807 36471900204957696 Bool.false 91791632949 1099511627776 7604771954705 36471900204957696 Bool.false 715106832407783029080064 1300771750553 1099511627776 48929632013335 12157300068319232 Bool.false 293217622183115743035392 133339936921 549755813888 3058689200095 759831254269952 (ep662 (BSN.head_sum_c_succ qz137 13 14 rfl rfl) (ep727 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep728 ep739) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz432 qz356)

noncomputable def ep741 := @Enclosure.Complex.IsNear.of_eq qz157 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 127564766229 549755813888 920960629523 4558987525619712 Bool.true 62257163691 549755813888 1837920537907 9117975051239424 (BSN.cpow_neg_s_mk qz146 102256 1000 15 qz147 rfl)

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz356 102256 1000 0 1 12195965485668069 4503599627370496 250000000099513 33171000000000000000 77944415418904628979 281474976710656000 1597750000635987583 2073187500000000000000 qz148 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 250000000099513 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz357) Bool.false 51153586820399524478976 18889465931478580854784 1000000000398052 132684000000000000000 12195965485668069 4503599627370496 250000000099513 33171000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep743 := nat_lit 903823416209032742984860558785432481

noncomputable def ep744 := BSN.cos_dyadic_bound_f 975036553 2147483648 2 1 1048576 265628 ep743 ep59 ep743 ep743 ep60 ep743 942338 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 975036553) qz288 0 1 ep743 ep59 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 975036553) qz289 0 1 ep743 ep60 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145182787) qz61)

noncomputable def ep745 := @Enclosure.Real.IsNear.cos_image qz170 qz448 Bool.false 145182787 524288 809 1048576 Bool.false 942338 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 77944415418904628979 281474976710656000 1597750000635987583 2073187500000000000000 145182787 524288 809 1048576 (ep742 rfl) rfl) (Enclosure.sfrac_false_div 145182787 524288) (BSN.cos_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34306048882061527220224) qz364) 226375608064910080 72057594037927936 Bool.false 942338 1048576 44 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145182787 524288 226375608064910080 72057594037927936 44 34306048882061527220224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 942338 1048576 34306048882061527220224 75557863725914323419136 975036553 2147483648 265628 265368 (ep744 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep746 := BSN.sin_dyadic_bound_f 975036553 2147483648 2 1 1048576 265628 ep743 ep63 ep743 ep743 ep64 ep743 459902 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 975036553) qz292 0 1 ep743 ep63 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 975036553) qz293 0 1 ep743 ep64 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable def ep747 := @Enclosure.Real.IsNear.sin_image qz170 qz448 Bool.false 145182787 524288 809 1048576 Bool.false 459902 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 77944415418904628979 281474976710656000 1597750000635987583 2073187500000000000000 145182787 524288 809 1048576 (ep742 rfl) rfl) (Enclosure.sfrac_false_div 145182787 524288) (BSN.sin_reduce0 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34306048882061527220224) qz364) 226375608064910080 72057594037927936 Bool.false 459902 1048576 44 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 145182787 524288 226375608064910080 72057594037927936 44 34306048882061527220224 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 459902 1048576 34306048882061527220224 75557863725914323419136 975036553 2147483648 265628 265368 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep748 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 127564766229 549755813888 920960629523 4558987525619712 Bool.true 62257163691 549755813888 1837920537907 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz170) 270741 1048576 1 1048576 471169 524288 27097483 34782314496 127564766229 549755813888 920960629523 4558987525619712 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 942338 1048576 108389932 139129257984 471169 524288 27097483 34782314496 (ep745 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 270741 1048576 1 1048576 229951 524288 27097483 34782314496 62257163691 549755813888 1837920537907 9117975051239424 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 229951 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 459902 1048576 108389932 139129257984 229951 524288 27097483 34782314496 (ep747 rfl rfl) rfl)) rfl)

noncomputable def ep749 := @ep659 127564766229 549755813888 920960629523 4558987525619712 Bool.true 62257163691 549755813888 1837920537907 9117975051239424 Bool.false 855365776171095732256768 1555901283011 1099511627776 154156581076189 36471900204957696 Bool.false 39078167850474788618240 35541386615 274877906944 38542190939047 9117975051239424 (ep660 (BSN.head_sum_c_succ qz137 14 15 rfl rfl) (ep740 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep741 ep748) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz432 qz361)

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq qz156 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 197242422489 1099511627776 7128401206885 36471900204957696 Bool.true 191448537903 1099511627776 7127668061443 36471900204957696 (BSN.cpow_neg_s_mk qz146 102256 1000 16 qz147 rfl)

noncomputable def ep751 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz361 102256 1000 0 1 3121657384082679 1125899906842624 62500000033171 8292750000000000000 19950512341672401489 70368744177664000 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 52372720210750067441664 18889465931478580854784 1000000000530736 132684000000000000000 3121657384082679 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep266 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep752 := nat_lit 267864215875281711501220203342607517820491027743307099885933465637294929084416

noncomputable def ep753 := nat_lit 56181032603829604345808895991584612314655489397932405592802168806504923136

noncomputable def ep754 := nat_lit 803480285560637475294968992235839384236843772251125434846614792574271777406976

noncomputable def ep755 := BSN.cos_dyadic_bound_f 1654621696 2147483648 3 2 1048576 265628 ep752 ep80 ep753 ep754 ep82 ep753 752423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654621696) qz288 0 2 ep752 ep80 ep753 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654621696) qz289 0 2 ep754 ep82 ep753 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37160725) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep756 := @Enclosure.Real.IsNear.cos_image qz171 qz449 Bool.false 37160725 131072 809 1048576 Bool.false 752423 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 19950512341672401489 70368744177664000 399437500211995861 518296875000000000000 37160725 131072 809 1048576 (ep751 rfl) rfl) (Enclosure.sfrac_false_div 37160725 131072) (BSN.cos_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14554206359058277990400) qz299) 226375608064910080 72057594037927936 Bool.false 752423 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 37160725 131072 226375608064910080 72057594037927936 45 14554206359058277990400 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752423 1048576 14554206359058277990400 18889465931478580854784 1654621696 2147483648 265628 265368 (ep755 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep757 := nat_lit 7495400763390147395822221294154285056

noncomputable def ep758 := BSN.sin_dyadic_bound_f 1654621696 2147483648 2 1 1048576 265628 ep757 ep63 ep757 ep757 ep64 ep757 730321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654621696) qz292 0 1 ep757 ep63 ep757 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654621696) qz293 0 1 ep757 ep64 ep757 rfl rfl rfl rfl) rfl rfl

noncomputable def ep759 := @Enclosure.Real.IsNear.sin_image qz171 qz449 Bool.false 37160725 131072 809 1048576 Bool.false 730321 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 19950512341672401489 70368744177664000 399437500211995861 518296875000000000000 37160725 131072 809 1048576 (ep751 rfl) rfl) (Enclosure.sfrac_false_div 37160725 131072) (BSN.sin_reduce0 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14554206359058277990400) qz299) 226375608064910080 72057594037927936 Bool.false 730321 1048576 45 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 37160725 131072 226375608064910080 72057594037927936 45 14554206359058277990400 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730321 1048576 14554206359058277990400 18889465931478580854784 1654621696 2147483648 265628 265368 (ep758 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep760 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 197242422489 1099511627776 7128401206885 36471900204957696 Bool.true 191448537903 1099511627776 7127668061443 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz171) 262143 1048576 1 1048576 752423 1048576 27097483 34782314496 197242422489 1099511627776 7128401206885 36471900204957696 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 752423 1048576 108389932 139129257984 752423 1048576 27097483 34782314496 (ep756 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 262143 1048576 1 1048576 730321 1048576 27097483 34782314496 191448537903 1099511627776 7127668061443 36471900204957696 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 730321 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 730321 1048576 108389932 139129257984 730321 1048576 27097483 34782314496 (ep759 rfl rfl) rfl)) rfl)

noncomputable def ep761 := @ep656 197242422489 1099511627776 7128401206885 36471900204957696 Bool.true 191448537903 1099511627776 7127668061443 36471900204957696 Bool.false ep657 438285926375 274877906944 80642491141537 18235950102478848 Bool.true 13546805535790902280192 49282991443 1099511627776 161296431817631 36471900204957696 (ep658 (BSN.head_sum_c_succ qz137 15 16 rfl rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep750 ep760) rfl rfl

theorem EMRow30.d12 : Enclosure.Complex.IsNear qz155 Bool.false 438285926375 274877906944 80642491141537 18235950102478848 Bool.true 49282991443 1099511627776 161296431817631 36471900204957696 := ep655 (BSN.head_sum_c_succ qz137 16 17 rfl rfl) (ep761 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow30.d13 : @Eq Nat (Nat.pow 21 1) 21 := @Eq.refl Nat 21

noncomputable def ep762 := nat_lit 79101878356826229491110958027

noncomputable def ep763 := nat_lit 37673654046331567315143884800

noncomputable def ep764 := nat_lit 1727906935361598485493076473353228489

noncomputable def ep765 := nat_lit 290170270119379605593891865873717657600

noncomputable abbrev qz540 := (@HAdd.hAdd Complex Complex Complex qz547 (@HAdd.hAdd Complex Complex Complex qz547 qz550 (@HMul.hMul Complex Complex Complex qz549 Complex.I (@HDiv.hDiv Complex Complex Complex qz551 (↑qz554) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz450 := qz540

noncomputable abbrev qz172 := (Complex.Stirling.logGammaStirling 1 qz450)

noncomputable abbrev qz541 := (@HAdd.hAdd Complex Complex Complex qz547 qz550 (@HMul.hMul Complex Complex Complex qz549 Complex.I (@HDiv.hDiv Complex Complex Complex qz551 (↑qz554) (2 : Complex))))

noncomputable abbrev qz451 := qz541

noncomputable abbrev qz173 := qz451

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz432 (2 : Real)) (Real.log Real.pi))

noncomputable def ep766 := Complex.re (@HMul.hMul Complex Complex Complex qz62 (Complex.exp (@HMul.hMul Complex Complex Complex qz62 Complex.I ↑(@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174))) (zetaApproximant qz137 1 21))

noncomputable def ep767 := @Enclosure.Real.IsNear.of_eq ep766 (@HSub.hSub Real Real Real qz370 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.im (zetaApproximant qz137 1 21))))

noncomputable def ep768 := nat_lit 27685743637067356311250135653

noncomputable def ep769 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.im (zetaApproximant qz137 1 21))) ep768

noncomputable def ep770 := nat_lit 13185778916216048560300359680

noncomputable def ep771 := nat_lit 1290734884703818774582512880069741837

noncomputable def ep772 := nat_lit 217627702589534704195418899405288243200

noncomputable def ep773 := nat_lit 1724243563519787226006871

noncomputable def ep774 := nat_lit 263715578324320971206007193600

noncomputable def ep775 := nat_lit 20781267269520358149177899780718119

noncomputable def ep776 := nat_lit 870510810358138816781675597621152972800

noncomputable def ep777 := nat_lit 7301139159093681079050003373839918062836573089222382059520

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.re (zetaApproximant qz137 1 21)) 1048575 1048576 10910035

noncomputable def ep779 := nat_lit 659557979629207315405518257

noncomputable def ep780 := nat_lit 125136987427654995000950784000

noncomputable def ep781 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) Bool.true 1048575 1048576 43640140

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95531861) qz17)

noncomputable def ep782 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174) qz452 Bool.false 95531861 1048576 321

noncomputable def ep783 := nat_lit 1086947328000000000000000000

noncomputable def ep784 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174) Bool.false 102576555233722638111 1125899906842624000 332068161841108710709787 ep783

noncomputable def ep785 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174 168472927426073468703 1125899906842624000 120072300841108710709787 ep783 479459211 8192000

noncomputable def ep786 := nat_lit 840307140474655851405312000

noncomputable def ep787 := nat_lit 4347789312000000000000000000

noncomputable def ep788 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 14479311305877814353 180143985094819840 880840656812789034672593 ep787 Bool.false 168472927426073468703 1125899906842624000

noncomputable def ep789 := @Enclosure.Complex.IsNear.subLitP qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 13061762851165385673 180143985094819840 864456656764963352240593 ep787 Bool.false 171977021224806920703 1125899906842624000 37293433613340587793929

noncomputable def ep790 := nat_lit 362315776000000000000000000

noncomputable def ep791 := nat_lit 65209021001732734549328553037529088

noncomputable def ep792 := nat_lit 47420913323630068090317343102599168

noncomputable abbrev qz453 := (@HSub.hSub Complex Complex Complex qz529 qz540 qz532)

noncomputable abbrev qz454 := (Complex.log qz540)

noncomputable abbrev qz175 := (@HSub.hSub Complex Complex Complex qz367 (@HMul.hMul Complex Complex Complex qz366 qz453 qz454) qz450)

noncomputable abbrev qz176 := qz450

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq qz172 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz175 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k)))))) Bool.true 13061762851165385673

noncomputable def ep794 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz175 qz68) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) Bool.true 13061775747407623113 180143985094819840

noncomputable def ep795 := nat_lit 448798754190904375622095601664

noncomputable def ep796 := nat_lit 36931784091202179416692516454400

noncomputable def ep797 := @ep794 26381111973663157901 132684000000000000000000 Bool.false 34395770555557559603 225179981368524800 3414250009356842509 33171000000000000000000 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000 Bool.true ep795 13061762851165385673 180143985094819840 864456656764963352240593 ep787 Bool.false ep796

noncomputable def ep798 := @Enclosure.Complex.IsNear.addLitP qz175 qz68 Bool.true 13227316843696042953 180143985094819840 6500375001167254319 33171000000000000000000

noncomputable def ep799 := nat_lit 1712033070764211976667136

noncomputable def ep800 := @ep798 Bool.false 34395770555557559603 225179981368524800 3414250009356842509 33171000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep799 13061775747407623113 180143985094819840 26381111973663157901 132684000000000000000000 Bool.false 34395770555557559603 34395770555557559603 225179981368524800

noncomputable abbrev qz177 := (@HMul.hMul Complex Complex Complex qz366 qz453 qz454)

noncomputable def ep801 := @Enclosure.Complex.IsNear.subLitP qz177 qz176 Bool.true 12821992877232698313 180143985094819840 6500375001167254319 33171000000000000000000 Bool.false 229543863214837477887

noncomputable def ep802 := @ep801 1125899906842624000 3414250009356842509 33171000000000000000000 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 Bool.true 52909267374784171812000 13227316843696042953 180143985094819840 6500375001167254319 33171000000000000000000 Bool.false 687915411111151192060000 34395770555557559603 225179981368524800 3414250009356842509 33171000000000000000000

noncomputable abbrev qz178 := qz453

noncomputable abbrev qz179 := qz454

noncomputable def ep803 := @Enclosure.Complex.IsNear.mul qz178 qz179 Bool.true 12821992877232698313 180143985094819840 6500375001167254319 33171000000000000000000 Bool.false 229543863214837477887 1125899906842624000 3414250009356842509

noncomputable abbrev qz180 := (Complex.re qz453)

noncomputable abbrev qz181 := (Complex.re qz454)

noncomputable abbrev qz182 := (Complex.im qz453)

noncomputable abbrev qz183 := (Complex.im qz454)

noncomputable def ep804 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz180 qz181) (@HMul.hMul Real Real Real qz0 qz182 qz183) 248122164847425099 36028797018963968 875000002554167 265368000000000000000 219728182835465997 2814749767106560

noncomputable def ep805 := nat_lit 7218140293006541748459191880646656

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz181 7000 4000 0 1 35446023549632157 9007199254740992 125000000364881 66342000000000000000

noncomputable def ep807 := @Enclosure.Complex.IsNear.re_isNear qz178 Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable abbrev qz455 := (Enclosure.sfrac Bool.false 204512 4000)

noncomputable abbrev qz184 := qz455

noncomputable def ep808 := @Enclosure.Complex.IsNear.of_eq qz178 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz184) Bool.false 7000 4000 0 1 Bool.false 204512 4000 0

noncomputable abbrev qz456 := (Complex.log (Complex.mk qz83 qz184))

noncomputable def ep809 := @Enclosure.Complex.IsNear.of_eq qz179 qz456 Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000

noncomputable def ep810 := nat_lit 466415097547261849902252562518215121898045440

noncomputable def ep811 := nat_lit 2349161158254954107176092390870600350957568

noncomputable def ep812 := nat_lit 20919723172288010387513987124407291609088

noncomputable def ep813 := BSN.log_dyadic_bound 9138158144 74674158144 3 2 ep810 1048576 265368 ep811 ep812 257928 83812316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9138158144) (BSN.artanhQ 74674158144) 0 2 ep811 ep810 ep812 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz542 := (Real.log (Enclosure.sfrac Bool.false 41906158144 16000000))

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz542 1 2 0 1 35446023549632157 4503599627370496 125000000364881 33171000000000000000 35446023549632157 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 41906158144 16000000 35446023549632157 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41906158144) qz385)) Bool.false 297342796716632709267456 37778931862957161709568 1000000002919048 265368000000000000000 35446023549632157 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 41906158144 16000000 11 83812316288 65536000000 257928 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep813 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep815 := BSN.arctan_dyadic_bound_f 9000 204512 1 0 1048576 265368 0 1 1 0 1 1 46115 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz457 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 204512)))

noncomputable def ep816 := @Enclosure.Real.IsNear.subLit_ff_p qz85 qz457 884279719003555 562949953421312 1 2000000000000000 46115 1048576 1 265368 901274053531847884800 859521916896675 562949953421312 250000000033171 66342000000000000000 qz86 (ep815 rfl) rfl rfl

noncomputable abbrev qz458 := (Complex.mk qz83 qz184)

noncomputable abbrev qz459 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204512) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep817 := @Enclosure.Complex.IsNear.re_isNear qz179 Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (ep809 (@congrArg Complex Complex qz176 qz458 Complex.log (BSN.w_shift_mk qz146 Bool.false 102256 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz456 Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz456) (@HMul.hMul Real Real Real qz0 qz84 qz542) Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 9000 204512 4000 41906158144 16000000 rfl rfl rfl) (ep814 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz456) qz459 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 9000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz459 (@HSub.hSub Real Real Real qz370 qz85 qz457) Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 204512 9000 rfl rfl) ep816))))

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ff qz182 qz183 204512 4000 0 1 859521916896675 562949953421312 250000000033171 66342000000000000000

noncomputable def ep819 := @Enclosure.Complex.IsNear.im_isNear qz178 Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable def ep820 := @Enclosure.Complex.IsNear.im_isNear qz179 Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (ep809 (@congrArg Complex Complex qz176 qz458 Complex.log (BSN.w_shift_mk qz146 Bool.false 102256 1000 2 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz456 Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz456) (@HMul.hMul Real Real Real qz0 qz84 qz542) Bool.false 35446023549632157 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 9000 204512 4000 41906158144 16000000 rfl rfl rfl) (ep814 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz456) qz459 Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 9000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz459 (@HSub.hSub Real Real Real qz370 qz85 qz457) Bool.false 859521916896675 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 204512 9000 rfl rfl) ep816))))

noncomputable abbrev qz460 := (Enclosure.Real.IsNear.const Bool.false 204512 4000)

noncomputable abbrev qz185 := (@ep808 1 (BSN.w_sub_half_mk qz432 Bool.false 102256 1000 2 qz433 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz455 Bool.false 7000 4000 0 1 Bool.false 204512 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz460))

noncomputable def ep821 := @ep804 1597750000211995861 8292750000000000000000 ep805 12821992877232698313 180143985094819840 6500375001167254319 33171000000000000000000 (@ep806 248122164847425099 36028797018963968 875000002554167 265368000000000000000 (ep807 qz185) ep817 rfl) (@ep818 219728182835465997 2814749767106560 1597750000211995861 8292750000000000000000 (ep819 qz185) ep820 rfl) rfl

noncomputable def ep822 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz180 qz183) (@HMul.hMul Real Real Real qz0 qz182 qz181) 6016653418276725 2251799813685248 1750000000232197 265368000000000000000 226535536505699115387 1125899906842624000

noncomputable def ep823 := nat_lit 516886828419763084711579187178110976

noncomputable def ep824 := @Enclosure.Real.IsNear.mulLit_ff qz180 qz183 7000 4000 0 1 859521916896675 562949953421312 250000000033171 66342000000000000000

noncomputable def ep825 := @Enclosure.Real.IsNear.mulLit_ff qz182 qz181 204512 4000 0 1 35446023549632157 9007199254740992 125000000364881 66342000000000000000

noncomputable def ep826 := @ep822 798875002331954471 8292750000000000000000 ep823 229543863214837477887 1125899906842624000 3414250009356842509 33171000000000000000000 (@ep824 6016653418276725 2251799813685248 1750000000232197 265368000000000000000 (ep807 qz185) ep820 rfl) (@ep825 226535536505699115387 1125899906842624000 798875002331954471 8292750000000000000000 (ep819 qz185) ep817 rfl) rfl

noncomputable def ep827 := @Enclosure.Complex.IsNear.of_eq qz176 qz458 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 (BSN.w_shift_mk qz146 Bool.false 102256 1000 2 qz147 rfl)

noncomputable abbrev qz461 := (ep827 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 204512 4000) Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 204512 4000)))

noncomputable abbrev qz186 := qz461

noncomputable def ep828 := ep802 (@ep803 33171000000000000000000 (ep821 rfl) (ep826 rfl)) qz186 rfl rfl rfl rfl rfl rfl

noncomputable def ep829 := @ep800 3414250009356842509 33171000000000000000000 (ep828 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz89 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep346 131072 3 1048576 (ep348 rfl) (ep350 rfl) rfl rfl) (@ep351 1 0 1 (ep353 rfl) (ep355 rfl) rfl rfl))

noncomputable abbrev qz462 := (@HPow.hPow Complex Int Complex qz534 qz540 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz187 := qz462

noncomputable def ep830 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz187)) Bool.false 2459763 34359738368 3 34359738368

noncomputable def ep831 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz187) Bool.false 0 1 0 1 Bool.false

noncomputable def ep832 := @ep831 0 1 0 1 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000 Bool.false 2459763 2459763 34359738368 3 34359738368 Bool.true 1746705037 1746705037 1073741824000 6391

noncomputable def ep833 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz63 (@HMul.hMul Complex Complex Complex qz62 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz71 qz176 (@HSub.hSub Int Int Int qz379 qz73 (@HMul.hMul Int Int Int qz380 qz74 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false

noncomputable def ep834 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92) qz187 Bool.false 2459763 34359738368 3 34359738368 Bool.true 1746705037 1073741824000 6391 3221225472000

noncomputable abbrev qz188 := (Complex.re qz462)

noncomputable abbrev qz189 := (Complex.im qz462)

noncomputable def ep835 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz189) 2459763 34359738368 3 34359738368 0 1 0

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188 1 12 0 1 7379289 8589934592 9 8589934592 2459763

noncomputable def ep837 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391 268435456000

noncomputable abbrev qz463 := (@HPow.hPow Complex Nat Complex qz536 qz540 1)

noncomputable abbrev qz190 := (@Inv.inv Complex Complex.instInv qz463)

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq qz187 qz190 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391

noncomputable def ep839 := @Enclosure.Complex.IsNear.of_parts qz190 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391

noncomputable abbrev qz191 := (Complex.re qz463)

noncomputable abbrev qz192 := qz463

noncomputable def ep840 := @Enclosure.Real.IsNear.mulLit_ff qz191 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192)) 9000 4000 0 1 819921 2147483648 1 2147483648

noncomputable def ep841 := @Enclosure.Complex.IsNear.re_isNear qz192 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable def ep842 := @Enclosure.Complex.IsNear.of_eq qz192 qz176 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0

noncomputable def ep843 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192)) Bool.false 819921 2147483648 1 2147483648 819921 2147483648 1

noncomputable abbrev qz193 := (Complex.im qz463)

noncomputable def ep844 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192) (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 qz191 qz191) (@HMul.hMul Real Real Real qz0 qz193 qz193)) Bool.false 654783721 250000 0 1

noncomputable def ep845 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz191 qz191) (@HMul.hMul Real Real Real qz0 qz193 qz193) 81 16 0 1 40844881 15625

noncomputable def ep846 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz191 9000 4000 0 1 9000 4000 0 1

noncomputable def ep847 := @Enclosure.Real.IsNear.mulLit_ff qz193 qz193 204512 4000 0 1 204512 4000 0 1

noncomputable def ep848 := @Enclosure.Complex.IsNear.im_isNear qz192 Bool.false 9000 4000 0 1 Bool.false 204512 4000 0 1

noncomputable abbrev qz194 := (ep841 (@ep842 1 (BSN.pow_one_c qz450) qz461))

noncomputable abbrev qz195 := (ep848 (@ep842 1 (BSN.pow_one_c qz450) qz461))

noncomputable def ep849 := @ep845 0 1 654783721 654783721 250000 0 1 (@ep846 81 16 0 1 qz194 qz194 rfl) (@ep847 40844881 15625 0 1 qz195 qz195 rfl)

noncomputable def ep850 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192) 654783721 250000 0 1 409960 409961 1073741824 (ep844 (Enclosure.Complex.normSq_eq_mul_add_mul qz192) (ep849 rfl rfl)) rfl

noncomputable def ep851 := @Enclosure.Real.IsNear.of_eq (Complex.re qz190) (@HMul.hMul Real Real Real qz0 qz191 (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192))) Bool.false 7379289 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz192) (@ep840 7379289 8589934592 9 8589934592 qz194 (@ep843 2147483648 (ep850 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep852 := @Enclosure.Real.IsNear.of_eq (Complex.im qz190) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz193) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192))) Bool.true 5240115111 268435456000 6391 268435456000 (Enclosure.Complex.inv_im_eq_mul qz192)

noncomputable def ep853 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz193) (@Inv.inv Real Real.instInv (@DFunLike.coe qz98 Complex (fun (x : Complex) => Real) qz99 Complex.normSq qz192)) 204512 4000 0 1 819921 2147483648 1

noncomputable def ep854 := @ep853 2147483648 5240115111 268435456000 6391 268435456000 (@Enclosure.Real.IsNear.neg qz193 Bool.false 204512 4000 0 1 qz195) (@ep843 2147483648 (ep850 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz189 0 1 0 1 5240115111 268435456000 6391 268435456000 0

noncomputable def ep856 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 7379289 8589934592 9 8589934592 Bool.true 5240115111 268435456000 6391 268435456000

noncomputable abbrev qz196 := (@ep838 268435456000 (BSN.zpow_one_sub_two_mul qz450 1 1 rfl rfl) (@ep839 268435456000 ep851 (ep852 ep854)))

noncomputable def ep857 := @ep835 1 2459763 2459763 34359738368 3 34359738368 (@ep836 34359738368 3 34359738368 ep365 (ep837 qz196) rfl) (@ep855 1 0 1 ep385 (ep856 qz196) rfl) rfl

noncomputable def ep858 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz189) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188) 1746705037 1073741824000 6391 3221225472000 0 1 0

noncomputable def ep859 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz189 1 12 0 1 5240115111 268435456000 6391 268435456000 1746705037

noncomputable def ep860 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 (@Rat.cast Complex Complex.instRatCast (bernoulli qz91)) qz92)) qz188 0 1 0 1 7379289 8589934592 9 8589934592 0

noncomputable def ep861 := @ep858 1 1746705037 1746705037 1073741824000 6391 3221225472000 (@ep859 1073741824000 6391 3221225472000 ep365 (ep856 qz196) rfl) (@ep860 1 0 1 ep385 (ep837 qz196) rfl) rfl

noncomputable def ep862 := @ep832 3221225472000 (@ep833 0 1 0 1 (BSN.stirling_sum_base qz176) qz105) (ep834 (ep857 rfl) (ep861 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep863 := @ep797 171977021224806920703 1125899906842624000 37293433613340587793929 ep790 (ep829 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep830 Bool.true 1746705037 1073741824000 6391 3221225472000 (BSN.stirling_sum_succ qz176 0 1 rfl) (ep862 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep864 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz146 2) Bool.false 35438711367810717 4503599627370496 125000000364881 33171000000000000000 Bool.false 876023449683363 281474976710656

noncomputable abbrev qz197 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz451 qz390))

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 1) qz197) Bool.false 35438711367810717 4503599627370496 125000000364881 33171000000000000000 Bool.false 876023449683363 281474976710656 250000000033171 33171000000000000000

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 1) qz197 Bool.false 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000 Bool.false

noncomputable def ep867 := nat_lit 638407069242251622778923833622528

noncomputable def ep868 := nat_lit 986314720390452514729872064512

noncomputable abbrev qz198 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz451 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz146 0) qz198) Bool.false 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz146 0) qz198 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz464 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz184))

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq qz198 qz464 Bool.false 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000

noncomputable def ep872 := nat_lit 464419585851951803838470740989335198698045440

noncomputable def ep873 := nat_lit 2302952418347331775448654301014641310957568

noncomputable def ep874 := nat_lit 20196720218008838626313349828422651609088

noncomputable def ep875 := BSN.log_dyadic_bound 9058158144 74594158144 3 2 ep872 1048576 265368 ep873 ep874 255925 83652316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9058158144) (BSN.artanhQ 74594158144) 0 2 ep873 ep872 ep874 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 41826158144 16000000)) 1 2 0 1 35437420730138269 4503599627370496 125000000364881 33171000000000000000 35437420730138269 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 41826158144 16000000 35437420730138269 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41826158144) qz385)) Bool.false 297270631036203724439552 37778931862957161709568 1000000002919048 265368000000000000000 35437420730138269 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 41826158144 16000000 11 83652316288 65536000000 255925 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep875 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep877 := BSN.arctan_dyadic_bound_f 1000 204512 1 0 1048576 265368 0 1 1 0 1 1 5127 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz465 := (@Nat.cast Real Real.instNatCast 204512)

noncomputable def ep878 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz396 qz465)) 884279719003555 562949953421312 1 2000000000000000 5127 1048576 1 265368 924348246222680621056 881527181837731 562949953421312 250000000033171 66342000000000000000 qz86 (ep877 rfl) rfl rfl

noncomputable abbrev qz199 := (@HAdd.hAdd Complex Complex Complex qz274 qz451 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz466 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz184)

noncomputable def ep879 := @ep870 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000 Bool.false 35437420730138269 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 881527181837731 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz146 0) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz146) qz105) (ep871 (@congrArg Complex Complex qz199 qz466 Complex.log (BSN.w_shift_mk qz146 Bool.false 102256 1000 0 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz464 Bool.false 35437420730138269 9007199254740992 125000000364881 66342000000000000000 Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz464) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 41826158144 16000000))) Bool.false 35437420730138269 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 1000 204512 4000 41826158144 16000000 rfl rfl rfl) (ep876 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz464) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz465 qz396)) Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 1000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz465 qz396)) (@HSub.hSub Real Real Real qz370 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz396 qz465))) Bool.false 881527181837731 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 204512 1000 rfl rfl) ep878)))) rfl rfl

noncomputable abbrev qz467 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz184))

noncomputable def ep880 := @Enclosure.Complex.IsNear.of_eq qz197 qz467 Bool.false 35440002005483165 9007199254740992 125000000364881 66342000000000000000 Bool.false 870519717528995 562949953421312 250000000033171 66342000000000000000

noncomputable def ep881 := nat_lit 465017565678448693880079415381439175658045440

noncomputable def ep882 := nat_lit 2316756817318720129941289959139429022957568

noncomputable def ep883 := nat_lit 20411620915927523552155127705218043609088

noncomputable def ep884 := BSN.log_dyadic_bound 9082158144 74618158144 3 2 ep881 1048576 265368 ep882 ep883 256526 83700316288 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 9082158144) (BSN.artanhQ 74618158144) 0 2 ep882 ep881 ep883 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep885 := @Enclosure.Real.IsNear.mulLit_ff qz84 (Real.log (Enclosure.sfrac Bool.false 41850158144 16000000)) 1 2 0 1 35440002005483165 4503599627370496 125000000364881 33171000000000000000 35440002005483165 9007199254740992 125000000364881 66342000000000000000 qz384 (BSN.isNear_log_sfrac 41850158144 16000000 35440002005483165 4503599627370496 125000000364881 33171000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41850158144) qz385)) Bool.false 297292284343212121784320 37778931862957161709568 1000000002919048 265368000000000000000 35440002005483165 4503599627370496 125000000364881 33171000000000000000 (BSN.log_rat_reduce_isNear 41850158144 16000000 11 83700316288 65536000000 256526 1048576 24973259072661432 36028797018963968 265368 1000000000000000 rfl rfl rfl rfl (ep884 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep886 := BSN.arctan_dyadic_bound_f 5000 204512 1 0 1048576 265368 0 1 1 0 1 1 25630 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 204512) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 204512) 0 0 rfl) rfl rfl rfl

noncomputable def ep887 := @Enclosure.Real.IsNear.subLit_ff_p qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz400 qz465)) 884279719003555 562949953421312 1 2000000000000000 25630 1048576 1 265368 912806083327683461120 870519717528995 562949953421312 250000000033171 66342000000000000000 qz86 (ep886 rfl) rfl rfl

noncomputable abbrev qz200 := (@HAdd.hAdd Complex Complex Complex qz274 qz451 qz390)

noncomputable abbrev qz468 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz184)

noncomputable def ep888 := @ep866 35440002005483165 9007199254740992 125000000364881 66342000000000000000 Bool.false 870519717528995 562949953421312 250000000033171 66342000000000000000 Bool.false ep867 35438711367810717 4503599627370496 125000000364881 33171000000000000000 Bool.false ep868 876023449683363 281474976710656 250000000033171 33171000000000000000 (ep869 (BSN.log_sum_c_succ qz146 0 1 rfl) (ep879 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep880 (@congrArg Complex Complex qz200 qz468 Complex.log (BSN.w_shift_mk qz146 Bool.false 102256 1000 1 qz147 rfl)) (@Enclosure.Complex.IsNear.of_parts qz467 Bool.false 35440002005483165 9007199254740992 125000000364881 66342000000000000000 Bool.false 870519717528995 562949953421312 250000000033171 66342000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz467) (@HMul.hMul Real Real Real qz0 qz84 (Real.log (Enclosure.sfrac Bool.false 41850158144 16000000))) Bool.false 35440002005483165 9007199254740992 125000000364881 66342000000000000000 (Enclosure.clog_re_eq 5000 204512 4000 41850158144 16000000 rfl rfl rfl) (ep885 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz467) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz465 qz400)) Bool.false 870519717528995 562949953421312 250000000033171 66342000000000000000 (Enclosure.clog_im_eq 5000 204512 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz465 qz400)) (@HSub.hSub Real Real Real qz370 qz85 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz400 qz465))) Bool.false 870519717528995 562949953421312 250000000033171 66342000000000000000 (BSN.arctan_recip 204512 5000 rfl rfl) ep887)))) rfl rfl

noncomputable def ep889 := @ep789 ep790 Bool.false 35438711367810717 4503599627370496 125000000364881 33171000000000000000 Bool.false 876023449683363 281474976710656 250000000033171 33171000000000000000 Bool.true ep791 14479311305877814353 180143985094819840 880840656812789034672593 ep787 Bool.false ep792 168472927426073468703 1125899906842624000 120072300841108710709787 ep783 (@ep793 180143985094819840 864456656764963352240593 ep787 Bool.false 171977021224806920703 1125899906842624000 37293433613340587793929 ep790 (BSN.logGammaStirling_unfold 1 qz176) (ep863 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep864 250000000033171 33171000000000000000 (BSN.log_sum_c_eq qz146 2) (ep865 (BSN.log_sum_c_succ qz146 1 2 rfl) (ep888 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz201 := (@HDiv.hDiv Real Real Real qz271 qz432 (2 : Real))

noncomputable def ep890 := @Enclosure.Real.IsNear.mulLit_ff qz201 (Real.log Real.pi) 102256 2000 0 1 75021 65536 1 262144 479459211 8192000 6391 32768000 (@Enclosure.Real.IsNear.of_eq qz201 (Enclosure.sfrac Bool.false 102256 2000) Bool.false 102256 2000 0 1 (BSN.t_half_eq qz146 Bool.false 102256 1000 qz147) (Enclosure.Real.IsNear.const Bool.false 102256 2000)) EMRow30.d5 rfl

noncomputable def ep891 := @ep785 6391 32768000 ep786 102576555233722638111 1125899906842624000 332068161841108710709787 ep783 (@ep788 120072300841108710709787 ep783 (ep889 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep890 rfl rfl

noncomputable def ep892 := BSN.cos_dyadic_bound_f 204612 2147483648 1 0 1048576 265628 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 204612) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 204612) qz289 0 0 rfl) rfl rfl

noncomputable def ep893 := @ep782 1048576 Bool.true 1048575 1048576 1 132684 (@ep784 95531861 1048576 321 1048576 ep891 rfl) (Enclosure.sfrac_false_div 95531861 1048576) (BSN.cos_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14398319793801265152) qz20) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 14 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 95531861 1048576 226375608064910080 72057594037927936 14 14398319793801265152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 14398319793801265152 151115727451828646838272 204612 2147483648 265628 265368 (ep892 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep894 := nat_lit 2263488964957131138662400

noncomputable def ep895 := nat_lit 65951680998250575915668633

noncomputable def ep896 := nat_lit 12513698742765499500095078400

noncomputable abbrev qz202 := qz431

noncomputable abbrev qz469 := (@HPow.hPow Complex Complex Complex qz523 (@Nat.cast Complex Complex.instNatCast 21) qz538)

noncomputable abbrev qz203 := qz469

noncomputable abbrev qz470 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz375 qz470 (@HSub.hSub Complex Complex Complex qz367 qz430 (1 : Complex))) qz374)

noncomputable abbrev qz205 := qz470

noncomputable def ep897 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz137 1 21) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 21, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz202) (@HMul.hMul Complex Complex Complex qz62 qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) Bool.false 660080195433501569063971 314373467355157102592000 ep779

noncomputable def ep898 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 21, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz202) (@HMul.hMul Complex Complex Complex qz62 qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) Bool.false 1218841755413 549755813888 46961401628747 9117975051239424

noncomputable def ep899 := nat_lit 15049929083187078376191257

noncomputable def ep900 := nat_lit 1500285512727243716024483

noncomputable def ep901 := nat_lit 90720731267973689020622104860557312

noncomputable def ep902 := nat_lit 86173902145815095675090287898656768

noncomputable def ep903 := @ep898 Bool.false 43092522169 549755813888 93923663680063 18235950102478848 Bool.true 9226179706518622496851 78593366838789275648000 ep899 ep780 Bool.true 20673808204968630984439 ep894 ep900 ep896 Bool.false ep901 660080195433501569063971 314373467355157102592000 ep779 ep780 Bool.false ep902 156749414865435202364261 ep894

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 21, @HPow.hPow Complex Complex Complex qz7 (@Nat.cast Complex Complex.instNatCast n) qz202) (BSN.headSumC qz137 21) Bool.false 1218841755413 549755813888 46961401628747 9117975051239424 Bool.false 43092522169 549755813888 93923663680063

noncomputable abbrev qz206 := (@HPow.hPow Complex Complex Complex qz275 qz403 qz431)

noncomputable def ep905 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 20) qz206) Bool.false 1218841755413 549755813888 46961401628747 9117975051239424 Bool.false 43092522169 549755813888 93923663680063 18235950102478848

noncomputable def ep906 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 20) qz206 Bool.false 18994046547 8589934592 15124262317099 3039325017079808 Bool.true 159588878497 1099511627776 60486336727117 12157300068319232 Bool.false

noncomputable abbrev qz207 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 19) qz431)

noncomputable def ep907 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 19) qz207) Bool.false 18994046547 8589934592 15124262317099 3039325017079808 Bool.true 159588878497 1099511627776 60486336727117 12157300068319232

noncomputable def ep908 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 19) qz207 Bool.false 2210645114457 1099511627776 174934179838777 36471900204957696 Bool.true 281924195711 1099511627776 174915591075745 36471900204957696 Bool.false

noncomputable def ep909 := nat_lit 2673174404728970507452416

noncomputable abbrev qz208 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz431)

noncomputable def ep910 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz137 18) qz208) Bool.false 2210645114457 1099511627776 174934179838777 36471900204957696 Bool.true 281924195711 1099511627776 174915591075745 36471900204957696

noncomputable def ep911 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz137 18) qz208 Bool.false 979711892319 549755813888 84101632713581 18235950102478848 Bool.true 218285284721 1099511627776 168209852756539 36471900204957696 Bool.false

noncomputable def ep912 := nat_lit 1215315004115838950178816

noncomputable abbrev qz209 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz431)

noncomputable def ep913 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz137 18) (@HAdd.hAdd Complex Complex Complex qz4 qz155 qz209) Bool.false 979711892319 549755813888 84101632713581 18235950102478848 Bool.true 218285284721 1099511627776 168209852756539 36471900204957696

noncomputable def ep914 := @Enclosure.Complex.IsNear.addLitP qz155 qz209 Bool.false 438285926375 274877906944 80642491141537 18235950102478848 Bool.true 49282991443 1099511627776 161296431817631 36471900204957696 Bool.false

noncomputable abbrev qz210 := (@HMul.hMul Real Real Real qz268 qz432 qz406)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz210)))) Bool.false 103140039569 549755813888 864785393011 4558987525619712 Bool.true 84501146639 549755813888 1728355234727 9117975051239424 (BSN.cpow_neg_s_mk qz146 102256 1000 17 qz147 rfl)

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz406 102256 1000 0 1 3189913004350711 1125899906842624 62500000033171 8292750000000000000 20386734010805394001 70368744177664000 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz407) Bool.false 53517859495200818200576 18889465931478580854784 1000000000530736 132684000000000000000 3189913004350711 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep444 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep917 := nat_lit 168690343998298508728170973866642933836687865551676690383731054376678148119361

noncomputable def ep918 := nat_lit 22284772631847836977762833400798875260384237779614837760651064133025897281

noncomputable def ep919 := nat_lit 506026462449631830510557395933127203759542828179470841475671861001768392563521

noncomputable def ep920 := BSN.cos_dyadic_bound_f 1474012023 2147483648 3 2 1048576 265628 ep917 ep80 ep918 ep919 ep82 ep918 811114 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1474012023) qz288 0 2 ep917 ep80 ep918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1474012023) qz289 0 2 ep919 ep82 ep918 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303786009) qz17)

noncomputable def ep921 := @Enclosure.Real.IsNear.cos_image qz210 qz471 Bool.false 303786009 1048576 809 1048576 Bool.false 811114 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 20386734010805394001 70368744177664000 399437500211995861 518296875000000000000 303786009 1048576 809 1048576 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 303786009 1048576) (BSN.cos_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103724375030752637616128) qz20) 226375608064910080 72057594037927936 Bool.false 811114 1048576 46 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 303786009 1048576 226375608064910080 72057594037927936 46 103724375030752637616128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 811114 1048576 103724375030752637616128 151115727451828646838272 1474012023 2147483648 265628 265368 (ep920 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep922 := nat_lit 4720675018665004117989530594272295841

noncomputable def ep923 := BSN.sin_dyadic_bound_f 1474012023 2147483648 2 1 1048576 265628 ep922 ep63 ep922 ep922 ep64 ep922 664534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1474012023) qz292 0 1 ep922 ep63 ep922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1474012023) qz293 0 1 ep922 ep64 ep922 rfl rfl rfl rfl) rfl rfl

noncomputable def ep924 := @Enclosure.Real.IsNear.sin_image qz210 qz471 Bool.false 303786009 1048576 809 1048576 Bool.false 664534 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz210 Bool.false 20386734010805394001 70368744177664000 399437500211995861 518296875000000000000 303786009 1048576 809 1048576 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 303786009 1048576) (BSN.sin_reduce0 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103724375030752637616128) qz20) 226375608064910080 72057594037927936 Bool.false 664534 1048576 46 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 303786009 1048576 226375608064910080 72057594037927936 46 103724375030752637616128 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 664534 1048576 103724375030752637616128 151115727451828646838272 1474012023 2147483648 265628 265368 (ep923 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep925 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz119 (Real.cos qz210)) (@HMul.hMul Real Real Real qz0 qz119 (@Neg.neg Real Real.instNeg (Real.sin qz210))) Bool.false 103140039569 549755813888 864785393011 4558987525619712 Bool.true 84501146639 549755813888 1728355234727 9117975051239424 (@Enclosure.Real.IsNear.mulLit_ff qz119 (Real.cos qz210) 254317 1048576 1 1048576 405557 524288 27097483 34782314496 103140039569 549755813888 864785393011 4558987525619712 qz409 (@Enclosure.Real.IsNear.recentre' (Real.cos qz210) Bool.false 811114 1048576 108389932 139129257984 405557 524288 27097483 34782314496 (ep921 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz119 (@Neg.neg Real Real.instNeg (Real.sin qz210)) 254317 1048576 1 1048576 332267 524288 27097483 34782314496 84501146639 549755813888 1728355234727 9117975051239424 qz409 (@Enclosure.Real.IsNear.neg (Real.sin qz210) Bool.false 332267 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz210) Bool.false 664534 1048576 108389932 139129257984 332267 524288 27097483 34782314496 (ep924 rfl rfl) rfl)) rfl)

noncomputable def ep926 := @ep914 103140039569 549755813888 864785393011 4558987525619712 Bool.true 84501146639 549755813888 1728355234727 9117975051239424 Bool.false 269301154368792230363136 979711892319 549755813888 84101632713581 18235950102478848 Bool.true 120003604361567166005248 218285284721 1099511627776 168209852756539 36471900204957696 EMRow30.d12 (ep915 ep925) rfl rfl

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz432 qz411)

noncomputable def ep927 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 251221329819 1099511627776 2243638137205 12157300068319232 Bool.true 31819455495 549755813888 1117623053201 6078650034159616 (BSN.cpow_neg_s_mk qz146 102256 1000 18 qz147 rfl)

noncomputable def ep928 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz411 102256 1000 0 1 3254268794313975 1125899906842624 62500000033171 8292750000000000000 831921274578424569 2814749767106560 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz412) Bool.false 54597570484265130393600 18889465931478580854784 1000000000530736 132684000000000000000 3254268794313975 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep455 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep929 := nat_lit 80579132399004611638859805439402561

noncomputable def ep930 := BSN.cos_dyadic_bound_f 532789487 2147483648 2 1 1048576 265628 ep929 ep59 ep929 ep929 ep60 ep929 1016469 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 532789487) qz288 0 1 ep929 ep59 ep929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 532789487) qz289 0 1 ep929 ep60 ep929 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309914825) qz17)

noncomputable def ep931 := @Enclosure.Real.IsNear.cos_image qz211 qz472 Bool.false 309914825 1048576 809 1048576 Bool.false 1016469 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 831921274578424569 2814749767106560 399437500211995861 518296875000000000000 309914825 1048576 809 1048576 (ep928 rfl) rfl) (Enclosure.sfrac_false_div 309914825 1048576) (BSN.cos_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37491727143982711439360) qz20) 226375608064910080 72057594037927936 Bool.false 1016469 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 309914825 1048576 226375608064910080 72057594037927936 47 37491727143982711439360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1016469 1048576 37491727143982711439360 151115727451828646838272 532789487 2147483648 265628 265368 (ep930 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep932 := BSN.sin_dyadic_bound_f 532789487 2147483648 2 1 1048576 265628 ep929 ep63 ep929 ep929 ep64 ep929 257490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 532789487) qz292 0 1 ep929 ep63 ep929 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 532789487) qz293 0 1 ep929 ep64 ep929 rfl rfl rfl rfl) rfl rfl

noncomputable def ep933 := @Enclosure.Real.IsNear.sin_image qz211 qz472 Bool.false 309914825 1048576 809 1048576 Bool.false 257490 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 831921274578424569 2814749767106560 399437500211995861 518296875000000000000 309914825 1048576 809 1048576 (ep928 rfl) rfl) (Enclosure.sfrac_false_div 309914825 1048576) (BSN.sin_reduce0 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37491727143982711439360) qz20) 226375608064910080 72057594037927936 Bool.false 257490 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q0 309914825 1048576 226375608064910080 72057594037927936 47 37491727143982711439360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 257490 1048576 37491727143982711439360 151115727451828646838272 532789487 2147483648 265628 265368 (ep932 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep934 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz121 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz121 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 251221329819 1099511627776 2243638137205 12157300068319232 Bool.true 31819455495 549755813888 1117623053201 6078650034159616 (@Enclosure.Real.IsNear.mulLit_ff qz121 (Real.cos qz211) 247151 1048576 1 1048576 1016469 1048576 27097483 34782314496 251221329819 1099511627776 2243638137205 12157300068319232 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 1016469 1048576 108389932 139129257984 1016469 1048576 27097483 34782314496 (ep931 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz121 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 247151 1048576 1 1048576 128745 524288 27097483 34782314496 31819455495 549755813888 1117623053201 6078650034159616 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 128745 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 257490 1048576 108389932 139129257984 128745 524288 27097483 34782314496 (ep933 rfl rfl) rfl)) rfl)

noncomputable def ep935 := @ep911 251221329819 1099511627776 2243638137205 12157300068319232 Bool.true 31819455495 549755813888 1117623053201 6078650034159616 Bool.false ep912 2210645114457 1099511627776 174934179838777 36471900204957696 Bool.true 154989465667820603834368 281924195711 1099511627776 174915591075745 36471900204957696 (ep913 (BSN.head_sum_c_succ qz137 17 18 rfl rfl) (ep926 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep927 ep934) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz432 qz416)

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq qz207 (Complex.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 220592843559 1099511627776 6556967966411 36471900204957696 Bool.false 61167658607 549755813888 3271709552803 18235950102478848 (BSN.cpow_neg_s_mk qz146 102256 1000 19 qz147 rfl)

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz416 102256 1000 0 1 3315143513283831 1125899906842624 62500000033171 8292750000000000000 21187082193396963921 70368744177664000 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz417) Bool.false 55618878793361701994496 18889465931478580854784 1000000000530736 132684000000000000000 3315143513283831 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep470 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep938 := nat_lit 1756718094215200795442550392487181065538032560736613353302731242151408252952385

noncomputable def ep939 := nat_lit 745474824002098608605791006124688712239478417631537078414766809420940910401

noncomputable def ep940 := nat_lit 4599721382753332018887984509170796151827411836872107722427815059371768662925121

noncomputable def ep941 := BSN.sin_dyadic_bound_f 2285883657 2147483648 3 2 1048576 265628 ep938 ep73 ep939 ep940 ep76 ep939 917001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2285883657) qz292 0 2 ep938 ep73 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2285883657) qz293 0 2 ep940 ep76 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157856063) qz61)

noncomputable def ep942 := @Enclosure.Real.IsNear.cos_image qz212 qz473 Bool.false 157856063 524288 405 524288 Bool.false 917001 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 21187082193396963921 70368744177664000 399437500211995861 518296875000000000000 157856063 524288 405 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 157856063 524288) (BSN.cos_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80427381142258288951296) qz364) 226375608064910080 72057594037927936 Bool.false 917001 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 157856063 524288 226375608064910080 72057594037927936 47 80427381142258288951296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 917001 1048576 80427381142258288951296 75557863725914323419136 2285883657 2147483648 265628 265368 (ep941 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep943 := nat_lit 976285818930223596849686125162267120282124524150399212758590586443858336489281

noncomputable def ep944 := nat_lit 2927366507142666593331846793474551983421894615615934564118942225712733127647041

noncomputable def ep945 := BSN.cos_dyadic_bound_f 2285883657 2147483648 3 2 1048576 265628 ep943 ep80 ep939 ep944 ep82 ep939 508546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2285883657) qz288 0 2 ep943 ep80 ep939 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2285883657) qz289 0 2 ep944 ep82 ep939 rfl rfl rfl rfl) rfl rfl

noncomputable def ep946 := @Enclosure.Real.IsNear.sin_image qz212 qz473 Bool.false 157856063 524288 405 524288 Bool.true 508546 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 21187082193396963921 70368744177664000 399437500211995861 518296875000000000000 157856063 524288 405 524288 (ep937 rfl) rfl) (Enclosure.sfrac_false_div 157856063 524288) (BSN.sin_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80427381142258288951296) qz364) 226375608064910080 72057594037927936 Bool.false 508546 1048576 47 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 157856063 524288 226375608064910080 72057594037927936 47 80427381142258288951296 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508546 1048576 80427381142258288951296 75557863725914323419136 2285883657 2147483648 265628 265368 (ep945 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep947 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz123 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz123 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 220592843559 1099511627776 6556967966411 36471900204957696 Bool.false 61167658607 549755813888 3271709552803 18235950102478848 (@Enclosure.Real.IsNear.mulLit_ff qz123 (Real.cos qz212) 240559 1048576 1 1048576 917001 1048576 13565327 17391157248 220592843559 1099511627776 6556967966411 36471900204957696 qz419 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 917001 1048576 54261308 69564628992 917001 1048576 13565327 17391157248 (ep942 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz123 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 240559 1048576 1 1048576 254273 524288 13565327 17391157248 61167658607 549755813888 3271709552803 18235950102478848 qz419 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 254273 524288 13565327 17391157248 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 508546 1048576 54261308 69564628992 254273 524288 13565327 17391157248 (ep946 rfl rfl) rfl)) rfl)

noncomputable def ep948 := @ep908 220592843559 1099511627776 6556967966411 36471900204957696 Bool.false 61167658607 549755813888 3271709552803 18235950102478848 Bool.false ep909 18994046547 8589934592 15124262317099 3039325017079808 Bool.true 87734913785591377166336 159588878497 1099511627776 60486336727117 12157300068319232 (ep910 (BSN.head_sum_c_succ qz137 18 19 rfl rfl) (ep935 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep936 ep947) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz432 qz424)

noncomputable def ep949 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 3222776405 549755813888 794307338725 4558987525619712 Bool.false 245773922835 1099511627776 6388317178775 36471900204957696 (BSN.cpow_neg_s_mk qz146 102256 1000 20 qz147 rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz130 102256 1000 0 1 3372893643545847 1125899906842624 62500000033171 8292750000000000000 21556163275901508177 70368744177664000 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz425 Bool.false 56587765202795681021952 18889465931478580854784 1000000000530736 132684000000000000000 3372893643545847 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep492 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep951 := BSN.sin_dyadic_bound_f 56307328 2147483648 1 0 1048576 265628 0 1 1 0 1 1 27490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 56307328) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 56307328) qz293 0 0 rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 321211863) qz17)

noncomputable def ep952 := @Enclosure.Real.IsNear.cos_image qz213 qz474 Bool.false 321211863 1048576 809 1048576 Bool.false 27490 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 21556163275901508177 70368744177664000 399437500211995861 518296875000000000000 321211863 1048576 809 1048576 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 321211863 1048576) (BSN.cos_reduce3 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3962275998175315623936) qz20) 226375608064910080 72057594037927936 Bool.false 27490 1048576 48 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 321211863 1048576 226375608064910080 72057594037927936 48 3962275998175315623936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27490 1048576 3962275998175315623936 151115727451828646838272 56307328 2147483648 265628 265368 (ep951 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep953 := BSN.cos_dyadic_bound_f 56307328 2147483648 1 0 1048576 265628 0 1 1 0 1 1 1048215 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 56307328) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 56307328) qz289 0 0 rfl) rfl rfl

noncomputable def ep954 := @Enclosure.Real.IsNear.sin_image qz213 qz474 Bool.false 321211863 1048576 809 1048576 Bool.true 1048215 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 21556163275901508177 70368744177664000 399437500211995861 518296875000000000000 321211863 1048576 809 1048576 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 321211863 1048576) (BSN.sin_reduce3 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3962275998175315623936) qz20) 226375608064910080 72057594037927936 Bool.false 1048215 1048576 48 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q3 321211863 1048576 226375608064910080 72057594037927936 48 3962275998175315623936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048215 1048576 3962275998175315623936 151115727451828646838272 56307328 2147483648 265628 265368 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 3222776405 549755813888 794307338725 4558987525619712 Bool.false 245773922835 1099511627776 6388317178775 36471900204957696 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz213) 234469 1048576 1 1048576 13745 524288 27097483 34782314496 3222776405 549755813888 794307338725 4558987525619712 qz428 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 27490 1048576 108389932 139129257984 13745 524288 27097483 34782314496 (ep952 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 234469 1048576 1 1048576 1048215 1048576 27097483 34782314496 245773922835 1099511627776 6388317178775 36471900204957696 qz428 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 1048215 1048576 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 1048215 1048576 108389932 139129257984 1048215 1048576 27097483 34782314496 (ep954 rfl rfl) rfl)) rfl)

noncomputable def ep956 := @ep906 3222776405 549755813888 794307338725 4558987525619712 Bool.false 245773922835 1099511627776 6388317178775 36471900204957696 Bool.false 10469770956996131946496 1218841755413 549755813888 46961401628747 9117975051239424 Bool.false 94761458390021112332288 43092522169 549755813888 93923663680063 18235950102478848 (ep907 (BSN.head_sum_c_succ qz137 19 20 rfl rfl) (ep948 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep949 ep955) rfl rfl

noncomputable def ep957 := @Enclosure.Complex.IsNear.mul qz203 (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.true 9226179706518622496851 78593366838789275648000 ep899 ep780 Bool.true

noncomputable abbrev qz214 := (Complex.re qz469)

noncomputable abbrev qz215 := (Complex.im qz469)

noncomputable def ep958 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 2361857859621373516285 22634889649571311386624 258528114362911536677855

noncomputable def ep959 := nat_lit 3003287698263719880022818816

noncomputable def ep960 := nat_lit 6703767183624374732193792000

noncomputable def ep961 := nat_lit 1074001163369982416748435078440502921686679552

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 14313137945 68719476736 1566710946835 9117975051239424 165013281413

noncomputable abbrev qz475 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz539 (Real.log (Enclosure.sfrac Bool.false 21 1)))

noncomputable abbrev qz216 := (Real.cos qz475)

noncomputable abbrev qz217 := (Real.sin qz475)

noncomputable abbrev qz476 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz477 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep963 := @Enclosure.Complex.IsNear.of_eq qz203 (Complex.mk (@HMul.hMul Real Real Real qz0 qz476 qz216) (@HMul.hMul Real Real Real qz0 qz476 qz477)) Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (BSN.cpow_neg_s_mk qz146 102256 1000 21 qz147 rfl)

noncomputable abbrev qz478 := (Real.sqrt (@Nat.cast Real Real.instNatCast 21))

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz16)

noncomputable def ep964 := @Enclosure.Real.IsNear.inv_image qz478 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq qz478 (Real.sqrt qz479) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz479) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep965 := BSN.log_dyadic_bound 5 37 3 2 28112415 524288 132684 173000 1875 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 37) 0 2 173000 28112415 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz480 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable def ep966 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz480 102256 1000 0 1 3427826275261687 1125899906842624 62500000033171 8292750000000000000 21907237725197441617 70368744177664000 399437500211995861 518296875000000000000 qz148 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 62500000033171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz479) Bool.false 57509381830540779323392 18889465931478580854784 1000000000530736 132684000000000000000 3427826275261687 1125899906842624 62500000033171 8292750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 132684 1000000000000000 rfl rfl rfl rfl (ep965 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep967 := nat_lit 179024278797382011830297171637438736

noncomputable def ep968 := BSN.cos_dyadic_bound_f 650471066 2147483648 2 1 1048576 265628 ep967 ep59 ep967 ep967 ep60 ep967 1000840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 650471066) qz288 0 1 ep967 ep59 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 650471066) qz289 0 1 ep967 ep60 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz475

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20402705) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep969 := @Enclosure.Real.IsNear.cos_image qz218 qz481 Bool.false 20402705 65536 809 1048576 Bool.true 1000840 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 21907237725197441617 70368744177664000 399437500211995861 518296875000000000000 20402705 65536 809 1048576 (ep966 rfl) rfl) (Enclosure.sfrac_false_div 20402705 65536) (BSN.cos_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860802003099472363520) qz435) 226375608064910080 72057594037927936 Bool.false 1000840 1048576 49 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 20402705 65536 226375608064910080 72057594037927936 49 2860802003099472363520 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1000840 1048576 2860802003099472363520 9444732965739290427392 650471066 2147483648 265628 265368 (ep968 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep970 := BSN.sin_dyadic_bound_f 650471066 2147483648 2 1 1048576 265628 ep967 ep63 ep967 ep967 ep64 ep967 312778 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 650471066) qz292 0 1 ep967 ep63 ep967 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 650471066) qz293 0 1 ep967 ep64 ep967 rfl rfl rfl rfl) rfl rfl

noncomputable def ep971 := @Enclosure.Real.IsNear.sin_image qz218 qz481 Bool.false 20402705 65536 809 1048576 Bool.true 312778 1048576 1 132684 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 21907237725197441617 70368744177664000 399437500211995861 518296875000000000000 20402705 65536 809 1048576 (ep966 rfl) rfl) (Enclosure.sfrac_false_div 20402705 65536) (BSN.sin_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2860802003099472363520) qz435) 226375608064910080 72057594037927936 Bool.false 312778 1048576 49 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 20402705 65536 226375608064910080 72057594037927936 49 2860802003099472363520 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312778 1048576 2860802003099472363520 9444732965739290427392 650471066 2147483648 265628 265368 (ep970 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep972 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz476 qz216) (@HMul.hMul Real Real Real qz0 qz476 qz477) Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (@Enclosure.Real.IsNear.mulLit_ft qz476 qz216 114409 524288 1 524288 125105 131072 27097483 34782314496 14313137945 68719476736 1566710946835 9117975051239424 (@Enclosure.Real.IsNear.recentre' qz476 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep964 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 1000840 1048576 108389932 139129257984 125105 131072 27097483 34782314496 (ep969 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz476 qz477 114409 524288 1 524288 156389 524288 27097483 34782314496 17892309101 274877906944 777649547267 4558987525619712 (@Enclosure.Real.IsNear.recentre' qz476 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep964 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 156389 524288 27097483 34782314496 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 312778 1048576 108389932 139129257984 156389 524288 27097483 34782314496 (ep971 rfl rfl) rfl)) rfl)

noncomputable def ep973 := @ep962 329380995384 0 1 2361857859621373516285 22634889649571311386624 258528114362911536677855 ep959 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (ep963 ep972))

noncomputable def ep974 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 165013281413 329380995384 0 1 Bool.false

noncomputable def ep975 := @Enclosure.Complex.IsNear.addLitP qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) Bool.false 652221221 1307067442 0 1 Bool.true 134211000

noncomputable def ep976 := @ep975 653533721 0 1 Bool.false 1 504 0 1 Bool.false 913 2250 0 1 Bool.false 330026562826 165013281413 329380995384 0 1 Bool.false 294701537273 294701537273 1470450872250 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz375 qz470 (@HSub.hSub Complex Complex Complex qz367 qz430 (1 : Complex)))

noncomputable def ep977 := @Enclosure.Complex.IsNear.addLitP qz219 qz89 Bool.true 42000000 41826158144 0 1 Bool.true 8589504000 41826158144 0 1

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 42000000 41826158144) (Enclosure.sfrac Bool.true 8589504000 41826158144)) Bool.true 42000000 41826158144 0 1 Bool.true 8589504000 41826158144 0 1

noncomputable def ep979 := @ep977 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 41742158144 652221221 1307067442 0 1 Bool.true 8589504000 134211000 653533721 0 1 (ep978 (BSN.N_div_s_sub_one_mk qz146 102256 1000 21 qz147 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 42000000 41826158144) (Enclosure.sfrac Bool.true 8589504000 41826158144) Bool.true 42000000 41826158144 0 1 Bool.true 8589504000 41826158144 0 1 (Enclosure.Real.IsNear.const Bool.true 42000000 41826158144) (Enclosure.Real.IsNear.const Bool.true 8589504000 41826158144))) qz90 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz404 qz470 1))

noncomputable def ep980 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 504 0 1

noncomputable def ep981 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep982 := @ep981 0 1 0 1 Bool.false 1 504 0 1 Bool.false 913 2250 0 1 Bool.false 1 1 504 0 1 Bool.false 913 913 2250 0

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (Complex.mk qz11 qz11) Bool.false 0 1 0 1 Bool.false

noncomputable def ep984 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 504 0 1 Bool.false 913 2250 0 1

noncomputable def ep985 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 504 0 1 0 1 0

noncomputable def ep986 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 21 0 1 1

noncomputable def ep987 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep988 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) qz137 Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 (BSN.ascPochhammer_one_eval qz137)

noncomputable def ep990 := ep989 (@Enclosure.Complex.IsNear.of_eq qz137 (Complex.mk qz84 qz146) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_crit_mk qz146 Bool.false 102256 1000 qz147) (@Enclosure.Complex.IsNear.mk qz84 qz146 Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 qz384 qz148))

noncomputable def ep991 := @ep988 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 102256 1000 0 1 0 1 0

noncomputable def ep993 := @ep992 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep994 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) 6391 750 0 1 0 1 0 1 6391

noncomputable def ep995 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 102256 1000 0 1 6391 750 0

noncomputable def ep996 := @ep995 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep997 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep998 := @ep997 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep520) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep999 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 (@ep987 1 24 0 1 (ep991 rfl) (ep993 rfl) rfl rfl) (@ep994 6391 750 0 1 (ep996 rfl) (ep998 rfl) rfl rfl)

noncomputable def ep1000 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 ep999

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz404 qz470 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 21) qz283) Bool.false 1 21 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 21 1 21 EMRow30.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 21) qz283 Bool.false 1 21 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 21) qz295))

noncomputable def ep1001 := @ep986 504 0 1 ep1000 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 21 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1002 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 6391 750 0 1 0 1 0 1 0

noncomputable def ep1003 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 6391 750 0 1 ep999

noncomputable def ep1004 := @ep1002 1 0 1 ep1003 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 21 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1005 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 913 2250 0

noncomputable def ep1006 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep1007 := @ep1006 1 0 1 ep1000 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 21 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1008 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz91)) ↑qz133) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 6391 750 0 1 1 21 0 1 913

noncomputable def ep1009 := @ep1008 2250 0 1 ep1003 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 21 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep1010 := @ep982 1 (@ep983 0 1 0 1 (BSN.bern_sum_base qz137 21) qz105) (ep984 (@ep985 1 1 1 504 0 1 (ep1001 rfl) (ep1004 rfl) rfl rfl) (@ep1005 1 913 913 2250 0 1 (ep1007 rfl) (ep1009 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1011 := ep976 (ep979 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep980 Bool.false 913 2250 0 1 (BSN.bern_sum_succ qz137 21 0 1 1 rfl rfl) (ep1010 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 17892309101 274877906944 777649547267 4558987525619712 294701537273

noncomputable def ep1013 := @ep1012 1470450872250 0 1 5272890997428388621573 404194458028059131904000 229174517039237375782891 ep960 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (ep963 ep972))

noncomputable def ep1014 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))) Bool.false 165013281413 329380995384 0 1 Bool.false

noncomputable def ep1015 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1))))))) 843620751118401624797 20209722901402956595200 92342424898942374776191

noncomputable def ep1016 := nat_lit 2681506873449749892877516800

noncomputable def ep1017 := nat_lit 1501643849131859940011409408

noncomputable def ep1018 := nat_lit 16712477405566675638277080648073350544883712

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 14313137945 68719476736 1566710946835 9117975051239424 294701537273

noncomputable def ep1020 := @ep1019 1470450872250 0 1 843620751118401624797 20209722901402956595200 92342424898942374776191 ep1016 (@Enclosure.Complex.IsNear.re_isNear qz203 Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (ep963 ep972))

noncomputable def ep1021 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz204 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz70 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz70 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz114 qz205 (@HSub.hSub Nat Nat Nat qz113 (@HMul.hMul Nat Nat Nat qz70 2 k) 1)))))) 17892309101 274877906944 777649547267 4558987525619712 165013281413

noncomputable def ep1022 := @ep1021 329380995384 0 1 2952468636811694039713 90539558598285245546496 128322503583861516048271 ep1017 (@Enclosure.Complex.IsNear.im_isNear qz203 Bool.true 14313137945 68719476736 1566710946835 9117975051239424 Bool.false 17892309101 274877906944 777649547267 4558987525619712 (ep963 ep972))

noncomputable abbrev qz482 := (ep1011 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1023 := @ep957 20673808204968630984439 ep894 ep900 ep896 (@ep958 ep959 5272890997428388621573 404194458028059131904000 229174517039237375782891 ep960 ep961 9226179706518622496851 78593366838789275648000 ep899 ep780 (ep973 (@ep974 294701537273 1470450872250 0 1 qz482) rfl) (ep1013 (@ep1014 294701537273 1470450872250 0 1 qz482) rfl) rfl rfl) (@ep1015 ep1016 2952468636811694039713 90539558598285245546496 128322503583861516048271 ep1017 ep1018 20673808204968630984439 ep894 ep900 ep896 (ep1020 (@ep1014 294701537273 1470450872250 0 1 qz482) rfl) (ep1022 (@ep974 294701537273 1470450872250 0 1 qz482) rfl) rfl rfl)

noncomputable def ep1024 := @ep903 ep895 ep896 (@ep904 18235950102478848 (BSN.head_sum_c_eq qz137 21) (ep905 (BSN.head_sum_c_succ qz137 20 21 rfl rfl) (ep956 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1023 rfl rfl rfl

noncomputable def ep1025 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz137 1 21) Bool.false 660080195433501569063971 314373467355157102592000 ep779 ep780 Bool.false 156749414865435202364261 ep894 ep895 ep896 (@ep897 ep780 Bool.false 156749414865435202364261 ep894 ep895 ep896 (BSN.zetaApproximant_eq_folded' qz137 1 21 rfl) (ep1024 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1026 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) (Complex.im (zetaApproximant qz137 1 21)) 99 1048576 10910035

noncomputable def ep1027 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174)) Bool.true 99 1048576 43640140

noncomputable def ep1028 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174) qz452 Bool.false 95531861 1048576 321

noncomputable def ep1029 := BSN.sin_dyadic_bound_f 204612 2147483648 1 0 1048576 265628 0 1 1 0 1 1 99 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 204612) qz292 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 204612) qz293 0 0 rfl) rfl rfl

noncomputable def ep1030 := @ep1028 1048576 Bool.true 99 1048576 1 132684 (@ep784 95531861 1048576 321 1048576 ep891 rfl) (Enclosure.sfrac_false_div 95531861 1048576) (BSN.sin_reduce2 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14398319793801265152) qz20) 226375608064910080 72057594037927936 Bool.false 99 1048576 14 1000000000000000 265368 132684 (BSN.sin_reduce_arg_pos_rat_q2 95531861 1048576 226375608064910080 72057594037927936 14 14398319793801265152 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 99 1048576 14398319793801265152 151115727451828646838272 204612 2147483648 265628 265368 (ep1029 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1031 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz137 1 21) Bool.false 660080195433501569063971 314373467355157102592000 ep779 ep780 Bool.false 156749414865435202364261 ep894 ep895 ep896 (@ep897 ep780 Bool.false 156749414865435202364261 ep894 ep895 ep896 (BSN.zetaApproximant_eq_folded' qz137 1 21 rfl) (ep1024 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow30.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 1 21 qz146) Bool.true ep762 ep763 ep764 ep765 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 21 qz146) ep766 Bool.true ep762 ep763 ep764 ep765 (@Eq.refl Real ep766) (@ep767 Bool.true ep762 ep763 ep764 ep765 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz370 (Complex.im (@HSub.hSub Complex Complex Complex qz63 qz172 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz173 (@Nat.cast Complex Complex.instNatCast j))))) qz174) (zetaApproximant qz137 1 21)) (@ep769 ep770 ep771 ep772 ep773 ep774 ep775 ep776 ep777 ep762 ep763 ep764 ep765 (@ep778 34782314496 660080195433501569063971 314373467355157102592000 ep779 ep780 ep768 ep770 ep771 ep772 (@ep781 139129257984 1048575 1048576 10910035 34782314496 (ep893 rfl rfl) rfl) ep1025 rfl) (@ep1026 34782314496 156749414865435202364261 ep894 ep895 ep896 ep773 ep774 ep775 ep776 (@ep1027 139129257984 99 1048576 10910035 34782314496 (ep1030 rfl rfl) rfl) ep1031 rfl) rfl rfl))

theorem EMRow30.d15 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow30.d16 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow30.d17 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow30.d18 : @Eq Nat (Nat.pow 20 (Nat.succ (Nat.mul 2 3))) 1280000000 := @Eq.refl Nat 1280000000

noncomputable abbrev qz543 := (@HAdd.hAdd Complex Complex Complex qz547 qz546 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz483 := qz543

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz483) (@HAdd.hAdd Real Real Real qz394 (Complex.re qz273) qz296))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz484 := (@HPow.hPow Complex Complex Complex qz523 (@Nat.cast Complex Complex.instNatCast 20) (@HSub.hSub Complex Complex Complex qz529 qz524 qz525))

noncomputable abbrev qz225 := qz484

noncomputable def ep1032 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 25843613951 618475290624 47730965 618475290624 559939609727677985 504403158265495552 159669267655

noncomputable def ep1033 := nat_lit 359344413356093401079157358592

noncomputable def ep1034 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) 26561 1769472 1 1769472 2918973 1048576 5281 1048576 25843613951 618475290624

noncomputable abbrev qz226 := qz272

noncomputable abbrev qz544 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz485 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz544 qz226 2))

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz485 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1036 := nat_lit 781950621441006189802102638025

noncomputable def ep1037 := nat_lit 19807040628566084398385987584

noncomputable def ep1038 := nat_lit 26986075409044041160201671

noncomputable def ep1039 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz486 := (@HPow.hPow Real Nat Real qz544 qz226 1)

noncomputable def ep1040 := @Enclosure.Real.IsNear.mulLit_ff qz486 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1036 ep1037 ep1038 ep1039

noncomputable def ep1041 := ep1040 (@Enclosure.Real.IsNear.of_eq qz486 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz487 := (@HPow.hPow Real Nat Real qz544 qz226 2)

noncomputable def ep1042 := @Enclosure.Real.IsNear.inv_image qz487 ep1036 ep1037 ep1038 ep1039 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz487 (@HMul.hMul Real Real Real qz0 qz486 qz226) Bool.false ep1036 ep1037 ep1038 ep1039 (BSN.pow_succ_r qz226 1 2 rfl) ep1041) rfl rfl rfl

noncomputable def ep1043 := ep1035 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz485 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1042 rfl rfl rfl) rfl)

noncomputable def ep1044 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 2918973 1048576 5281 1048576

noncomputable def ep1045 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 2918973 1048576 5281 1048576

noncomputable def ep1046 := nat_lit 2158296984766318956439669752517788391302953

noncomputable def ep1047 := nat_lit 278515619297388893158190432309477376000000

noncomputable def ep1048 := nat_lit 3436593457223966933670428893635227221692146963982541034159

noncomputable def ep1049 := nat_lit 122572798964820180906582350979576755969925107329007616000000

noncomputable def ep1050 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)))) ep1046 ep1047 ep1048 ep1049 1456846 1462127

noncomputable def ep1051 := nat_lit 13487741058442272103336178709718812408529256512801

noncomputable def ep1052 := nat_lit 1740592070763941482716723755765814037315584000000

noncomputable def ep1053 := nat_lit 1665421112199870586504225967569916366809643221167448619

noncomputable def ep1054 := nat_lit 59849999494541103958292163564246462875939993812992000000

noncomputable def ep1055 := nat_lit 4291046108462573330914436911731249039787321521

noncomputable def ep1056 := nat_lit 12377543614321361654874480041001344265355264000000

noncomputable def ep1057 := nat_lit 890035153056274914130141794897879395379229207986422843

noncomputable def ep1058 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))) ep1051 ep1052 ep1053 ep1054 ep1055 ep1056 ep1057

noncomputable def ep1059 := nat_lit 4226648240166213134709736240675060550687072666517504000000

noncomputable def ep1060 := nat_lit 166952572170373861070516634344523180908713012349213568062208036640108118385518304454380617728000000

noncomputable def ep1061 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20)) ep293 ep294 ep295 ep296 ep293 ep294 ep295 ep296 ep1051

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)) 65506076881939536059961 ep424 ep425 ep426 65506076881939536059961 ep424 ep425 ep426 ep1055

noncomputable def ep1063 := @ep1032 504403158265495552 ep1033 5229149440945088297 4539628424389459968 351783833899775 4539628424389459968 (@ep1034 47730965 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz485) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow30.d15 EMRow30.d16 rfl) (ep1043 rfl)) (ep1044 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 20)) (@ep1045 2918973 1048576 5281 1048576 (@ep1050 524288 (@ep1058 ep1059 ep1060 ep1046 ep1047 ep1048 ep1049 (@ep1061 ep1052 ep1053 ep1054 ep558 ep558 rfl) (@ep1062 ep1056 ep1057 ep1059 ep564 ep564 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz483)

noncomputable abbrev qz488 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1064 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz488) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 559939609727677985 504403158265495552 159669267655 504403158265495552 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz14 3)

noncomputable def ep1065 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz488) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 104916565 3670016 1 3670016 5336999069 137438953472 1471 137438953472

noncomputable def ep1066 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz488 104916565 1048576 1 1048576 2 7 0 1 104916565 3670016

noncomputable abbrev qz489 := (Complex.re qz543)

noncomputable abbrev qz490 := (Complex.im qz543)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz268 qz489 qz489) (@HMul.hMul Real Real Real qz268 qz490 qz490))

noncomputable abbrev qz229 := qz483

noncomputable def ep1067 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 104916565 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1068 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 104916565 1048576 1 1048576 104916565

noncomputable def ep1069 := @Enclosure.Real.IsNear.sqrt_image qz228 400450001 40000 0 1 52458282 52458283 524288

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz489 qz489)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz490 qz490)

noncomputable def ep1070 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 399960001 40000 0 1

noncomputable abbrev qz232 := qz489

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz491 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz491 qz14) Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz14 Bool.false 99995 1000 3 qz15)

noncomputable abbrev qz492 := (ep1072 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz14 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz19))

noncomputable def ep1073 := @ep1071 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz492)

noncomputable def ep1074 := ep1073 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz492)

noncomputable abbrev qz233 := qz490

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 99995 1000 0 1 99995 1000 0 1 399960001 40000

noncomputable def ep1076 := @ep1075 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz492)

noncomputable def ep1077 := ep1076 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz492)

noncomputable def ep1078 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 5336999069 137438953472

noncomputable def ep1079 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 5336999069 137438953472

noncomputable def ep1080 := nat_lit 714033998944123922161037559556007070759135047072755884012313

noncomputable def ep1081 := nat_lit 473526530495212545497993885800075698368522143924224000000000000

noncomputable def ep1082 := nat_lit 469563263800201195188682123961748822297705269094752762893291323041167

noncomputable def ep1083 := nat_lit 565352060027922787918672534147826356194231499138258698240000000000000000000000

noncomputable def ep1084 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1080 ep1081 ep1082 ep1083

noncomputable def ep1085 := nat_lit 595921357790575845144710062834822369514571675313472856787849

noncomputable def ep1086 := nat_lit 126056813399752631258145670898828442659759997553499337073352888016757

noncomputable def ep1087 := nat_lit 188450686675974262639557511382608785398077166379419566080000000000000000000000

noncomputable def ep1088 := nat_lit 820226674677417201502274282786004869753912303883909911281

noncomputable def ep1089 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1085 ep1081 ep1086 ep1087 ep1088

noncomputable def ep1090 := nat_lit 3288378683994531565958290873611636794225848221696000000000000

noncomputable def ep1091 := nat_lit 5712051475058956338390319454078968394901579777140921979577041186931

noncomputable def ep1092 := nat_lit 35334503751745174244917033384239147262139468696141168640000000000000000000000

noncomputable def ep1093 := nat_lit 2348014181775230964862067380503646519880960112859412317821614740262186852415863352289667146578623328417742848000000000000

noncomputable def ep1094 := nat_lit 771959427554697232706390048957

noncomputable def ep1095 := nat_lit 21760664753063325144711168000000

noncomputable def ep1096 := nat_lit 7088848894254402629283761285039

noncomputable def ep1097 := nat_lit 751898969295691206640848076800000000000

noncomputable def ep1098 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1094 ep1095 ep1096 ep1097 ep1094 ep1095 ep1096

noncomputable def ep1099 := nat_lit 28639599764616425266010122841

noncomputable def ep1100 := nat_lit 1813388729421943762059264000000

noncomputable def ep1101 := nat_lit 962025349744259172317772553291

noncomputable def ep1102 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1094 ep1095 ep1096 ep1097 Bool.true ep1099 ep1100 ep1101

noncomputable def ep1103 := nat_lit 187974742323922801660212019200000000000

noncomputable def ep1104 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1094 ep1095 ep1096 ep1097 Bool.true ep1099 ep1100 ep1101 ep1103

noncomputable def ep1105 := nat_lit 2361802697005347358663401

noncomputable def ep1106 := nat_lit 3022314549036572936765440000

noncomputable def ep1107 := nat_lit 66340312914227493027929401

noncomputable def ep1108 := nat_lit 313291237206538002767020032000000000

noncomputable def ep1109 := nat_lit 754954448136258731724013561757

noncomputable def ep1110 := nat_lit 6929632143260256646016730722639

noncomputable abbrev qz234 := (Complex.re qz484)

noncomputable abbrev qz235 := (Complex.im qz484)

noncomputable def ep1111 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1105 ep1106 ep1107 ep1108 ep1109 ep1095 ep1110

noncomputable def ep1112 := nat_lit 2333104209164505763028004492850178735247320426825646080000

noncomputable def ep1113 := nat_lit 16317251937840520977448960000

noncomputable def ep1114 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 1199830003 19200000 0 1 29526716590267005 2361183241434822606848 55291426909106467 ep1113 ep1105

noncomputable def ep1115 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1199830003 19200000 0 1 0 1 0 1 1199830003

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3599490009 80000 0 1 1199830003 19200000 0

noncomputable def ep1117 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz11) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow30.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz11 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz493 := (@HAdd.hAdd Complex Complex Complex qz522 qz521 qz526)

noncomputable abbrev qz236 := qz493

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1

noncomputable abbrev qz237 := (Complex.re qz493)

noncomputable abbrev qz238 := (Complex.im qz493)

noncomputable def ep1119 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 399930001 16000 0 1 399960001 20000 0 1

noncomputable def ep1120 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 399930001 40000 0 1 5 2 0 1 399930001 16000

noncomputable abbrev qz494 := (@HAdd.hAdd Complex Complex Complex qz522 qz521 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz494

noncomputable def ep1121 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1

noncomputable abbrev qz240 := (Complex.re qz494)

noncomputable abbrev qz241 := (Complex.im qz494)

noncomputable def ep1122 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 399960001 40000 0 1

noncomputable def ep1123 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1124 := @ep1123 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable abbrev qz495 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1125 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz495 qz14) Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz14 Bool.false 99995 1000 1 qz15)

noncomputable abbrev qz496 := (ep1125 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz14 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz19))

noncomputable def ep1126 := ep1124 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz496)

noncomputable def ep1127 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 99995 1000 0 1 99995 1000 0 1 399960001 40000

noncomputable def ep1128 := @ep1127 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep1129 := ep1128 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz496)

noncomputable def ep1130 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 (@ep1122 1599720004 399930001 40000 0 1 (ep1126 rfl) (ep1129 rfl) rfl rfl)

noncomputable def ep1131 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 19999 400 0 1 59997 400 0 1

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 99995 1000 0 1 19999 400

noncomputable def ep1133 := @ep1132 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep1134 := ep1133 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz496)

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 99995 1000 0 1 3 2 0 1 59997 400

noncomputable def ep1136 := @ep1135 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep522)

noncomputable def ep1137 := ep1136 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz496)

noncomputable abbrev qz242 := (ep1121 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1130 (@ep1131 31998400 19999 100 0 1 (ep1134 rfl) (ep1137 rfl) rfl rfl)))

noncomputable def ep1138 := @ep1120 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz242)

noncomputable abbrev qz497 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1139 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz497 qz14) Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz14 Bool.false 99995 1000 2 qz15)

noncomputable abbrev qz498 := (ep1139 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz14 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz19))

noncomputable def ep1140 := ep1138 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz498)

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 19999 100 0 1 99995 1000 0 1 399960001 20000

noncomputable def ep1142 := @ep1141 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz242)

noncomputable def ep1143 := ep1142 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz498)

noncomputable def ep1144 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 (@ep1119 14397960036000 3599490009 80000 0 1 (ep1140 rfl) (ep1143 rfl) rfl rfl)

noncomputable def ep1145 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 7998200089999 8000000 0 1 19999 40 0 1

noncomputable def ep1146 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 399930001 40000 0 1 99995 1000 0 1 7998200089999 8000000

noncomputable def ep1147 := @ep1146 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz242)

noncomputable def ep1148 := ep1147 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz498)

noncomputable def ep1149 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 19999 100 0 1 5 2 0 1 19999 40

noncomputable def ep1150 := @ep1149 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz242)

noncomputable def ep1151 := ep1150 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz498)

noncomputable abbrev qz243 := (ep1118 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1144 (@ep1145 319768011599960 7994200289999 8000000 0 1 (ep1148 rfl) (ep1151 rfl) rfl rfl)))

noncomputable def ep1152 := @ep1116 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz243)

noncomputable def ep1153 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 7994200289999 8000000 0 1 0 1 0

noncomputable def ep1154 := @ep1153 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz243)

noncomputable def ep1155 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 7994200289999 5760000000 0 1 0 1 0 1 7994200289999

noncomputable def ep1156 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 7994200289999 8000000 0 1 7994200289999 5760000000 0

noncomputable def ep1157 := @ep1156 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz243)

noncomputable def ep1158 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3599490009 80000 0 1 0 1 0

noncomputable def ep1159 := @ep1158 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz243)

noncomputable def ep1160 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 (@ep1115 1199830003 19200000 0 1 (ep1152 rfl) (ep1154 rfl) rfl rfl) (@ep1155 7994200289999 5760000000 0 1 (ep1157 rfl) (ep1159 rfl) rfl rfl)

noncomputable def ep1161 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 ep1160

noncomputable def ep1162 := nat_lit 130538015502724167819591680000

noncomputable def ep1163 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.true 29526716590267005 2361183241434822606848 55291426909106467 ep1113 Bool.false 472188849884541215 18889465931478580854784 866832440003967361 ep1162

noncomputable abbrev qz499 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 1280000000)))

noncomputable def ep1164 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz499 qz128) (@HMul.hMul Real Real Real qz0 qz499 qz422)) Bool.true 29526716590267005 2361183241434822606848 55291426909106467 ep1113 Bool.false 472188849884541215 18889465931478580854784 866832440003967361

noncomputable abbrev qz500 := (Real.sqrt (@Nat.cast Real Real.instNatCast 1280000000))

noncomputable abbrev qz501 := (@Nat.cast Real Real.instNatCast 1280000000)

noncomputable def ep1165 := @Enclosure.Real.IsNear.inv_image qz500 4917165483517163 137438953472 1 137438953472 1920767 1920768 68719476736 (@Enclosure.Real.IsNear.of_eq qz500 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz501 qz16)) Bool.false 4917165483517163 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 1280000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz501 qz16)) Bool.false 4917165483517163 137438953472 1 137438953472 4917165483517163 137438953472 1 137438953472 (BSN.sqrt_enclosure 1280000000 1 2458582741758581 2458582741758582 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1166 := nat_lit 7417073856812098318501937152

noncomputable def ep1167 := nat_lit 2475880078570760549798248448

noncomputable def ep1168 := nat_lit 21229440000000000000000000

noncomputable def ep1169 := BSN.log_dyadic_bound 4 36 6 5 38005766984454635520 68719476736 21229440000 157571184526884864 990904320 15334308083 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 36) 0 5 157571184526884864 38005766984454635520 990904320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1170 := @Enclosure.Real.IsNear.mulLit_ff qz14 qz130 99995 1000 0 1 3372894687714551 1125899906842624 390658171 8292750000000000000 67454520859603305449 225179981368524800 7812772761829 1658550000000000000000 qz19 (BSN.isNear_log_sfrac 20 1 3372894687714551 1125899906842624 390658171 8292750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz425 Bool.false ep1166 ep1167 1000084917760000 ep1168 3372894687714551 1125899906842624 390658171 8292750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 15334308083 68719476736 24973259072661432 36028797018963968 21229440000 1000000000000000 rfl rfl rfl rfl (ep1169 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1171 := nat_lit 21925336329814276097582301184

noncomputable def ep1172 := nat_lit 7418189462824577424079455067485192770740243876587053069847625670045522424516677777198806674930081706202677522041708303139704558467962547825806894149836959649606764751558377047686641

noncomputable def ep1173 := nat_lit 118471658034259428782235204372444635462331972429639033257780066369387519461588934825569028614577116538889267969336012369372246813616988720376390556367654990461123310430062324062617600

noncomputable def ep1174 := nat_lit 837138975607167629907319708304204371190224742074349061282457552322783289530584357139469916727183550844975155209955777735038972070912449269210672757134972047305994073816792561

noncomputable def ep1175 := nat_lit 44976888902011099055214124549665707565784715233783894689067097044229857752249391702194678466552902400833361316551824090577944926946153229994852268343083208483124174317466711846387185

noncomputable def ep1176 := nat_lit 10780920881117608019183403597892461827072209491097152026457986039614264271004593069126781603926517605038923385209577125612874460039145973554251540629456604131962221249135671489698201600

noncomputable def ep1177 := BSN.cos_dyadic_bound_f 311577769164931 281474976710656 4 3 137438953472 42500343751 ep1172 ep1173 ep1174 ep1175 ep1176 ep1174 61489413144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 311577769164931) (BSN.cosEvenQ 281474976710656) 0 3 ep1172 ep1173 ep1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 311577769164931) (BSN.cosOddQ 281474976710656) 0 3 ep1175 ep1176 ep1174 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz502 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41170972204347) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1178 := @Enclosure.Real.IsNear.cos_image qz131 qz502 Bool.false 41170972204347 137438953472 649 137438953472 Bool.true 61489413144 137438953472 1 21229440000 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 67454520859603305449 225179981368524800 7812772761829 1658550000000000000000 41170972204347 137438953472 649 137438953472 (ep1170 rfl) rfl) (Enclosure.sfrac_false_div 41170972204347 137438953472) (BSN.cos_reduce2 qz502 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1171) (@Nat.cast Real Real.instNatCast ep1037)) 226375608064910080 72057594037927936 Bool.false 61489413144 137438953472 47 1000000000000000 42458880000 21229440000 (BSN.sin_reduce_arg_pos_rat_q2 41170972204347 137438953472 226375608064910080 72057594037927936 47 ep1171 ep1037 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 61489413144 137438953472 ep1171 ep1037 311577769164931 281474976710656 42500343751 42458880000 (ep1177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1179 := nat_lit 19279637093172818166980686372514366059463178197517550446081541588397308914609207583824590925559103234804835052216644713750085893984244148737093401052922813985222743476380080815832561

noncomputable def ep1180 := nat_lit 1540131554445372574169057656841780261010315641585307432351140862802037753000656152732397371989502515005560483601368160801839208577020853364893077232779514875994603035590810212814028800

noncomputable def ep1181 := nat_lit 96368609184869943681078204921700898993797075860044146732651376282517149728373072161495822637228776210043706516810710648421335144880842969910338841832648772137909010840337726125211121

noncomputable def ep1182 := nat_lit 53904604405588040095917017989462309135361047455485760132289930198071321355022965345633908019632588025194616926047885628064372300195729867771257703147283020659811106245678357448491008000

noncomputable def ep1183 := BSN.sin_dyadic_bound_f 311577769164931 281474976710656 4 3 137438953472 42500343751 ep1179 ep1180 ep1174 ep1181 ep1182 ep1174 122916711649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 311577769164931) (BSN.sinEvenQ 281474976710656) 0 3 ep1179 ep1180 ep1174 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 311577769164931) (BSN.sinOddQ 281474976710656) 0 3 ep1181 ep1182 ep1174 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1184 := @Enclosure.Real.IsNear.sin_image qz131 qz502 Bool.false 41170972204347 137438953472 649 137438953472 Bool.true 122916711649 137438953472 1 21229440000 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 67454520859603305449 225179981368524800 7812772761829 1658550000000000000000 41170972204347 137438953472 649 137438953472 (ep1170 rfl) rfl) (Enclosure.sfrac_false_div 41170972204347 137438953472) (BSN.sin_reduce2 qz502 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1171) (@Nat.cast Real Real.instNatCast ep1037)) 226375608064910080 72057594037927936 Bool.false 122916711649 137438953472 47 1000000000000000 42458880000 21229440000 (BSN.sin_reduce_arg_pos_rat_q2 41170972204347 137438953472 226375608064910080 72057594037927936 47 ep1171 ep1037 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122916711649 137438953472 ep1171 ep1037 311577769164931 281474976710656 42500343751 42458880000 (ep1183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1185 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz499 qz128) (@HMul.hMul Real Real Real qz0 qz499 qz422) Bool.true 29526716590267005 2361183241434822606848 55291426909106467 ep1113 Bool.false 472188849884541215 18889465931478580854784 866832440003967361 ep1162 (@Enclosure.Real.IsNear.mulLit_ft qz499 qz128 3841535 137438953472 1 137438953472 7686176643 17179869184 13589204603 2849367203512320000 29526716590267005 2361183241434822606848 55291426909106467 ep1113 (@Enclosure.Real.IsNear.recentre' qz499 Bool.false 3841535 137438953472 1 137438953472 3841535 137438953472 1 137438953472 (ep1165 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz128 Bool.true 61489413144 137438953472 13915345513472 2917752016396615680000 7686176643 17179869184 13589204603 2849367203512320000 (ep1178 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz499 qz422 3841535 137438953472 1 137438953472 122916711649 137438953472 13589204603 2849367203512320000 472188849884541215 18889465931478580854784 866832440003967361 ep1162 (@Enclosure.Real.IsNear.recentre' qz499 Bool.false 3841535 137438953472 1 137438953472 3841535 137438953472 1 137438953472 (ep1165 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz129 Bool.true 122916711649 137438953472 13589204603 2849367203512320000 (@Enclosure.Real.IsNear.recentre' qz129 Bool.true 122916711649 137438953472 13915345513472 2917752016396615680000 122916711649 137438953472 13589204603 2849367203512320000 (ep1184 rfl rfl) rfl)) rfl)

noncomputable def ep1186 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 7994200289999 5760000000 0 1 472188849884541215 18889465931478580854784 866832440003967361 ep1162 ep1109

noncomputable def ep1187 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 ep1160

noncomputable def ep1188 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.true 29526716590267005 2361183241434822606848 55291426909106467 ep1113 Bool.false 472188849884541215 18889465931478580854784 866832440003967361 ep1162

noncomputable def ep1189 := nat_lit 113309269834707127129414729

noncomputable def ep1190 := nat_lit 72535549176877750482370560000

noncomputable def ep1191 := nat_lit 1040051569090457478760532083

noncomputable def ep1192 := nat_lit 2506329897652304022136160256000000000

noncomputable def ep1193 := nat_lit 5245388585080683907374248511

noncomputable def ep1194 := nat_lit 302231454903657293676544000000

noncomputable def ep1195 := nat_lit 442010741031237430705366323533

noncomputable def ep1196 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) ep1189 ep1190 ep1191 ep1192 ep1193 ep1194 ep1195

noncomputable def ep1197 := nat_lit 93987371161961400830106009600000000000

noncomputable def ep1198 := nat_lit 346231516188738527028049665093048325850523278413660160000

noncomputable def ep1199 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 1199830003 19200000 0 1 472188849884541215 18889465931478580854784 866832440003967361 ep1162 ep1189

noncomputable def ep1200 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 7994200289999 5760000000 0 1 29526716590267005 2361183241434822606848 55291426909106467 ep1113 ep1193

noncomputable abbrev qz503 := (@ep1164 ep1162 (BSN.cpow_neg_s_sub_mk qz14 99995 1000 20 3 1280000000 qz15 rfl EMRow30.d18) ep1185)

noncomputable def ep1201 := ep1104 (@ep1111 ep1097 ep1112 ep1094 ep1095 ep1096 ep1097 (@ep1114 ep1106 ep1107 ep1108 ep1161 (ep1163 qz503) rfl) (@ep1186 ep1095 ep1110 ep1097 ep1187 (ep1188 qz503) rfl) rfl rfl) (@ep1196 ep1197 ep1198 ep1099 ep1100 ep1101 ep1103 (@ep1199 ep1190 ep1191 ep1192 ep1161 (ep1188 qz503) rfl) (@ep1200 ep1194 ep1195 ep1197 ep1187 (ep1163 qz503) rfl) rfl rfl)

noncomputable def ep1202 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1099 ep1100 ep1101 ep1103 ep1099 ep1100 ep1101

noncomputable def ep1203 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1094 ep1095 ep1096 ep1097 Bool.true ep1099 ep1100 ep1101

noncomputable def ep1204 := @ep1065 559939609727677985 504403158265495552 159669267655 504403158265495552 (@ep1066 1 3670016 (ep1067 (@ep1068 1048576 1 1048576 (ep1069 (@ep1070 1601800004 400450001 40000 0 1 (ep1074 rfl) (ep1077 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1078 1471 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1079 1471 137438953472 5336999069 137438953472 1471 137438953472 (@ep1084 2668498799 2668500270 68719476736 (@ep1089 ep1090 ep1091 ep1092 ep1093 ep1080 ep1081 ep1082 ep1083 (@ep1098 ep1097 ep1085 ep1081 ep1086 ep1087 (@ep1102 ep1103 ep1201) (@ep1102 ep1103 ep1201) rfl) (@ep1202 ep1103 ep1088 ep1090 ep1091 ep1092 (@ep1203 ep1103 ep1201) (@ep1203 ep1103 ep1201) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow30.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 5229149440945088297 4539628424389459968 351783833899775 4539628424389459968 := ep1063 (ep1064 ep1204) rfl rfl

theorem EMRow30.d20 : @Eq Nat (Nat.pow 21 (Nat.succ (Nat.mul 2 3))) 1801088541 := @Eq.refl Nat 1801088541

noncomputable abbrev qz545 := (@HAdd.hAdd Complex Complex Complex qz547 qz553 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz504 := qz545

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz504) (@HAdd.hAdd Real Real Real qz394 (Complex.re qz430) qz296))

noncomputable abbrev qz505 := (@HPow.hPow Complex Complex Complex qz523 (@Nat.cast Complex Complex.instNatCast 21) (@HSub.hSub Complex Complex Complex qz529 qz538 qz525))

noncomputable abbrev qz245 := qz505

noncomputable def ep1205 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 4875829331 154618822656 1427199 17179869184 516179745995896887 504403158265495552 170997230753

noncomputable def ep1206 := nat_lit 82270488318478645172407107584

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21)) 26561 1769472 1 1769472 550713 262144 715 131072 4875829331 154618822656

noncomputable def ep1208 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21)) (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz137 1 21)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz137 1 21)) (Complex.im (zetaApproximant qz137 1 21))))) Bool.false 550713 262144 715 131072

noncomputable def ep1209 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz137 1 21)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz137 1 21)) (Complex.im (zetaApproximant qz137 1 21))))) Bool.false 2202852 1048576 5720 1048576

noncomputable def ep1210 := nat_lit 864973055833320654049406823868657329470441

noncomputable def ep1211 := nat_lit 195987679359651008575971103566987264000000

noncomputable def ep1212 := nat_lit 358893342250784198510169804783052824395674430326548141937

noncomputable def ep1213 := nat_lit 15659265622469084282726881239358856053533063990214656000000

noncomputable def ep1214 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz137 1 21)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz137 1 21)) (Complex.im (zetaApproximant qz137 1 21)))) ep1210 ep1211 ep1212 ep1213 1098566 1104286

noncomputable def ep1215 := nat_lit 435705864403529625669027500689614818745090288841

noncomputable def ep1216 := nat_lit 98830676976904028469180020449544413118464000000

noncomputable def ep1217 := nat_lit 347027777723466871362589398166929910542172362506631258937

noncomputable def ep1218 := nat_lit 24570379060656318400116742077377388364130076121

noncomputable def ep1219 := nat_lit 5123382294482704835842292260104382376061173760000

noncomputable def ep1220 := nat_lit 3955188175772442382526802205374304617834022606638961

noncomputable def ep1221 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz137 1 21)) (Complex.re (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz137 1 21)) (Complex.im (zetaApproximant qz137 1 21))) ep1215 ep1216 ep1217 ep1213 ep1218 ep1219 ep1220

noncomputable def ep1222 := nat_lit 5219755207489694760908960413119618684511021330071552000

noncomputable def ep1223 := nat_lit 2234716018483469694246097940694888772061187639655744689550660550743079487438734088034488156160000

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz137 1 21)) (Complex.re (zetaApproximant qz137 1 21)) 660080195433501569063971 314373467355157102592000 ep779 ep780 660080195433501569063971 314373467355157102592000 ep779 ep780 ep1215

noncomputable def ep1225 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz137 1 21)) (Complex.im (zetaApproximant qz137 1 21)) 156749414865435202364261 ep894 ep895 ep896 156749414865435202364261 ep894 ep895 ep896 ep1218

noncomputable def ep1226 := @ep1205 504403158265495552 ep1206 4788772687227386351 4539628424389459968 42073742552225 504403158265495552 (@ep1207 1427199 17179869184 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz485) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow30.d15 EMRow30.d16 rfl) (ep1043 rfl)) (ep1208 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz137 1 21)) (@ep1209 550713 262144 715 131072 (@ep1214 524288 (@ep1221 ep1222 ep1223 ep1210 ep1211 ep1212 ep1213 (@ep1224 ep1216 ep1217 ep1213 ep1025 ep1025 rfl) (@ep1225 ep1219 ep1220 ep1222 ep1031 ep1031 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz504)

noncomputable def ep1227 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz488) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 516179745995896887 504403158265495552 170997230753 504403158265495552 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz146 3)

noncomputable def ep1228 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz488) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 107285977 3670016 1 3670016 4811250831 137438953472 1549 137438953472

noncomputable def ep1229 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz488 107285977 1048576 1 1048576 2 7 0 1 107285977 3670016

noncomputable abbrev qz506 := (Complex.re qz545)

noncomputable abbrev qz507 := (Complex.im qz545)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz268 qz506 qz506) (@HMul.hMul Real Real Real qz268 qz507 qz507))

noncomputable abbrev qz248 := qz504

noncomputable def ep1230 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 107285977 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1231 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 107285977 1048576 1 1048576 107285977

noncomputable def ep1232 := @Enclosure.Real.IsNear.sqrt_image qz247 654283721 62500 0 1 53642988 53642989 524288

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz506 qz506)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz507 qz507)

noncomputable def ep1233 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 163379524 15625 0 1

noncomputable abbrev qz251 := qz506

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1235 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz491 qz146) Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 102256 1000 3 qz147)

noncomputable abbrev qz508 := (ep1235 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz146 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz148))

noncomputable def ep1236 := @ep1234 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1237 := ep1236 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable abbrev qz252 := qz507

noncomputable def ep1238 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 102256 1000 0 1 102256 1000 0 1 163379524 15625

noncomputable def ep1239 := @ep1238 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1240 := ep1239 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 102256 1000 0 1 qz508)

noncomputable def ep1241 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 4811250831 137438953472

noncomputable def ep1242 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 4811250831 137438953472

noncomputable def ep1243 := nat_lit 192153471238615273326920296651281492087885340390072394156221

noncomputable def ep1244 := nat_lit 156802114677168443963923019104558791838924800000000000000000000

noncomputable def ep1245 := nat_lit 2894762634613433921133675353764070355765180072169514971641793492527954421

noncomputable def ep1246 := nat_lit 3670674955425067521357246980361563802483588842820033320268595200000000000000000000

noncomputable def ep1247 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1243 ep1244 ep1245 ep1246

noncomputable def ep1248 := nat_lit 44449975974456024071065393385929718739956296580784464553361

noncomputable def ep1249 := nat_lit 313604229354336887927846038209117583677849600000000000000000000

noncomputable def ep1250 := nat_lit 1336442792942892874491042334160352272550565672500122898788906137182456497

noncomputable def ep1251 := nat_lit 14682699821700270085428987921446255209934355371280133281074380800000000000000000000

noncomputable def ep1252 := nat_lit 339856966502774522582775199916633265435814384199360323759081

noncomputable def ep1253 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1248 ep1249 ep1250 ep1251 ep1252

noncomputable def ep1254 := nat_lit 10242607745510842810043659080895929150510154616177936987778267832929361187

noncomputable def ep1255 := nat_lit 120520282531093361645073823467940577928245925425921286509349485565552182275462933985289352567359484723200000000000000000000

noncomputable def ep1256 := nat_lit 210831629445052727057839750231

noncomputable def ep1257 := nat_lit 17708874310761169551360000000000

noncomputable def ep1258 := nat_lit 655069736550028400900082087810511

noncomputable def ep1259 := nat_lit 171363355602650767451623564247040000000000

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1256 ep1257 ep1258 ep1259 ep1256 ep1257 ep1258

noncomputable def ep1261 := nat_lit 582972526370475303020989405741

noncomputable def ep1262 := nat_lit 1815663573194503513693534090025521

noncomputable def ep1263 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1256 ep1257 ep1258 ep1259 Bool.true ep1261 ep1257 ep1262

noncomputable def ep1264 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.true ep1256 ep1257 ep1258 ep1259 Bool.true ep1261 ep1257 ep1262 ep1259

noncomputable def ep1265 := nat_lit 69403587847340572792730357

noncomputable def ep1266 := nat_lit 47223664828696452136960000000

noncomputable def ep1267 := nat_lit 210202481791562187597899646917

noncomputable def ep1268 := nat_lit 456968948273735379870996171325440000000

noncomputable def ep1269 := nat_lit 46201321000575003065141466589

noncomputable def ep1270 := nat_lit 4427218577690292387840000000000

noncomputable def ep1271 := nat_lit 20580135924221163591102490007737

noncomputable abbrev qz253 := (Complex.re qz505)

noncomputable abbrev qz254 := (Complex.im qz505)

noncomputable def ep1272 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1265 ep1266 ep1267 ep1268 ep1269 ep1270 ep1271

noncomputable def ep1273 := nat_lit 6120119842951813123272270151680000000000

noncomputable def ep1274 := nat_lit 2489060551050274941058139191325821920709403150909440000000

noncomputable def ep1275 := nat_lit 15232298275791179329033205710848

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1960476163 30000000 0 1 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 ep1265

noncomputable def ep1277 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) 1960476163 30000000 0 1 0 1 0 1 1960476163

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5881428489 125000 0 1 1960476163 30000000 0

noncomputable abbrev qz509 := (@HAdd.hAdd Complex Complex Complex qz522 qz537 qz526)

noncomputable abbrev qz255 := qz509

noncomputable def ep1279 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1

noncomputable abbrev qz256 := (Complex.re qz509)

noncomputable abbrev qz257 := (Complex.im qz509)

noncomputable def ep1280 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 653471221 25000 0 1 326759048 15625 0 1

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 653471221 62500 0 1 5 2 0 1 653471221 25000

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz522 qz537 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz510

noncomputable def ep1282 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz62 (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1

noncomputable abbrev qz259 := (Complex.re qz510)

noncomputable abbrev qz260 := (Complex.im qz510)

noncomputable def ep1283 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 163379524 15625 0 1

noncomputable def ep1284 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1285 := @ep1284 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep1286 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz495 qz146) Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 102256 1000 1 qz147)

noncomputable abbrev qz511 := (ep1286 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz146 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz148))

noncomputable def ep1287 := ep1285 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz511)

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 102256 1000 0 1 102256 1000 0 1 163379524 15625

noncomputable def ep1289 := @ep1288 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep1290 := ep1289 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz511)

noncomputable def ep1291 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 (@ep1283 653471221 653471221 62500 0 1 (ep1287 rfl) (ep1290 rfl) rfl rfl)

noncomputable def ep1292 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 6391 125 0 1 19173 125 0 1

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 102256 1000 0 1 6391 125

noncomputable def ep1294 := @ep1293 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep1295 := ep1294 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz511)

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 102256 1000 0 1 3 2 0 1 19173 125

noncomputable def ep1297 := @ep1296 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 102256 1000 0 1 ep990)

noncomputable def ep1298 := ep1297 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 102256 1000 0 1 qz511)

noncomputable abbrev qz261 := (ep1282 (BSN.ascPochhammer_succ_eval_c 1 2 qz430 rfl) (ep1291 (@ep1292 3195500 25564 125 0 1 (ep1295 rfl) (ep1298 rfl) rfl rfl)))

noncomputable def ep1299 := @ep1281 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz261)

noncomputable def ep1300 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz497 qz146) Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 (BSN.s_add_nat_mk qz146 Bool.false 102256 1000 2 qz147)

noncomputable abbrev qz512 := (ep1300 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz146 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz148))

noncomputable def ep1301 := ep1299 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz512)

noncomputable def ep1302 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 25564 125 0 1 102256 1000 0 1 326759048 15625

noncomputable def ep1303 := @ep1302 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz261)

noncomputable def ep1304 := ep1303 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz512)

noncomputable def ep1305 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 (@ep1280 18379464028125 5881428489 125000 0 1 (ep1301 rfl) (ep1304 rfl) rfl rfl)

noncomputable def ep1306 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 4176334573411 3906250 0 1 12782 25 0 1

noncomputable def ep1307 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 653471221 62500 0 1 102256 1000 0 1 4176334573411 3906250

noncomputable def ep1308 := @ep1307 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz261)

noncomputable def ep1309 := ep1308 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz512)

noncomputable def ep1310 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 25564 125 0 1 5 2 0 1 12782 25

noncomputable def ep1311 := @ep1310 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 653471221 62500 0 1 Bool.false 25564 125 0 1 qz261)

noncomputable def ep1312 := ep1311 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 102256 1000 0 1 qz512)

noncomputable abbrev qz262 := (ep1279 (BSN.ascPochhammer_succ_eval_c 2 3 qz430 rfl) (ep1305 (@ep1306 104358434647775 4174337385911 3906250 0 1 (ep1309 rfl) (ep1312 rfl) rfl rfl)))

noncomputable def ep1313 := @ep1278 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz262)

noncomputable def ep1314 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 4174337385911 3906250 0 1 0 1 0

noncomputable def ep1315 := @ep1314 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz262)

noncomputable def ep1316 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) 4174337385911 2812500000 0 1 0 1 0 1 4174337385911

noncomputable def ep1317 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 4174337385911 3906250 0 1 4174337385911 2812500000 0

noncomputable def ep1318 := @ep1317 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz262)

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5881428489 125000 0 1 0 1 0

noncomputable def ep1320 := @ep1319 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1117) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5881428489 125000 0 1 Bool.true 4174337385911 3906250 0 1 qz262)

noncomputable def ep1321 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 (@ep1277 1960476163 30000000 0 1 (ep1313 rfl) (ep1315 rfl) rfl rfl) (@ep1316 4174337385911 2812500000 0 1 (ep1318 rfl) (ep1320 rfl) rfl rfl)

noncomputable def ep1322 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 ep1321

noncomputable def ep1323 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.true 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 Bool.false 33203823789982497 4722366482869645213696 34511094372911723369 ep1275

noncomputable abbrev qz513 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 1801088541)))

noncomputable def ep1324 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz513 qz216) (@HMul.hMul Real Real Real qz0 qz513 qz477)) Bool.true 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 Bool.false 33203823789982497 4722366482869645213696 34511094372911723369

noncomputable abbrev qz514 := (Real.sqrt (@Nat.cast Real Real.instNatCast 1801088541))

noncomputable abbrev qz515 := (@Nat.cast Real Real.instNatCast 1801088541)

noncomputable def ep1325 := @Enclosure.Real.IsNear.inv_image qz514 5832803839903753 137438953472 1 137438953472 1619244 1619245 68719476736 (@Enclosure.Real.IsNear.of_eq qz514 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz515 qz16)) Bool.false 5832803839903753 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 1801088541) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz515 qz16)) Bool.false 5832803839903753 137438953472 1 137438953472 5832803839903753 137438953472 1 137438953472 (BSN.sqrt_enclosure 1801088541 1 2916401919951876 2916401919951877 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1326 := nat_lit 14399842078125000000000000

noncomputable def ep1327 := nat_lit 1612782312750000000000000

noncomputable def ep1328 := nat_lit 7537872452288246512636395520

noncomputable def ep1329 := nat_lit 25804517004000000000000000

noncomputable def ep1330 := BSN.log_dyadic_bound 5 37 7 6 889587219309193167697935 68719476736 25804517004 5475184526753597622000 2537841796875 18687142634 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 5) (BSN.artanhQ 37) 0 6 5475184526753597622000 889587219309193167697935 2537841796875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ff qz146 qz480 102256 1000 0 1 3427827528998135 1125899906842624 62506451129251 ep1327 4381449147565416157 14073748835532800 57068389881006163 ep1326 qz148 (BSN.isNear_log_sfrac 21 1 3427827528998135 1125899906842624 62506451129251 ep1327 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz479) Bool.false ep1328 ep1167 1000103218068016 ep1329 3427827528998135 1125899906842624 62506451129251 ep1327 (BSN.log_rat_reduce_isNear 21 1 4 42 32 18687142634 68719476736 24973259072661432 36028797018963968 25804517004 1000000000000000 rfl rfl rfl rfl (ep1330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1332 := nat_lit 6001804371701833502677794816

noncomputable def ep1333 := nat_lit 558057267780038059695777921878588607402172812854870764571826430220760017986812094255377060937429441332869648138995521

noncomputable def ep1334 := nat_lit 1588688889838625401839090896837790508620815087385166809651675190059187501826767531852223215396959798637323240569170821120

noncomputable def ep1335 := nat_lit 2800375567389328564363790634834233737959217091212841452237234570390429549917313817849445288204809232468061816641

noncomputable def ep1336 := nat_lit 1674166202588979400430205038054496153739042520130429868032574816193139273101336448138495483921711914380144008293353281

noncomputable def ep1337 := nat_lit 71491000042738143082759090357700572887936678932332506434325383552663437582204538933350044692863190938679545825612686950400

noncomputable def ep1338 := BSN.cos_dyadic_bound_f 85290769955319 281474976710656 3 2 137438953472 51659433456 ep1333 ep1334 ep1335 ep1336 ep1337 ep1335 131177447412 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 85290769955319) (BSN.cosEvenQ 281474976710656) 0 2 ep1333 ep1334 ep1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 85290769955319) (BSN.cosOddQ 281474976710656) 0 2 ep1336 ep1337 ep1335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz516 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42787589331693) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1339 := @Enclosure.Real.IsNear.cos_image qz218 qz516 Bool.false 42787589331693 137438953472 273 68719476736 Bool.true 131177447412 137438953472 1 25804517004 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4381449147565416157 14073748835532800 57068389881006163 ep1326 42787589331693 137438953472 273 68719476736 (ep1331 rfl) rfl) (Enclosure.sfrac_false_div 42787589331693 137438953472) (BSN.cos_reduce2 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1332) (@Nat.cast Real Real.instNatCast ep1037)) 226375608064910080 72057594037927936 Bool.false 131177447412 137438953472 49 1000000000000000 51609034008 25804517004 (BSN.sin_reduce_arg_pos_rat_q2 42787589331693 137438953472 226375608064910080 72057594037927936 49 ep1332 ep1037 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131177447412 137438953472 ep1332 ep1037 85290769955319 281474976710656 51659433456 51609034008 (ep1338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1340 := nat_lit 1004500841703614595989548768348951625936920695765094405956125784609711720032621835808624430131142430551779392200738625

noncomputable def ep1341 := nat_lit 14298200008547628616551818071540114577587335786466501286865076710532687516440907786670008938572638187735909165122537390080

noncomputable def ep1342 := nat_lit 2630831003853786263916856851919559764884930840652337670998930575598035777485214465752596989336811176992093459854231361

noncomputable def ep1343 := nat_lit 262133666823373191303449997978235433922434489418552523592526406359765937801416642755616830540498366775158334693913185484800

noncomputable def ep1344 := BSN.sin_dyadic_bound_f 85290769955319 281474976710656 3 2 137438953472 51659433456 ep1340 ep1341 ep1335 ep1342 ep1343 ep1335 41011501092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 85290769955319) (BSN.sinEvenQ 281474976710656) 0 2 ep1340 ep1341 ep1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 85290769955319) (BSN.sinOddQ 281474976710656) 0 2 ep1342 ep1343 ep1335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1345 := @Enclosure.Real.IsNear.sin_image qz218 qz516 Bool.false 42787589331693 137438953472 273 68719476736 Bool.true 41011501092 137438953472 1 25804517004 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4381449147565416157 14073748835532800 57068389881006163 ep1326 42787589331693 137438953472 273 68719476736 (ep1331 rfl) rfl) (Enclosure.sfrac_false_div 42787589331693 137438953472) (BSN.sin_reduce2 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1332) (@Nat.cast Real Real.instNatCast ep1037)) 226375608064910080 72057594037927936 Bool.false 41011501092 137438953472 49 1000000000000000 51609034008 25804517004 (BSN.sin_reduce_arg_pos_rat_q2 42787589331693 137438953472 226375608064910080 72057594037927936 49 ep1332 ep1037 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 41011501092 137438953472 ep1332 ep1037 85290769955319 281474976710656 51659433456 51609034008 (ep1344 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1346 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz513 qz216) (@HMul.hMul Real Real Real qz0 qz513 qz477) Bool.true 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 Bool.false 33203823789982497 4722366482869645213696 34511094372911723369 ep1275 (@Enclosure.Real.IsNear.mulLit_ft qz513 qz216 3238489 137438953472 1 137438953472 32794361853 34359738368 1778338154707 443318226485023604736 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 (@Enclosure.Real.IsNear.recentre' qz513 Bool.false 3238489 137438953472 1 137438953472 3238489 137438953472 1 137438953472 (ep1325 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 131177447412 137438953472 7113352618828 1773272905940094418944 32794361853 34359738368 1778338154707 443318226485023604736 (ep1339 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz513 qz477 3238489 137438953472 1 137438953472 10252875273 34359738368 1778338154707 443318226485023604736 33203823789982497 4722366482869645213696 34511094372911723369 ep1275 (@Enclosure.Real.IsNear.recentre' qz513 Bool.false 3238489 137438953472 1 137438953472 3238489 137438953472 1 137438953472 (ep1325 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.true 10252875273 34359738368 1778338154707 443318226485023604736 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 41011501092 137438953472 7113352618828 1773272905940094418944 10252875273 34359738368 1778338154707 443318226485023604736 (ep1345 rfl rfl) rfl)) rfl)

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 4174337385911 2812500000 0 1 33203823789982497 4722366482869645213696 34511094372911723369 ep1275 ep1269

noncomputable def ep1348 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1960476163 30000000 0 1 Bool.false 4174337385911 2812500000 0 1 ep1321

noncomputable def ep1349 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.true 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 Bool.false 33203823789982497 4722366482869645213696 34511094372911723369 ep1275

noncomputable def ep1350 := nat_lit 21698435020237667851906337

noncomputable def ep1351 := nat_lit 67658177877136866568174553147

noncomputable def ep1352 := nat_lit 147777359875766107116363570529

noncomputable def ep1353 := nat_lit 63938991303234899597516736878407

noncomputable def ep1354 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1350 ep1266 ep1351 ep1268 ep1352 ep1270 ep1353

noncomputable def ep1355 := nat_lit 6882524797414432381673656755772938648227459985571840000000

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 1960476163 30000000 0 1 33203823789982497 4722366482869645213696 34511094372911723369 ep1275 ep1350

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 4174337385911 2812500000 0 1 106204180122960117 4722366482869645213696 107220116091542699159 ep1275 ep1352

noncomputable abbrev qz517 := (@ep1324 ep1275 (BSN.cpow_neg_s_sub_mk qz146 102256 1000 21 3 1801088541 qz147 rfl EMRow30.d20) ep1346)

noncomputable def ep1358 := ep1264 (@ep1272 ep1273 ep1274 ep1256 ep1257 ep1258 ep1259 (@ep1276 ep1266 ep1267 ep1268 ep1322 (ep1323 qz517) rfl) (@ep1347 ep1270 ep1271 ep1273 ep1348 (ep1349 qz517) rfl) rfl rfl) (@ep1354 ep1273 ep1355 ep1261 ep1257 ep1262 ep1259 (@ep1356 ep1266 ep1351 ep1268 ep1322 (ep1349 qz517) rfl) (@ep1357 ep1270 ep1353 ep1273 ep1348 (ep1323 qz517) rfl) rfl rfl)

noncomputable def ep1359 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1261 ep1257 ep1262 ep1259 ep1261 ep1257 ep1262

noncomputable def ep1360 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.true ep1256 ep1257 ep1258 ep1259 Bool.true ep1261 ep1257 ep1262

noncomputable def ep1361 := @ep1228 516179745995896887 504403158265495552 170997230753 504403158265495552 (@ep1229 1 3670016 (ep1230 (@ep1231 1048576 1 1048576 (ep1232 (@ep1233 654283721 654283721 62500 0 1 (ep1237 rfl) (ep1240 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1241 1549 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1242 1549 137438953472 4811250831 137438953472 1549 137438953472 (@ep1247 2405624641 2405626190 68719476736 (@ep1253 ep1249 ep1254 ep1251 ep1255 ep1243 ep1244 ep1245 ep1246 (@ep1260 ep1259 ep1248 ep1249 ep1250 ep1251 (@ep1263 ep1259 ep1358) (@ep1263 ep1259 ep1358) rfl) (@ep1359 ep1259 ep1252 ep1249 ep1254 ep1251 (@ep1360 ep1259 ep1358) (@ep1360 ep1259 ep1358) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow30.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 4788772687227386351 4539628424389459968 42073742552225 504403158265495552 := ep1226 (ep1227 ep1361) rfl rfl

noncomputable def EMRow30.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz518 := (EMRow30.d3 qz527 qz539 (@Enclosure.dec_le_dec qz527 qz539 99995 1000 102256 1000 (@Eq.refl Real qz527) (@Eq.refl Real qz539) rfl rfl rfl) 20 21 1 1)

noncomputable abbrev qz263 := qz518

noncomputable def ep1362 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz14 99995 1000 qz15) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz518)

noncomputable def ep1363 := @Enclosure.Real.IsNear.pos_val qz264 ep278 ep279

noncomputable def ep1364 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 20 qz14) Bool.false

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz518)

noncomputable def ep1365 := BSN.mul_neg_of_pos_neg_r qz264 qz265 (@ep1363 ep280 ep281 (@ep1364 ep278 ep279 ep280 ep281 (@Eq.refl Real (hardyZApproximantEM 1 20 qz14)) EMRow30.d10) rfl rfl rfl)

noncomputable def ep1366 := @Enclosure.Real.IsNear.neg_val qz265 ep762 ep763

noncomputable def ep1367 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 21 qz146) Bool.true

noncomputable def ep1368 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 20 qz14)

noncomputable def ep1369 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 20 qz14) Bool.false

noncomputable def ep1370 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz14) (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 5229149440945088297 4539628424389459968 351783833899775 4539628424389459968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1371 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 21 qz146)

noncomputable def ep1372 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 21 qz146) Bool.true

noncomputable def ep1373 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 21 qz146) (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 4788772687227386351 4539628424389459968 42073742552225 504403158265495552 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz394 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz137 1 21))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz62 (@HMul.hMul Complex Complex Complex qz62 (@HDiv.hDiv Complex Complex Complex qz69 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz137 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1374 := @List.cons EMRow30.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1362 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 21 rfl) (ep1365 (@ep1366 ep764 ep765 (@ep1367 ep762 ep763 ep764 ep765 (@Eq.refl Real (hardyZApproximantEM 1 21 qz146)) EMRow30.d14) rfl rfl rfl)) (ep1368 (hardyZErrorBoundEM 1 20 qz14) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz14 rfl) (@ep1369 Bool.false ep278 ep279 ep280 ep281 5229149440945088297 4539628424389459968 351783833899775 4539628424389459968 (@ep1364 ep278 ep279 ep280 ep281 (@Eq.refl Real (hardyZApproximantEM 1 20 qz14)) EMRow30.d10) (ep1370 EMRow30.d19) rfl rfl rfl rfl rfl)) (ep1371 (hardyZErrorBoundEM 1 21 qz146) (BSN.hardyZErrorBoundEM_le_strong 1 21 qz146 rfl) (@ep1372 Bool.false ep762 ep763 ep764 ep765 4788772687227386351 4539628424389459968 42073742552225 504403158265495552 (@ep1367 ep762 ep763 ep764 ep765 (@Eq.refl Real (hardyZApproximantEM 1 21 qz146)) EMRow30.d14) (ep1373 EMRow30.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow30.d0)

noncomputable abbrev qz519 := (@Enclosure.dec_le_dec qz527 qz539 99995 1000 102256 1000 (@Eq.refl Real qz527) (@Eq.refl Real qz539) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1374 (@List.IsChain.singleton EMRow30.d1 EMRow30.d22 (EMRow30.d2 qz285 qz432 qz519))))

noncomputable abbrev qz520 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1375 := And (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz520 qz266)) (@Option.some Real qz14))

noncomputable def ep1376 := ep1375 (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz520 qz266)) (@Option.some Real qz146))

noncomputable def ep1377 := @And.intro (@Eq Nat (@List.length qz520 qz266) 1) ep1376

noncomputable def ep1378 := @And.intro (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz520 qz266)) (@Option.some Real qz14))

noncomputable def ep1379 := @ep1378 (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz520 qz266)) (@Option.some Real qz146))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1374 (@List.IsChain.singleton EMRow30.d1 EMRow30.d22 (EMRow30.d2 qz285 qz432 qz519)))

theorem EMRow30.d23 : Zeta.Certificates.BatchSpec 1 99995 1000 102256 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz520 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz520 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz14)) (@Eq (Option Real) (@Option.map qz520 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz520 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz146)))) qz267 (ep1377 (@Eq.refl Nat 1) (ep1379 (@Eq.refl (Option Real) (@Option.some Real qz14)) (@Eq.refl (Option Real) (@Option.some Real qz146))))

theorem solution : Zeta.Certificates.BatchSpec 1 99995 1000 102256 1000 := EMRow30.d23
#print axioms solution
#check solution
