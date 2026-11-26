-- Prove2me | solution 1 for RHHeight1000.em_main_0019_0019
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:16:04.260182+00:00
-- url     : https://prove2.me/submissions/dbac5bf3-8b93-47a4-bb37-9bc9ead6d427

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow19.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow19.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow19.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow19.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow19.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz268 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz268

noncomputable abbrev qz269 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz269 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 50000000015779 7889500000000000000 4138529546116343 2251799813685248 50000000015779 7889500000000000000 481788 262144

noncomputable abbrev qz270 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 262144 qz270 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 524288 157790 ep10 ep11 236759 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz271 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz271

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 50000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000315580 157790000000000000000 4138529546116343 2251799813685248 50000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 236759 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 524288 157790 ep18 ep19 236759 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 50000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 34716502058787923820544 18889465931478580854784 1000000000315580 157790000000000000000 4138529546116343 2251799813685248 50000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 236759 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz272 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz272)

theorem EMRow19.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 131072 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz269) Bool.false 120447 65536 1 131072 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz269) Bool.false 481788 262144 2 262144 120447 65536 1 131072 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 600168 524288 1 157790 600168 524288 1 157790 300084 262144 2 262144 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 524288 157790 ep28 ep29 600168 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 524288 157790 ep34 ep35 600168 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 300084 262144 2 262144 75021 65536 1 131072 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 600168 524288 1 157790 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 600168 524288 157790 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 600168 524288 1 157790 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 600168 524288 157790 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow19.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 131072 := ep37

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 73635 1000)))

noncomputable abbrev qz512 := qz536

noncomputable abbrev qz273 := qz512

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz537 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz513 := qz537

noncomputable abbrev qz274 := qz513

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz514 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz514

noncomputable abbrev qz515 := (@Neg.neg Complex Complex.instNeg qz536)

noncomputable abbrev qz276 := qz515

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 8) qz276)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 689280776103 274877906944 69520406486061 21686492468346880 Bool.true 39117928617 274877906944 69550436921071 21686492468346880

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 11807775571 4294967296 15553606494871 5421623117086720 Bool.false 15914416409 137438953472 15560632094621 5421623117086720 Bool.true

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 7) qz276)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.false 11807775571 4294967296 15553606494871 5421623117086720 Bool.false 15914416409 137438953472 15560632094621 5421623117086720

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.false 720622587381 274877906944 54435833576157 21686492468346880 Bool.true 16491449165 68719476736 27219482656591 10843246234173440 Bool.false

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 6) qz276)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.false 720622587381 274877906944 54435833576157 21686492468346880 Bool.true 16491449165 68719476736 27219482656591 10843246234173440

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.false 304205571679 137438953472 22995445494411 10843246234173440 Bool.true 67172334503 274877906944 46034939250747 21686492468346880 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 5) qz276)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.false 304205571679 137438953472 22995445494411 10843246234173440 Bool.true 67172334503 274877906944 46034939250747 21686492468346880

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 529114899903 274877906944 36777009068437 21686492468346880 Bool.true 40276619407 68719476736 4602016489439 2710811558543360 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 4) qz276)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 529114899903 274877906944 36777009068437 21686492468346880 Bool.true 40276619407 68719476736 4602016489439 2710811558543360

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 263032957335 137438953472 1325227277801 1084324623417344 Bool.true 11851063517 137438953472 2650323258543 2168649246834688 Bool.false

noncomputable abbrev qz516 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz277 := qz516

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz275 qz277 qz276)

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 263032957335 137438953472 1325227277801 1084324623417344 Bool.true 11851063517 137438953472 2650323258543 2168649246834688

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 51729132965 34359738368 1458539590617 2168649246834688 Bool.true 8295039 16777216 729204904171 1084324623417344 Bool.false

noncomputable abbrev qz517 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz278 := qz517

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz275 qz278 qz276)

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 51729132965 34359738368 1458539590617 2168649246834688 Bool.true 8295039 16777216 729204904171 1084324623417344

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz279 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz279

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz280 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz280))

noncomputable abbrev qz538 := (Enclosure.sfrac Bool.false 73635 1000)

noncomputable abbrev qz518 := qz538

noncomputable abbrev qz281 := qz518

noncomputable abbrev qz282 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log qz282))

noncomputable abbrev qz16 := qz281

noncomputable abbrev qz283 := (@Eq.refl Real qz518)

noncomputable abbrev qz17 := qz283

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.false 17369394597 34359738368 1458539590617 2168649246834688 Bool.true 8295039 16777216 729204904171 1084324623417344 (BSN.cpow_neg_s_mk qz16 73635 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz280) 741455 524288 1 524288 185363 185365 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz280) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz280 qz18)) Bool.false 741455 524288 1 524288 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz280 qz18)) Bool.false 741455 524288 1 524288 741455 524288 1 524288 (BSN.sqrt_enclosure 2 1 370727 370728 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 262144 78895 24381081 945 181704 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 1067207913240925353784183105829957325812498926939272335215205313747184190625

noncomputable def ep57 := nat_lit 71239273651864456168798555229954474558164150722024956391463162036118429368320

noncomputable def ep58 := nat_lit 228294119493679091766200992030762875655850443960827804843169827875390625

noncomputable def ep59 := nat_lit 3201167151483788703169016915505810451686185079929895350035929601585801790625

noncomputable def ep60 := nat_lit 3205767314333900527595934985347951355117386782491123037615842291625329321574400

noncomputable abbrev qz284 := (BSN.cosEvenQ 1073741824)

noncomputable abbrev qz285 := (BSN.cosOddQ 1073741824)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 831403485 1073741824 3 2 524288 157945 ep56 ep57 ep58 ep59 ep60 ep58 374817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 831403485) qz284 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 831403485) qz285 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (Real.log qz282)

noncomputable abbrev qz20 := (Enclosure.Real.IsNear.const Bool.false 73635 1000)

noncomputable abbrev qz519 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz286 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6689887) qz519)

noncomputable abbrev qz287 := (BSN.isNear_log_sfrac 2 1 181704 262144 1 78895 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 181704 262144 78895 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 14626204802138603782144)

noncomputable abbrev qz289 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz15 qz286 Bool.false 6689887 131072 245 262144 Bool.false 374817 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 334494351 6553600 14727 15779000 6689887 131072 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz19 73635 1000 0 1 181704 262144 1 78895 334494351 6553600 14727 15779000 qz20 qz287 rfl) rfl) (Enclosure.sfrac_false_div 6689887 131072) (BSN.cos_reduce0 qz286 (@HDiv.hDiv Real Real Real qz1 qz288 qz289) 226375608064910080 72057594037927936 Bool.false 374817 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 6689887 131072 226375608064910080 72057594037927936 8 14626204802138603782144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 374817 524288 14626204802138603782144 18889465931478580854784 831403485 1073741824 157945 157790 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 477801338940860536980102012590300625

noncomputable def ep64 := nat_lit 159507359494189904748456847233641349120

noncomputable def ep65 := nat_lit 1116551516459329333239197930635489443840

noncomputable abbrev qz290 := (BSN.sinEvenQ 1073741824)

noncomputable abbrev qz291 := (BSN.sinOddQ 1073741824)

noncomputable def ep66 := BSN.sin_dyadic_bound_f 831403485 1073741824 2 1 524288 157945 ep63 ep64 ep63 ep63 ep65 ep63 366592 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 831403485) qz290 0 1 ep63 ep64 ep63 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 831403485) qz291 0 1 ep63 ep65 ep63 rfl rfl rfl rfl) rfl rfl

noncomputable def ep67 := @Enclosure.Real.IsNear.sin_image qz15 qz286 Bool.false 6689887 131072 245 262144 Bool.false 366592 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 334494351 6553600 14727 15779000 6689887 131072 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz19 73635 1000 0 1 181704 262144 1 78895 334494351 6553600 14727 15779000 qz20 qz287 rfl) rfl) (Enclosure.sfrac_false_div 6689887 131072) (BSN.sin_reduce0 qz286 (@HDiv.hDiv Real Real Real qz1 qz288 qz289) 226375608064910080 72057594037927936 Bool.false 366592 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 6689887 131072 226375608064910080 72057594037927936 8 14626204802138603782144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 366592 524288 14626204802138603782144 18889465931478580854784 831403485 1073741824 157945 157790 (ep66 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 370728 524288 2 524288 46341 65536 1 262144 (ep54 rfl rfl) rfl)

noncomputable def ep68 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.false 17369394597 34359738368 1458539590617 2168649246834688 Bool.true 8295039 16777216 729204904171 1084324623417344 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz15) 46341 65536 1 262144 374817 524288 19591419 20681850880 17369394597 34359738368 1458539590617 2168649246834688 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.false 374817 524288 19591419 20681850880 374817 524288 19591419 20681850880 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 46341 65536 1 262144 179 256 19591419 20681850880 8295039 16777216 729204904171 1084324623417344 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.false 179 256 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.false 366592 524288 19591419 20681850880 179 256 19591419 20681850880 (ep67 rfl rfl) rfl)) rfl)

noncomputable abbrev qz293 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz293

noncomputable def ep69 := @ep51 17369394597 34359738368 1458539590617 2168649246834688 Bool.true 8295039 16777216 729204904171 1084324623417344 Bool.false 51729132965 51729132965 34359738368 1458539590617 2168649246834688 Bool.true 8295039 8295039 16777216 729204904171 1084324623417344 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep53 ep68) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep70 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 56116425475 137438953472 1191914964985 2168649246834688 Bool.false 56101895971 137438953472 1191913450201 2168649246834688 (BSN.cpow_neg_s_mk qz16 73635 1000 3 qz17 rfl)

noncomputable def ep71 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 908093 524288 1 524288 151348 151350 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz18)) Bool.false 908093 524288 1 524288 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz18)) Bool.false 908093 524288 1 524288 908093 524288 1 524288 (BSN.sqrt_enclosure 3 1 454046 454047 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep72 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 262144 78895 16925142283965 34459425 287994 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep73 := nat_lit 506112438925680240410662384755921121

noncomputable def ep74 := BSN.sin_dyadic_bound_f 843454681 1073741824 2 1 524288 157945 ep73 ep64 ep73 ep73 ep65 ep73 370775 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 843454681) qz290 0 1 ep73 ep64 ep73 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 843454681) qz291 0 1 ep73 ep65 ep73 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10603219) qz519)

noncomputable abbrev qz296 := (BSN.isNear_log_sfrac 3 1 287994 262144 1 78895 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 287994 262144 78895 rfl rfl rfl (ep72 rfl)))

noncomputable def ep75 := @Enclosure.Real.IsNear.cos_image qz23 qz295 Bool.false 10603219 131072 245 262144 Bool.false 370775 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 2120643819 26214400 14727 15779000 10603219 131072 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz24 73635 1000 0 1 287994 262144 1 78895 2120643819 26214400 14727 15779000 qz20 qz296 rfl) rfl) (Enclosure.sfrac_false_div 10603219 131072) (BSN.cos_reduce3 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14838211680009828958208) qz289) 226375608064910080 72057594037927936 Bool.false 370775 524288 12 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 10603219 131072 226375608064910080 72057594037927936 12 14838211680009828958208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 370775 524288 14838211680009828958208 18889465931478580854784 843454681 1073741824 157945 157790 (ep74 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep76 := nat_lit 1130457372163631246166555292273797101434129011888213143237958916331572585921

noncomputable def ep77 := nat_lit 256149800835300411422216828974168256898316399670118275903041669173896641

noncomputable def ep78 := nat_lit 3390859816889223137676821443163442967788590402865299193162070665656369964481

noncomputable def ep79 := BSN.cos_dyadic_bound_f 843454681 1073741824 3 2 524288 157945 ep76 ep57 ep77 ep78 ep60 ep77 370679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 843454681) qz284 0 2 ep76 ep57 ep77 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 843454681) qz285 0 2 ep78 ep60 ep77 rfl rfl rfl rfl) rfl rfl

noncomputable def ep80 := @Enclosure.Real.IsNear.sin_image qz23 qz295 Bool.false 10603219 131072 245 262144 Bool.true 370679 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 2120643819 26214400 14727 15779000 10603219 131072 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz24 73635 1000 0 1 287994 262144 1 78895 2120643819 26214400 14727 15779000 qz20 qz296 rfl) rfl) (Enclosure.sfrac_false_div 10603219 131072) (BSN.sin_reduce3 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14838211680009828958208) qz289) 226375608064910080 72057594037927936 Bool.false 370679 524288 12 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 10603219 131072 226375608064910080 72057594037927936 12 14838211680009828958208 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 370679 524288 14838211680009828958208 18889465931478580854784 843454681 1073741824 157945 157790 (ep79 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 302698 524288 2 524288 151349 262144 1 262144 (ep71 rfl rfl) rfl)

noncomputable def ep81 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 56116425475 137438953472 1191914964985 2168649246834688 Bool.false 56101895971 137438953472 1191913450201 2168649246834688 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 151349 262144 1 262144 370775 524288 19591419 20681850880 56116425475 137438953472 1191914964985 2168649246834688 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 370775 524288 19591419 20681850880 370775 524288 19591419 20681850880 (ep75 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 151349 262144 1 262144 370679 524288 19591419 20681850880 56101895971 137438953472 1191913450201 2168649246834688 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.true 370679 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.true 370679 524288 19591419 20681850880 370679 524288 19591419 20681850880 (ep80 rfl rfl) rfl)) rfl)

noncomputable def ep82 := @ep49 56116425475 137438953472 1191914964985 2168649246834688 Bool.false 56101895971 137438953472 1191913450201 2168649246834688 Bool.false 9037743596191906529280 263032957335 137438953472 1325227277801 1084324623417344 Bool.true 198827852454428672 11851063517 137438953472 2650323258543 2168649246834688 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep69 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep70 ep81) rfl rfl

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz298))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep83 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.false 3048985233 274877906944 10272463512417 21686492468346880 Bool.true 68702175297 137438953472 5156449665041 10843246234173440 (BSN.cpow_neg_s_mk qz16 73635 1000 4 qz17 rfl)

noncomputable def ep84 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz298) 1048577 524288 1 524288 131071 131072 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz298) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz18)) Bool.false 1048577 524288 1 524288 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz18)) Bool.false 1048577 524288 1 524288 1048577 524288 1 524288 (BSN.sqrt_enclosure 4 1 524288 524289 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep85 := nat_lit 471225594319403171539306640625

noncomputable def ep86 := nat_lit 73155514365408823868279100600

noncomputable def ep87 := BSN.log_dyadic_bound 3 5 13 12 ep85 262144 78895 ep86 89313862490502916491225 363408 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base12 (BSN.artanhP 3) (BSN.artanhQ 5) 0 12 ep86 ep85 89313862490502916491225 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep88 := nat_lit 17130117241881589006671102176957459857268784551539517552193945432527126147041

noncomputable def ep89 := nat_lit 58443294871560821445559008330705478148424697579131070391317059268343508961

noncomputable def ep90 := nat_lit 51273465135901645377122188514210968615509504259460290515799202179044691423201

noncomputable def ep91 := BSN.cos_dyadic_bound_f 1662806971 1073741824 3 2 524288 157945 ep88 ep57 ep89 ep90 ep60 ep89 11631 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1662806971) qz284 0 2 ep88 ep57 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1662806971) qz285 0 2 ep90 ep60 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz299 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6689887) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz300 := (BSN.isNear_log_sfrac 4 1 363408 262144 1 78895 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 363408 262144 78895 rfl rfl rfl (ep87 rfl)))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep92 := @Enclosure.Real.IsNear.cos_image qz26 qz299 Bool.false 6689887 65536 245 262144 Bool.false 11631 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 334494351 3276800 14727 15779000 6689887 65536 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 73635 1000 0 1 363408 262144 1 78895 334494351 3276800 14727 15779000 qz20 qz300 rfl) rfl) (Enclosure.sfrac_false_div 6689887 65536) (BSN.cos_reduce0 qz299 (@HDiv.hDiv Real Real Real qz1 qz288 qz301) 226375608064910080 72057594037927936 Bool.false 11631 524288 16 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 6689887 65536 226375608064910080 72057594037927936 16 14626204802138603782144 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 11631 524288 14626204802138603782144 9444732965739290427392 1662806971 1073741824 157945 157790 (ep91 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep93 := nat_lit 30787456399489611554851536711858863360565072434707826737636048131134152257505

noncomputable def ep94 := nat_lit 641153462866780105519186997069590271023477356498224607523168458325065864314880

noncomputable def ep95 := nat_lit 80539191902204550837508833946142547551144406866249524484603707961774033088481

noncomputable def ep96 := nat_lit 11754480152557635267851761612942488302097084869134117804591421735959540845772800

noncomputable def ep97 := BSN.sin_dyadic_bound_f 1662806971 1073741824 3 2 524288 157945 ep93 ep94 ep89 ep95 ep96 ep89 524158 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1662806971) qz290 0 2 ep93 ep94 ep89 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1662806971) qz291 0 2 ep95 ep96 ep89 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz26 qz299 Bool.false 6689887 65536 245 262144 Bool.false 524158 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 334494351 3276800 14727 15779000 6689887 65536 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 73635 1000 0 1 363408 262144 1 78895 334494351 3276800 14727 15779000 qz20 qz300 rfl) rfl) (Enclosure.sfrac_false_div 6689887 65536) (BSN.sin_reduce0 qz299 (@HDiv.hDiv Real Real Real qz1 qz288 qz301) 226375608064910080 72057594037927936 Bool.false 524158 524288 16 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 6689887 65536 226375608064910080 72057594037927936 16 14626204802138603782144 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524158 524288 14626204802138603782144 9444732965739290427392 1662806971 1073741824 157945 157790 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz302 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 262143 524288 1 524288 262143 524288 1 524288 (ep84 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.false 3048985233 274877906944 10272463512417 21686492468346880 Bool.true 68702175297 137438953472 5156449665041 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz26) 262143 524288 1 524288 11631 524288 19591419 20681850880 3048985233 274877906944 10272463512417 21686492468346880 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.false 11631 524288 19591419 20681850880 11631 524288 19591419 20681850880 (ep92 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 262143 524288 1 524288 262079 262144 19591419 20681850880 68702175297 137438953472 5156449665041 10843246234173440 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.false 262079 262144 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.false 524158 524288 19591419 20681850880 262079 262144 19591419 20681850880 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 3048985233 274877906944 10272463512417 21686492468346880 Bool.true 68702175297 137438953472 5156449665041 10843246234173440 Bool.false 72720998109110354313216 529114899903 274877906944 36777009068437 21686492468346880 Bool.true 11071152841376250462208 40276619407 68719476736 4602016489439 2710811558543360 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep82 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep83 ep99) rfl rfl

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz303))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 79296243455 274877906944 1842776384077 4337298493669376 Bool.false 93934143125 274877906944 1843761467047 4337298493669376 (BSN.cpow_neg_s_mk qz16 73635 1000 5 qz17 rfl)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz303) 1172343 524288 1 524288 117234 117235 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz303) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz18)) Bool.false 1172343 524288 1 524288 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz18)) Bool.false 1172343 524288 1 524288 1172343 524288 1 524288 (BSN.sqrt_enclosure 5 1 586171 586172 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 39510257877627786146545168145625

noncomputable def ep104 := nat_lit 8181717556663416291180905432700

noncomputable def ep105 := nat_lit 6646766139202842132480000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 16 15 ep103 262144 78895 ep104 ep105 421904 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base15 (BSN.artanhP 2) (BSN.artanhQ 3) 0 15 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 321154390293084568224635264786497536

noncomputable def ep108 := BSN.sin_dyadic_bound_f 752798016 1073741824 2 1 524288 157945 ep107 ep64 ep107 ep107 ep65 ep107 338195 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 752798016) qz290 0 1 ep107 ep64 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 752798016) qz291 0 1 ep107 ep65 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz31 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31066901) qz30)

noncomputable abbrev qz305 := (BSN.isNear_log_sfrac 5 1 421904 262144 1 78895 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 421904 262144 78895 rfl rfl rfl (ep106 rfl)))

noncomputable abbrev qz306 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz29 qz304 Bool.false 31066901 262144 245 262144 Bool.false 338195 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 388336263 3276800 14727 15779000 31066901 262144 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz31 73635 1000 0 1 421904 262144 1 78895 388336263 3276800 14727 15779000 qz20 qz305 rfl) rfl) (Enclosure.sfrac_false_div 31066901 262144) (BSN.cos_reduce3 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26486725506410764828672) qz306) 226375608064910080 72057594037927936 Bool.false 338195 524288 18 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 31066901 262144 226375608064910080 72057594037927936 18 26486725506410764828672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338195 524288 26486725506410764828672 37778931862957161709568 752798016 1073741824 157945 157790 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := nat_lit 31901471898837980949691369446728269824

noncomputable def ep111 := nat_lit 478522078482569714245370541700924047360

noncomputable def ep112 := BSN.cos_dyadic_bound_f 752798016 1073741824 2 1 524288 157945 ep107 ep110 ep107 ep107 ep111 ep107 400625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 752798016) qz284 0 1 ep107 ep110 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 752798016) qz285 0 1 ep107 ep111 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz29 qz304 Bool.false 31066901 262144 245 262144 Bool.true 400625 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 388336263 3276800 14727 15779000 31066901 262144 245 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz31 73635 1000 0 1 421904 262144 1 78895 388336263 3276800 14727 15779000 qz20 qz305 rfl) rfl) (Enclosure.sfrac_false_div 31066901 262144) (BSN.sin_reduce3 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26486725506410764828672) qz306) 226375608064910080 72057594037927936 Bool.false 400625 524288 18 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 31066901 262144 226375608064910080 72057594037927936 18 26486725506410764828672 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400625 524288 26486725506410764828672 37778931862957161709568 752798016 1073741824 157945 157790 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 234469 524288 1 524288 234469 524288 1 524288 (ep102 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 79296243455 274877906944 1842776384077 4337298493669376 Bool.false 93934143125 274877906944 1843761467047 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz29) 234469 524288 1 524288 338195 524288 19591419 20681850880 79296243455 274877906944 1842776384077 4337298493669376 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 338195 524288 19591419 20681850880 338195 524288 19591419 20681850880 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 234469 524288 1 524288 400625 524288 19591419 20681850880 93934143125 274877906944 1843761467047 4337298493669376 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 400625 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 400625 524288 19591419 20681850880 400625 524288 19591419 20681850880 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep45 79296243455 274877906944 1842776384077 4337298493669376 Bool.false 93934143125 274877906944 1843761467047 4337298493669376 Bool.false 167238781647652967677952 304205571679 137438953472 22995445494411 10843246234173440 Bool.true 4616047678181718622208 67172334503 274877906944 46034939250747 21686492468346880 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep114) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz32 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz309 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz268 qz281 qz309)

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 112211444023 274877906944 1688988517467 4337298493669376 Bool.false 1206537843 274877906944 1680805212487 4337298493669376 (BSN.cpow_neg_s_mk qz16 73635 1000 6 qz17 rfl)

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz308) 1284239 524288 1 524288 107019 107020 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz308) (Real.sqrt qz310) Bool.false 1284239 524288 1 524288 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz310) Bool.false 1284239 524288 1 524288 1284239 524288 1 524288 (BSN.sqrt_enclosure 6 1 642119 642120 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := BSN.log_dyadic_bound 2 10 4 3 105000000 262144 78895 1434560 960 106290 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep119 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz309 73635 1000 0 1 4034681531866359 2251799813685248 100000000015779 7889500000000000000 59418754919795868993 450359962737049600 1472700000232377333 1577900000000000000000 qz20 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 16922680887833197019136 9444732965739290427392 1000000000157790 78895000000000000000 4034681531866359 2251799813685248 100000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep120 := nat_lit 31708585469789823312195426373539653331657060553103638699806107512787356176705

noncomputable def ep121 := nat_lit 61985709412126387378916539720751332128423561389955703463403475351246295361

noncomputable def ep122 := nat_lit 82945937462782284999993585152103589902322472825401982598646675954350581698881

noncomputable def ep123 := BSN.sin_dyadic_bound_f 1675083447 1073741824 3 2 524288 157945 ep120 ep94 ep121 ep122 ep96 ep121 524257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1675083447) qz290 0 2 ep120 ep94 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1675083447) qz291 0 2 ep122 ep96 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz311 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34586267) qz30)

noncomputable def ep124 := @Enclosure.Real.IsNear.cos_image qz33 qz311 Bool.false 34586267 262144 491 524288 Bool.false 524257 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 59418754919795868993 450359962737049600 1472700000232377333 1577900000000000000000 34586267 262144 491 524288 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 34586267 262144) (BSN.cos_reduce3 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58936759299641037553664) qz306) 226375608064910080 72057594037927936 Bool.false 524257 524288 20 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 34586267 262144 226375608064910080 72057594037927936 20 58936759299641037553664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524257 524288 58936759299641037553664 37778931862957161709568 1675083447 1073741824 157945 157790 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep125 := nat_lit 17643430020733069123388088669620141331866555223453112923653794607260196229441

noncomputable def ep126 := nat_lit 52806318643374954595406432929418921331342818547579427364034576871078096097601

noncomputable def ep127 := BSN.cos_dyadic_bound_f 1675083447 1073741824 3 2 524288 157945 ep125 ep57 ep121 ep126 ep60 ep121 5637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1675083447) qz284 0 2 ep125 ep57 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1675083447) qz285 0 2 ep126 ep60 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz33 qz311 Bool.false 34586267 262144 491 524288 Bool.true 5637 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 59418754919795868993 450359962737049600 1472700000232377333 1577900000000000000000 34586267 262144 491 524288 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 34586267 262144) (BSN.sin_reduce3 qz311 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58936759299641037553664) qz306) 226375608064910080 72057594037927936 Bool.false 5637 524288 20 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 34586267 262144 226375608064910080 72057594037927936 20 58936759299641037553664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 5637 524288 58936759299641037553664 37778931862957161709568 1675083447 1073741824 157945 157790 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz312 := (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 214039 524288 1 524288 214039 524288 1 524288 (ep117 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 112211444023 274877906944 1688988517467 4337298493669376 Bool.false 1206537843 274877906944 1680805212487 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz32 (Real.cos qz33) 214039 524288 1 524288 524257 524288 39261733 41363701760 112211444023 274877906944 1688988517467 4337298493669376 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 524257 524288 39261733 41363701760 524257 524288 39261733 41363701760 (ep124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 214039 524288 1 524288 5637 524288 39261733 41363701760 1206537843 274877906944 1680805212487 4337298493669376 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.true 5637 524288 39261733 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.true 5637 524288 39261733 41363701760 5637 524288 39261733 41363701760 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep43 112211444023 274877906944 1688988517467 4337298493669376 Bool.false 1206537843 274877906944 1680805212487 4337298493669376 Bool.false 99041614257929513336832 720622587381 274877906944 54435833576157 21686492468346880 Bool.true 18132540115794306007040 16491449165 68719476736 27219482656591 10843246234173440 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep129) rfl rfl

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz313))

noncomputable abbrev qz314 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz268 qz281 qz314)

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 35075049163 274877906944 7778592403327 21686492468346880 Bool.false 48897314739 137438953472 3901781532651 10843246234173440 (BSN.cpow_neg_s_mk qz16 73635 1000 7 qz17 rfl)

noncomputable abbrev qz315 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz313) 1387135 524288 1 524288 99081 99082 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz313) (Real.sqrt qz315) Bool.false 1387135 524288 1 524288 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz315) Bool.false 1387135 524288 1 524288 1387135 524288 1 524288 (BSN.sqrt_enclosure 7 1 693567 693568 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 3 11 5 4 202569142545 262144 78895 5259111624 688905 146699 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz314 73635 1000 0 1 4381792198794487 2251799813685248 100000000015779 7889500000000000000 64530653711646410049 450359962737049600 1472700000232377333 1577900000000000000000 qz20 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 100000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 18378568546572512002048 9444732965739290427392 1000000000157790 78895000000000000000 4381792198794487 2251799813685248 100000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := nat_lit 18693712907222929456995996337890625

noncomputable def ep136 := BSN.sin_dyadic_bound_f 369763375 1073741824 2 1 524288 157945 ep135 ep64 ep135 ep135 ep65 ep135 177001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 369763375) qz290 0 1 ep135 ep64 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 369763375) qz291 0 1 ep135 ep65 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz316 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4695223) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep137 := @Enclosure.Real.IsNear.cos_image qz35 qz316 Bool.false 4695223 32768 245 262144 Bool.false 177001 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 64530653711646410049 450359962737049600 1472700000232377333 1577900000000000000000 4695223 32768 245 262144 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 4695223 32768) (BSN.cos_reduce3 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1626236521625646268416) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 177001 524288 22 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 4695223 32768 226375608064910080 72057594037927936 22 1626236521625646268416 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 177001 524288 1626236521625646268416 4722366482869645213696 369763375 1073741824 157945 157790 (ep136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep138 := BSN.cos_dyadic_bound_f 369763375 1073741824 2 1 524288 157945 ep135 ep110 ep135 ep135 ep111 ep135 493506 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 369763375) qz284 0 1 ep135 ep110 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 369763375) qz285 0 1 ep135 ep111 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz35 qz316 Bool.false 4695223 32768 245 262144 Bool.true 493506 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 64530653711646410049 450359962737049600 1472700000232377333 1577900000000000000000 4695223 32768 245 262144 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 4695223 32768) (BSN.sin_reduce3 qz316 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1626236521625646268416) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 493506 524288 22 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 4695223 32768 226375608064910080 72057594037927936 22 1626236521625646268416 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 493506 524288 1626236521625646268416 4722366482869645213696 369763375 1073741824 157945 157790 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz317 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 198163 524288 1 524288 198163 524288 1 524288 (ep132 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 35075049163 274877906944 7778592403327 21686492468346880 Bool.false 48897314739 137438953472 3901781532651 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 198163 524288 1 524288 177001 524288 19591419 20681850880 35075049163 274877906944 7778592403327 21686492468346880 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 177001 524288 19591419 20681850880 177001 524288 19591419 20681850880 (ep137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 198163 524288 1 524288 246753 262144 19591419 20681850880 48897314739 137438953472 3901781532651 10843246234173440 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 246753 262144 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 493506 524288 19591419 20681850880 246753 262144 19591419 20681850880 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep41 35075049163 274877906944 7778592403327 21686492468346880 Bool.false 48897314739 137438953472 3901781532651 10843246234173440 Bool.false 207724584615742365761536 11807775571 4294967296 15553606494871 5421623117086720 Bool.false 1093630368185292161024 15914416409 137438953472 15560632094621 5421623117086720 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep140) rfl rfl

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz318))

noncomputable abbrev qz319 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz268 qz281 qz319)

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 66416860441 274877906944 7305980506577 21686492468346880 Bool.true 70946761435 274877906944 7307908542587 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 8 qz17 rfl)

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep143 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz318) 1482911 524288 1 524288 92681 92682 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz318) (Real.sqrt qz320) Bool.false 1482911 524288 1 524288 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz320) Bool.false 1482911 524288 1 524288 1482911 524288 1 524288 (BSN.sqrt_enclosure 8 1 741455 741456 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep144 := BSN.log_dyadic_bound 0 16 1 0 1 262144 78895 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz319 73635 1000 0 1 9364972152248037 4503599627370496 200000000047337 15779000000000000000 137917944886156840899 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 19639770079031275290624 9444732965739290427392 1000000000236685 78895000000000000000 9364972152248037 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep146 := nat_lit 426059804857313052764673737999650816

noncomputable def ep147 := BSN.sin_dyadic_bound_f 807918664 1073741824 2 1 524288 157945 ep146 ep64 ep146 ep146 ep65 ep146 358307 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 807918664) qz290 0 1 ep146 ep64 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 807918664) qz291 0 1 ep146 ep65 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz38 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz39 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz321 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80278809) qz38)

noncomputable def ep148 := @Enclosure.Real.IsNear.cos_image qz37 qz321 Bool.false 80278809 524288 491 524288 Bool.true 358307 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 137917944886156840899 900719925474099200 2945400000697131999 3155800000000000000000 80278809 524288 491 524288 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 80278809 524288) (BSN.cos_reduce1 qz321 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56852221830560185581568) qz39) 226375608064910080 72057594037927936 Bool.false 358307 524288 24 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 80278809 524288 226375608064910080 72057594037927936 24 56852221830560185581568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 358307 524288 56852221830560185581568 75557863725914323419136 807918664 1073741824 157945 157790 (ep147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep149 := nat_lit 951616969388912689351423786284948953670422898604104123625256642886013812736

noncomputable def ep150 := nat_lit 181526957315051679190102772312841414268984085584859484330940537929465856

noncomputable def ep151 := nat_lit 2854487854252107964695891153310221178182730727641142651907108047582182506496

noncomputable def ep152 := BSN.cos_dyadic_bound_f 807918664 1073741824 3 2 524288 157945 ep149 ep57 ep150 ep151 ep60 ep150 382745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 807918664) qz284 0 2 ep149 ep57 ep150 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 807918664) qz285 0 2 ep151 ep60 ep150 rfl rfl rfl rfl) rfl rfl

noncomputable def ep153 := @Enclosure.Real.IsNear.sin_image qz37 qz321 Bool.false 80278809 524288 491 524288 Bool.false 382745 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 137917944886156840899 900719925474099200 2945400000697131999 3155800000000000000000 80278809 524288 491 524288 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 80278809 524288) (BSN.sin_reduce1 qz321 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56852221830560185581568) qz39) 226375608064910080 72057594037927936 Bool.false 382745 524288 24 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 80278809 524288 226375608064910080 72057594037927936 24 56852221830560185581568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 382745 524288 56852221830560185581568 75557863725914323419136 807918664 1073741824 157945 157790 (ep152 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz322 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 185363 524288 1 524288 185363 524288 1 524288 (ep143 rfl rfl) rfl)

noncomputable def ep154 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 66416860441 274877906944 7305980506577 21686492468346880 Bool.true 70946761435 274877906944 7307908542587 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 185363 524288 1 524288 358307 524288 39261733 41363701760 66416860441 274877906944 7305980506577 21686492468346880 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 358307 524288 39261733 41363701760 358307 524288 39261733 41363701760 (ep148 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 185363 524288 1 524288 382745 524288 39261733 41363701760 70946761435 274877906944 7307908542587 21686492468346880 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.false 382745 524288 39261733 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.false 382745 524288 39261733 41363701760 382745 524288 39261733 41363701760 (ep153 rfl rfl) rfl)) rfl)

noncomputable def ep155 := @ep39 66416860441 274877906944 7305980506577 21686492468346880 Bool.true 70946761435 274877906944 7307908542587 21686492468346880 Bool.false 2960438391123883327488 689280776103 274877906944 69520406486061 21686492468346880 Bool.true 5376327171112880308224 39117928617 274877906944 69550436921071 21686492468346880 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep142 ep154) rfl rfl

theorem EMRow19.d6 : Enclosure.Complex.IsNear qz3 Bool.false 689280776103 274877906944 69520406486061 21686492468346880 Bool.true 39117928617 274877906944 69550436921071 21686492468346880 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep155 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz40 := (BSN.headSumC qz273 17)

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz276)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq qz40 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz41) Bool.false 60131491285 17179869184 11686397973789 2168649246834688 Bool.false 7090250217 68719476736 11684405527901 2168649246834688

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz41 Bool.false 1030756360011 274877906944 111676542168119 21686492468346880 Bool.false 3922544053 34359738368 55848061993007 10843246234173440 Bool.true

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz276)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz42) Bool.false 1030756360011 274877906944 111676542168119 21686492468346880 Bool.false 3922544053 34359738368 55848061993007 10843246234173440

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz42 Bool.false 259180167725 68719476736 53184403493789 10843246234173440 Bool.true 39341925219 274877906944 106350647488743 21686492468346880 Bool.true

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz276)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz43) Bool.false 259180167725 68719476736 53184403493789 10843246234173440 Bool.true 39341925219 274877906944 106350647488743 21686492468346880

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz43 Bool.false 242658780857 68719476736 50420609977351 10843246234173440 Bool.true 35714747049 137438953472 50421101493201 10843246234173440 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz276)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz44) Bool.false 242658780857 68719476736 50420609977351 10843246234173440 Bool.true 35714747049 137438953472 50421101493201 10843246234173440

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz44 Bool.false 112459246723 34359738368 47552532019933 10843246234173440 Bool.true 10890368987 68719476736 23782356980099 5421623117086720 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz276)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz45) Bool.false 112459246723 34359738368 47552532019933 10843246234173440 Bool.true 10890368987 68719476736 23782356980099 5421623117086720

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz45 Bool.false 842358258833 274877906944 89132923292711 21686492468346880 Bool.false 1414330559 34359738368 44579279440873 10843246234173440 Bool.false

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz276)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz46) Bool.false 842358258833 274877906944 89132923292711 21686492468346880 Bool.false 1414330559 34359738368 44579279440873 10843246234173440

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz46 Bool.false 775862959799 274877906944 82905713395501 21686492468346880 Bool.false 60784360969 274877906944 82939846212721 21686492468346880 Bool.false

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz276)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz47) Bool.false 775862959799 274877906944 82905713395501 21686492468346880 Bool.false 60784360969 274877906944 82939846212721 21686492468346880

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz47 Bool.false 689333554529 274877906944 76368179812583 21686492468346880 Bool.false 13127010091 68719476736 9554943755521 2710811558543360 Bool.false

noncomputable abbrev qz48 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 9) qz276)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz48) Bool.false 689333554529 274877906944 76368179812583 21686492468346880 Bool.false 13127010091 68719476736 9554943755521 2710811558543360

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP qz3 qz48 Bool.false 689280776103 274877906944 69520406486061 21686492468346880 Bool.true 39117928617 274877906944 69550436921071 21686492468346880 Bool.false

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz323))

noncomputable abbrev qz324 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz268 qz281 qz324)

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq qz48 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 26389213 137438953472 3423886663261 10843246234173440 Bool.false 91625968981 274877906944 6889113123097 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 9 qz17 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep173 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz323) 1572865 524288 1 524288 87381 87382 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz323) (Real.sqrt qz325) Bool.false 1572865 524288 1 524288 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 1572865 524288 1 524288 1572865 524288 1 524288 (BSN.sqrt_enclosure 9 1 786432 786433 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep174 := BSN.log_dyadic_bound 1 17 2 1 867 262144 78895 1 1 30876 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep175 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz324 73635 1000 0 1 9895417793173221 4503599627370496 200000000047337 15779000000000000000 145729817840062025667 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 20752195215788806766592 9444732965739290427392 1000000000236685 78895000000000000000 9895417793173221 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep176 := BSN.sin_dyadic_bound_f 619618 1073741824 1 0 524288 157945 0 1 1 0 1 1 302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 619618) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 619618) qz291 0 0 rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42412959) qz30)

noncomputable def ep177 := @Enclosure.Real.IsNear.cos_image qz50 qz326 Bool.false 42412959 262144 245 262144 Bool.false 302 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 145729817840062025667 900719925474099200 2945400000697131999 3155800000000000000000 42412959 262144 245 262144 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 42412959 262144) (BSN.cos_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21800880081823858688) qz306) 226375608064910080 72057594037927936 Bool.false 302 524288 25 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 42412959 262144 226375608064910080 72057594037927936 25 21800880081823858688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 302 524288 21800880081823858688 37778931862957161709568 619618 1073741824 157945 157790 (ep176 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep178 := BSN.cos_dyadic_bound_f 619618 1073741824 1 0 524288 157945 0 1 1 0 1 1 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 619618) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 619618) qz285 0 0 rfl) rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.sin_image qz50 qz326 Bool.false 42412959 262144 245 262144 Bool.true 524287 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 145729817840062025667 900719925474099200 2945400000697131999 3155800000000000000000 42412959 262144 245 262144 (ep175 rfl) rfl) (Enclosure.sfrac_false_div 42412959 262144) (BSN.sin_reduce3 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21800880081823858688) qz306) 226375608064910080 72057594037927936 Bool.false 524287 524288 25 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 42412959 262144 226375608064910080 72057594037927936 25 21800880081823858688 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 524287 524288 21800880081823858688 37778931862957161709568 619618 1073741824 157945 157790 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 174763 524288 1 524288 174763 524288 1 524288 (ep173 rfl rfl) rfl)

noncomputable def ep180 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 26389213 137438953472 3423886663261 10843246234173440 Bool.false 91625968981 274877906944 6889113123097 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 174763 524288 1 524288 151 262144 19591419 20681850880 26389213 137438953472 3423886663261 10843246234173440 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 302 524288 19591419 20681850880 151 262144 19591419 20681850880 (ep177 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 174763 524288 1 524288 524287 524288 19591419 20681850880 91625968981 274877906944 6889113123097 21686492468346880 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 524287 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 524287 524288 19591419 20681850880 524287 524288 19591419 20681850880 (ep179 rfl rfl) rfl)) rfl)

noncomputable def ep181 := @ep171 26389213 137438953472 3423886663261 10843246234173440 Bool.false 91625968981 274877906944 6889113123097 21686492468346880 Bool.false 94741282327599605874688 689333554529 274877906944 76368179812583 21686492468346880 Bool.false 14433300232987387887616 13127010091 68719476736 9554943755521 2710811558543360 EMRow19.d6 (ep172 ep180) rfl rfl

noncomputable abbrev qz328 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz328))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep182 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 43264702635 137438953472 3268766791459 10843246234173440 Bool.false 8276320605 274877906944 6500296168553 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 10 qz17 rfl)

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep183 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz328) 1657945 524288 1 524288 82897 82898 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz328) (Real.sqrt qz329) Bool.false 1657945 524288 1 524288 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz329) Bool.false 1657945 524288 1 524288 1657945 524288 1 524288 (BSN.sqrt_enclosure 10 1 828972 828973 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep184 := BSN.log_dyadic_bound 2 18 3 2 1574640 262144 78895 6528 48 58495 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz53 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep185 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz53 73635 1000 0 1 10369908600166117 4503599627370496 200000000047337 15779000000000000000 152717643954646405059 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 21747274560655572598784 9444732965739290427392 1000000000236685 78895000000000000000 10369908600166117 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep184 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep186 := nat_lit 25359660153885909021438382823132731813676264453294263309797293172585106735360

noncomputable def ep187 := nat_lit 39679319209569435386124298866858069089254847592827738904800198575530148096

noncomputable def ep188 := nat_lit 66353914838599982636951563290991765495388565719668016138861329416219659305216

noncomputable def ep189 := BSN.sin_dyadic_bound_f 1584238366 1073741824 3 2 524288 157945 ep186 ep94 ep187 ep188 ep96 ep187 521906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1584238366) qz290 0 2 ep186 ep94 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1584238366) qz291 0 2 ep188 ep96 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11111671) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep190 := @Enclosure.Real.IsNear.cos_image qz52 qz330 Bool.false 11111671 65536 245 262144 Bool.false 521906 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 152717643954646405059 900719925474099200 2945400000697131999 3155800000000000000000 11111671 65536 245 262144 (ep185 rfl) rfl) (Enclosure.sfrac_false_div 11111671 65536) (BSN.cos_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13935108036845163773952) qz301) 226375608064910080 72057594037927936 Bool.false 521906 524288 26 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 11111671 65536 226375608064910080 72057594037927936 26 13935108036845163773952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 521906 524288 13935108036845163773952 9444732965739290427392 1584238366 1073741824 157945 157790 (ep189 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep191 := nat_lit 14106335338474202538748490145681232371637593517426958611622851850803072696576

noncomputable def ep192 := nat_lit 42239647377003468745473221839309980976734270857095220357058955155258157793536

noncomputable def ep193 := BSN.cos_dyadic_bound_f 1584238366 1073741824 3 2 524288 157945 ep191 ep57 ep187 ep192 ep60 ep187 49919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1584238366) qz284 0 2 ep191 ep57 ep187 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1584238366) qz285 0 2 ep192 ep60 ep187 rfl rfl rfl rfl) rfl rfl

noncomputable def ep194 := @Enclosure.Real.IsNear.sin_image qz52 qz330 Bool.false 11111671 65536 245 262144 Bool.true 49919 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 152717643954646405059 900719925474099200 2945400000697131999 3155800000000000000000 11111671 65536 245 262144 (ep185 rfl) rfl) (Enclosure.sfrac_false_div 11111671 65536) (BSN.sin_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13935108036845163773952) qz301) 226375608064910080 72057594037927936 Bool.false 49919 524288 26 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 11111671 65536 226375608064910080 72057594037927936 26 13935108036845163773952 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 49919 524288 13935108036845163773952 9444732965739290427392 1584238366 1073741824 157945 157790 (ep193 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 165795 524288 1 524288 165795 524288 1 524288 (ep183 rfl rfl) rfl)

noncomputable def ep195 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 43264702635 137438953472 3268766791459 10843246234173440 Bool.false 8276320605 274877906944 6500296168553 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 165795 524288 1 524288 260953 262144 19591419 20681850880 43264702635 137438953472 3268766791459 10843246234173440 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 521906 524288 19591419 20681850880 260953 262144 19591419 20681850880 (ep190 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 165795 524288 1 524288 49919 524288 19591419 20681850880 8276320605 274877906944 6500296168553 21686492468346880 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 49919 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 49919 524288 19591419 20681850880 49919 524288 19591419 20681850880 (ep194 rfl rfl) rfl)) rfl)

noncomputable def ep196 := @ep169 43264702635 137438953472 3268766791459 10843246234173440 Bool.false 8276320605 274877906944 6500296168553 21686492468346880 Bool.false 106633793232462967472128 775862959799 274877906944 82905713395501 21686492468346880 Bool.false 4177069479521821917184 60784360969 274877906944 82939846212721 21686492468346880 (ep170 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep182 ep195) rfl rfl

noncomputable abbrev qz332 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz332))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep197 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.false 33247649517 137438953472 622720989721 2168649246834688 Bool.true 49469716497 274877906944 1243742533805 4337298493669376 (BSN.cpow_neg_s_mk qz16 73635 1000 11 qz17 rfl)

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep198 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz332) 1738867 524288 1 524288 79039 79040 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz332) (Real.sqrt qz333) Bool.false 1738867 524288 1 524288 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz333) Bool.false 1738867 524288 1 524288 1738867 524288 1 524288 (BSN.sqrt_enclosure 11 1 869433 869434 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep199 := BSN.log_dyadic_bound 3 19 4 3 4939817505 262144 78895 41676111 10935 83480 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz56 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep200 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz56 73635 1000 0 1 10799147631728357 4503599627370496 200000000047337 15779000000000000000 159039047172463513539 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 22647454054174387339264 9444732965739290427392 1000000000236685 78895000000000000000 10799147631728357 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep201 := nat_lit 222482197326801677905819824854142976

noncomputable def ep202 := BSN.cos_dyadic_bound_f 686789768 1073741824 2 1 524288 157945 ep201 ep110 ep201 ep201 ep111 ep201 420646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 686789768) qz284 0 1 ep201 ep110 ep201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 686789768) qz285 0 1 ep201 ep111 ep201 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92572909) qz38)

noncomputable def ep203 := @Enclosure.Real.IsNear.cos_image qz55 qz334 Bool.false 92572909 524288 245 262144 Bool.false 420646 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 159039047172463513539 900719925474099200 2945400000697131999 3155800000000000000000 92572909 524288 245 262144 (ep200 rfl) rfl) (Enclosure.sfrac_false_div 92572909 524288) (BSN.cos_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48328533536906221191168) qz39) 226375608064910080 72057594037927936 Bool.false 420646 524288 28 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 92572909 524288 226375608064910080 72057594037927936 28 48328533536906221191168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 420646 524288 48328533536906221191168 75557863725914323419136 686789768 1073741824 157945 157790 (ep202 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep204 := BSN.sin_dyadic_bound_f 686789768 1073741824 2 1 524288 157945 ep201 ep64 ep201 ep201 ep65 ep201 312943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 686789768) qz290 0 1 ep201 ep64 ep201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 686789768) qz291 0 1 ep201 ep65 ep201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.sin_image qz55 qz334 Bool.false 92572909 524288 245 262144 Bool.false 312943 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 159039047172463513539 900719925474099200 2945400000697131999 3155800000000000000000 92572909 524288 245 262144 (ep200 rfl) rfl) (Enclosure.sfrac_false_div 92572909 524288) (BSN.sin_reduce0 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48328533536906221191168) qz39) 226375608064910080 72057594037927936 Bool.false 312943 524288 28 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 92572909 524288 226375608064910080 72057594037927936 28 48328533536906221191168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 312943 524288 48328533536906221191168 75557863725914323419136 686789768 1073741824 157945 157790 (ep204 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 158079 524288 1 524288 158079 524288 1 524288 (ep198 rfl rfl) rfl)

noncomputable def ep206 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.false 33247649517 137438953472 622720989721 2168649246834688 Bool.true 49469716497 274877906944 1243742533805 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz55) 158079 524288 1 524288 210323 262144 19591419 20681850880 33247649517 137438953472 622720989721 2168649246834688 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.false 420646 524288 19591419 20681850880 210323 262144 19591419 20681850880 (ep203 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 158079 524288 1 524288 312943 524288 19591419 20681850880 49469716497 274877906944 1243742533805 4337298493669376 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 312943 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 312943 524288 19591419 20681850880 312943 524288 19591419 20681850880 (ep205 rfl rfl) rfl)) rfl)

noncomputable def ep207 := @ep167 33247649517 137438953472 622720989721 2168649246834688 Bool.true 49469716497 274877906944 1243742533805 4337298493669376 Bool.false 115772837542503620018176 842358258833 274877906944 89132923292711 21686492468346880 Bool.false 3110145790278860013568 1414330559 34359738368 44579279440873 10843246234173440 (ep168 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep196 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep197 ep206) rfl rfl

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz336))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep208 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 57315714951 274877906944 1194428149431 4337298493669376 Bool.true 13719030105 68719476736 597086903865 2168649246834688 (BSN.cpow_neg_s_mk qz16 73635 1000 12 qz17 rfl)

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep209 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz336) 1816187 524288 1 524288 75674 75675 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz336) (Real.sqrt qz337) Bool.false 1816187 524288 1 524288 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz337) Bool.false 1816187 524288 1 524288 1816187 524288 1 524288 (BSN.sqrt_enclosure 12 1 908093 908094 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep210 := BSN.log_dyadic_bound 4 20 4 3 6720000000 262144 78895 91811840 61440 106290 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz59 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable def ep211 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz59 73635 1000 0 1 11191020447815397 4503599627370496 200000000047337 15779000000000000000 164810158134977351619 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 23469270914176955449344 9444732965739290427392 1000000000236685 78895000000000000000 11191020447815397 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep212 := nat_lit 1009690394781531935852174565885277855569838623826453377932736166867148800000

noncomputable def ep213 := nat_lit 204353985884903231835770612868256918850433297000474666784788505600000000

noncomputable def ep214 := nat_lit 3028662476372826001092852156430097052871815004885359184464638923590246400000

noncomputable def ep215 := BSN.cos_dyadic_bound_f 819969860 1073741824 3 2 524288 157945 ep212 ep57 ep213 ep214 ep60 ep213 378699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 819969860) qz284 0 2 ep212 ep57 ep213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 819969860) qz285 0 2 ep214 ep60 ep213 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95932137) qz38)

noncomputable def ep216 := @Enclosure.Real.IsNear.cos_image qz58 qz338 Bool.false 95932137 524288 491 524288 Bool.false 378699 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 164810158134977351619 900719925474099200 2945400000697131999 3155800000000000000000 95932137 524288 491 524288 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 95932137 524288) (BSN.cos_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57700249342045086285824) qz39) 226375608064910080 72057594037927936 Bool.false 378699 524288 29 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 95932137 524288 226375608064910080 72057594037927936 29 57700249342045086285824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 378699 524288 57700249342045086285824 75557863725914323419136 819969860 1073741824 157945 157790 (ep215 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep217 := nat_lit 452055290738758229430305849664160000

noncomputable def ep218 := BSN.sin_dyadic_bound_f 819969860 1073741824 2 1 524288 157945 ep217 ep64 ep217 ep217 ep65 ep217 362580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 819969860) qz290 0 1 ep217 ep64 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 819969860) qz291 0 1 ep217 ep65 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable def ep219 := @Enclosure.Real.IsNear.sin_image qz58 qz338 Bool.false 95932137 524288 491 524288 Bool.false 362580 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 164810158134977351619 900719925474099200 2945400000697131999 3155800000000000000000 95932137 524288 491 524288 (ep211 rfl) rfl) (Enclosure.sfrac_false_div 95932137 524288) (BSN.sin_reduce0 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57700249342045086285824) qz39) 226375608064910080 72057594037927936 Bool.false 362580 524288 29 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 95932137 524288 226375608064910080 72057594037927936 29 57700249342045086285824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 362580 524288 57700249342045086285824 75557863725914323419136 819969860 1073741824 157945 157790 (ep218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 151349 524288 1 524288 151349 524288 1 524288 (ep209 rfl rfl) rfl)

noncomputable def ep220 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 57315714951 274877906944 1194428149431 4337298493669376 Bool.true 13719030105 68719476736 597086903865 2168649246834688 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 151349 524288 1 524288 378699 524288 39261733 41363701760 57315714951 274877906944 1194428149431 4337298493669376 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 378699 524288 39261733 41363701760 378699 524288 39261733 41363701760 (ep216 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 151349 524288 1 524288 90645 131072 39261733 41363701760 13719030105 68719476736 597086903865 2168649246834688 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 90645 131072 39261733 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 362580 524288 39261733 41363701760 90645 131072 39261733 41363701760 (ep219 rfl rfl) rfl)) rfl)

noncomputable def ep221 := @ep165 57315714951 274877906944 1194428149431 4337298493669376 Bool.true 13719030105 68719476736 597086903865 2168649246834688 Bool.false 247300498845737047556096 112459246723 34359738368 47552532019933 10843246234173440 Bool.true 374190229124301193216 10890368987 68719476736 23782356980099 5421623117086720 (ep166 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep207 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep208 ep220) rfl rfl

noncomputable abbrev qz340 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz340))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep222 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 17740287411 68719476736 1434038978709 5421623117086720 Bool.true 13934009075 137438953472 2856387533003 10843246234173440 (BSN.cpow_neg_s_mk qz16 73635 1000 13 qz17 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep223 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz340) 1890347 524288 1 524288 72705 72706 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz340) (Real.sqrt qz341) Bool.false 1890347 524288 1 524288 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 1890347 524288 1 524288 1890347 524288 1 524288 (BSN.sqrt_enclosure 13 1 945173 945174 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep224 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 262144 78895 699352521000 41015625 127272 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz62 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable def ep225 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz62 73635 1000 0 1 11551488463034085 4503599627370496 200000000047337 15779000000000000000 34023754119020593959 180143985094819840 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 24225227133228857425920 9444732965739290427392 1000000000236685 78895000000000000000 11551488463034085 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep226 := nat_lit 26067025236257901424724615234584576

noncomputable def ep227 := BSN.cos_dyadic_bound_f 401811968 1073741824 2 1 524288 157945 ep226 ep110 ep226 ep226 ep111 ep226 488004 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 401811968) qz284 0 1 ep226 ep110 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 401811968) qz285 0 1 ep226 ep111 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99022157) qz38)

noncomputable def ep228 := @Enclosure.Real.IsNear.cos_image qz61 qz342 Bool.false 99022157 524288 245 262144 Bool.false 488004 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 34023754119020593959 180143985094819840 2945400000697131999 3155800000000000000000 99022157 524288 245 262144 (ep225 rfl) rfl) (Enclosure.sfrac_false_div 99022157 524288) (BSN.cos_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28275003595658943791104) qz39) 226375608064910080 72057594037927936 Bool.false 488004 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 99022157 524288 226375608064910080 72057594037927936 30 28275003595658943791104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 488004 524288 28275003595658943791104 75557863725914323419136 401811968 1073741824 157945 157790 (ep227 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep229 := BSN.sin_dyadic_bound_f 401811968 1073741824 2 1 524288 157945 ep226 ep64 ep226 ep226 ep65 ep226 191650 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 401811968) qz290 0 1 ep226 ep64 ep226 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 401811968) qz291 0 1 ep226 ep65 ep226 rfl rfl rfl rfl) rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.sin_image qz61 qz342 Bool.false 99022157 524288 245 262144 Bool.false 191650 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 34023754119020593959 180143985094819840 2945400000697131999 3155800000000000000000 99022157 524288 245 262144 (ep225 rfl) rfl) (Enclosure.sfrac_false_div 99022157 524288) (BSN.sin_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28275003595658943791104) qz39) 226375608064910080 72057594037927936 Bool.false 191650 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 99022157 524288 226375608064910080 72057594037927936 30 28275003595658943791104 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 191650 524288 28275003595658943791104 75557863725914323419136 401811968 1073741824 157945 157790 (ep229 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 145411 524288 1 524288 145411 524288 1 524288 (ep223 rfl rfl) rfl)

noncomputable def ep231 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 17740287411 68719476736 1434038978709 5421623117086720 Bool.true 13934009075 137438953472 2856387533003 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 145411 524288 1 524288 122001 131072 19591419 20681850880 17740287411 68719476736 1434038978709 5421623117086720 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 488004 524288 19591419 20681850880 122001 131072 19591419 20681850880 (ep228 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 145411 524288 1 524288 95825 262144 19591419 20681850880 13934009075 137438953472 2856387533003 10843246234173440 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 95825 262144 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 191650 524288 19591419 20681850880 95825 262144 19591419 20681850880 (ep230 rfl rfl) rfl)) rfl)

noncomputable def ep232 := @ep163 17740287411 68719476736 1434038978709 5421623117086720 Bool.true 13934009075 137438953472 2856387533003 10843246234173440 Bool.false 8337692222944366821376 242658780857 68719476736 50420609977351 10843246234173440 Bool.true 2454298728965880152064 35714747049 137438953472 50421101493201 10843246234173440 (ep164 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep221 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep222 ep231) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep233 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 4130346717 17179869184 1381896758219 5421623117086720 Bool.false 32087568879 274877906944 5508444502341 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 14 qz17 rfl)

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep234 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 1961707 524288 1 524288 70060 70061 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz345) Bool.false 1961707 524288 1 524288 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz345) Bool.false 1961707 524288 1 524288 1961707 524288 1 524288 (BSN.sqrt_enclosure 14 1 980853 980854 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep235 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 262144 78895 1346332575744 176359680 146699 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz65 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable def ep236 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz65 73635 1000 0 1 11885241781671653 4503599627370496 200000000047337 15779000000000000000 175033955718678433731 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 24925158572916270432256 9444732965739290427392 1000000000236685 78895000000000000000 11885241781671653 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep235 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep237 := nat_lit 8374954764128735205467244366514274301732404314810976903525573904000000000000

noncomputable def ep238 := nat_lit 4336631566561847168016796541870823555943796225720003906250000000000000000

noncomputable def ep239 := nat_lit 21927384121610349214142184241707689456875245154425202360052098320000000000000

noncomputable def ep240 := BSN.sin_dyadic_bound_f 1201279500 1073741824 3 2 524288 157945 ep237 ep94 ep238 ep239 ep96 ep238 471632 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1201279500) qz290 0 2 ep237 ep94 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1201279500) qz291 0 2 ep239 ep96 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 101883171) qz38)

noncomputable def ep241 := @Enclosure.Real.IsNear.cos_image qz64 qz346 Bool.false 101883171 524288 245 262144 Bool.false 471632 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 175033955718678433731 900719925474099200 2945400000697131999 3155800000000000000000 101883171 524288 245 262144 (ep236 rfl) rfl) (Enclosure.sfrac_false_div 101883171 524288) (BSN.cos_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84532529889908927496192) qz39) 226375608064910080 72057594037927936 Bool.false 471632 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 101883171 524288 226375608064910080 72057594037927936 30 84532529889908927496192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 471632 524288 84532529889908927496192 75557863725914323419136 1201279500 1073741824 157945 157790 (ep240 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep242 := nat_lit 4654680038545547046223143224304317200320644084328640503694763280000000000000

noncomputable def ep243 := nat_lit 13955366852503517444333396079829209953850044660534481503271789840000000000000

noncomputable def ep244 := BSN.cos_dyadic_bound_f 1201279500 1073741824 3 2 524288 157945 ep242 ep57 ep238 ep243 ep60 ep238 228999 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1201279500) qz284 0 2 ep242 ep57 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1201279500) qz285 0 2 ep243 ep60 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.sin_image qz64 qz346 Bool.false 101883171 524288 245 262144 Bool.true 228999 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 175033955718678433731 900719925474099200 2945400000697131999 3155800000000000000000 101883171 524288 245 262144 (ep236 rfl) rfl) (Enclosure.sfrac_false_div 101883171 524288) (BSN.sin_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84532529889908927496192) qz39) 226375608064910080 72057594037927936 Bool.false 228999 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 101883171 524288 226375608064910080 72057594037927936 30 84532529889908927496192 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 228999 524288 84532529889908927496192 75557863725914323419136 1201279500 1073741824 157945 157790 (ep244 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 140121 524288 1 524288 140121 524288 1 524288 (ep234 rfl rfl) rfl)

noncomputable def ep246 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 4130346717 17179869184 1381896758219 5421623117086720 Bool.false 32087568879 274877906944 5508444502341 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 140121 524288 1 524288 29477 32768 19591419 20681850880 4130346717 17179869184 1381896758219 5421623117086720 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 471632 524288 19591419 20681850880 29477 32768 19591419 20681850880 (ep241 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 140121 524288 1 524288 228999 524288 19591419 20681850880 32087568879 274877906944 5508444502341 21686492468346880 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.true 228999 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.true 228999 524288 19591419 20681850880 228999 524288 19591419 20681850880 (ep245 rfl rfl) rfl)) rfl)

noncomputable def ep247 := @ep161 4130346717 17179869184 1381896758219 5421623117086720 Bool.false 32087568879 274877906944 5508444502341 21686492468346880 Bool.false 4452681376602678886400 259180167725 68719476736 53184403493789 10843246234173440 Bool.true 5407113029673044410368 39341925219 274877906944 106350647488743 21686492468346880 (ep162 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep232 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep233 ep246) rfl rfl

noncomputable abbrev qz348 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz348))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz268 qz281 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep248 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.true 5964310889 274877906944 5307735180541 21686492468346880 Bool.false 70722277643 274877906944 5345476497271 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 15 qz17 rfl)

noncomputable abbrev qz349 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep249 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz348) 2030559 524288 1 524288 67685 67686 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz348) (Real.sqrt qz349) Bool.false 2030559 524288 1 524288 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz349) Bool.false 2030559 524288 1 524288 2030559 524288 1 524288 (BSN.sqrt_enclosure 15 1 1015279 1015280 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep250 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 262144 78895 14087658153505881 266939110305 164785 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz68 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable def ep251 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz68 73635 1000 0 1 12195956895733477 4503599627370496 200000000047337 15779000000000000000 179609857203466915779 900719925474099200 2945400000697131999 3155800000000000000000 qz20 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 25576775395801252757504 9444732965739290427392 1000000000236685 78895000000000000000 12195956895733477 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep250 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep252 := nat_lit 14541740407644864016904208886657157111797367958494460246748265640734431412161

noncomputable def ep253 := nat_lit 42159299724906137116954773752200821125676192181065387071720617643672633281

noncomputable def ep254 := nat_lit 43540902623484779776478717112467069693140751491121249966101355686915948969921

noncomputable def ep255 := BSN.cos_dyadic_bound_f 1596289561 1073741824 3 2 524288 157945 ep252 ep57 ep253 ep254 ep60 ep253 44059 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1596289561) qz284 0 2 ep252 ep57 ep253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1596289561) qz285 0 2 ep254 ep60 ep253 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13068337) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep256 := @Enclosure.Real.IsNear.cos_image qz67 qz350 Bool.false 13068337 65536 245 262144 Bool.true 44059 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 179609857203466915779 900719925474099200 2945400000697131999 3155800000000000000000 13068337 65536 245 262144 (ep251 rfl) rfl) (Enclosure.sfrac_false_div 13068337 65536) (BSN.cos_reduce2 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14041111475780776361984) qz301) 226375608064910080 72057594037927936 Bool.false 44059 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 13068337 65536 226375608064910080 72057594037927936 31 14041111475780776361984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 44059 524288 14041111475780776361984 9444732965739290427392 1596289561 1073741824 157945 157790 (ep255 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep257 := nat_lit 26141405293980830320734012176981122144334721371545176134489501659207038435265

noncomputable def ep258 := nat_lit 68397327379918993284685438448875566191435080233372784011261147155071535448001

noncomputable def ep259 := BSN.sin_dyadic_bound_f 1596289561 1073741824 3 2 524288 157945 ep257 ep94 ep253 ep258 ep96 ep253 522433 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1596289561) qz290 0 2 ep257 ep94 ep253 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1596289561) qz291 0 2 ep258 ep96 ep253 rfl rfl rfl rfl) rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.sin_image qz67 qz350 Bool.false 13068337 65536 245 262144 Bool.true 522433 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 179609857203466915779 900719925474099200 2945400000697131999 3155800000000000000000 13068337 65536 245 262144 (ep251 rfl) rfl) (Enclosure.sfrac_false_div 13068337 65536) (BSN.sin_reduce2 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14041111475780776361984) qz301) 226375608064910080 72057594037927936 Bool.false 522433 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 13068337 65536 226375608064910080 72057594037927936 31 14041111475780776361984 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 522433 524288 14041111475780776361984 9444732965739290427392 1596289561 1073741824 157945 157790 (ep259 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 135371 524288 1 524288 135371 524288 1 524288 (ep249 rfl rfl) rfl)

noncomputable def ep261 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.true 5964310889 274877906944 5307735180541 21686492468346880 Bool.false 70722277643 274877906944 5345476497271 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ft qz66 (Real.cos qz67) 135371 524288 1 524288 44059 524288 19591419 20681850880 5964310889 274877906944 5307735180541 21686492468346880 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.true 44059 524288 19591419 20681850880 44059 524288 19591419 20681850880 (ep256 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 135371 524288 1 524288 522433 524288 19591419 20681850880 70722277643 274877906944 5345476497271 21686492468346880 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 522433 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 522433 524288 19591419 20681850880 522433 524288 19591419 20681850880 (ep260 rfl rfl) rfl)) rfl)

noncomputable def ep262 := @ep159 5964310889 274877906944 5307735180541 21686492468346880 Bool.false 70722277643 274877906944 5345476497271 21686492468346880 Bool.false 70833037702259955204096 1030756360011 274877906944 111676542168119 21686492468346880 Bool.false 8625765593474196832256 3922544053 34359738368 55848061993007 10843246234173440 (ep160 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep247 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep248 ep261) rfl rfl

noncomputable abbrev qz352 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz69 := (@Inv.inv Real Real.instInv (Real.sqrt qz352))

noncomputable abbrev qz353 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz268 qz281 qz353)

noncomputable def ep263 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.true 68652499451 274877906944 5187437569771 21686492468346880 Bool.true 754837889 68719476736 1286982823249 5421623117086720 (BSN.cpow_neg_s_mk qz16 73635 1000 16 qz17 rfl)

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep264 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz352) 2097153 524288 1 524288 65535 65536 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz352) (Real.sqrt qz354) Bool.false 2097153 524288 1 524288 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz354) Bool.false 2097153 524288 1 524288 2097153 524288 1 524288 (BSN.sqrt_enclosure 16 1 1048576 1048577 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep265 := BSN.log_dyadic_bound 0 32 1 0 1 262144 78895 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep266 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz353 73635 1000 0 1 3121657384082679 1125899906842624 50000000015779 3944750000000000000 45972648295385613633 225179981368524800 736350000232377333 788950000000000000000 qz20 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 26186360105375033720832 9444732965739290427392 1000000000315580 78895000000000000000 3121657384082679 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep267 := nat_lit 29089594384929359232319776687843818861301634169163732637803032436348833440000

noncomputable def ep268 := nat_lit 52185899690141237926800613126579439577218640206639114129539439136100000000

noncomputable def ep269 := nat_lit 76102541456269045508956023665957444591712592644618074533274402050883735200000

noncomputable def ep270 := BSN.sin_dyadic_bound_f 1639434790 1073741824 3 2 524288 157945 ep267 ep94 ep268 ep269 ep96 ep268 523781 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1639434790) qz290 0 2 ep267 ep94 ep268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1639434790) qz291 0 2 ep269 ep96 ep268 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz355 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26759603) qz519)

noncomputable def ep271 := @Enclosure.Real.IsNear.cos_image qz70 qz355 Bool.false 26759603 131072 491 524288 Bool.true 523781 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 45972648295385613633 225179981368524800 736350000232377333 788950000000000000000 26759603 131072 491 524288 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 26759603 131072) (BSN.cos_reduce1 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28841241843614693195776) qz289) 226375608064910080 72057594037927936 Bool.false 523781 524288 32 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 26759603 131072 226375608064910080 72057594037927936 32 28841241843614693195776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523781 524288 28841241843614693195776 18889465931478580854784 1639434790 1073741824 157945 157790 (ep270 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep272 := nat_lit 16184079502600817901478453987969490229424116156293913293948146659809840800000

noncomputable def ep273 := nat_lit 48447866708422171228581760737655311809117911188468461653585361101157322400000

noncomputable def ep274 := BSN.cos_dyadic_bound_f 1639434790 1073741824 3 2 524288 157945 ep272 ep57 ep268 ep273 ep60 ep268 23036 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1639434790) qz284 0 2 ep272 ep57 ep268 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1639434790) qz285 0 2 ep273 ep60 ep268 rfl rfl rfl rfl) rfl rfl

noncomputable def ep275 := @Enclosure.Real.IsNear.sin_image qz70 qz355 Bool.false 26759603 131072 491 524288 Bool.false 23036 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 45972648295385613633 225179981368524800 736350000232377333 788950000000000000000 26759603 131072 491 524288 (ep266 rfl) rfl) (Enclosure.sfrac_false_div 26759603 131072) (BSN.sin_reduce1 qz355 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28841241843614693195776) qz289) 226375608064910080 72057594037927936 Bool.false 23036 524288 32 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 26759603 131072 226375608064910080 72057594037927936 32 28841241843614693195776 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23036 524288 28841241843614693195776 18889465931478580854784 1639434790 1073741824 157945 157790 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz356 := (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 131071 524288 1 524288 131071 524288 1 524288 (ep264 rfl rfl) rfl)

noncomputable def ep276 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.true 68652499451 274877906944 5187437569771 21686492468346880 Bool.true 754837889 68719476736 1286982823249 5421623117086720 (@Enclosure.Real.IsNear.mulLit_ft qz69 (Real.cos qz70) 131071 524288 1 524288 523781 524288 39261733 41363701760 68652499451 274877906944 5187437569771 21686492468346880 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.true 523781 524288 39261733 41363701760 523781 524288 39261733 41363701760 (ep271 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz69 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 131071 524288 1 524288 5759 131072 39261733 41363701760 754837889 68719476736 1286982823249 5421623117086720 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.false 5759 131072 39261733 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.false 23036 524288 39261733 41363701760 5759 131072 39261733 41363701760 (ep275 rfl rfl) rfl)) rfl)

noncomputable def ep277 := @ep157 68652499451 274877906944 5187437569771 21686492468346880 Bool.true 754837889 68719476736 1286982823249 5421623117086720 Bool.false 264461095453474831728640 60131491285 17179869184 11686397973789 2168649246834688 Bool.false 243619142419775225856 7090250217 68719476736 11684405527901 2168649246834688 (ep158 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep262 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep263 ep276) rfl rfl

theorem EMRow19.d7 : Enclosure.Complex.IsNear qz40 Bool.false 60131491285 17179869184 11686397973789 2168649246834688 Bool.false 7090250217 68719476736 11684405527901 2168649246834688 := ep156 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep277 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow19.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow19.d9 : @Eq Nat (Nat.pow 19 1) 19 := @Eq.refl Nat 19

noncomputable def ep278 := nat_lit 1719731538908737329988523837067

noncomputable def ep279 := nat_lit 475118496759779469565729177600

noncomputable def ep280 := nat_lit 35798798583639201761080664748568167

noncomputable def ep281 := nat_lit 4731740096956745127565235700015038464

noncomputable abbrev qz539 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz520 := qz539

noncomputable abbrev qz357 := qz520

noncomputable abbrev qz71 := qz357

noncomputable abbrev qz521 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz358 := qz521

noncomputable abbrev qz72 := qz358

noncomputable abbrev qz540 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz541 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz522 := (@HAdd.hAdd Complex Complex Complex qz537 (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz538) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz359 := qz522

noncomputable abbrev qz73 := (Complex.Stirling.logGammaStirling 1 qz359)

noncomputable abbrev qz523 := (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz538) (2 : Complex))))

noncomputable abbrev qz360 := qz523

noncomputable abbrev qz74 := qz360

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz281 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz361 := (@instHSub Real Real.instSub)

noncomputable def ep282 := Complex.re (@HMul.hMul Complex Complex Complex qz71 (Complex.exp (@HMul.hMul Complex Complex Complex qz71 Complex.I ↑(@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75))) (zetaApproximant qz5 1 19))

noncomputable def ep283 := @Enclosure.Real.IsNear.of_eq ep282 (@HSub.hSub Real Real Real qz361 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19))))

noncomputable def ep284 := nat_lit 1719728922853801558740095188799

noncomputable def ep285 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19))) ep284

noncomputable def ep286 := nat_lit 4465052542079364602483742234729185447

noncomputable def ep287 := nat_lit 591467512119593140945654462501879808000

noncomputable def ep288 := nat_lit 118779624189944867391432294400

noncomputable def ep289 := nat_lit 2449320218883904412835214710458857

noncomputable def ep290 := nat_lit 147866878029898285236413615625469952000

noncomputable def ep291 := nat_lit 204269065899175369477684684991550719850358796301227576524800

noncomputable def ep292 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.re (zetaApproximant qz5 1 19)) 524287 524288 9019489

noncomputable def ep293 := nat_lit 3280128866162620012970177

noncomputable def ep294 := nat_lit 256012414701542990218763633

noncomputable def ep295 := nat_lit 42897575914607392789522022400

noncomputable def ep296 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) Bool.true 524287 524288 9019489

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14000295) qz30)

noncomputable def ep297 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) qz362 Bool.false 14000295 262144 111

noncomputable def ep298 := nat_lit 82727403520000000000000000

noncomputable def ep299 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) Bool.false 96209296696241339621 1801439850948198400 34855772808278481886463 ep298

noncomputable def ep300 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75 172132929404483452133 1801439850948198400 11618039508278481886463 ep298 1104834267 26214400

noncomputable def ep301 := nat_lit 2522068987313948973360742400

noncomputable def ep302 := nat_lit 103409254400000000000000000

noncomputable def ep303 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 5207547144189125249 90071992547409920 25752027919107451210061 ep302 Bool.false 172132929404483452133 1801439850948198400

noncomputable def ep304 := @Enclosure.Complex.IsNear.subLitP qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 4557898896746971529 90071992547409920 25096667918073358666061 ep302 Bool.false 177718954692742850533 1801439850948198400 10569463508195754482943

noncomputable def ep305 := nat_lit 11726353689042217537793088135626752

noncomputable def ep306 := nat_lit 48451112295263973060405915967029248

noncomputable abbrev qz542 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz524 := qz542

noncomputable abbrev qz363 := (@HSub.hSub Complex Complex Complex qz521 qz522 qz524)

noncomputable abbrev qz364 := (Complex.log qz522)

noncomputable abbrev qz76 := (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 qz363 qz364) qz359)

noncomputable abbrev qz365 := qz524

noncomputable abbrev qz77 := (@HMul.hMul Complex Complex Complex qz357 qz365 ↑(Real.log qz272))

noncomputable abbrev qz525 := qz541

noncomputable abbrev qz366 := qz525

noncomputable abbrev qz78 := qz366

noncomputable abbrev qz79 := (@instHMul Nat instMulNat)

noncomputable abbrev qz526 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz367 := qz526

noncomputable abbrev qz80 := qz367

noncomputable abbrev qz81 := qz359

noncomputable abbrev qz368 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz82 := qz368

noncomputable abbrev qz369 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz83 := qz369

noncomputable abbrev qz370 := (@instHSub Int Int.instSub)

noncomputable abbrev qz371 := (@instHMul Int Int.instMul)

noncomputable def ep307 := @Enclosure.Complex.IsNear.of_eq qz73 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz76 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k)))))) Bool.true 4557898896746971529

noncomputable def ep308 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz76 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) Bool.true 4557911309380714889 90071992547409920

noncomputable def ep309 := nat_lit 39152053400005447008196231168

noncomputable def ep310 := nat_lit 152659419656927254315410233753600

noncomputable def ep311 := @ep308 3063553686866267833 12623200000000000000000 Bool.false 177723016934012594149 1801439850948198400 161270000233481863 1262320000000000000000 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200 Bool.true ep309 4557898896746971529 90071992547409920 25096667918073358666061 ep302 Bool.false ep310

noncomputable def ep312 := @Enclosure.Complex.IsNear.addLitP qz76 qz77 Bool.true 4640681857524924809 90071992547409920 3015400000342830333 12623200000000000000000

noncomputable def ep313 := @ep312 Bool.false 177723016934012594149 1801439850948198400 161270000233481863 1262320000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true 597414551143149061931008 4557911309380714889 90071992547409920 3063553686866267833 12623200000000000000000 Bool.false 177723016934012594149 177723016934012594149 1801439850948198400

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz357 qz363 qz364)

noncomputable def ep314 := @Enclosure.Complex.IsNear.subLitP qz84 qz81 Bool.true 4438019874293252489 90071992547409920 3015400000342830333 12623200000000000000000 Bool.false 244047528646297888741

noncomputable def ep315 := @ep314 1801439850948198400 161270000233481863 1262320000000000000000 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 Bool.true 18562727430099699236000 4640681857524924809 90071992547409920 3015400000342830333 12623200000000000000000 Bool.false 710892067736050376596000 177723016934012594149 1801439850948198400 161270000233481863 1262320000000000000000

noncomputable abbrev qz85 := qz363

noncomputable abbrev qz86 := qz364

noncomputable def ep316 := @Enclosure.Complex.IsNear.mul qz85 qz86 Bool.true 4438019874293252489 90071992547409920 3015400000342830333 12623200000000000000000 Bool.false 244047528646297888741 1801439850948198400 161270000233481863

noncomputable abbrev qz87 := (Complex.re qz363)

noncomputable abbrev qz88 := (Complex.re qz364)

noncomputable abbrev qz89 := (Complex.im qz363)

noncomputable abbrev qz90 := (Complex.im qz364)

noncomputable def ep317 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz87 qz88) (@HMul.hMul Real Real Real qz0 qz89 qz90) 113737749526934981 18014398509481984 70000000110453 12623200000000000000 2503354310963963697 45035996273704960

noncomputable def ep318 := nat_lit 39974129304259894818846748954329088

noncomputable def ep319 := @Enclosure.Real.IsNear.mulLit_ff qz87 qz88 7000 4000 0 1 16248249932419283 4503599627370496 10000000015779 3155800000000000000

noncomputable def ep320 := @Enclosure.Complex.IsNear.re_isNear qz85 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable abbrev qz372 := (Enclosure.sfrac Bool.false 147270 4000)

noncomputable abbrev qz91 := qz372

noncomputable def ep321 := @Enclosure.Complex.IsNear.of_eq qz85 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz91) Bool.false 7000 4000 0 1 Bool.false 147270 4000 0

noncomputable abbrev qz373 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz92 := qz373

noncomputable abbrev qz374 := (Complex.log (Complex.mk qz92 qz91))

noncomputable def ep322 := @Enclosure.Complex.IsNear.of_eq qz86 qz374 Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000

noncomputable def ep323 := nat_lit 323886156795824618099505280117597211929663347328713705000000000000

noncomputable def ep324 := nat_lit 2177117418528250907644929032709179128219670282478791000000000000

noncomputable def ep325 := nat_lit 365952443258372944763663647842192863557372444815000000000000

noncomputable def ep326 := BSN.log_dyadic_bound 5385452900 38153452900 4 3 ep323 524288 157790 ep324 ep325 149003 43538905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5385452900) (BSN.artanhQ 38153452900) 0 3 ep324 ep323 ep325 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz93 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz375 := (Real.log (Enclosure.sfrac Bool.false 21769452900 16000000))

noncomputable abbrev qz376 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz375 1 2 0 1 16248249932419283 2251799813685248 10000000015779 1577900000000000000 16248249932419283 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 21769452900 16000000 16248249932419283 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21769452900) qz377)) Bool.false 136300199369091856728064 18889465931478580854784 1000000001577900 157790000000000000000 16248249932419283 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 21769452900 16000000 10 43538905800 32768000000 149003 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep328 := BSN.arctan_dyadic_bound_f 9000 147270 1 0 524288 157790 0 1 1 0 1 1 32000 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz94 := (@HMul.hMul Real Real Real qz268 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz95 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz376 BSN.pi_near_15 rfl)

noncomputable abbrev qz378 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 147270)))

noncomputable def ep329 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz378 884279719003555 562949953421312 1 2000000000000000 32000 524288 1 157790 445602846807453859840 849919980635555 562949953421312 200000000015779 31558000000000000000 qz95 (ep328 rfl) rfl rfl

noncomputable abbrev qz379 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147270) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep330 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (ep322 (@congrArg Complex Complex qz81 (Complex.mk qz92 qz91) Complex.log (BSN.w_shift_mk qz16 Bool.false 73635 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz374 Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz374) (@HMul.hMul Real Real Real qz0 qz93 qz375) Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 9000 147270 4000 21769452900 16000000 rfl rfl rfl) (ep327 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz374) qz379 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 9000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz379 (@HSub.hSub Real Real Real qz361 qz94 qz378) Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 147270 9000 rfl rfl) ep329))))

noncomputable def ep331 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz90 147270 4000 0 1 849919980635555 562949953421312 200000000015779 31558000000000000000

noncomputable def ep332 := @Enclosure.Complex.IsNear.im_isNear qz85 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable def ep333 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (ep322 (@congrArg Complex Complex qz81 (Complex.mk qz92 qz91) Complex.log (BSN.w_shift_mk qz16 Bool.false 73635 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz374 Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz374) (@HMul.hMul Real Real Real qz0 qz93 qz375) Bool.false 16248249932419283 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 9000 147270 4000 21769452900 16000000 rfl rfl rfl) (ep327 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz374) qz379 Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 9000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz379 (@HSub.hSub Real Real Real qz361 qz94 qz378) Bool.false 849919980635555 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 147270 9000 rfl rfl) ep329))))

noncomputable abbrev qz380 := (Enclosure.Real.IsNear.const Bool.false 147270 4000)

noncomputable abbrev qz96 := (@ep321 1 (BSN.w_sub_half_mk qz281 Bool.false 73635 1000 2 qz283 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz372 Bool.false 7000 4000 0 1 Bool.false 147270 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz380))

noncomputable def ep334 := @ep317 2945400000232377333 12623200000000000000000 ep318 4438019874293252489 90071992547409920 3015400000342830333 12623200000000000000000 (@ep319 113737749526934981 18014398509481984 70000000110453 12623200000000000000 (ep320 qz96) ep330 rfl) (@ep331 2503354310963963697 45035996273704960 2945400000232377333 12623200000000000000000 (ep332 qz96) ep333 rfl) rfl

noncomputable def ep335 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz87 qz90) (@HMul.hMul Real Real Real qz0 qz89 qz88) 5949439864448885 2251799813685248 1400000000110453 126232000000000000000 239287976754738780741 1801439850948198400

noncomputable def ep336 := nat_lit 549546179536078809919096941096992768

noncomputable def ep337 := @Enclosure.Real.IsNear.mulLit_ff qz87 qz90 7000 4000 0 1 849919980635555 562949953421312 200000000015779 31558000000000000000

noncomputable def ep338 := @Enclosure.Real.IsNear.mulLit_ff qz89 qz88 147270 4000 0 1 16248249932419283 4503599627370496 10000000015779 3155800000000000000

noncomputable def ep339 := @ep335 147270000232377333 1262320000000000000000 ep336 244047528646297888741 1801439850948198400 161270000233481863 1262320000000000000000 (@ep337 5949439864448885 2251799813685248 1400000000110453 126232000000000000000 (ep320 qz96) ep333 rfl) (@ep338 239287976754738780741 1801439850948198400 147270000232377333 1262320000000000000000 (ep332 qz96) ep330 rfl) rfl

noncomputable def ep340 := @Enclosure.Complex.IsNear.of_eq qz81 (Complex.mk qz92 qz91) Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 73635 1000 2 qz17 rfl)

noncomputable abbrev qz381 := (ep340 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 147270 4000) Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 147270 4000)))

noncomputable abbrev qz97 := qz381

noncomputable def ep341 := ep315 (@ep316 1262320000000000000000 (ep334 rfl) (ep339 rfl)) qz97 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz98 := qz365

noncomputable def ep342 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz98) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz98) (Complex.im ↑qz2)) 120447 131072 1 262144 0 1 0 1 120447 120447

noncomputable def ep343 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz98) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 131072 120447 131072 1 262144

noncomputable abbrev qz99 := (@Enclosure.Complex.IsNear.of_eq qz365 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz279) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz279 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz376 qz293))

noncomputable def ep344 := ep343 (@Enclosure.Complex.IsNear.re_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow19.d4)

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz98) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep346 := ep345 (@Enclosure.Complex.IsNear.im_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep347 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz98) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz98) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep348 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz98) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep349 := ep348 (@Enclosure.Complex.IsNear.re_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep350 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz98) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 131072 0 1 0 1

noncomputable def ep351 := ep350 (@Enclosure.Complex.IsNear.im_isNear qz98 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz99) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 131072 (Complex.ofReal_re qz2) EMRow19.d4)

noncomputable def ep352 := @ep313 161270000233481863 1262320000000000000000 (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz98 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep342 131072 1 262144 (ep344 rfl) (ep346 rfl) rfl rfl) (@ep347 1 0 1 (ep349 rfl) (ep351 rfl) rfl rfl))

noncomputable abbrev qz100 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz382 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz101 := (@HMul.hMul Complex Complex Complex qz357 (@HMul.hMul Complex Complex Complex qz357 (2 : Complex) qz382) (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 (2 : Complex) qz382) (1 : Complex)))

noncomputable abbrev qz383 := (@HPow.hPow Complex Int Complex qz526 qz522 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz102 := qz383

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102)) Bool.false 1183761 8589934592 3 8589934592

noncomputable def ep354 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102) Bool.false 0 1 0 1 Bool.false

noncomputable def ep355 := @ep354 0 1 0 1 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200 Bool.false 1183761 1183761 8589934592 3 8589934592 Bool.true 1937027583 1937027583 858993459200 4909

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz81 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep357 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz102 Bool.false 1183761 8589934592 3 8589934592 Bool.true 1937027583 858993459200 4909 858993459200

noncomputable abbrev qz103 := (Complex.re qz383)

noncomputable abbrev qz104 := (Complex.im qz383)

noncomputable def ep358 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104) 1183761 8589934592 3 8589934592 0 1 0

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103 1 12 0 1 3551283 2147483648 9 2147483648 1183761

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz384 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep361 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep360 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz384)

noncomputable def ep362 := @Enclosure.Complex.IsNear.re_isNear qz102 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727 214748364800

noncomputable abbrev qz527 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz385 := (@HPow.hPow Complex Nat Complex qz527 qz522 1)

noncomputable abbrev qz105 := (@Inv.inv Complex Complex.instInv qz385)

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz102 qz105 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727

noncomputable def ep364 := @Enclosure.Complex.IsNear.of_parts qz105 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727

noncomputable abbrev qz106 := (Complex.re qz385)

noncomputable abbrev qz107 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz108 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := qz385

noncomputable def ep365 := @Enclosure.Real.IsNear.mulLit_ff qz106 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) 9000 4000 0 1 394587 536870912 1 536870912

noncomputable def ep366 := @Enclosure.Complex.IsNear.re_isNear qz109 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq qz109 qz81 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0

noncomputable def ep368 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) Bool.false 394587 536870912 1 536870912 394587 536870912 1

noncomputable abbrev qz110 := (Complex.im qz385)

noncomputable abbrev qz386 := (@instHAdd Real Real.instAdd)

noncomputable def ep369 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 qz106 qz106) (@HMul.hMul Real Real Real qz0 qz110 qz110)) Bool.false 217694529 160000 0 1

noncomputable def ep370 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz106 qz106) (@HMul.hMul Real Real Real qz0 qz110 qz110) 81 16 0 1 216884529 160000

noncomputable def ep371 := @Enclosure.Real.IsNear.mulLit_ff qz106 qz106 9000 4000 0 1 9000 4000 0 1

noncomputable def ep372 := @Enclosure.Real.IsNear.mulLit_ff qz110 qz110 147270 4000 0 1 147270 4000 0 1

noncomputable def ep373 := @Enclosure.Complex.IsNear.im_isNear qz109 Bool.false 9000 4000 0 1 Bool.false 147270 4000 0 1

noncomputable abbrev qz111 := (ep366 (@ep367 1 (BSN.pow_one_c qz359) qz381))

noncomputable abbrev qz112 := (ep373 (@ep367 1 (BSN.pow_one_c qz359) qz381))

noncomputable def ep374 := @ep370 0 1 3483112464 217694529 160000 0 1 (@ep371 81 16 0 1 qz111 qz111 rfl) (@ep372 216884529 160000 0 1 qz112 qz112 rfl)

noncomputable def ep375 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109) 217694529 160000 0 1 197293 197294 268435456 (ep369 (Enclosure.Complex.normSq_eq_mul_add_mul qz109) (ep374 rfl rfl)) rfl

noncomputable def ep376 := @Enclosure.Real.IsNear.of_eq (Complex.re qz105) (@HMul.hMul Real Real Real qz0 qz106 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109))) Bool.false 3551283 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz109) (@ep365 3551283 2147483648 9 2147483648 qz111 (@ep368 536870912 (ep375 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep377 := @Enclosure.Real.IsNear.of_eq (Complex.im qz105) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz110) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109))) Bool.true 5811082749 214748364800 14727 214748364800 (Enclosure.Complex.inv_im_eq_mul qz109)

noncomputable def ep378 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz110) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz109)) 147270 4000 0 1 394587 536870912 1

noncomputable def ep379 := @ep378 536870912 5811082749 214748364800 14727 214748364800 (@Enclosure.Real.IsNear.neg qz110 Bool.false 147270 4000 0 1 qz112) (@ep368 536870912 (ep375 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep380 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104 0 1 0 1 5811082749 214748364800 14727 214748364800 0

noncomputable def ep381 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep360 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz384)

noncomputable def ep382 := @Enclosure.Complex.IsNear.im_isNear qz102 Bool.false 3551283 2147483648 9 2147483648 Bool.true 5811082749 214748364800 14727 214748364800

noncomputable abbrev qz113 := (@ep363 214748364800 (BSN.zpow_one_sub_two_mul qz359 1 1 rfl rfl) (@ep364 214748364800 ep376 (ep377 ep379)))

noncomputable def ep383 := @ep358 1 1183761 1183761 8589934592 3 8589934592 (@ep359 8589934592 3 8589934592 ep361 (ep362 qz113) rfl) (@ep380 1 0 1 ep381 (ep382 qz113) rfl) rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103) 1937027583 858993459200 4909 858993459200 0 1 0

noncomputable def ep385 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz104 1 12 0 1 5811082749 214748364800 14727 214748364800 1937027583

noncomputable def ep386 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz103 0 1 0 1 3551283 2147483648 9 2147483648 0

noncomputable def ep387 := @ep384 1 1937027583 1937027583 858993459200 4909 858993459200 (@ep385 858993459200 4909 858993459200 ep361 (ep382 qz113) rfl) (@ep386 1 0 1 ep381 (ep362 qz113) rfl) rfl

noncomputable abbrev qz114 := (@Enclosure.Complex.IsNear.mk qz279 qz279 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz293 qz293)

noncomputable def ep388 := @ep355 858993459200 (@ep356 0 1 0 1 (BSN.stirling_sum_base qz81) qz114) (ep357 (ep383 rfl) (ep387 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep389 := @ep311 177718954692742850533 1801439850948198400 10569463508195754482943 ep298 (ep352 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep353 Bool.true 1937027583 858993459200 4909 858993459200 (BSN.stirling_sum_succ qz81 0 1 rfl) (ep388 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep390 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 16241206186053843 2251799813685248 10000000015779 1577900000000000000 Bool.false 872816451290531 281474976710656

noncomputable abbrev qz115 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz360 qz382))

noncomputable def ep391 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz115) Bool.false 16241206186053843 2251799813685248 10000000015779 1577900000000000000 Bool.false 872816451290531 281474976710656 200000000015779 15779000000000000000

noncomputable def ep392 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz115 Bool.false 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000 Bool.false

noncomputable def ep393 := nat_lit 146287780255118963727649531232256

noncomputable def ep394 := nat_lit 982703961198718521042318393344

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz360 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz116) Bool.false 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz116 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz387 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz91))

noncomputable def ep397 := @Enclosure.Complex.IsNear.of_eq qz116 qz387 Bool.false 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000

noncomputable def ep398 := nat_lit 319832718101888446484774846217285437889243588232713705000000000000

noncomputable def ep399 := nat_lit 2094604240920848505696167342766028298465722703278791000000000000

noncomputable def ep400 := nat_lit 334523043436708935757576056006158969534644444815000000000000

noncomputable def ep401 := BSN.log_dyadic_bound 5305452900 38073452900 4 3 ep398 524288 157790 ep399 ep400 147073 43378905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5305452900) (BSN.artanhQ 38073452900) 0 3 ep399 ep398 ep400 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep402 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 21689452900 16000000)) 1 2 0 1 16239960645538003 2251799813685248 10000000015779 1577900000000000000 16239960645538003 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 21689452900 16000000 16239960645538003 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21689452900) qz377)) Bool.false 136230663790845256269824 18889465931478580854784 1000000001577900 157790000000000000000 16239960645538003 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 21689452900 16000000 10 43378905800 32768000000 147073 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep401 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep403 := BSN.arctan_dyadic_bound_f 1000 147270 1 0 524288 157790 0 1 1 0 1 1 3559 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 147270)

noncomputable def ep404 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz389)) 884279719003555 562949953421312 1 2000000000000000 3559 524288 1 157790 461613706432709394432 880458271851939 562949953421312 200000000015779 31558000000000000000 qz95 (ep403 rfl) rfl rfl

noncomputable abbrev qz117 := (@HAdd.hAdd Complex Complex Complex qz274 qz360 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz390 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz91)

noncomputable def ep405 := @ep396 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000 Bool.false 16239960645538003 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 880458271851939 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz114) (ep397 (@congrArg Complex Complex qz117 qz390 Complex.log (BSN.w_shift_mk qz16 Bool.false 73635 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz387 Bool.false 16239960645538003 4503599627370496 10000000015779 3155800000000000000 Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz387) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 21689452900 16000000))) Bool.false 16239960645538003 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 1000 147270 4000 21689452900 16000000 rfl rfl rfl) (ep402 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz387) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz388)) Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 1000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz388)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz389))) Bool.false 880458271851939 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 147270 1000 rfl rfl) ep404)))) rfl rfl

noncomputable abbrev qz391 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz91))

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq qz115 qz391 Bool.false 16242451726569683 4503599627370496 10000000015779 3155800000000000000 Bool.false 865174630729123 562949953421312 200000000015779 31558000000000000000

noncomputable def ep407 := nat_lit 321044285440535443234292068227742264027967435961513705000000000000

noncomputable def ep408 := nat_lit 2119127492330418211217470301553999747906690977038791000000000000

noncomputable def ep409 := nat_lit 343705933447473946118780052338749280301462844815000000000000

noncomputable def ep410 := BSN.log_dyadic_bound 5329452900 38097452900 4 3 ep407 524288 157790 ep408 ep409 147653 43426905800 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5329452900) (BSN.artanhQ 38097452900) 0 3 ep408 ep407 ep409 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep411 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 21713452900 16000000)) 1 2 0 1 16242451726569683 2251799813685248 10000000015779 1577900000000000000 16242451726569683 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 21713452900 16000000 16242451726569683 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21713452900) qz377)) Bool.false 136251560493116255371264 18889465931478580854784 1000000001577900 157790000000000000000 16242451726569683 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 21713452900 16000000 10 43426905800 32768000000 147653 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep410 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep412 := BSN.arctan_dyadic_bound_f 5000 147270 1 0 524288 157790 0 1 1 0 1 1 17793 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 147270) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 147270) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep413 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz389)) 884279719003555 562949953421312 1 2000000000000000 17793 524288 1 157790 453600676795710439424 865174630729123 562949953421312 200000000015779 31558000000000000000 qz95 (ep412 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz274 qz360 qz382)

noncomputable abbrev qz393 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz91)

noncomputable def ep414 := @ep392 16242451726569683 4503599627370496 10000000015779 3155800000000000000 Bool.false 865174630729123 562949953421312 200000000015779 31558000000000000000 Bool.false ep393 16241206186053843 2251799813685248 10000000015779 1577900000000000000 Bool.false ep394 872816451290531 281474976710656 200000000015779 15779000000000000000 (ep395 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep405 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep406 (@congrArg Complex Complex qz118 qz393 Complex.log (BSN.w_shift_mk qz16 Bool.false 73635 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz391 Bool.false 16242451726569683 4503599627370496 10000000015779 3155800000000000000 Bool.false 865174630729123 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz391) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 21713452900 16000000))) Bool.false 16242451726569683 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 5000 147270 4000 21713452900 16000000 rfl rfl rfl) (ep411 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz391) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz392)) Bool.false 865174630729123 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 5000 147270 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz392)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz389))) Bool.false 865174630729123 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 147270 5000 rfl rfl) ep413)))) rfl rfl

noncomputable def ep415 := @ep304 ep298 Bool.false 16241206186053843 2251799813685248 10000000015779 1577900000000000000 Bool.false 872816451290531 281474976710656 200000000015779 15779000000000000000 Bool.true ep305 5207547144189125249 90071992547409920 25752027919107451210061 ep302 Bool.false ep306 172132929404483452133 1801439850948198400 11618039508278481886463 ep298 (@ep307 90071992547409920 25096667918073358666061 ep302 Bool.false 177718954692742850533 1801439850948198400 10569463508195754482943 ep298 (BSN.logGammaStirling_unfold 1 qz81) (ep389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep390 200000000015779 15779000000000000000 (BSN.log_sum_c_eq qz16 2) (ep391 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep414 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz119 := (@HDiv.hDiv Real Real Real qz271 qz281 (2 : Real))

noncomputable def ep416 := @Enclosure.Real.IsNear.mulLit_ff qz119 (Real.log Real.pi) 73635 2000 0 1 75021 65536 1 131072 1104834267 26214400 14727 52428800 (@Enclosure.Real.IsNear.of_eq qz119 (Enclosure.sfrac Bool.false 73635 2000) Bool.false 73635 2000 0 1 (BSN.t_half_eq qz16 Bool.false 73635 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 73635 2000)) EMRow19.d5 rfl

noncomputable def ep417 := @ep300 14727 52428800 ep301 96209296696241339621 1801439850948198400 34855772808278481886463 ep298 (@ep303 11618039508278481886463 ep298 (ep415 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep416 rfl rfl

noncomputable def ep418 := nat_lit 32578066970948947632339534617769715436017289585412280655197802667677554114560

noncomputable def ep419 := nat_lit 65424738761693949058486934158863832821490808879394011999221017079929962496

noncomputable def ep420 := nat_lit 85217582965918786929080278486472998984048582842656001887043125340073707503616

noncomputable def ep421 := BSN.sin_dyadic_bound_f 1686427788 1073741824 3 2 524288 157945 ep418 ep94 ep419 ep420 ep96 ep419 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686427788) qz290 0 2 ep418 ep94 ep419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686427788) qz291 0 2 ep420 ep96 ep419 rfl rfl rfl rfl) rfl rfl

noncomputable def ep422 := @ep297 262144 Bool.true 524287 524288 1 78895 (@ep299 14000295 262144 111 262144 ep417 rfl) (Enclosure.sfrac_false_div 14000295 262144) (BSN.cos_reduce1 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335902823727581102080) qz306) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 14000295 262144 226375608064910080 72057594037927936 8 59335902823727581102080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 59335902823727581102080 37778931862957161709568 1686427788 1073741824 157945 157790 (ep421 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep423 := nat_lit 42665822278657120565132461

noncomputable def ep424 := nat_lit 7149595985767898798253670400

noncomputable abbrev qz120 := qz275

noncomputable abbrev qz121 := qz276

noncomputable abbrev qz394 := (@HPow.hPow Complex Complex Complex qz514 (@Nat.cast Complex Complex.instNatCast 19) qz515)

noncomputable abbrev qz122 := qz394

noncomputable abbrev qz395 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable abbrev qz123 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz273 (1 : Complex))) qz365)

noncomputable abbrev qz124 := (@instHSub Nat instSubNat)

noncomputable abbrev qz396 := qz527

noncomputable abbrev qz125 := qz396

noncomputable abbrev qz126 := qz395

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 19) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (@HMul.hMul Complex Complex Complex qz71 qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) Bool.false ep293 906216615218695582515200 ep294

noncomputable def ep426 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (@HMul.hMul Complex Complex Complex qz71 qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) Bool.false 1026651212121 274877906944 126739423839003 21686492468346880

noncomputable def ep427 := nat_lit 1383792771438948154500710400

noncomputable def ep428 := nat_lit 230632128573158025750118400

noncomputable def ep429 := nat_lit 901634957237376894296448386453209088

noncomputable def ep430 := nat_lit 1834427819375819189899706211762176

noncomputable def ep431 := @ep426 Bool.false 5404543187 137438953472 63373897812069 10843246234173440 Bool.true 104531606561383454366623 906216615218695582515200 171352755845181009217103 ep427 Bool.true 4470461844811373687517 453108307609347791257600 28375776111448332348691 ep428 Bool.false ep429 ep293 906216615218695582515200 ep294 ep295 Bool.false ep430 13347219060057389942083 453108307609347791257600

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 19, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz121) (BSN.headSumC qz5 19) Bool.false 1026651212121 274877906944 126739423839003 21686492468346880 Bool.false 5404543187 137438953472 63373897812069

noncomputable abbrev qz127 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz276)

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz127) Bool.false 1026651212121 274877906944 126739423839003 21686492468346880 Bool.false 5404543187 137438953472 63373897812069 10843246234173440

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz127 Bool.false 61332380881 17179869184 12186842305625 2168649246834688 Bool.true 35478030651 274877906944 24375237154397 4337298493669376 Bool.false

noncomputable abbrev qz128 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz276)

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz40 qz128) Bool.false 61332380881 17179869184 12186842305625 2168649246834688 Bool.true 35478030651 274877906944 24375237154397 4337298493669376

noncomputable def ep436 := @Enclosure.Complex.IsNear.addLitP qz40 qz128 Bool.false 60131491285 17179869184 11686397973789 2168649246834688 Bool.false 7090250217 68719476736 11684405527901 2168649246834688 Bool.false

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz397))

noncomputable abbrev qz398 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz268 qz281 qz398)

noncomputable def ep437 := @Enclosure.Complex.IsNear.of_eq qz128 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 300222399 4294967296 125111082959 542162311708672 Bool.true 63839031519 274877906944 1006426098595 4337298493669376 (BSN.cpow_neg_s_mk qz16 73635 1000 17 qz17 rfl)

noncomputable abbrev qz399 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep438 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz397) 2161695 524288 1 524288 63579 63580 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz397) (Real.sqrt qz399) Bool.false 2161695 524288 1 524288 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz399) Bool.false 2161695 524288 1 524288 2161695 524288 1 524288 (BSN.sqrt_enclosure 17 1 1080847 1080848 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep439 := BSN.log_dyadic_bound 1 33 2 1 3267 262144 78895 1 1 15892 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep440 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz398 73635 1000 0 1 3189913004350711 1125899906842624 50000000015779 3944750000000000000 46977848815072920897 225179981368524800 736350000232377333 788950000000000000000 qz20 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz399) Bool.false 26758929747600409100288 9444732965739290427392 1000000000315580 78895000000000000000 3189913004350711 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep439 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep441 := nat_lit 7941837694018338218779467752594550092773966660178109390704719667488369079841

noncomputable def ep442 := nat_lit 12607950063305666342443600448187934195786064511415559158189445373944329761

noncomputable def ep443 := nat_lit 23800297181928403323653516056887274409930327851511497053797780111717218580001

noncomputable def ep444 := BSN.cos_dyadic_bound_f 1372715571 1073741824 3 2 524288 157945 ep441 ep57 ep442 ep443 ep60 ep442 151104 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1372715571) qz284 0 2 ep441 ep57 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1372715571) qz285 0 2 ep443 ep60 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109378827) qz38)

noncomputable def ep445 := @Enclosure.Real.IsNear.cos_image qz130 qz400 Bool.false 109378827 524288 491 524288 Bool.false 151104 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 46977848815072920897 225179981368524800 736350000232377333 788950000000000000000 109378827 524288 491 524288 (ep440 rfl) rfl) (Enclosure.sfrac_false_div 109378827 524288) (BSN.cos_reduce0 qz400 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96596270871606265380864) qz39) 226375608064910080 72057594037927936 Bool.false 151104 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 109378827 524288 226375608064910080 72057594037927936 33 96596270871606265380864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 151104 524288 96596270871606265380864 75557863725914323419136 1372715571 1073741824 157945 157790 (ep444 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep446 := nat_lit 14285221489182364260729087074311639819636511136711464455941943845179908879905

noncomputable def ep447 := nat_lit 37393262457279887699259843174852466681778637444082972193591831921056232437281

noncomputable def ep448 := BSN.sin_dyadic_bound_f 1372715571 1073741824 3 2 524288 157945 ep446 ep94 ep442 ep447 ep96 ep442 502041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1372715571) qz290 0 2 ep446 ep94 ep442 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1372715571) qz291 0 2 ep447 ep96 ep442 rfl rfl rfl rfl) rfl rfl

noncomputable def ep449 := @Enclosure.Real.IsNear.sin_image qz130 qz400 Bool.false 109378827 524288 491 524288 Bool.false 502041 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 46977848815072920897 225179981368524800 736350000232377333 788950000000000000000 109378827 524288 491 524288 (ep440 rfl) rfl) (Enclosure.sfrac_false_div 109378827 524288) (BSN.sin_reduce0 qz400 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96596270871606265380864) qz39) 226375608064910080 72057594037927936 Bool.false 502041 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 109378827 524288 226375608064910080 72057594037927936 33 96596270871606265380864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 502041 524288 96596270871606265380864 75557863725914323419136 1372715571 1073741824 157945 157790 (ep448 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz401 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 127159 524288 1 524288 127159 524288 1 524288 (ep438 rfl rfl) rfl)

noncomputable def ep450 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 300222399 4294967296 125111082959 542162311708672 Bool.true 63839031519 274877906944 1006426098595 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 127159 524288 1 524288 2361 8192 39261733 41363701760 300222399 4294967296 125111082959 542162311708672 qz401 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 151104 524288 39261733 41363701760 2361 8192 39261733 41363701760 (ep445 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 127159 524288 1 524288 502041 524288 39261733 41363701760 63839031519 274877906944 1006426098595 4337298493669376 qz401 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.false 502041 524288 39261733 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.false 502041 524288 39261733 41363701760 502041 524288 39261733 41363701760 (ep449 rfl rfl) rfl)) rfl)

noncomputable def ep451 := @ep436 300222399 4294967296 125111082959 542162311708672 Bool.true 63839031519 274877906944 1006426098595 4337298493669376 Bool.false 263420570069710667776 61332380881 17179869184 12186842305625 2168649246834688 Bool.true 2438031701960489435136 35478030651 274877906944 24375237154397 4337298493669376 EMRow19.d7 (ep437 ep450) rfl rfl

noncomputable abbrev qz402 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz131 := (@Inv.inv Real Real.instInv (Real.sqrt qz402))

noncomputable abbrev qz403 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz268 qz281 qz403)

noncomputable def ep452 := @Enclosure.Complex.IsNear.of_eq qz127 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)))) Bool.false 45333118025 274877906944 4871000782753 21686492468346880 Bool.false 46287117025 274877906944 4871609852153 21686492468346880 (BSN.cpow_neg_s_mk qz16 73635 1000 18 qz17 rfl)

noncomputable abbrev qz404 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz18)

noncomputable def ep453 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz402) 2224365 524288 1 524288 61787 61788 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz402) (Real.sqrt qz404) Bool.false 2224365 524288 1 524288 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz404) Bool.false 2224365 524288 1 524288 2224365 524288 1 524288 (BSN.sqrt_enclosure 18 1 1112182 1112183 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep454 := BSN.log_dyadic_bound 2 34 2 1 3468 262144 78895 4 4 30876 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep455 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz403 73635 1000 0 1 3254268794313975 1125899906842624 50000000015779 3944750000000000000 1917024661354476393 9007199254740992 736350000232377333 788950000000000000000 qz20 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 27298785242132565196800 9444732965739290427392 1000000000315580 78895000000000000000 3254268794313975 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep454 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep456 := nat_lit 479486859083136928175971945777463296

noncomputable def ep457 := BSN.sin_dyadic_bound_f 832135744 1073741824 2 1 524288 157945 ep456 ep64 ep456 ep456 ep65 ep456 366847 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 832135744) qz290 0 1 ep456 ep64 ep456 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 832135744) qz291 0 1 ep456 ep65 ep456 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111585521) qz38)

noncomputable def ep458 := @Enclosure.Real.IsNear.cos_image qz132 qz405 Bool.false 111585521 524288 245 262144 Bool.false 366847 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1917024661354476393 9007199254740992 736350000232377333 788950000000000000000 111585521 524288 245 262144 (ep455 rfl) rfl) (Enclosure.sfrac_false_div 111585521 524288) (BSN.cos_reduce3 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58556347304062234918912) qz39) 226375608064910080 72057594037927936 Bool.false 366847 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 111585521 524288 226375608064910080 72057594037927936 33 58556347304062234918912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 366847 524288 58556347304062234918912 75557863725914323419136 832135744 1073741824 157945 157790 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep459 := nat_lit 1070973466911227984950281186639195306690403706715460028913811043378733776896

noncomputable def ep460 := nat_lit 229907648033412010122922523932445095576862393825095858330910616627183616

noncomputable def ep461 := nat_lit 3212460585437617130830597714869721029880057395358729895024771308902946963456

noncomputable def ep462 := BSN.cos_dyadic_bound_f 832135744 1073741824 3 2 524288 157945 ep459 ep57 ep460 ep461 ep60 ep460 374567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 832135744) qz284 0 2 ep459 ep57 ep460 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 832135744) qz285 0 2 ep461 ep60 ep460 rfl rfl rfl rfl) rfl rfl

noncomputable def ep463 := @Enclosure.Real.IsNear.sin_image qz132 qz405 Bool.false 111585521 524288 245 262144 Bool.true 374567 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 1917024661354476393 9007199254740992 736350000232377333 788950000000000000000 111585521 524288 245 262144 (ep455 rfl) rfl) (Enclosure.sfrac_false_div 111585521 524288) (BSN.sin_reduce3 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58556347304062234918912) qz39) 226375608064910080 72057594037927936 Bool.false 374567 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 111585521 524288 226375608064910080 72057594037927936 33 58556347304062234918912 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 374567 524288 58556347304062234918912 75557863725914323419136 832135744 1073741824 157945 157790 (ep462 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz406 := (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 123575 524288 1 524288 123575 524288 1 524288 (ep453 rfl rfl) rfl)

noncomputable def ep464 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132))) Bool.false 45333118025 274877906944 4871000782753 21686492468346880 Bool.false 46287117025 274877906944 4871609852153 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz132) 123575 524288 1 524288 366847 524288 19591419 20681850880 45333118025 274877906944 4871000782753 21686492468346880 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 366847 524288 19591419 20681850880 366847 524288 19591419 20681850880 (ep458 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz131 (@Neg.neg Real Real.instNeg (Real.sin qz132)) 123575 524288 1 524288 374567 524288 19591419 20681850880 46287117025 274877906944 4871609852153 21686492468346880 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz132) Bool.true 374567 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' (Real.sin qz132) Bool.true 374567 524288 19591419 20681850880 374567 524288 19591419 20681850880 (ep463 rfl rfl) rfl)) rfl)

noncomputable def ep465 := @ep434 45333118025 274877906944 4871000782753 21686492468346880 Bool.false 46287117025 274877906944 4871609852153 21686492468346880 Bool.false 17637733521833815179264 1026651212121 274877906944 126739423839003 21686492468346880 Bool.false 2971179038462030381056 5404543187 137438953472 63373897812069 10843246234173440 (ep435 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep451 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep452 ep464) rfl rfl

noncomputable def ep466 := @Enclosure.Complex.IsNear.mul qz122 (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.true 104531606561383454366623 906216615218695582515200 171352755845181009217103 ep427 Bool.true

noncomputable abbrev qz133 := (Complex.re qz394)

noncomputable abbrev qz134 := (Complex.im qz394)

noncomputable def ep467 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 519707219068885505909 4531083076093477912576 759076128299239627021

noncomputable def ep468 := nat_lit 6918963857194740772503552

noncomputable def ep469 := nat_lit 461264257146316051500236800

noncomputable def ep470 := nat_lit 473641393407146521606597605097244070246350848

noncomputable def ep471 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 31500228147 137438953472 15336244681 69956427317248 49495567141

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz135 := (@Inv.inv Real Real.instInv (Real.sqrt qz407))

noncomputable abbrev qz408 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz518 (Real.log (Enclosure.sfrac Bool.false 19 1)))

noncomputable abbrev qz136 := (Real.cos qz408)

noncomputable abbrev qz137 := (Real.sin qz408)

noncomputable abbrev qz409 := (@Neg.neg Real Real.instNeg qz137)

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz409)) Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (BSN.cpow_neg_s_mk qz16 73635 1000 19 qz17 rfl)

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18)

noncomputable def ep473 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz407) 2285319 524288 1 524288 60139 60140 262144 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz407) (Real.sqrt qz410) Bool.false 2285319 524288 1 524288 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz410) Bool.false 2285319 524288 1 524288 2285319 524288 1 524288 (BSN.sqrt_enclosure 19 1 1142659 1142660 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep474 := BSN.log_dyadic_bound 3 35 3 2 22509375 262144 78895 55368 243 45049 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz411 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz138 := qz411

noncomputable abbrev qz412 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18))

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz138 73635 1000 0 1 3315141365800183 1125899906842624 50000000015779 3944750000000000000 48822086894139295041 225179981368524800 736350000232377333 788950000000000000000 qz20 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 27809421382282341515264 9444732965739290427392 1000000000315580 78895000000000000000 3315141365800183 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep476 := BSN.cos_dyadic_bound_f 46950988 1073741824 1 0 524288 157945 0 1 1 0 1 1 523786 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 46950988) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 46950988) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz139 := qz408

noncomputable abbrev qz413 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113672779) qz38)

noncomputable def ep477 := @Enclosure.Real.IsNear.cos_image qz139 qz413 Bool.false 113672779 524288 245 262144 Bool.true 523786 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 48822086894139295041 225179981368524800 736350000232377333 788950000000000000000 113672779 524288 245 262144 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 113672779 524288) (BSN.cos_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3303882133490282528768) qz39) 226375608064910080 72057594037927936 Bool.false 523786 524288 34 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 113672779 524288 226375608064910080 72057594037927936 34 3303882133490282528768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523786 524288 3303882133490282528768 75557863725914323419136 46950988 1073741824 157945 157790 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := BSN.sin_dyadic_bound_f 46950988 1073741824 1 0 524288 157945 0 1 1 0 1 1 22917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 46950988) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 46950988) qz291 0 0 rfl) rfl rfl

noncomputable def ep479 := @Enclosure.Real.IsNear.sin_image qz139 qz413 Bool.false 113672779 524288 245 262144 Bool.true 22917 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 48822086894139295041 225179981368524800 736350000232377333 788950000000000000000 113672779 524288 245 262144 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 113672779 524288) (BSN.sin_reduce2 qz413 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3303882133490282528768) qz39) 226375608064910080 72057594037927936 Bool.false 22917 524288 34 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 113672779 524288 226375608064910080 72057594037927936 34 3303882133490282528768 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 22917 524288 3303882133490282528768 75557863725914323419136 46950988 1073741824 157945 157790 (ep478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz414 := (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 120279 524288 1 524288 120279 524288 1 524288 (ep473 rfl rfl) rfl)

noncomputable def ep480 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 qz136) (@HMul.hMul Real Real Real qz0 qz135 qz409) Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (@Enclosure.Real.IsNear.mulLit_ft qz135 qz136 120279 524288 1 524288 261893 262144 19591419 20681850880 31500228147 137438953472 15336244681 69956427317248 qz414 (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 523786 524288 19591419 20681850880 261893 262144 19591419 20681850880 (ep477 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 qz409 120279 524288 1 524288 22917 524288 19591419 20681850880 2756433843 274877906944 30417547041 139912854634496 qz414 (@Enclosure.Real.IsNear.neg qz137 Bool.true 22917 524288 19591419 20681850880 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 22917 524288 19591419 20681850880 22917 524288 19591419 20681850880 (ep479 rfl rfl) rfl)) rfl)

noncomputable def ep481 := @ep471 98903905224 0 1 519707219068885505909 4531083076093477912576 759076128299239627021 ep468 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (ep472 ep480))

noncomputable def ep482 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 49495567141 98903905224 0 1 Bool.false

noncomputable def ep483 := @Enclosure.Complex.IsNear.addLitP qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) Bool.false 216134529 433789058 0 1 Bool.true 55962600

noncomputable def ep484 := @ep483 216894529 0 1 Bool.false 1 456 0 1 Bool.false 4909 15200 0 1 Bool.false 98991134282 49495567141 98903905224 0 1 Bool.false 214103722861 214103722861 3296796840800 0 1

noncomputable abbrev qz140 := (@HDiv.hDiv Complex Complex Complex qz366 qz395 (@HSub.hSub Complex Complex Complex qz358 qz273 (1 : Complex)))

noncomputable def ep485 := @Enclosure.Complex.IsNear.addLitP qz140 qz98 Bool.true 38000000 21689452900 0 1 Bool.true 5596260000 21689452900 0 1

noncomputable def ep486 := @Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk (Enclosure.sfrac Bool.true 38000000 21689452900) (Enclosure.sfrac Bool.true 5596260000 21689452900)) Bool.true 38000000 21689452900 0 1 Bool.true 5596260000 21689452900 0 1

noncomputable def ep487 := @ep485 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 21613452900 216134529 433789058 0 1 Bool.true 5596260000 55962600 216894529 0 1 (ep486 (BSN.N_div_s_sub_one_mk qz16 73635 1000 19 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 38000000 21689452900) (Enclosure.sfrac Bool.true 5596260000 21689452900) Bool.true 38000000 21689452900 0 1 Bool.true 5596260000 21689452900 0 1 (Enclosure.Real.IsNear.const Bool.true 38000000 21689452900) (Enclosure.Real.IsNear.const Bool.true 5596260000 21689452900))) qz99 rfl

noncomputable abbrev qz141 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz142 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz396 qz395 1))

noncomputable def ep488 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142)) Bool.false 1 456 0 1

noncomputable def ep489 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142) Bool.false 0 1 0 1 Bool.false

noncomputable def ep490 := @ep489 0 1 0 1 Bool.false 1 456 0 1 Bool.false 4909 15200 0 1 Bool.false 1 1 456 0 1 Bool.false 4909 4909 15200 0

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep492 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz142 Bool.false 1 456 0 1 Bool.false 4909 15200 0 1

noncomputable def ep493 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142)) 1 456 0 1 0 1 0

noncomputable def ep494 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142) 1 24 0 1 1 19 0 1 1

noncomputable def ep495 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep496 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep497 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow19.d8 rfl) qz384

noncomputable def ep498 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep499 := ep498 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz93 qz16) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 73635 1000 qz17) (@Enclosure.Complex.IsNear.mk qz93 qz16 Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 qz376 qz20))

noncomputable def ep500 := @ep496 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep501 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 73635 1000 0 1 0 1 0

noncomputable def ep502 := @ep501 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep503 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 4909 800 0 1 0 1 0 1 4909

noncomputable def ep504 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 73635 1000 0 1 4909 800 0

noncomputable def ep505 := @ep504 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep506 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep507 := @ep506 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep508 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 (@ep495 1 24 0 1 (ep500 rfl) (ep502 rfl) rfl rfl) (@ep503 4909 800 0 1 (ep505 rfl) (ep507 rfl) rfl rfl)

noncomputable def ep509 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 ep508

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz396 qz395 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 19) qz279) Bool.false 1 19 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 19 1 19 EMRow19.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 19) qz279 Bool.false 1 19 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 19) qz293))

noncomputable def ep510 := @ep494 456 0 1 ep509 (@Enclosure.Complex.IsNear.re_isNear qz142 Bool.false 1 19 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep511 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142) 4909 800 0 1 0 1 0 1 0

noncomputable def ep512 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 4909 800 0 1 ep508

noncomputable def ep513 := @ep511 1 0 1 ep512 (@Enclosure.Complex.IsNear.im_isNear qz142 Bool.false 1 19 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep514 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142)) 0 1 0 1 4909 15200 0

noncomputable def ep515 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz142) 1 24 0 1 0 1 0 1 0

noncomputable def ep516 := @ep515 1 0 1 ep509 (@Enclosure.Complex.IsNear.im_isNear qz142 Bool.false 1 19 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz142) 4909 800 0 1 1 19 0 1 4909

noncomputable def ep518 := @ep517 15200 0 1 ep512 (@Enclosure.Complex.IsNear.re_isNear qz142 Bool.false 1 19 0 1 Bool.false 0 1 0 1 qz143)

noncomputable def ep519 := @ep490 1 (@ep491 0 1 0 1 (BSN.bern_sum_base qz5 19) qz114) (ep492 (@ep493 1 1 1 456 0 1 (ep510 rfl) (ep513 rfl) rfl rfl) (@ep514 1 4909 4909 15200 0 1 (ep516 rfl) (ep518 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep520 := ep484 (ep487 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep488 Bool.false 4909 15200 0 1 (BSN.bern_sum_succ qz5 19 0 1 1 rfl rfl) (ep519 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep521 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 2756433843 274877906944 30417547041 139912854634496 214103722861

noncomputable def ep522 := @ep521 3296796840800 0 1 590162747606353184823 906216615218695582515200 6512510061777694604301 ep469 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (ep472 ep480))

noncomputable def ep523 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 49495567141 98903905224 0 1 Bool.false

noncomputable def ep524 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 6744316117243559568567 453108307609347791257600 3283547080909309352341

noncomputable def ep525 := nat_lit 4612642571463160515002368

noncomputable def ep526 := nat_lit 40512068014692886338647224862128361737027584

noncomputable def ep527 := @Enclosure.Real.IsNear.mulLit_tf qz133 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 31500228147 137438953472 15336244681 69956427317248 214103722861

noncomputable def ep528 := @ep527 3296796840800 0 1 6744316117243559568567 453108307609347791257600 3283547080909309352341 ep428 (@Enclosure.Complex.IsNear.re_isNear qz122 Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (ep472 ep480))

noncomputable def ep529 := @Enclosure.Real.IsNear.mulLit_ff qz134 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz123 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz126 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 2756433843 274877906944 30417547041 139912854634496 49495567141

noncomputable def ep530 := @ep529 98903905224 0 1 45477085448643717621 9062166152186955825152 501844580610780459927 ep525 (@Enclosure.Complex.IsNear.im_isNear qz122 Bool.true 31500228147 137438953472 15336244681 69956427317248 Bool.false 2756433843 274877906944 30417547041 139912854634496 (ep472 ep480))

noncomputable abbrev qz415 := (ep520 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep531 := @ep466 4470461844811373687517 453108307609347791257600 28375776111448332348691 ep428 (@ep467 ep468 590162747606353184823 906216615218695582515200 6512510061777694604301 ep469 ep470 104531606561383454366623 906216615218695582515200 171352755845181009217103 ep427 (ep481 (@ep482 214103722861 3296796840800 0 1 qz415) rfl) (ep522 (@ep523 214103722861 3296796840800 0 1 qz415) rfl) rfl rfl) (@ep524 ep428 45477085448643717621 9062166152186955825152 501844580610780459927 ep525 ep526 4470461844811373687517 453108307609347791257600 28375776111448332348691 ep428 (ep528 (@ep523 214103722861 3296796840800 0 1 qz415) rfl) (ep530 (@ep482 214103722861 3296796840800 0 1 qz415) rfl) rfl rfl)

noncomputable def ep532 := @ep431 ep423 ep424 (@ep432 10843246234173440 (BSN.head_sum_c_eq qz5 19) (ep433 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep531 rfl rfl rfl

noncomputable def ep533 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 19) Bool.false ep293 906216615218695582515200 ep294 ep295 Bool.false 13347219060057389942083 453108307609347791257600 ep423 ep424 (@ep425 ep295 Bool.false 13347219060057389942083 453108307609347791257600 ep423 ep424 (BSN.zetaApproximant_eq_folded' qz5 1 19 rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) (Complex.im (zetaApproximant qz5 1 19)) 49 262144 9019489

noncomputable def ep535 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75)) Bool.false 98 524288 9019489

noncomputable def ep536 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) qz362 Bool.false 14000295 262144 111

noncomputable def ep537 := nat_lit 18128003756643501550881291202831559167930267906953219924887321934078610046976

noncomputable def ep538 := nat_lit 54253161792407116754526899740176949838147822103100871750663523768075970215936

noncomputable def ep539 := BSN.cos_dyadic_bound_f 1686427788 1073741824 3 2 524288 157945 ep537 ep57 ep419 ep538 ep60 ep419 98 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686427788) qz284 0 2 ep537 ep57 ep419 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686427788) qz285 0 2 ep538 ep60 ep419 rfl rfl rfl rfl) rfl rfl

noncomputable def ep540 := @ep536 262144 Bool.false 98 524288 1 78895 (@ep299 14000295 262144 111 262144 ep417 rfl) (Enclosure.sfrac_false_div 14000295 262144) (BSN.sin_reduce1 qz362 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59335902823727581102080) qz306) 226375608064910080 72057594037927936 Bool.false 98 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 14000295 262144 226375608064910080 72057594037927936 8 59335902823727581102080 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 98 524288 59335902823727581102080 37778931862957161709568 1686427788 1073741824 157945 157790 (ep539 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep541 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 19) Bool.false ep293 906216615218695582515200 ep294 ep295 Bool.false 13347219060057389942083 453108307609347791257600 ep423 ep424 (@ep425 ep295 Bool.false 13347219060057389942083 453108307609347791257600 ep423 ep424 (BSN.zetaApproximant_eq_folded' qz5 1 19 rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow19.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 19 qz16) Bool.true ep278 ep279 ep280 ep281 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 19 qz16) ep282 Bool.true ep278 ep279 ep280 ep281 (@Eq.refl Real ep282) (@ep283 Bool.true ep278 ep279 ep280 ep281 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz73 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz74 (@Nat.cast Complex Complex.instNatCast j))))) qz75) (zetaApproximant qz5 1 19)) (@ep285 ep279 ep286 ep287 654013733942812107162067 ep288 ep289 ep290 ep291 ep278 ep279 ep280 ep281 (@ep292 20681850880 ep293 906216615218695582515200 ep294 ep295 ep284 ep279 ep286 ep287 (@ep296 20681850880 524287 524288 9019489 20681850880 (ep422 rfl rfl) rfl) ep533 rfl) (@ep534 20681850880 13347219060057389942083 453108307609347791257600 ep423 ep424 654013733942812107162067 ep288 ep289 ep290 (@ep535 20681850880 49 262144 9019489 20681850880 (ep540 rfl rfl) rfl) ep541 rfl) rfl rfl))

noncomputable abbrev qz543 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 76170 1000)))

noncomputable abbrev qz528 := qz543

noncomputable abbrev qz416 := qz528

noncomputable abbrev qz144 := (BSN.headSumC qz416 9)

noncomputable abbrev qz145 := qz416

noncomputable abbrev qz529 := (@Neg.neg Complex Complex.instNeg qz543)

noncomputable abbrev qz417 := qz529

noncomputable abbrev qz146 := qz417

noncomputable abbrev qz418 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 8) qz146)

noncomputable def ep542 := @Enclosure.Complex.IsNear.of_eq qz144 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 8) qz418) Bool.true 108906003625 274877906944 71865350342571 21686492468346880 Bool.true 23060115999 137438953472 35960907786483 10843246234173440

noncomputable def ep543 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 8) qz418 Bool.true 66915234347 137438953472 32171520661947 10843246234173440 Bool.false 47812653615 274877906944 64370134892529 21686492468346880 Bool.false

noncomputable abbrev qz419 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 7) qz146)

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 7) qz419) Bool.true 66915234347 137438953472 32171520661947 10843246234173440 Bool.false 47812653615 274877906944 64370134892529 21686492468346880

noncomputable def ep545 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 7) qz419 Bool.true 23037190235 137438953472 28138847196121 10843246234173440 Bool.true 7800999683 274877906944 56317584887667 21686492468346880 Bool.true

noncomputable abbrev qz420 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 6) qz146)

noncomputable def ep546 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 6) qz420) Bool.true 23037190235 137438953472 28138847196121 10843246234173440 Bool.true 7800999683 274877906944 56317584887667 21686492468346880

noncomputable def ep547 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 6) qz420 Bool.true 12934977513 137438953472 23798239357851 10843246234173440 Bool.true 118185192763 274877906944 47603128854147 21686492468346880 Bool.true

noncomputable abbrev qz421 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 5) qz146)

noncomputable def ep548 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 5) qz421) Bool.true 12934977513 137438953472 23798239357851 10843246234173440 Bool.true 118185192763 274877906944 47603128854147 21686492468346880

noncomputable def ep549 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 5) qz421 Bool.false 96769758831 274877906944 38053537742357 21686492468346880 Bool.true 126614822251 274877906944 38098617714197 21686492468346880 Bool.true

noncomputable abbrev qz422 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 4) qz146)

noncomputable def ep550 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 4) qz422) Bool.false 96769758831 274877906944 38053537742357 21686492468346880 Bool.true 126614822251 274877906944 38098617714197 21686492468346880

noncomputable def ep551 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 4) qz422 Bool.false 24791091915 137438953472 1370809937023 1084324623417344 Bool.true 127849245941 137438953472 2743663112535 2168649246834688 Bool.false

noncomputable abbrev qz147 := qz277

noncomputable def ep552 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 3) (@HPow.hPow Complex Complex Complex qz120 qz147 qz146)) Bool.false 24791091915 137438953472 1370809937023 1084324623417344 Bool.true 127849245941 137438953472 2743663112535 2168649246834688

noncomputable def ep553 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 3) (@HPow.hPow Complex Complex Complex qz120 qz147 qz146) Bool.false 7223922403 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 34359738368 188386062089 271081155854336 Bool.true

noncomputable abbrev qz148 := qz278

noncomputable def ep554 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 2) (@HPow.hPow Complex Complex Complex qz120 qz148 qz146)) Bool.false 7223922403 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 34359738368 188386062089 271081155854336

noncomputable def ep555 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 2) (@HPow.hPow Complex Complex Complex qz120 qz148 qz146) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep556 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz145)

noncomputable abbrev qz544 := (Enclosure.sfrac Bool.false 76170 1000)

noncomputable abbrev qz530 := qz544

noncomputable abbrev qz423 := qz530

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log qz282))

noncomputable abbrev qz150 := qz423

noncomputable abbrev qz424 := (@Eq.refl Real qz530)

noncomputable abbrev qz151 := qz424

noncomputable def ep557 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz120 qz148 qz146) (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 9955946781 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 34359738368 188386062089 271081155854336 (BSN.cpow_neg_s_mk qz150 76170 1000 2 qz151 rfl)

noncomputable def ep558 := nat_lit 4551264237242333018493251132945151594739234326697522241934382390708728299520

noncomputable def ep559 := nat_lit 1281318213564031748674467109020802801019913219258586747812299474814959616

noncomputable def ep560 := nat_lit 11917903249003197092270184782394125257877295758043282445569781586039826087936

noncomputable def ep561 := BSN.sin_dyadic_bound_f 1031471244 1073741824 3 2 524288 157945 ep558 ep94 ep559 ep560 ep96 ep559 429682 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1031471244) qz290 0 2 ep558 ep94 ep559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1031471244) qz291 0 2 ep560 ep96 ep559 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz152 := (Enclosure.Real.IsNear.const Bool.false 76170 1000)

noncomputable abbrev qz425 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27680787) qz38)

noncomputable def ep562 := @Enclosure.Real.IsNear.cos_image qz149 qz425 Bool.false 27680787 524288 507 524288 Bool.true 429682 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 173004921 3276800 7617 7889500 27680787 524288 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz19 76170 1000 0 1 181704 262144 1 78895 173004921 3276800 7617 7889500 qz152 qz287 rfl) rfl) (Enclosure.sfrac_false_div 27680787 524288) (BSN.cos_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72583336155232226770944) qz39) 226375608064910080 72057594037927936 Bool.false 429682 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 27680787 524288 226375608064910080 72057594037927936 8 72583336155232226770944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 429682 524288 72583336155232226770944 75557863725914323419136 1031471244 1073741824 157945 157790 (ep561 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep563 := nat_lit 2529049606562880135495661503684649020544472365151627284073684572382544592896

noncomputable def ep564 := nat_lit 7584586183261512342989635576835905456031377269016364678725429118198003859456

noncomputable def ep565 := BSN.cos_dyadic_bound_f 1031471244 1073741824 3 2 524288 157945 ep563 ep57 ep559 ep564 ep60 ep559 300417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1031471244) qz284 0 2 ep563 ep57 ep559 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1031471244) qz285 0 2 ep564 ep60 ep559 rfl rfl rfl rfl) rfl rfl

noncomputable def ep566 := @Enclosure.Real.IsNear.sin_image qz149 qz425 Bool.false 27680787 524288 507 524288 Bool.false 300417 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 173004921 3276800 7617 7889500 27680787 524288 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz19 76170 1000 0 1 181704 262144 1 78895 173004921 3276800 7617 7889500 qz152 qz287 rfl) rfl) (Enclosure.sfrac_false_div 27680787 524288) (BSN.sin_reduce1 qz425 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72583336155232226770944) qz39) 226375608064910080 72057594037927936 Bool.false 300417 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 27680787 524288 226375608064910080 72057594037927936 8 72583336155232226770944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 300417 524288 72583336155232226770944 75557863725914323419136 1031471244 1073741824 157945 157790 (ep565 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep567 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 9955946781 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 34359738368 188386062089 271081155854336 (@Enclosure.Real.IsNear.mulLit_ft qz14 (Real.cos qz149) 46341 65536 1 262144 214841 262144 40524053 41363701760 9955946781 17179869184 1509128169147 2168649246834688 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 429682 524288 40524053 41363701760 214841 262144 40524053 41363701760 (ep562 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 46341 65536 1 262144 300417 524288 40524053 41363701760 13921624197 34359738368 188386062089 271081155854336 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.false 300417 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.false 300417 524288 40524053 41363701760 300417 524288 40524053 41363701760 (ep566 rfl rfl) rfl)) rfl)

noncomputable def ep568 := @ep555 9955946781 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 34359738368 188386062089 271081155854336 Bool.false 7223922403 7223922403 17179869184 1509128169147 2168649246834688 Bool.true 13921624197 13921624197 34359738368 188386062089 271081155854336 (ep556 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep557 ep567) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep569 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz120 qz147 qz146) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 33000287309 137438953472 1232491704899 2168649246834688 Bool.true 72162749153 137438953472 1236574615823 2168649246834688 (BSN.cpow_neg_s_mk qz150 76170 1000 3 qz151 rfl)

noncomputable def ep570 := nat_lit 44984960199189578639010663504824481

noncomputable def ep571 := BSN.sin_dyadic_bound_f 460539447 1073741824 2 1 524288 157945 ep570 ep64 ep570 ep570 ep65 ep570 218041 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 460539447) qz290 0 1 ep570 ep64 ep570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 460539447) qz291 0 1 ep570 ep65 ep570 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz426 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43873005) qz38)

noncomputable def ep572 := @Enclosure.Real.IsNear.cos_image qz153 qz426 Bool.false 43873005 524288 127 131072 Bool.true 218041 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1096825149 13107200 7617 7889500 43873005 524288 127 131072 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz24 76170 1000 0 1 287994 262144 1 78895 1096825149 13107200 7617 7889500 qz152 qz296 rfl) rfl) (Enclosure.sfrac_false_div 43873005 524288) (BSN.cos_reduce1 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32407582567779522314240) qz39) 226375608064910080 72057594037927936 Bool.false 218041 524288 13 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 43873005 524288 226375608064910080 72057594037927936 13 32407582567779522314240 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 218041 524288 32407582567779522314240 75557863725914323419136 460539447 1073741824 157945 157790 (ep571 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep573 := BSN.cos_dyadic_bound_f 460539447 1073741824 2 1 524288 157945 ep570 ep110 ep570 ep570 ep111 ep570 476797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 460539447) qz284 0 1 ep570 ep110 ep570 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 460539447) qz285 0 1 ep570 ep111 ep570 rfl rfl rfl rfl) rfl rfl

noncomputable def ep574 := @Enclosure.Real.IsNear.sin_image qz153 qz426 Bool.false 43873005 524288 127 131072 Bool.false 476797 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1096825149 13107200 7617 7889500 43873005 524288 127 131072 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz24 76170 1000 0 1 287994 262144 1 78895 1096825149 13107200 7617 7889500 qz152 qz296 rfl) rfl) (Enclosure.sfrac_false_div 43873005 524288) (BSN.sin_reduce1 qz426 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32407582567779522314240) qz39) 226375608064910080 72057594037927936 Bool.false 476797 524288 13 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 43873005 524288 226375608064910080 72057594037927936 13 32407582567779522314240 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 476797 524288 32407582567779522314240 75557863725914323419136 460539447 1073741824 157945 157790 (ep573 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep575 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 33000287309 137438953472 1232491704899 2168649246834688 Bool.true 72162749153 137438953472 1236574615823 2168649246834688 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz153) 151349 262144 1 262144 218041 524288 10150737 10340925440 33000287309 137438953472 1232491704899 2168649246834688 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 218041 524288 10150737 10340925440 218041 524288 10150737 10340925440 (ep572 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 151349 262144 1 262144 476797 524288 10150737 10340925440 72162749153 137438953472 1236574615823 2168649246834688 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 476797 524288 10150737 10340925440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 476797 524288 10150737 10340925440 476797 524288 10150737 10340925440 (ep574 rfl rfl) rfl)) rfl)

noncomputable def ep576 := @ep553 33000287309 137438953472 1232491704899 2168649246834688 Bool.true 72162749153 137438953472 1236574615823 2168649246834688 Bool.false 425907716028220047360 24791091915 137438953472 1370809937023 1084324623417344 Bool.true 4392866641078845964288 127849245941 137438953472 2743663112535 2168649246834688 (ep554 (BSN.head_sum_c_succ qz145 2 3 rfl rfl) (ep568 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep569 ep575) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz422 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 47187575001 274877906944 10637339001897 21686492468346880 Bool.false 129083669631 274877906944 10661986588847 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 4 qz151 rfl)

noncomputable def ep578 := nat_lit 20053761811661608668067936326782976

noncomputable def ep579 := BSN.sin_dyadic_bound_f 376312776 1073741824 2 1 524288 157945 ep578 ep64 ep578 ep578 ep65 ep578 180007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 376312776) qz290 0 1 ep578 ep64 ep578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 376312776) qz291 0 1 ep578 ep65 ep578 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz427 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27680787) qz30)

noncomputable def ep580 := @Enclosure.Real.IsNear.cos_image qz154 qz427 Bool.false 27680787 262144 507 524288 Bool.false 180007 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 173004921 1638400 7617 7889500 27680787 262144 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz27 76170 1000 0 1 363408 262144 1 78895 173004921 1638400 7617 7889500 qz152 qz300 rfl) rfl) (Enclosure.sfrac_false_div 27680787 262144) (BSN.cos_reduce3 qz427 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13240328754664438759424) qz306) 226375608064910080 72057594037927936 Bool.false 180007 524288 16 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 27680787 262144 226375608064910080 72057594037927936 16 13240328754664438759424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 180007 524288 13240328754664438759424 37778931862957161709568 376312776 1073741824 157945 157790 (ep579 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep581 := BSN.cos_dyadic_bound_f 376312776 1073741824 2 1 524288 157945 ep578 ep110 ep578 ep578 ep111 ep578 492417 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 376312776) qz284 0 1 ep578 ep110 ep578 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 376312776) qz285 0 1 ep578 ep111 ep578 rfl rfl rfl rfl) rfl rfl

noncomputable def ep582 := @Enclosure.Real.IsNear.sin_image qz154 qz427 Bool.false 27680787 262144 507 524288 Bool.true 492417 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 173004921 1638400 7617 7889500 27680787 262144 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz27 76170 1000 0 1 363408 262144 1 78895 173004921 1638400 7617 7889500 qz152 qz300 rfl) rfl) (Enclosure.sfrac_false_div 27680787 262144) (BSN.sin_reduce3 qz427 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13240328754664438759424) qz306) 226375608064910080 72057594037927936 Bool.false 492417 524288 16 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 27680787 262144 226375608064910080 72057594037927936 16 13240328754664438759424 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 492417 524288 13240328754664438759424 37778931862957161709568 376312776 1073741824 157945 157790 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 47187575001 274877906944 10637339001897 21686492468346880 Bool.false 129083669631 274877906944 10661986588847 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz154) 262143 524288 1 524288 180007 524288 40524053 41363701760 47187575001 274877906944 10637339001897 21686492468346880 qz302 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 180007 524288 40524053 41363701760 180007 524288 40524053 41363701760 (ep580 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 262143 524288 1 524288 492417 524288 40524053 41363701760 129083669631 274877906944 10661986588847 21686492468346880 qz302 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 492417 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 492417 524288 40524053 41363701760 492417 524288 40524053 41363701760 (ep582 rfl rfl) rfl)) rfl)

noncomputable def ep584 := @ep551 47187575001 274877906944 10637339001897 21686492468346880 Bool.false 129083669631 274877906944 10661986588847 21686492468346880 Bool.false 13299934381470470111232 96769758831 274877906944 38053537742357 21686492468346880 Bool.true 17401808664220739305472 126614822251 274877906944 38098617714197 21686492468346880 (ep552 (BSN.head_sum_c_succ qz145 3 4 rfl rfl) (ep576 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep577 ep583) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep585 := @Enclosure.Complex.IsNear.of_eq qz421 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 122639713857 274877906944 1908588194669 4337298493669376 Bool.false 526851843 17179869184 950451113995 2168649246834688 (BSN.cpow_neg_s_mk qz150 76170 1000 5 qz151 rfl)

noncomputable def ep586 := BSN.cos_dyadic_bound_f 73689420 1073741824 1 0 524288 157945 0 1 1 0 1 1 523053 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 73689420) qz284 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 73689420) qz285 0 0 rfl) rfl rfl

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64272855) qz38)

noncomputable def ep587 := @Enclosure.Real.IsNear.cos_image qz155 qz428 Bool.false 64272855 524288 507 524288 Bool.true 523053 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 200852673 1638400 7617 7889500 64272855 524288 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz31 76170 1000 0 1 421904 262144 1 78895 200852673 1638400 7617 7889500 qz152 qz305 rfl) rfl) (Enclosure.sfrac_false_div 64272855 524288) (BSN.cos_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5185432008638532157440) qz39) 226375608064910080 72057594037927936 Bool.false 523053 524288 19 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 64272855 524288 226375608064910080 72057594037927936 19 5185432008638532157440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 523053 524288 5185432008638532157440 75557863725914323419136 73689420 1073741824 157945 157790 (ep586 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep588 := BSN.sin_dyadic_bound_f 73689420 1073741824 1 0 524288 157945 0 1 1 0 1 1 35952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 73689420) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 73689420) qz291 0 0 rfl) rfl rfl

noncomputable def ep589 := @Enclosure.Real.IsNear.sin_image qz155 qz428 Bool.false 64272855 524288 507 524288 Bool.true 35952 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 200852673 1638400 7617 7889500 64272855 524288 507 524288 (@Enclosure.Real.IsNear.mulLit_ff qz150 qz31 76170 1000 0 1 421904 262144 1 78895 200852673 1638400 7617 7889500 qz152 qz305 rfl) rfl) (Enclosure.sfrac_false_div 64272855 524288) (BSN.sin_reduce2 qz428 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5185432008638532157440) qz39) 226375608064910080 72057594037927936 Bool.false 35952 524288 19 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 64272855 524288 226375608064910080 72057594037927936 19 5185432008638532157440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 35952 524288 5185432008638532157440 75557863725914323419136 73689420 1073741824 157945 157790 (ep588 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep590 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 122639713857 274877906944 1908588194669 4337298493669376 Bool.false 526851843 17179869184 950451113995 2168649246834688 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz155) 234469 524288 1 524288 523053 524288 40524053 41363701760 122639713857 274877906944 1908588194669 4337298493669376 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 523053 524288 40524053 41363701760 523053 524288 40524053 41363701760 (ep587 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 234469 524288 1 524288 2247 32768 40524053 41363701760 526851843 17179869184 950451113995 2168649246834688 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 2247 32768 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 35952 524288 40524053 41363701760 2247 32768 40524053 41363701760 (ep589 rfl rfl) rfl)) rfl)

noncomputable def ep591 := @ep549 122639713857 274877906944 1908588194669 4337298493669376 Bool.false 526851843 17179869184 950451113995 2168649246834688 Bool.true 7111079090282293100544 12934977513 137438953472 23798239357851 10843246234173440 Bool.true 2030406151154163515392 118185192763 274877906944 47603128854147 21686492468346880 (ep550 (BSN.head_sum_c_succ qz145 4 5 rfl rfl) (ep584 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep585 ep590) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz268 qz423 qz309)

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq qz420 (Complex.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 5051106361 68719476736 434060783827 1084324623417344 Bool.false 13798024135 34359738368 108930700419 271081155854336 (BSN.cpow_neg_s_mk qz150 76170 1000 6 qz151 rfl)

noncomputable def ep593 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz309 76170 1000 0 1 4034681531866359 2251799813685248 100000000015779 7889500000000000000 30732169228226056503 225179981368524800 761700000120188643 788950000000000000000 qz152 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 100000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz310) Bool.false 16922680887833197019136 9444732965739290427392 1000000000157790 78895000000000000000 4034681531866359 2251799813685248 100000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 106290 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep594 := nat_lit 11097725771402764493510574844692658513966904040376123538066149488024029822976

noncomputable def ep595 := nat_lit 24588038305016783118752679189371841594078454624035891154544137680673898496

noncomputable def ep596 := nat_lit 33244001237598259914294219175699231858712555211880298831889360188710741671936

noncomputable def ep597 := BSN.cos_dyadic_bound_f 1492246212 1073741824 3 2 524288 157945 ep594 ep57 ep595 ep596 ep60 ep595 94396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1492246212) qz284 0 2 ep594 ep57 ep595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1492246212) qz285 0 2 ep596 ep60 ep595 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz429 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71553907) qz38)

noncomputable def ep598 := @Enclosure.Real.IsNear.cos_image qz156 qz429 Bool.false 71553907 524288 507 524288 Bool.true 94396 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 30732169228226056503 225179981368524800 761700000120188643 788950000000000000000 71553907 524288 507 524288 (ep593 rfl) rfl) (Enclosure.sfrac_false_div 71553907 524288) (BSN.cos_reduce2 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105007491969640472510464) qz39) 226375608064910080 72057594037927936 Bool.false 94396 524288 21 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 71553907 524288 226375608064910080 72057594037927936 21 105007491969640472510464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 94396 524288 105007491969640472510464 75557863725914323419136 1492246212 1073741824 157945 157790 (ep597 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep599 := nat_lit 19956235957880962661824032577095287851865164508977793655595433768298714562560

noncomputable def ep600 := nat_lit 52226523065765827417823057173704866154208827644598163369452112217870780399616

noncomputable def ep601 := BSN.sin_dyadic_bound_f 1492246212 1073741824 3 2 524288 157945 ep599 ep94 ep595 ep600 ep96 ep595 515720 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1492246212) qz290 0 2 ep599 ep94 ep595 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1492246212) qz291 0 2 ep600 ep96 ep595 rfl rfl rfl rfl) rfl rfl

noncomputable def ep602 := @Enclosure.Real.IsNear.sin_image qz156 qz429 Bool.false 71553907 524288 507 524288 Bool.true 515720 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 30732169228226056503 225179981368524800 761700000120188643 788950000000000000000 71553907 524288 507 524288 (ep593 rfl) rfl) (Enclosure.sfrac_false_div 71553907 524288) (BSN.sin_reduce2 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105007491969640472510464) qz39) 226375608064910080 72057594037927936 Bool.false 515720 524288 21 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 71553907 524288 226375608064910080 72057594037927936 21 105007491969640472510464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515720 524288 105007491969640472510464 75557863725914323419136 1492246212 1073741824 157945 157790 (ep601 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep603 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz32 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 5051106361 68719476736 434060783827 1084324623417344 Bool.false 13798024135 34359738368 108930700419 271081155854336 (@Enclosure.Real.IsNear.mulLit_ft qz32 (Real.cos qz156) 214039 524288 1 524288 23599 131072 40524053 41363701760 5051106361 68719476736 434060783827 1084324623417344 qz312 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 94396 524288 40524053 41363701760 23599 131072 40524053 41363701760 (ep598 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz32 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 214039 524288 1 524288 64465 65536 40524053 41363701760 13798024135 34359738368 108930700419 271081155854336 qz312 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 64465 65536 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 515720 524288 40524053 41363701760 64465 65536 40524053 41363701760 (ep602 rfl rfl) rfl)) rfl)

noncomputable def ep604 := @ep547 5051106361 68719476736 434060783827 1084324623417344 Bool.false 13798024135 34359738368 108930700419 271081155854336 Bool.true 1583103658416888872960 23037190235 137438953472 28138847196121 10843246234173440 Bool.true 268040308116730937344 7800999683 274877906944 56317584887667 21686492468346880 (ep548 (BSN.head_sum_c_succ qz145 5 6 rfl rfl) (ep591 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep592 ep603) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz268 qz423 qz314)

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq qz419 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 2742377757 8589934592 2016336732913 5421623117086720 Bool.false 27806826649 137438953472 4026275002431 10843246234173440 (BSN.cpow_neg_s_mk qz150 76170 1000 7 qz151 rfl)

noncomputable def ep606 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz314 76170 1000 0 1 4381792198794487 2251799813685248 100000000015779 7889500000000000000 33376111178217607479 225179981368524800 761700000120188643 788950000000000000000 qz152 (BSN.isNear_log_sfrac 7 1 4381792198794487 2251799813685248 100000000015779 7889500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz315) Bool.false 18378568546572512002048 9444732965739290427392 1000000000157790 78895000000000000000 4381792198794487 2251799813685248 100000000015779 7889500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 146699 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep607 := nat_lit 135313313650018717312534069277586801

noncomputable def ep608 := BSN.cos_dyadic_bound_f 606506043 1073741824 2 1 524288 157945 ep607 ep110 ep607 ep607 ep111 ep607 442848 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 606506043) qz284 0 1 ep607 ep110 ep607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 606506043) qz285 0 1 ep607 ep111 ep607 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz430 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38854907) qz30)

noncomputable def ep609 := @Enclosure.Real.IsNear.cos_image qz157 qz430 Bool.false 38854907 262144 507 524288 Bool.true 442848 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 33376111178217607479 225179981368524800 761700000120188643 788950000000000000000 38854907 262144 507 524288 (ep606 rfl) rfl) (Enclosure.sfrac_false_div 38854907 262144) (BSN.cos_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21339534321516778881024) qz306) 226375608064910080 72057594037927936 Bool.false 442848 524288 23 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 38854907 262144 226375608064910080 72057594037927936 23 21339534321516778881024 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 442848 524288 21339534321516778881024 37778931862957161709568 606506043 1073741824 157945 157790 (ep608 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep610 := BSN.sin_dyadic_bound_f 606506043 1073741824 2 1 524288 157945 ep607 ep64 ep607 ep607 ep65 ep607 280646 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 606506043) qz290 0 1 ep607 ep64 ep607 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 606506043) qz291 0 1 ep607 ep65 ep607 rfl rfl rfl rfl) rfl rfl

noncomputable def ep611 := @Enclosure.Real.IsNear.sin_image qz157 qz430 Bool.false 38854907 262144 507 524288 Bool.true 280646 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 33376111178217607479 225179981368524800 761700000120188643 788950000000000000000 38854907 262144 507 524288 (ep606 rfl) rfl) (Enclosure.sfrac_false_div 38854907 262144) (BSN.sin_reduce2 qz430 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21339534321516778881024) qz306) 226375608064910080 72057594037927936 Bool.false 280646 524288 23 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 38854907 262144 226375608064910080 72057594037927936 23 21339534321516778881024 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 280646 524288 21339534321516778881024 37778931862957161709568 606506043 1073741824 157945 157790 (ep610 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep612 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 2742377757 8589934592 2016336732913 5421623117086720 Bool.false 27806826649 137438953472 4026275002431 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz157) 198163 524288 1 524288 13839 16384 40524053 41363701760 2742377757 8589934592 2016336732913 5421623117086720 qz317 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 442848 524288 40524053 41363701760 13839 16384 40524053 41363701760 (ep609 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 198163 524288 1 524288 140323 262144 40524053 41363701760 27806826649 137438953472 4026275002431 10843246234173440 qz317 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 140323 262144 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 280646 524288 40524053 41363701760 140323 262144 40524053 41363701760 (ep611 rfl rfl) rfl)) rfl)

noncomputable def ep613 := @ep545 2742377757 8589934592 2016336732913 5421623117086720 Bool.false 27806826649 137438953472 4026275002431 10843246234173440 Bool.true 574797486249081831424 66915234347 137438953472 32171520661947 10843246234173440 Bool.false 6571321075564837601280 47812653615 274877906944 64370134892529 21686492468346880 (ep546 (BSN.head_sum_c_succ qz145 6 7 rfl rfl) (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep605 ep612) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz268 qz423 qz319)

noncomputable def ep614 := @Enclosure.Complex.IsNear.of_eq qz418 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 24924465069 274877906944 7522309018677 21686492468346880 Bool.true 93932885613 274877906944 7551680680437 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 8 qz151 rfl)

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz319 76170 1000 0 1 9364972152248037 4503599627370496 200000000047337 15779000000000000000 71332992883673297829 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz320) Bool.false 19639770079031275290624 9444732965739290427392 1000000000236685 78895000000000000000 9364972152248037 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep616 := nat_lit 8795316511046697665663956671631606154411141849968372507702001884425811403361

noncomputable def ep617 := nat_lit 15458149276609760457334643576387713722531702094100323519846106386719056481

noncomputable def ep618 := nat_lit 26355033234586873476077200727742043035788362145716916876066313440503996097121

noncomputable def ep619 := BSN.cos_dyadic_bound_f 1408136277 1073741824 3 2 524288 157945 ep616 ep57 ep617 ep618 ep60 ep617 134463 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1408136277) qz284 0 2 ep616 ep57 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1408136277) qz285 0 2 ep618 ep60 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83042533) qz38)

noncomputable def ep620 := @Enclosure.Real.IsNear.cos_image qz158 qz431 Bool.false 83042533 524288 507 524288 Bool.false 134463 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 71332992883673297829 450359962737049600 1523400000360565929 1577900000000000000000 83042533 524288 507 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 83042533 524288) (BSN.cos_reduce0 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99088781476910151499776) qz39) 226375608064910080 72057594037927936 Bool.false 134463 524288 25 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 83042533 524288 226375608064910080 72057594037927936 25 99088781476910151499776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 134463 524288 99088781476910151499776 75557863725914323419136 1408136277 1073741824 157945 157790 (ep619 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep621 := nat_lit 15819203200462767989829254294075780906962029968267790255047726506857085280865

noncomputable def ep622 := nat_lit 41406218997621309885002838490122417505540265256358526334664294774285297263201

noncomputable def ep623 := BSN.sin_dyadic_bound_f 1408136277 1073741824 3 2 524288 157945 ep621 ep94 ep617 ep622 ep96 ep617 506751 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1408136277) qz290 0 2 ep621 ep94 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1408136277) qz291 0 2 ep622 ep96 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable def ep624 := @Enclosure.Real.IsNear.sin_image qz158 qz431 Bool.false 83042533 524288 507 524288 Bool.false 506751 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 71332992883673297829 450359962737049600 1523400000360565929 1577900000000000000000 83042533 524288 507 524288 (ep615 rfl) rfl) (Enclosure.sfrac_false_div 83042533 524288) (BSN.sin_reduce0 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99088781476910151499776) qz39) 226375608064910080 72057594037927936 Bool.false 506751 524288 25 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 83042533 524288 226375608064910080 72057594037927936 25 99088781476910151499776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 506751 524288 99088781476910151499776 75557863725914323419136 1408136277 1073741824 157945 157790 (ep623 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep625 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 24924465069 274877906944 7522309018677 21686492468346880 Bool.true 93932885613 274877906944 7551680680437 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz158) 185363 524288 1 524288 134463 524288 40524053 41363701760 24924465069 274877906944 7522309018677 21686492468346880 qz322 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 134463 524288 40524053 41363701760 134463 524288 40524053 41363701760 (ep620 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 185363 524288 1 524288 506751 524288 40524053 41363701760 93932885613 274877906944 7551680680437 21686492468346880 qz322 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 506751 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 506751 524288 40524053 41363701760 506751 524288 40524053 41363701760 (ep624 rfl rfl) rfl)) rfl)

noncomputable def ep626 := @ep543 24924465069 274877906944 7522309018677 21686492468346880 Bool.true 93932885613 274877906944 7551680680437 21686492468346880 Bool.true 14967927165037838336000 108906003625 274877906944 71865350342571 21686492468346880 Bool.true 12677432839381935194112 23060115999 137438953472 35960907786483 10843246234173440 (ep544 (BSN.head_sum_c_succ qz145 7 8 rfl rfl) (ep613 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep614 ep625) rfl rfl

theorem EMRow19.d11 : Enclosure.Complex.IsNear qz144 Bool.true 108906003625 274877906944 71865350342571 21686492468346880 Bool.true 23060115999 137438953472 35960907786483 10843246234173440 := ep542 (BSN.head_sum_c_succ qz145 8 9 rfl rfl) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz159 := (BSN.headSumC qz416 17)

noncomputable abbrev qz160 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 16) qz417)

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq qz159 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 16) qz160) Bool.false 155238507281 274877906944 24170667630863 4337298493669376 Bool.false 44700829083 274877906944 24168117744463 4337298493669376

noncomputable def ep628 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 16) qz160 Bool.false 207736637053 274877906944 115510169507359 21686492468346880 Bool.false 358723357 274877906944 115502329395629 21686492468346880 Bool.true

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 15) qz417)

noncomputable def ep629 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 15) qz161) Bool.false 207736637053 274877906944 115510169507359 21686492468346880 Bool.false 358723357 274877906944 115502329395629 21686492468346880

noncomputable def ep630 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 15) qz161 Bool.false 86930631321 137438953472 27501151160237 5421623117086720 Bool.true 31004228083 137438953472 54990079670389 10843246234173440 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 14) qz417)

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 14) qz162) Bool.false 86930631321 137438953472 27501151160237 5421623117086720 Bool.true 31004228083 137438953472 54990079670389 10843246234173440

noncomputable def ep632 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 14) qz162 Bool.false 50236304325 137438953472 26068479236813 5421623117086720 Bool.true 2041497583 8589934592 26072231009643 5421623117086720 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 13) qz417)

noncomputable def ep633 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 13) qz163) Bool.false 50236304325 137438953472 26068479236813 5421623117086720 Bool.true 2041497583 8589934592 26072231009643 5421623117086720

noncomputable def ep634 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 13) qz163 Bool.false 37258811675 274877906944 98346935723541 21686492468346880 Bool.true 22712175475 274877906944 98373118607191 21686492468346880 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 12) qz417)

noncomputable def ep635 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 12) qz164) Bool.false 37258811675 274877906944 98346935723541 21686492468346880 Bool.true 22712175475 274877906944 98373118607191 21686492468346880

noncomputable def ep636 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 12) qz164 Bool.true 1198049209 17179869184 23043066260499 5421623117086720 Bool.false 8269182691 68719476736 46099390431273 10843246234173440 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 11) qz417)

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 11) qz165) Bool.true 1198049209 17179869184 23043066260499 5421623117086720 Bool.false 8269182691 68719476736 46099390431273 10843246234173440

noncomputable def ep638 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 11) qz165 Bool.true 2947683347 8589934592 21432178226239 5421623117086720 Bool.false 68009818579 274877906944 85775303952731 21686492468346880 Bool.false

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 10) qz417)

noncomputable def ep639 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 10) qz166) Bool.true 2947683347 8589934592 21432178226239 5421623117086720 Bool.false 68009818579 274877906944 85775303952731 21686492468346880

noncomputable def ep640 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 10) qz166 Bool.true 168814410499 274877906944 78974540989273 21686492468346880 Bool.false 5801800381 68719476736 19758814586147 5421623117086720 Bool.false

noncomputable abbrev qz432 := (@HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast 9) qz146)

noncomputable def ep641 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 10) (@HAdd.hAdd Complex Complex Complex qz4 qz144 qz432) Bool.true 168814410499 274877906944 78974540989273 21686492468346880 Bool.false 5801800381 68719476736 19758814586147 5421623117086720

noncomputable def ep642 := @Enclosure.Complex.IsNear.addLitP qz144 qz432 Bool.true 108906003625 274877906944 71865350342571 21686492468346880 Bool.true 23060115999 137438953472 35960907786483 10843246234173440 Bool.true

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz268 qz423 qz324)

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq qz432 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 29954203437 137438953472 3554595323351 10843246234173440 Bool.false 34663716761 137438953472 3556721385811 10843246234173440 (BSN.cpow_neg_s_mk qz150 76170 1000 9 qz151 rfl)

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz324 76170 1000 0 1 9895417793173221 4503599627370496 200000000047337 15779000000000000000 75373397330600424357 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 20752195215788806766592 9444732965739290427392 1000000000236685 78895000000000000000 9895417793173221 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 30876 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep174 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep645 := nat_lit 1610290964783169991591200579476219093774977610103697341849850887829309438081

noncomputable def ep646 := nat_lit 519649897228882430733554825230126550158158671393542114846206749763254401

noncomputable def ep647 := nat_lit 4829833594555052209912134628778197028224616512968304941319860249988401805441

noncomputable def ep648 := BSN.cos_dyadic_bound_f 921433199 1073741824 3 2 524288 157945 ep645 ep57 ep646 ep647 ep60 ep646 342798 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 921433199) qz284 0 2 ep645 ep57 ep646 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 921433199) qz285 0 2 ep647 ep60 ep646 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 87746183) qz38)

noncomputable def ep649 := @Enclosure.Real.IsNear.cos_image qz167 qz433 Bool.false 87746183 524288 507 524288 Bool.true 342798 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 75373397330600424357 450359962737049600 1523400000360565929 1577900000000000000000 87746183 524288 507 524288 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 87746183 524288) (BSN.cos_reduce2 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64840097063096167694336) qz39) 226375608064910080 72057594037927936 Bool.false 342798 524288 26 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 87746183 524288 226375608064910080 72057594037927936 26 64840097063096167694336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 342798 524288 64840097063096167694336 75557863725914323419136 921433199 1073741824 157945 157790 (ep648 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep650 := nat_lit 720867461624453147111611056815707201

noncomputable def ep651 := BSN.sin_dyadic_bound_f 921433199 1073741824 2 1 524288 157945 ep650 ep64 ep650 ep650 ep65 ep650 396694 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 921433199) qz290 0 1 ep650 ep64 ep650 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 921433199) qz291 0 1 ep650 ep65 ep650 rfl rfl rfl rfl) rfl rfl

noncomputable def ep652 := @Enclosure.Real.IsNear.sin_image qz167 qz433 Bool.false 87746183 524288 507 524288 Bool.true 396694 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 75373397330600424357 450359962737049600 1523400000360565929 1577900000000000000000 87746183 524288 507 524288 (ep644 rfl) rfl) (Enclosure.sfrac_false_div 87746183 524288) (BSN.sin_reduce2 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64840097063096167694336) qz39) 226375608064910080 72057594037927936 Bool.false 396694 524288 26 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 87746183 524288 226375608064910080 72057594037927936 26 64840097063096167694336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 396694 524288 64840097063096167694336 75557863725914323419136 921433199 1073741824 157945 157790 (ep651 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep653 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 29954203437 137438953472 3554595323351 10843246234173440 Bool.false 34663716761 137438953472 3556721385811 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz167) 174763 524288 1 524288 171399 262144 40524053 41363701760 29954203437 137438953472 3554595323351 10843246234173440 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 342798 524288 40524053 41363701760 171399 262144 40524053 41363701760 (ep649 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 174763 524288 1 524288 198347 262144 40524053 41363701760 34663716761 137438953472 3556721385811 10843246234173440 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 198347 262144 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 396694 524288 40524053 41363701760 198347 262144 40524053 41363701760 (ep652 rfl rfl) rfl)) rfl)

noncomputable def ep654 := @ep642 29954203437 137438953472 3554595323351 10843246234173440 Bool.false 34663716761 137438953472 3556721385811 10843246234173440 Bool.true 23201675909975169302528 168814410499 274877906944 78974540989273 21686492468346880 Bool.false 1594786745236181745664 5801800381 68719476736 19758814586147 5421623117086720 EMRow19.d11 (ep643 ep653) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 74488543395 274877906944 6754171915683 21686492468346880 Bool.false 44802617055 274877906944 6740045608143 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 10 qz151 rfl)

noncomputable def ep656 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz53 76170 1000 0 1 10369908600166117 4503599627370496 200000000047337 15779000000000000000 78987593807465313189 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 10 1 10369908600166117 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz329) Bool.false 21747274560655572598784 9444732965739290427392 1000000000236685 78895000000000000000 10369908600166117 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 58495 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep184 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep657 := nat_lit 5999364887971624350563264625265298049502391108158385217322282815896050134465

noncomputable def ep658 := nat_lit 2226002666290607882234508733340559482480178694063757067781080108931935681

noncomputable def ep659 := nat_lit 15709018321323117076808741956793229223820342136814905676781952292884717694401

noncomputable def ep660 := BSN.sin_dyadic_bound_f 1105199577 1073741824 3 2 524288 157945 ep657 ep94 ep658 ep659 ep96 ep658 449281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1105199577) qz290 0 2 ep657 ep94 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1105199577) qz291 0 2 ep659 ep96 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91953661) qz38)

noncomputable def ep661 := @Enclosure.Real.IsNear.cos_image qz168 qz434 Bool.false 91953661 524288 507 524288 Bool.false 449281 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 78987593807465313189 450359962737049600 1523400000360565929 1577900000000000000000 91953661 524288 507 524288 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 91953661 524288) (BSN.cos_reduce3 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77771506352444200189952) qz39) 226375608064910080 72057594037927936 Bool.false 449281 524288 27 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 91953661 524288 226375608064910080 72057594037927936 27 77771506352444200189952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 449281 524288 77771506352444200189952 75557863725914323419136 1105199577 1073741824 157945 157790 (ep660 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep662 := nat_lit 3333969827835920464927251240139983609493541806174242346098059822212886490561

noncomputable def ep663 := nat_lit 9997457478175180179017284702953269709515665061134599524158617306420795600321

noncomputable def ep664 := BSN.cos_dyadic_bound_f 1105199577 1073741824 3 2 524288 157945 ep662 ep57 ep658 ep663 ep60 ep658 270229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1105199577) qz284 0 2 ep662 ep57 ep658 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1105199577) qz285 0 2 ep663 ep60 ep658 rfl rfl rfl rfl) rfl rfl

noncomputable def ep665 := @Enclosure.Real.IsNear.sin_image qz168 qz434 Bool.false 91953661 524288 507 524288 Bool.true 270229 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 78987593807465313189 450359962737049600 1523400000360565929 1577900000000000000000 91953661 524288 507 524288 (ep656 rfl) rfl) (Enclosure.sfrac_false_div 91953661 524288) (BSN.sin_reduce3 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 77771506352444200189952) qz39) 226375608064910080 72057594037927936 Bool.false 270229 524288 27 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 91953661 524288 226375608064910080 72057594037927936 27 77771506352444200189952 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 270229 524288 77771506352444200189952 75557863725914323419136 1105199577 1073741824 157945 157790 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 74488543395 274877906944 6754171915683 21686492468346880 Bool.false 44802617055 274877906944 6740045608143 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz168) 165795 524288 1 524288 449281 524288 40524053 41363701760 74488543395 274877906944 6754171915683 21686492468346880 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 449281 524288 40524053 41363701760 449281 524288 40524053 41363701760 (ep661 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 165795 524288 1 524288 270229 524288 40524053 41363701760 44802617055 274877906944 6740045608143 21686492468346880 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 270229 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 270229 524288 40524053 41363701760 270229 524288 40524053 41363701760 (ep665 rfl rfl) rfl)) rfl)

noncomputable def ep667 := @ep640 74488543395 274877906944 6754171915683 21686492468346880 Bool.false 44802617055 274877906944 6740045608143 21686492468346880 Bool.true 25928096920225422770176 2947683347 8589934592 21432178226239 5421623117086720 Bool.false 4673599145659171078144 68009818579 274877906944 85775303952731 21686492468346880 (ep641 (BSN.head_sum_c_succ qz145 9 10 rfl rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 ep666) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep668 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 4697317485 17179869184 80544401713 271081155854336 Bool.true 34933087815 274877906944 1284695381963 4337298493669376 (BSN.cpow_neg_s_mk qz150 76170 1000 11 qz151 rfl)

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz56 76170 1000 0 1 10799147631728357 4503599627370496 200000000047337 15779000000000000000 82257107510874895269 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 11 1 10799147631728357 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz333) Bool.false 22647454054174387339264 9444732965739290427392 1000000000236685 78895000000000000000 10799147631728357 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 83480 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep199 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep670 := nat_lit 47635912122855278284507792244818176

noncomputable def ep671 := BSN.cos_dyadic_bound_f 467179332 1073741824 2 1 524288 157945 ep670 ep110 ep670 ep670 ep111 ep670 475440 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 467179332) qz284 0 1 ep670 ep110 ep670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 467179332) qz285 0 1 ep670 ep111 ep670 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23939969) qz519)

noncomputable def ep672 := @Enclosure.Real.IsNear.cos_image qz169 qz435 Bool.false 23939969 131072 507 524288 Bool.false 475440 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 82257107510874895269 450359962737049600 1523400000360565929 1577900000000000000000 23939969 131072 507 524288 (ep669 rfl) rfl) (Enclosure.sfrac_false_div 23939969 131072) (BSN.cos_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8218705732227519479808) qz289) 226375608064910080 72057594037927936 Bool.false 475440 524288 29 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 23939969 131072 226375608064910080 72057594037927936 29 8218705732227519479808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 475440 524288 8218705732227519479808 18889465931478580854784 467179332 1073741824 157945 157790 (ep671 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep673 := BSN.sin_dyadic_bound_f 467179332 1073741824 2 1 524288 157945 ep670 ep64 ep670 ep670 ep65 ep670 220985 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 467179332) qz290 0 1 ep670 ep64 ep670 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 467179332) qz291 0 1 ep670 ep65 ep670 rfl rfl rfl rfl) rfl rfl

noncomputable def ep674 := @Enclosure.Real.IsNear.sin_image qz169 qz435 Bool.false 23939969 131072 507 524288 Bool.false 220985 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 82257107510874895269 450359962737049600 1523400000360565929 1577900000000000000000 23939969 131072 507 524288 (ep669 rfl) rfl) (Enclosure.sfrac_false_div 23939969 131072) (BSN.sin_reduce0 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8218705732227519479808) qz289) 226375608064910080 72057594037927936 Bool.false 220985 524288 29 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 23939969 131072 226375608064910080 72057594037927936 29 8218705732227519479808 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 220985 524288 8218705732227519479808 18889465931478580854784 467179332 1073741824 157945 157790 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 4697317485 17179869184 80544401713 271081155854336 Bool.true 34933087815 274877906944 1284695381963 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz54 (Real.cos qz169) 158079 524288 1 524288 29715 32768 40524053 41363701760 4697317485 17179869184 80544401713 271081155854336 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 475440 524288 40524053 41363701760 29715 32768 40524053 41363701760 (ep672 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 158079 524288 1 524288 220985 524288 40524053 41363701760 34933087815 274877906944 1284695381963 4337298493669376 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 220985 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 220985 524288 40524053 41363701760 220985 524288 40524053 41363701760 (ep674 rfl rfl) rfl)) rfl)

noncomputable def ep676 := @ep638 4697317485 17179869184 80544401713 271081155854336 Bool.true 34933087815 274877906944 1284695381963 4337298493669376 Bool.true 10291164343307337728 1198049209 17179869184 23043066260499 5421623117086720 Bool.false 9092062520958534025216 8269182691 68719476736 46099390431273 10843246234173440 (ep639 (BSN.head_sum_c_succ qz145 10 11 rfl rfl) (ep667 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep668 ep675) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 12 1)))

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 56427599019 274877906944 1234934136309 4337298493669376 Bool.true 55788906239 274877906944 1234867548929 4337298493669376 (BSN.cpow_neg_s_mk qz150 76170 1000 12 qz151 rfl)

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz59 76170 1000 0 1 11191020447815397 4503599627370496 200000000047337 15779000000000000000 85242002751009878949 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz337) Bool.false 23469270914176955449344 9444732965739290427392 1000000000236685 78895000000000000000 11191020447815397 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 106290 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep210 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := nat_lit 1097312860352250462332015845028028124738544410970734665980858596117708800000

noncomputable def ep680 := nat_lit 241352804224122516836975673447281086301386019186959754645313945600000000

noncomputable def ep681 := nat_lit 3291455875448303141962373583737189812043030460873830078433285160461926400000

noncomputable def ep682 := BSN.cos_dyadic_bound_f 837204480 1073741824 3 2 524288 157945 ep679 ep57 ep680 ep681 ep60 ep680 372831 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 837204480) qz284 0 2 ep679 ep57 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 837204480) qz285 0 2 ep681 ep60 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99234751) qz38)

noncomputable def ep683 := @Enclosure.Real.IsNear.cos_image qz170 qz436 Bool.false 99234751 524288 127 131072 Bool.false 372831 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 85242002751009878949 450359962737049600 1523400000360565929 1577900000000000000000 99234751 524288 127 131072 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 99234751 524288) (BSN.cos_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58913027889457447043072) qz39) 226375608064910080 72057594037927936 Bool.false 372831 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 99234751 524288 226375608064910080 72057594037927936 30 58913027889457447043072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 372831 524288 58913027889457447043072 75557863725914323419136 837204480 1073741824 157945 157790 (ep682 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep684 := nat_lit 491276708407922099851083550556160000

noncomputable def ep685 := BSN.sin_dyadic_bound_f 837204480 1073741824 2 1 524288 157945 ep684 ep64 ep684 ep684 ep65 ep684 368611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 837204480) qz290 0 1 ep684 ep64 ep684 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 837204480) qz291 0 1 ep684 ep65 ep684 rfl rfl rfl rfl) rfl rfl

noncomputable def ep686 := @Enclosure.Real.IsNear.sin_image qz170 qz436 Bool.false 99234751 524288 127 131072 Bool.false 368611 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 85242002751009878949 450359962737049600 1523400000360565929 1577900000000000000000 99234751 524288 127 131072 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 99234751 524288) (BSN.sin_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58913027889457447043072) qz39) 226375608064910080 72057594037927936 Bool.false 368611 524288 30 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 99234751 524288 226375608064910080 72057594037927936 30 58913027889457447043072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 368611 524288 58913027889457447043072 75557863725914323419136 837204480 1073741824 157945 157790 (ep685 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep687 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 56427599019 274877906944 1234934136309 4337298493669376 Bool.true 55788906239 274877906944 1234867548929 4337298493669376 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz170) 151349 524288 1 524288 372831 524288 10150737 10340925440 56427599019 274877906944 1234934136309 4337298493669376 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 372831 524288 10150737 10340925440 372831 524288 10150737 10340925440 (ep683 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 151349 524288 1 524288 368611 524288 10150737 10340925440 55788906239 274877906944 1234867548929 4337298493669376 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 368611 524288 10150737 10340925440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 368611 524288 10150737 10340925440 368611 524288 10150737 10340925440 (ep686 rfl rfl) rfl)) rfl)

noncomputable def ep688 := @ep636 56427599019 274877906944 1234934136309 4337298493669376 Bool.true 55788906239 274877906944 1234867548929 4337298493669376 Bool.false 640101510527791923200 37258811675 274877906944 98346935723541 21686492468346880 Bool.true 1560768814178212249600 22712175475 274877906944 98373118607191 21686492468346880 (ep637 (BSN.head_sum_c_succ qz145 11 12 rfl rfl) (ep676 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep677 ep687) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 13 1)))

noncomputable def ep689 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 63213796975 274877906944 5926981223711 21686492468346880 Bool.true 42615747181 274877906944 5915805431381 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 13 qz151 rfl)

noncomputable def ep690 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz62 76170 1000 0 1 11551488463034085 4503599627370496 200000000047337 15779000000000000000 17597537524586125089 90071992547409920 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 13 1 11551488463034085 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 24225227133228857425920 9444732965739290427392 1000000000236685 78895000000000000000 11551488463034085 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 127272 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep224 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep691 := nat_lit 164554138674037601722545673449790321

noncomputable def ep692 := BSN.cos_dyadic_bound_f 636908731 1073741824 2 1 524288 157945 ep691 ep110 ep691 ep691 ep111 ep691 434725 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 636908731) qz284 0 1 ep691 ep110 ep691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 636908731) qz285 0 1 ep691 ep111 ep691 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102431149) qz38)

noncomputable def ep693 := @Enclosure.Real.IsNear.cos_image qz171 qz437 Bool.false 102431149 524288 507 524288 Bool.false 434725 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 17597537524586125089 90071992547409920 1523400000360565929 1577900000000000000000 102431149 524288 507 524288 (ep690 rfl) rfl) (Enclosure.sfrac_false_div 102431149 524288) (BSN.cos_reduce0 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44818467620204700499968) qz39) 226375608064910080 72057594037927936 Bool.false 434725 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 102431149 524288 226375608064910080 72057594037927936 31 44818467620204700499968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 434725 524288 44818467620204700499968 75557863725914323419136 636908731 1073741824 157945 157790 (ep692 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep694 := BSN.sin_dyadic_bound_f 636908731 1073741824 2 1 524288 157945 ep691 ep64 ep691 ep691 ep65 ep691 293071 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 636908731) qz290 0 1 ep691 ep64 ep691 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 636908731) qz291 0 1 ep691 ep65 ep691 rfl rfl rfl rfl) rfl rfl

noncomputable def ep695 := @Enclosure.Real.IsNear.sin_image qz171 qz437 Bool.false 102431149 524288 507 524288 Bool.false 293071 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 17597537524586125089 90071992547409920 1523400000360565929 1577900000000000000000 102431149 524288 507 524288 (ep690 rfl) rfl) (Enclosure.sfrac_false_div 102431149 524288) (BSN.sin_reduce0 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44818467620204700499968) qz39) 226375608064910080 72057594037927936 Bool.false 293071 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 102431149 524288 226375608064910080 72057594037927936 31 44818467620204700499968 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 293071 524288 44818467620204700499968 75557863725914323419136 636908731 1073741824 157945 157790 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 63213796975 274877906944 5926981223711 21686492468346880 Bool.true 42615747181 274877906944 5915805431381 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz171) 145411 524288 1 524288 434725 524288 40524053 41363701760 63213796975 274877906944 5926981223711 21686492468346880 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 434725 524288 40524053 41363701760 434725 524288 40524053 41363701760 (ep693 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 145411 524288 1 524288 293071 524288 40524053 41363701760 42615747181 274877906944 5915805431381 21686492468346880 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 293071 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 293071 524288 40524053 41363701760 293071 524288 40524053 41363701760 (ep695 rfl rfl) rfl)) rfl)

noncomputable def ep697 := @ep634 63213796975 274877906944 5926981223711 21686492468346880 Bool.true 42615747181 274877906944 5915805431381 21686492468346880 Bool.false 27617700370915629465600 50236304325 137438953472 26068479236813 5421623117086720 Bool.true 17957202644680797323264 2041497583 8589934592 26072231009643 5421623117086720 (ep635 (BSN.head_sum_c_succ qz145 12 13 rfl rfl) (ep688 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep689 ep696) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 14 1)))

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 9173581749 34359738368 44770997607 169425722408960 Bool.false 1659733245 137438953472 2845617651103 10843246234173440 (BSN.cpow_neg_s_mk qz150 76170 1000 14 qz151 rfl)

noncomputable def ep699 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz65 76170 1000 0 1 11885241781671653 4503599627370496 200000000047337 15779000000000000000 90529886650992980901 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 14 1 11885241781671653 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz345) Bool.false 24925158572916270432256 9444732965739290427392 1000000000236685 78895000000000000000 11885241781671653 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 146699 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep235 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep700 := nat_lit 28994380656571484997756311386598760120180749233083543838147341223013751193600

noncomputable def ep701 := nat_lit 51845445139590399150927979239762688907392505427408649541505036690890162176

noncomputable def ep702 := nat_lit 75853723379842171490736455950894279770813802982622048429223456953250764292096

noncomputable def ep703 := BSN.sin_dyadic_bound_f 1638094024 1073741824 3 2 524288 157945 ep700 ep94 ep701 ep702 ep96 ep701 523752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1638094024) qz290 0 2 ep700 ep94 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1638094024) qz291 0 2 ep702 ep96 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52695329) qz30)

noncomputable def ep704 := @Enclosure.Real.IsNear.cos_image qz172 qz438 Bool.false 52695329 262144 127 131072 Bool.false 523752 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 90529886650992980901 450359962737049600 1523400000360565929 1577900000000000000000 52695329 262144 127 131072 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 52695329 262144) (BSN.cos_reduce3 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57635309681993054158848) qz306) 226375608064910080 72057594037927936 Bool.false 523752 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 52695329 262144 226375608064910080 72057594037927936 31 57635309681993054158848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 523752 524288 57635309681993054158848 37778931862957161709568 1638094024 1073741824 157945 157790 (ep703 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep705 := nat_lit 16131031673712865176153918761105872372948146243014150420989191806870257401856

noncomputable def ep706 := nat_lit 48289404130859414730159900324838091741029653718187633963884565347228991881216

noncomputable def ep707 := BSN.cos_dyadic_bound_f 1638094024 1073741824 3 2 524288 157945 ep705 ep57 ep701 ep706 ep60 ep701 23690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1638094024) qz284 0 2 ep705 ep57 ep701 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1638094024) qz285 0 2 ep706 ep60 ep701 rfl rfl rfl rfl) rfl rfl

noncomputable def ep708 := @Enclosure.Real.IsNear.sin_image qz172 qz438 Bool.false 52695329 262144 127 131072 Bool.true 23690 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 90529886650992980901 450359962737049600 1523400000360565929 1577900000000000000000 52695329 262144 127 131072 (ep699 rfl) rfl) (Enclosure.sfrac_false_div 52695329 262144) (BSN.sin_reduce3 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57635309681993054158848) qz306) 226375608064910080 72057594037927936 Bool.false 23690 524288 31 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 52695329 262144 226375608064910080 72057594037927936 31 57635309681993054158848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 23690 524288 57635309681993054158848 37778931862957161709568 1638094024 1073741824 157945 157790 (ep707 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep709 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 9173581749 34359738368 44770997607 169425722408960 Bool.false 1659733245 137438953472 2845617651103 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz172) 140121 524288 1 524288 65469 65536 10150737 10340925440 9173581749 34359738368 44770997607 169425722408960 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 523752 524288 10150737 10340925440 65469 65536 10150737 10340925440 (ep704 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 140121 524288 1 524288 11845 262144 10150737 10340925440 1659733245 137438953472 2845617651103 10843246234173440 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 11845 262144 10150737 10340925440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 23690 524288 10150737 10340925440 11845 262144 10150737 10340925440 (ep708 rfl rfl) rfl)) rfl)

noncomputable def ep710 := @ep632 9173581749 34359738368 44770997607 169425722408960 Bool.false 1659733245 137438953472 2845617651103 10843246234173440 Bool.false 2986913748354626224128 86930631321 137438953472 27501151160237 5421623117086720 Bool.true 266324291308419547136 31004228083 137438953472 54990079670389 10843246234173440 (ep633 (BSN.head_sum_c_succ qz145 13 14 rfl rfl) (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep698 ep709) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz268 qz423 (Real.log (Enclosure.sfrac Bool.false 15 1)))

noncomputable def ep711 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 33875374411 274877906944 5505564866411 21686492468346880 Bool.false 62367179523 274877906944 5522170054851 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 15 qz151 rfl)

noncomputable def ep712 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz68 76170 1000 0 1 12195956895733477 4503599627370496 200000000047337 15779000000000000000 92896603674801894309 450359962737049600 1523400000360565929 1577900000000000000000 qz152 (BSN.isNear_log_sfrac 15 1 12195956895733477 4503599627370496 200000000047337 15779000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz349) Bool.false 25576775395801252757504 9444732965739290427392 1000000000236685 78895000000000000000 12195956895733477 4503599627370496 200000000047337 15779000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 164785 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep250 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep713 := nat_lit 81478419350628020075439062023373056

noncomputable def ep714 := BSN.sin_dyadic_bound_f 534269828 1073741824 2 1 524288 157945 ep713 ep64 ep713 ep713 ep65 ep713 250241 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 534269828) qz290 0 1 ep713 ep64 ep713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 534269828) qz291 0 1 ep713 ep65 ep713 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13518235) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep715 := @Enclosure.Real.IsNear.cos_image qz173 qz439 Bool.false 13518235 65536 507 524288 Bool.false 250241 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 92896603674801894309 450359962737049600 1523400000360565929 1577900000000000000000 13518235 65536 507 524288 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 13518235 65536) (BSN.cos_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4699487110022446448640) qz301) 226375608064910080 72057594037927936 Bool.false 250241 524288 32 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 13518235 65536 226375608064910080 72057594037927936 32 4699487110022446448640 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 250241 524288 4699487110022446448640 9444732965739290427392 534269828 1073741824 157945 157790 (ep714 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep716 := BSN.cos_dyadic_bound_f 534269828 1073741824 2 1 524288 157945 ep713 ep110 ep713 ep713 ep111 ep713 460713 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 534269828) qz284 0 1 ep713 ep110 ep713 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 534269828) qz285 0 1 ep713 ep111 ep713 rfl rfl rfl rfl) rfl rfl

noncomputable def ep717 := @Enclosure.Real.IsNear.sin_image qz173 qz439 Bool.false 13518235 65536 507 524288 Bool.true 460713 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 92896603674801894309 450359962737049600 1523400000360565929 1577900000000000000000 13518235 65536 507 524288 (ep712 rfl) rfl) (Enclosure.sfrac_false_div 13518235 65536) (BSN.sin_reduce3 qz439 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4699487110022446448640) qz301) 226375608064910080 72057594037927936 Bool.false 460713 524288 32 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 13518235 65536 226375608064910080 72057594037927936 32 4699487110022446448640 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 460713 524288 4699487110022446448640 9444732965739290427392 534269828 1073741824 157945 157790 (ep716 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep718 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 33875374411 274877906944 5505564866411 21686492468346880 Bool.false 62367179523 274877906944 5522170054851 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz173) 135371 524288 1 524288 250241 524288 40524053 41363701760 33875374411 274877906944 5505564866411 21686492468346880 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 250241 524288 40524053 41363701760 250241 524288 40524053 41363701760 (ep715 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 135371 524288 1 524288 460713 524288 40524053 41363701760 62367179523 274877906944 5522170054851 21686492468346880 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 460713 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 460713 524288 40524053 41363701760 460713 524288 40524053 41363701760 (ep717 rfl rfl) rfl)) rfl)

noncomputable def ep719 := @ep630 33875374411 274877906944 5505564866411 21686492468346880 Bool.false 62367179523 274877906944 5522170054851 21686492468346880 Bool.false 28551105994357018198016 207736637053 274877906944 115510169507359 21686492468346880 Bool.false 49302562772042645504 358723357 274877906944 115502329395629 21686492468346880 (ep631 (BSN.head_sum_c_succ qz145 14 15 rfl rfl) (ep710 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep711 ep718) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz268 qz423 qz353)

noncomputable def ep720 := @Enclosure.Complex.IsNear.of_eq qz160 (Complex.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.true 13124532443 68719476736 1335792161739 5421623117086720 Bool.false 22171052863 137438953472 2669129663343 10843246234173440 (BSN.cpow_neg_s_mk qz150 76170 1000 16 qz151 rfl)

noncomputable def ep721 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz353 76170 1000 0 1 3121657384082679 1125899906842624 50000000015779 3944750000000000000 23777664294557765943 112589990684262400 380850000120188643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz354) Bool.false 26186360105375033720832 9444732965739290427392 1000000000315580 78895000000000000000 3121657384082679 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep265 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep722 := nat_lit 321660703385785517556908170486850625

noncomputable def ep723 := BSN.cos_dyadic_bound_f 753094545 1073741824 2 1 524288 157945 ep722 ep110 ep722 ep722 ep111 ep722 400532 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 753094545) qz284 0 1 ep722 ep110 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 753094545) qz285 0 1 ep722 ep111 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110723377) qz38)

noncomputable def ep724 := @Enclosure.Real.IsNear.cos_image qz174 qz440 Bool.false 110723377 524288 507 524288 Bool.true 400532 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 23777664294557765943 112589990684262400 380850000120188643 394475000000000000000 110723377 524288 507 524288 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 110723377 524288) (BSN.cos_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52994317396727126032384) qz39) 226375608064910080 72057594037927936 Bool.false 400532 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 110723377 524288 226375608064910080 72057594037927936 33 52994317396727126032384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 400532 524288 52994317396727126032384 75557863725914323419136 753094545 1073741824 157945 157790 (ep723 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep725 := BSN.sin_dyadic_bound_f 753094545 1073741824 2 1 524288 157945 ep722 ep64 ep722 ep722 ep65 ep722 338306 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 753094545) qz290 0 1 ep722 ep64 ep722 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 753094545) qz291 0 1 ep722 ep65 ep722 rfl rfl rfl rfl) rfl rfl

noncomputable def ep726 := @Enclosure.Real.IsNear.sin_image qz174 qz440 Bool.false 110723377 524288 507 524288 Bool.true 338306 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 23777664294557765943 112589990684262400 380850000120188643 394475000000000000000 110723377 524288 507 524288 (ep721 rfl) rfl) (Enclosure.sfrac_false_div 110723377 524288) (BSN.sin_reduce2 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52994317396727126032384) qz39) 226375608064910080 72057594037927936 Bool.false 338306 524288 33 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 110723377 524288 226375608064910080 72057594037927936 33 52994317396727126032384 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 338306 524288 52994317396727126032384 75557863725914323419136 753094545 1073741824 157945 157790 (ep725 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep727 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz69 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.true 13124532443 68719476736 1335792161739 5421623117086720 Bool.false 22171052863 137438953472 2669129663343 10843246234173440 (@Enclosure.Real.IsNear.mulLit_ft qz69 (Real.cos qz174) 131071 524288 1 524288 100133 131072 40524053 41363701760 13124532443 68719476736 1335792161739 5421623117086720 qz356 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.true 400532 524288 40524053 41363701760 100133 131072 40524053 41363701760 (ep724 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz69 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 131071 524288 1 524288 169153 262144 40524053 41363701760 22171052863 137438953472 2669129663343 10843246234173440 qz356 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 169153 262144 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 338306 524288 40524053 41363701760 169153 262144 40524053 41363701760 (ep726 rfl rfl) rfl)) rfl)

noncomputable def ep728 := @ep628 13124532443 68719476736 1335792161739 5421623117086720 Bool.false 22171052863 137438953472 2669129663343 10843246234173440 Bool.false 10667908989628046114816 155238507281 274877906944 24170667630863 4337298493669376 Bool.false 6143635168498261426176 44700829083 274877906944 24168117744463 4337298493669376 (ep629 (BSN.head_sum_c_succ qz145 15 16 rfl rfl) (ep719 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep720 ep727) rfl rfl

theorem EMRow19.d12 : Enclosure.Complex.IsNear qz159 Bool.false 155238507281 274877906944 24170667630863 4337298493669376 Bool.false 44700829083 274877906944 24168117744463 4337298493669376 := ep627 (BSN.head_sum_c_succ qz145 16 17 rfl rfl) (ep728 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow19.d13 : @Eq Nat (Nat.pow 20 1) 20 := @Eq.refl Nat 20

noncomputable def ep729 := nat_lit 5446461814444766308246478719

noncomputable def ep730 := nat_lit 10034081478143735863286169600

noncomputable def ep731 := nat_lit 259669444814413870790878348537083287

noncomputable def ep732 := nat_lit 39035217324450592174678099781222400000

noncomputable abbrev qz531 := (@HAdd.hAdd Complex Complex Complex qz537 (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz544) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz441 := qz531

noncomputable abbrev qz175 := (Complex.Stirling.logGammaStirling 1 qz441)

noncomputable abbrev qz532 := (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz544) (2 : Complex))))

noncomputable abbrev qz442 := qz532

noncomputable abbrev qz176 := qz442

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz268 (@HDiv.hDiv Real Real Real qz271 qz423 (2 : Real)) (Real.log Real.pi))

noncomputable def ep733 := Complex.re (@HMul.hMul Complex Complex Complex qz71 (Complex.exp (@HMul.hMul Complex Complex Complex qz71 Complex.I ↑(@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177))) (zetaApproximant qz145 1 20))

noncomputable def ep734 := @Enclosure.Real.IsNear.of_eq ep733 (@HSub.hSub Real Real Real qz361 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz145 1 20))))

noncomputable def ep735 := nat_lit 21785517822235326691408524581

noncomputable def ep736 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz145 1 20))) ep735

noncomputable def ep737 := nat_lit 40136325912574943453144678400

noncomputable def ep738 := nat_lit 8293266702745750608795613337957854727

noncomputable def ep739 := nat_lit 1249126954382418949589699192999116800000

noncomputable def ep740 := nat_lit 8027265182514988690628935680

noncomputable def ep741 := nat_lit 16155531315493256512493815228810457

noncomputable def ep742 := nat_lit 174880773163959533946780182153738020204515107242959175680

noncomputable def ep743 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.re (zetaApproximant qz145 1 20)) 524287 524288 18591243

noncomputable def ep744 := nat_lit 193042562045090801740228319

noncomputable def ep745 := nat_lit 30198625878072740208967680000

noncomputable def ep746 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.false 524287 524288 18591243

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14823741) qz30)

noncomputable def ep747 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz443 Bool.false 14823741 262144 229

noncomputable def ep748 := nat_lit 41363701760000000000000000

noncomputable def ep749 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) Bool.false 50933987531736565603 900719925474099200 17994025952374405864073 ep748

noncomputable def ep750 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177 18040539753087045191 180143985094819840 5975161652374405864073 ep748 571434957 13107200

noncomputable def ep751 := nat_lit 133520392275195502534328320

noncomputable def ep752 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 26938190803813007399 450359962737049600 26582696719172986825037 ep302 Bool.false 18040539753087045191 180143985094819840

noncomputable def ep753 := @Enclosure.Complex.IsNear.subLitP qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 23659480209610955599 450359962737049600 25927336718138894281037 ep302 Bool.false 18599386236055397831 180143985094819840 5450873652333042162313

noncomputable def ep754 := nat_lit 60659413033043791119967072081149952

noncomputable def ep755 := nat_lit 5077960506847839789817467603255296

noncomputable abbrev qz444 := (@HSub.hSub Complex Complex Complex qz521 qz531 qz524)

noncomputable abbrev qz445 := (Complex.log qz531)

noncomputable abbrev qz178 := (@HSub.hSub Complex Complex Complex qz358 (@HMul.hMul Complex Complex Complex qz357 qz444 qz445) qz441)

noncomputable abbrev qz179 := qz441

noncomputable def ep756 := @Enclosure.Complex.IsNear.of_eq qz175 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k)))))) Bool.true 23659480209610955599

noncomputable def ep757 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz178 qz77) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) Bool.true 23659538224542309199 450359962737049600

noncomputable def ep758 := nat_lit 203233387481276558362026180608

noncomputable def ep759 := nat_lit 39941877804765234864207167488000

noncomputable def ep760 := @ep757 1582476843437133893 6311600000000000000000 Bool.false 92998895179086413027 900719925474099200 20792500030185227 157790000000000000000 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600 Bool.true ep758 23659480209610955599 450359962737049600 25927336718138894281037 ep302 Bool.false ep759

noncomputable def ep761 := @Enclosure.Complex.IsNear.addLitP qz178 qz77 Bool.true 24073390965263358799 450359962737049600 1558400000175415143 6311600000000000000000

noncomputable def ep762 := nat_lit 3101102994167209551331328

noncomputable def ep763 := @ep761 Bool.false 92998895179086413027 900719925474099200 20792500030185227 157790000000000000000 Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 Bool.true ep762 23659538224542309199 450359962737049600 1582476843437133893 6311600000000000000000 Bool.false 92998895179086413027 92998895179086413027 900719925474099200

noncomputable abbrev qz180 := (@HMul.hMul Complex Complex Complex qz357 qz444 qz445)

noncomputable def ep764 := @Enclosure.Complex.IsNear.subLitP qz180 qz179 Bool.true 23060081049104997199 450359962737049600 1558400000175415143 6311600000000000000000 Bool.false 127302813540767481059

noncomputable def ep765 := @ep764 900719925474099200 20792500030185227 157790000000000000000 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 Bool.true 96293563861053435196000 24073390965263358799 450359962737049600 1558400000175415143 6311600000000000000000 Bool.false 371995580716345652108000 92998895179086413027 900719925474099200 20792500030185227 157790000000000000000

noncomputable abbrev qz181 := qz444

noncomputable abbrev qz182 := qz445

noncomputable def ep766 := @Enclosure.Complex.IsNear.mul qz181 qz182 Bool.true 23060081049104997199 450359962737049600 1558400000175415143 6311600000000000000000 Bool.false 127302813540767481059 900719925474099200 20792500030185227

noncomputable abbrev qz183 := (Complex.re qz444)

noncomputable abbrev qz184 := (Complex.re qz445)

noncomputable abbrev qz185 := (Complex.im qz444)

noncomputable abbrev qz186 := (Complex.im qz445)

noncomputable def ep767 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz183 qz184) (@HMul.hMul Real Real Real qz0 qz185 qz186) 114800960091125189 18014398509481984 70000000110453 12623200000000000000 6482526262845781731 112589990684262400

noncomputable def ep768 := nat_lit 103853372419882701857621649815240704

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz184 7000 4000 0 1 16400137155875027 4503599627370496 10000000015779 3155800000000000000

noncomputable def ep770 := @Enclosure.Complex.IsNear.re_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable abbrev qz446 := (Enclosure.sfrac Bool.false 152340 4000)

noncomputable abbrev qz187 := qz446

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq qz181 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz187) Bool.false 7000 4000 0 1 Bool.false 152340 4000 0

noncomputable abbrev qz447 := (Complex.log (Complex.mk qz92 qz187))

noncomputable def ep772 := @Enclosure.Complex.IsNear.of_eq qz182 qz447 Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000

noncomputable def ep773 := nat_lit 409378574406279186293566994665881280282967105773178880000000000000

noncomputable def ep774 := nat_lit 4209941226640533764950290595157096262339387021848576000000000000

noncomputable def ep775 := nat_lit 1625082651902046509034027775944390023961253539840000000000000

noncomputable def ep776 := BSN.log_dyadic_bound 6904475600 39672475600 4 3 ep773 524288 157790 ep774 ep775 184367 46576951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6904475600) (BSN.artanhQ 39672475600) 0 3 ep774 ep773 ep775 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz448 := (Real.log (Enclosure.sfrac Bool.false 23288475600 16000000))

noncomputable def ep777 := @Enclosure.Real.IsNear.mulLit_ff qz93 qz448 1 2 0 1 16400137155875027 2251799813685248 10000000015779 1577900000000000000 16400137155875027 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 23288475600 16000000 16400137155875027 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23288475600) qz377)) Bool.false 137574321746870498492416 18889465931478580854784 1000000001577900 157790000000000000000 16400137155875027 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 23288475600 16000000 10 46576951200 32768000000 184367 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep776 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep778 := BSN.arctan_dyadic_bound_f 9000 152340 1 0 524288 157790 0 1 1 0 1 1 30938 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz449 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 152340)))

noncomputable def ep779 := @Enclosure.Real.IsNear.subLit_ff_p qz94 qz449 884279719003555 562949953421312 1 2000000000000000 30938 524288 1 157790 446200699657987293184 851060294452643 562949953421312 200000000015779 31558000000000000000 qz95 (ep778 rfl) rfl rfl

noncomputable abbrev qz450 := (Complex.mk qz92 qz187)

noncomputable abbrev qz451 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152340) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep780 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (ep772 (@congrArg Complex Complex qz179 qz450 Complex.log (BSN.w_shift_mk qz150 Bool.false 76170 1000 2 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz447 Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz447) (@HMul.hMul Real Real Real qz0 qz93 qz448) Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 9000 152340 4000 23288475600 16000000 rfl rfl rfl) (ep777 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz447) qz451 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 9000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz451 (@HSub.hSub Real Real Real qz361 qz94 qz449) Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 152340 9000 rfl rfl) ep779))))

noncomputable def ep781 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz186 152340 4000 0 1 851060294452643 562949953421312 200000000015779 31558000000000000000

noncomputable def ep782 := @Enclosure.Complex.IsNear.im_isNear qz181 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable def ep783 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (ep772 (@congrArg Complex Complex qz179 qz450 Complex.log (BSN.w_shift_mk qz150 Bool.false 76170 1000 2 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz447 Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz447) (@HMul.hMul Real Real Real qz0 qz93 qz448) Bool.false 16400137155875027 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 9000 152340 4000 23288475600 16000000 rfl rfl rfl) (ep777 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz447) qz451 Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 9000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz451 (@HSub.hSub Real Real Real qz361 qz94 qz449) Bool.false 851060294452643 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 152340 9000 rfl rfl) ep779))))

noncomputable abbrev qz452 := (Enclosure.Real.IsNear.const Bool.false 152340 4000)

noncomputable abbrev qz188 := (@ep771 1 (BSN.w_sub_half_mk qz423 Bool.false 76170 1000 2 qz424 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz446 Bool.false 7000 4000 0 1 Bool.false 152340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz452))

noncomputable def ep784 := @ep767 1523400000120188643 6311600000000000000000 ep768 23060081049104997199 450359962737049600 1558400000175415143 6311600000000000000000 (@ep769 114800960091125189 18014398509481984 70000000110453 12623200000000000000 (ep770 qz188) ep780 rfl) (@ep781 6482526262845781731 112589990684262400 1523400000120188643 6311600000000000000000 (ep782 qz188) ep783 rfl) rfl

noncomputable def ep785 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz183 qz186) (@HMul.hMul Real Real Real qz0 qz185 qz184) 5957422061168501 2251799813685248 1400000000110453 126232000000000000000 124919844716300080659 900719925474099200

noncomputable def ep786 := nat_lit 286660451812708080098321076827717632

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff qz183 qz186 7000 4000 0 1 851060294452643 562949953421312 200000000015779 31558000000000000000

noncomputable def ep788 := @Enclosure.Real.IsNear.mulLit_ff qz185 qz184 152340 4000 0 1 16400137155875027 4503599627370496 10000000015779 3155800000000000000

noncomputable def ep789 := @ep785 76170000120188643 631160000000000000000 ep786 127302813540767481059 900719925474099200 20792500030185227 157790000000000000000 (@ep787 5957422061168501 2251799813685248 1400000000110453 126232000000000000000 (ep770 qz188) ep783 rfl) (@ep788 124919844716300080659 900719925474099200 76170000120188643 631160000000000000000 (ep782 qz188) ep780 rfl) rfl

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq qz179 qz450 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 (BSN.w_shift_mk qz150 Bool.false 76170 1000 2 qz151 rfl)

noncomputable abbrev qz453 := (ep790 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 152340 4000) Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 152340 4000)))

noncomputable abbrev qz189 := qz453

noncomputable def ep791 := ep765 (@ep766 157790000000000000000 (ep784 rfl) (ep789 rfl)) qz189 rfl rfl rfl rfl rfl rfl

noncomputable def ep792 := @ep763 20792500030185227 157790000000000000000 (ep791 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz98 (↑qz2) Bool.false 120447 131072 1 262144 Bool.false 0 1 0 1 (@ep342 131072 1 262144 (ep344 rfl) (ep346 rfl) rfl rfl) (@ep347 1 0 1 (ep349 rfl) (ep351 rfl) rfl rfl))

noncomputable abbrev qz454 := (@HPow.hPow Complex Int Complex qz526 qz531 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz190 := qz454

noncomputable def ep793 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz190)) Bool.false 1106547 8589934592 3 8589934592

noncomputable def ep794 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz190) Bool.false 0 1 0 1 Bool.false

noncomputable def ep795 := @ep794 0 1 0 1 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600 Bool.false 1106547 1106547 8589934592 3 8589934592 Bool.true 936507611 936507611 429496729600 2539

noncomputable def ep796 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz71 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz80 qz179 (@HSub.hSub Int Int Int qz370 qz82 (@HMul.hMul Int Int Int qz371 qz83 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep797 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101) qz190 Bool.false 1106547 8589934592 3 8589934592 Bool.true 936507611 429496729600 2539 429496729600

noncomputable abbrev qz191 := (Complex.re qz454)

noncomputable abbrev qz192 := (Complex.im qz454)

noncomputable def ep798 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz191) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz192) 1106547 8589934592 3 8589934592 0 1 0

noncomputable def ep799 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz191 1 12 0 1 3319641 2147483648 9 2147483648 1106547

noncomputable def ep800 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617 107374182400

noncomputable abbrev qz455 := (@HPow.hPow Complex Nat Complex qz527 qz531 1)

noncomputable abbrev qz193 := (@Inv.inv Complex Complex.instInv qz455)

noncomputable def ep801 := @Enclosure.Complex.IsNear.of_eq qz190 qz193 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617

noncomputable def ep802 := @Enclosure.Complex.IsNear.of_parts qz193 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617

noncomputable abbrev qz194 := (Complex.re qz455)

noncomputable abbrev qz195 := qz455

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_ff qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195)) 9000 4000 0 1 368849 536870912 1 536870912

noncomputable def ep804 := @Enclosure.Complex.IsNear.re_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_eq qz195 qz179 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0

noncomputable def ep806 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195)) Bool.false 368849 536870912 1 536870912 368849 536870912 1

noncomputable abbrev qz196 := (Complex.im qz455)

noncomputable def ep807 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196)) Bool.false 58221189 40000 0 1

noncomputable def ep808 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz194 qz194) (@HMul.hMul Real Real Real qz0 qz196 qz196) 81 16 0 1 58018689 40000

noncomputable def ep809 := @Enclosure.Real.IsNear.mulLit_ff qz194 qz194 9000 4000 0 1 9000 4000 0 1

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff qz196 qz196 152340 4000 0 1 152340 4000 0 1

noncomputable def ep811 := @Enclosure.Complex.IsNear.im_isNear qz195 Bool.false 9000 4000 0 1 Bool.false 152340 4000 0 1

noncomputable abbrev qz197 := (ep804 (@ep805 1 (BSN.pow_one_c qz441) qz453))

noncomputable abbrev qz198 := (ep811 (@ep805 1 (BSN.pow_one_c qz441) qz453))

noncomputable def ep812 := @ep808 0 1 931539024 58221189 40000 0 1 (@ep809 81 16 0 1 qz197 qz197 rfl) (@ep810 58018689 40000 0 1 qz198 qz198 rfl)

noncomputable def ep813 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195) 58221189 40000 0 1 184424 184425 268435456 (ep807 (Enclosure.Complex.normSq_eq_mul_add_mul qz195) (ep812 rfl rfl)) rfl

noncomputable def ep814 := @Enclosure.Real.IsNear.of_eq (Complex.re qz193) (@HMul.hMul Real Real Real qz0 qz194 (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195))) Bool.false 3319641 2147483648 9 2147483648 (Enclosure.Complex.inv_re_eq_mul qz195) (@ep803 3319641 2147483648 9 2147483648 qz197 (@ep806 536870912 (ep813 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep815 := @Enclosure.Real.IsNear.of_eq (Complex.im qz193) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195))) Bool.true 2809522833 107374182400 7617 107374182400 (Enclosure.Complex.inv_im_eq_mul qz195)

noncomputable def ep816 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz196) (@Inv.inv Real Real.instInv (@DFunLike.coe qz107 Complex (fun (x : Complex) => Real) qz108 Complex.normSq qz195)) 152340 4000 0 1 368849 536870912 1

noncomputable def ep817 := @ep816 536870912 2809522833 107374182400 7617 107374182400 (@Enclosure.Real.IsNear.neg qz196 Bool.false 152340 4000 0 1 qz198) (@ep806 536870912 (ep813 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep818 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz192 0 1 0 1 2809522833 107374182400 7617 107374182400 0

noncomputable def ep819 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 3319641 2147483648 9 2147483648 Bool.true 2809522833 107374182400 7617 107374182400

noncomputable abbrev qz199 := (@ep801 107374182400 (BSN.zpow_one_sub_two_mul qz441 1 1 rfl rfl) (@ep802 107374182400 ep814 (ep815 ep817)))

noncomputable def ep820 := @ep798 1 1106547 1106547 8589934592 3 8589934592 (@ep799 8589934592 3 8589934592 ep361 (ep800 qz199) rfl) (@ep818 1 0 1 ep381 (ep819 qz199) rfl) rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz191) 936507611 429496729600 2539 429496729600 0 1 0

noncomputable def ep822 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz192 1 12 0 1 2809522833 107374182400 7617 107374182400 936507611

noncomputable def ep823 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 (@Rat.cast Complex Complex.instRatCast (bernoulli qz100)) qz101)) qz191 0 1 0 1 3319641 2147483648 9 2147483648 0

noncomputable def ep824 := @ep821 1 936507611 936507611 429496729600 2539 429496729600 (@ep822 429496729600 2539 429496729600 ep361 (ep819 qz199) rfl) (@ep823 1 0 1 ep381 (ep800 qz199) rfl) rfl

noncomputable def ep825 := @ep795 429496729600 (@ep796 0 1 0 1 (BSN.stirling_sum_base qz179) qz114) (ep797 (ep820 rfl) (ep824 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep826 := @ep760 18599386236055397831 180143985094819840 5450873652333042162313 ep748 (ep792 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep793 Bool.true 936507611 429496729600 2539 429496729600 (BSN.stirling_sum_succ qz179 0 1 rfl) (ep825 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep827 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz150 2) Bool.false 16393552971010259 2251799813685248 10000000015779 1577900000000000000 Bool.false 873197629638051 281474976710656

noncomputable abbrev qz200 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz442 qz382))

noncomputable def ep828 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz150 1) qz200) Bool.false 16393552971010259 2251799813685248 10000000015779 1577900000000000000 Bool.false 873197629638051 281474976710656 200000000015779 15779000000000000000

noncomputable def ep829 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz150 1) qz200 Bool.false 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000 Bool.false

noncomputable def ep830 := nat_lit 147659998103040580094241619836928

noncomputable def ep831 := nat_lit 983133129864681714399339085824

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz442 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep832 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz150 0) qz201) Bool.false 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000

noncomputable def ep833 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz150 0) qz201 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz456 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187))

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq qz201 qz456 Bool.false 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000

noncomputable def ep835 := nat_lit 404450377909545333017942743071634904783995666669178880000000000000

noncomputable def ep836 := nat_lit 4078423902544044669261707384808128600453312961048576000000000000

noncomputable def ep837 := nat_lit 1515329126926870048685187821818510608841381539840000000000000

noncomputable def ep838 := BSN.log_dyadic_bound 6824475600 39592475600 4 3 ep835 524288 157790 ep836 ep837 182563 46416951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6824475600) (BSN.artanhQ 39592475600) 0 3 ep836 ep835 ep837 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep839 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 23208475600 16000000)) 1 2 0 1 16392389034873043 2251799813685248 10000000015779 1577900000000000000 16392389034873043 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 23208475600 16000000 16392389034873043 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23208475600) qz377)) Bool.false 137509325797048287494144 18889465931478580854784 1000000001577900 157790000000000000000 16392389034873043 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 23208475600 16000000 10 46416951200 32768000000 182563 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep838 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep840 := BSN.arctan_dyadic_bound_f 1000 152340 1 0 524288 157790 0 1 1 0 1 1 3441 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz457 := (@Nat.cast Real Real.instNatCast 152340)

noncomputable def ep841 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz457)) 884279719003555 562949953421312 1 2000000000000000 3441 524288 1 157790 461680134527213109248 880584973387171 562949953421312 200000000015779 31558000000000000000 qz95 (ep840 rfl) rfl rfl

noncomputable abbrev qz202 := (@HAdd.hAdd Complex Complex Complex qz274 qz442 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz458 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz187)

noncomputable def ep842 := @ep833 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000 Bool.false 16392389034873043 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 880584973387171 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz150 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz150) qz114) (ep834 (@congrArg Complex Complex qz202 qz458 Complex.log (BSN.w_shift_mk qz150 Bool.false 76170 1000 0 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz456 Bool.false 16392389034873043 4503599627370496 10000000015779 3155800000000000000 Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz456) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 23208475600 16000000))) Bool.false 16392389034873043 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 1000 152340 4000 23208475600 16000000 rfl rfl rfl) (ep839 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz456) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz457 qz388)) Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 1000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz457 qz388)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz388 qz457))) Bool.false 880584973387171 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 152340 1000 rfl rfl) ep841)))) rfl rfl

noncomputable abbrev qz459 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187))

noncomputable def ep843 := @Enclosure.Complex.IsNear.of_eq qz200 qz459 Bool.false 16394716907147475 4503599627370496 10000000015779 3155800000000000000 Bool.false 865810285888931 562949953421312 200000000015779 31558000000000000000

noncomputable def ep844 := nat_lit 405923617089258979443600241174590665952629818400378880000000000000

noncomputable def ep845 := nat_lit 4117565499606241841277565156322818940650879179288576000000000000

noncomputable def ep846 := nat_lit 1547585798464563283482169137918359082337343139840000000000000

noncomputable def ep847 := BSN.log_dyadic_bound 6848475600 39616475600 4 3 ep844 524288 157790 ep845 ep846 183105 46464951200 32768000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6848475600) (BSN.artanhQ 39616475600) 0 3 ep845 ep844 ep846 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.mulLit_ff qz93 (Real.log (Enclosure.sfrac Bool.false 23232475600 16000000)) 1 2 0 1 16394716907147475 2251799813685248 10000000015779 1577900000000000000 16394716907147475 4503599627370496 10000000015779 3155800000000000000 qz376 (BSN.isNear_log_sfrac 23232475600 16000000 16394716907147475 2251799813685248 10000000015779 1577900000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23232475600) qz377)) Bool.false 137528853405032565964800 18889465931478580854784 1000000001577900 157790000000000000000 16394716907147475 2251799813685248 10000000015779 1577900000000000000 (BSN.log_rat_reduce_isNear 23232475600 16000000 10 46464951200 32768000000 183105 524288 24973259072661432 36028797018963968 157790 1000000000000000 rfl rfl rfl rfl (ep847 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep849 := BSN.arctan_dyadic_bound_f 5000 152340 1 0 524288 157790 0 1 1 0 1 1 17201 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 152340) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 152340) 0 0 rfl) rfl rfl rfl

noncomputable def ep850 := @Enclosure.Real.IsNear.subLit_ff_p qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz457)) 884279719003555 562949953421312 1 2000000000000000 17201 524288 1 157790 453933943168135856128 865810285888931 562949953421312 200000000015779 31558000000000000000 qz95 (ep849 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz274 qz442 qz382)

noncomputable abbrev qz460 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz187)

noncomputable def ep851 := @ep829 16394716907147475 4503599627370496 10000000015779 3155800000000000000 Bool.false 865810285888931 562949953421312 200000000015779 31558000000000000000 Bool.false ep830 16393552971010259 2251799813685248 10000000015779 1577900000000000000 Bool.false ep831 873197629638051 281474976710656 200000000015779 15779000000000000000 (ep832 (BSN.log_sum_c_succ qz150 0 1 rfl) (ep842 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep843 (@congrArg Complex Complex qz203 qz460 Complex.log (BSN.w_shift_mk qz150 Bool.false 76170 1000 1 qz151 rfl)) (@Enclosure.Complex.IsNear.of_parts qz459 Bool.false 16394716907147475 4503599627370496 10000000015779 3155800000000000000 Bool.false 865810285888931 562949953421312 200000000015779 31558000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz459) (@HMul.hMul Real Real Real qz0 qz93 (Real.log (Enclosure.sfrac Bool.false 23232475600 16000000))) Bool.false 16394716907147475 4503599627370496 10000000015779 3155800000000000000 (Enclosure.clog_re_eq 5000 152340 4000 23232475600 16000000 rfl rfl rfl) (ep848 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz459) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz457 qz392)) Bool.false 865810285888931 562949953421312 200000000015779 31558000000000000000 (Enclosure.clog_im_eq 5000 152340 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz457 qz392)) (@HSub.hSub Real Real Real qz361 qz94 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz392 qz457))) Bool.false 865810285888931 562949953421312 200000000015779 31558000000000000000 (BSN.arctan_recip 152340 5000 rfl rfl) ep850)))) rfl rfl

noncomputable def ep852 := @ep753 ep748 Bool.false 16393552971010259 2251799813685248 10000000015779 1577900000000000000 Bool.false 873197629638051 281474976710656 200000000015779 15779000000000000000 Bool.true ep754 26938190803813007399 450359962737049600 26582696719172986825037 ep302 Bool.false ep755 18040539753087045191 180143985094819840 5975161652374405864073 ep748 (@ep756 450359962737049600 25927336718138894281037 ep302 Bool.false 18599386236055397831 180143985094819840 5450873652333042162313 ep748 (BSN.logGammaStirling_unfold 1 qz179) (ep826 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep827 200000000015779 15779000000000000000 (BSN.log_sum_c_eq qz150 2) (ep828 (BSN.log_sum_c_succ qz150 1 2 rfl) (ep851 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz204 := (@HDiv.hDiv Real Real Real qz271 qz423 (2 : Real))

noncomputable def ep853 := @Enclosure.Real.IsNear.mulLit_ff qz204 (Real.log Real.pi) 76170 2000 0 1 75021 65536 1 131072 571434957 13107200 7617 26214400 (@Enclosure.Real.IsNear.of_eq qz204 (Enclosure.sfrac Bool.false 76170 2000) Bool.false 76170 2000 0 1 (BSN.t_half_eq qz150 Bool.false 76170 1000 qz151) (Enclosure.Real.IsNear.const Bool.false 76170 2000)) EMRow19.d5 rfl

noncomputable def ep854 := @ep750 7617 26214400 ep751 50933987531736565603 900719925474099200 17994025952374405864073 ep748 (@ep752 5975161652374405864073 ep748 (ep852 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep853 rfl rfl

noncomputable def ep855 := nat_lit 32545203444316372922907570641384943032050113043371499677817907164593798734080

noncomputable def ep856 := nat_lit 65293073331563102297057780531986707634822512428156002774573556139788820736

noncomputable def ep857 := nat_lit 85131724997339398346753162892289729462055821522041675151697590149709814784256

noncomputable def ep858 := BSN.sin_dyadic_bound_f 1686003178 1073741824 3 2 524288 157945 ep855 ep94 ep856 ep857 ep96 ep856 524287 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1686003178) qz290 0 2 ep855 ep94 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1686003178) qz291 0 2 ep857 ep96 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable def ep859 := @ep747 524288 Bool.false 524287 524288 1 78895 (@ep749 14823741 262144 229 524288 ep854 rfl) (Enclosure.sfrac_false_div 14823741 262144) (BSN.cos_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59320963182903219453952) qz306) 226375608064910080 72057594037927936 Bool.false 524287 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 14823741 262144 226375608064910080 72057594037927936 8 59320963182903219453952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 524287 524288 59320963182903219453952 37778931862957161709568 1686003178 1073741824 157945 157790 (ep858 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep860 := nat_lit 193045237186240846998626449

noncomputable abbrev qz461 := (@HPow.hPow Complex Complex Complex qz514 (@Nat.cast Complex Complex.instNatCast 20) qz529)

noncomputable abbrev qz205 := qz461

noncomputable abbrev qz462 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz366 qz462 (@HSub.hSub Complex Complex Complex qz358 qz416 (1 : Complex))) qz365)

noncomputable abbrev qz207 := qz462

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz145 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz146) (@HMul.hMul Complex Complex Complex qz71 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) Bool.false 41552656888756209273563 76553966355466734796800 ep744

noncomputable def ep862 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz146) (@HMul.hMul Complex Complex Complex qz71 qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) Bool.false 79321238485 137438953472 33994038496617 5421623117086720

noncomputable def ep863 := nat_lit 3694606926483683249380319

noncomputable def ep864 := nat_lit 3707600852315743108778449

noncomputable def ep865 := nat_lit 5710953676771744926300320076660736

noncomputable def ep866 := nat_lit 296900172904291388774309781569536

noncomputable def ep867 := @ep862 Bool.false 33340950115 274877906944 135968743773593 21686492468346880 Bool.true 2629543781825473910437 76553966355466734796800 ep863 ep745 Bool.true 8205394989849859025081 76553966355466734796800 ep864 ep745 Bool.false ep865 41552656888756209273563 76553966355466734796800 ep744 ep745 Bool.false ep866 1080116536847677302919 76553966355466734796800

noncomputable def ep868 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz120 (@Nat.cast Complex Complex.instNatCast n) qz146) (BSN.headSumC qz145 20) Bool.false 79321238485 137438953472 33994038496617 5421623117086720 Bool.false 33340950115 274877906944 135968743773593

noncomputable abbrev qz208 := (@HPow.hPow Complex Complex Complex qz275 qz395 qz417)

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 19) qz208) Bool.false 79321238485 137438953472 33994038496617 5421623117086720 Bool.false 33340950115 274877906944 135968743773593 21686492468346880

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 19) qz208 Bool.false 22504382419 34359738368 65543944392359 10843246234173440 Bool.true 3247536481 34359738368 65527799950719 10843246234173440 Bool.true

noncomputable abbrev qz209 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 18) qz417)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz145 18) qz209) Bool.false 22504382419 34359738368 65543944392359 10843246234173440 Bool.true 3247536481 34359738368 65527799950719 10843246234173440

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz145 18) qz209 Bool.false 117229919227 274877906944 25207998242173 4337298493669376 Bool.true 10070875623 274877906944 25207528469785 4337298493669376 Bool.false

noncomputable abbrev qz210 := (@HPow.hPow Complex Complex Complex qz275 (@Nat.cast Complex Complex.instNatCast 17) qz417)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz145 18) (@HAdd.hAdd Complex Complex Complex qz4 qz159 qz210) Bool.false 117229919227 274877906944 25207998242173 4337298493669376 Bool.true 10070875623 274877906944 25207528469785 4337298493669376

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP qz159 qz210 Bool.false 155238507281 274877906944 24170667630863 4337298493669376 Bool.false 44700829083 274877906944 24168117744463 4337298493669376 Bool.true

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz268 qz423 qz398)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.true 19004294027 137438953472 518665305655 2168649246834688 Bool.true 27385852353 137438953472 519705362661 2168649246834688 (BSN.cpow_neg_s_mk qz150 76170 1000 17 qz151 rfl)

noncomputable def ep876 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz398 76170 1000 0 1 3189913004350711 1125899906842624 50000000015779 3944750000000000000 24297567354139365687 112589990684262400 380850000120188643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz399) Bool.false 26758929747600409100288 9444732965739290427392 1000000000315580 78895000000000000000 3189913004350711 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 15892 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep439 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep877 := nat_lit 180034512186463519433114692227394576

noncomputable def ep878 := BSN.sin_dyadic_bound_f 651386782 1073741824 2 1 524288 157945 ep877 ep64 ep877 ep877 ep65 ep877 298906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 651386782) qz290 0 1 ep877 ep64 ep877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 651386782) qz291 0 1 ep877 ep65 ep877 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28286091) qz519)

noncomputable def ep879 := @Enclosure.Real.IsNear.cos_image qz211 qz463 Bool.false 28286091 131072 127 131072 Bool.true 298906 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 24297567354139365687 112589990684262400 380850000120188643 394475000000000000000 28286091 131072 127 131072 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 28286091 131072) (BSN.cos_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11459317456880619487232) qz289) 226375608064910080 72057594037927936 Bool.false 298906 524288 34 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 28286091 131072 226375608064910080 72057594037927936 34 11459317456880619487232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 298906 524288 11459317456880619487232 18889465931478580854784 651386782 1073741824 157945 157790 (ep878 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep880 := BSN.cos_dyadic_bound_f 651386782 1073741824 2 1 524288 157945 ep877 ep110 ep877 ep877 ep111 ep877 430734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 651386782) qz284 0 1 ep877 ep110 ep877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 651386782) qz285 0 1 ep877 ep111 ep877 rfl rfl rfl rfl) rfl rfl

noncomputable def ep881 := @Enclosure.Real.IsNear.sin_image qz211 qz463 Bool.false 28286091 131072 127 131072 Bool.false 430734 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 24297567354139365687 112589990684262400 380850000120188643 394475000000000000000 28286091 131072 127 131072 (ep876 rfl) rfl) (Enclosure.sfrac_false_div 28286091 131072) (BSN.sin_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11459317456880619487232) qz289) 226375608064910080 72057594037927936 Bool.false 430734 524288 34 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 28286091 131072 226375608064910080 72057594037927936 34 11459317456880619487232 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 430734 524288 11459317456880619487232 18889465931478580854784 651386782 1073741824 157945 157790 (ep880 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep882 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.true 19004294027 137438953472 518665305655 2168649246834688 Bool.true 27385852353 137438953472 519705362661 2168649246834688 (@Enclosure.Real.IsNear.mulLit_ft qz129 (Real.cos qz211) 127159 524288 1 524288 149453 262144 10150737 10340925440 19004294027 137438953472 518665305655 2168649246834688 qz401 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.true 298906 524288 10150737 10340925440 149453 262144 10150737 10340925440 (ep879 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz129 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 127159 524288 1 524288 215367 262144 10150737 10340925440 27385852353 137438953472 519705362661 2168649246834688 qz401 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 215367 262144 10150737 10340925440 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 430734 524288 10150737 10340925440 215367 262144 10150737 10340925440 (ep881 rfl rfl) rfl)) rfl)

noncomputable def ep883 := @ep874 19004294027 137438953472 518665305655 2168649246834688 Bool.true 27385852353 137438953472 519705362661 2168649246834688 Bool.false 16111957414165971206144 117229919227 274877906944 25207998242173 4337298493669376 Bool.true 1384130606171796013056 10070875623 274877906944 25207528469785 4337298493669376 EMRow19.d12 (ep875 ep882) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz268 qz423 qz403)

noncomputable def ep884 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 62805140125 274877906944 5047897573853 21686492468346880 Bool.true 15909416225 274877906944 5017957552513 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 18 qz151 rfl)

noncomputable def ep885 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz403 76170 1000 0 1 3254268794313975 1125899906842624 50000000015779 3944750000000000000 991510616251581903 4503599627370496 380850000120188643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz404) Bool.false 27298785242132565196800 9444732965739290427392 1000000000315580 78895000000000000000 3254268794313975 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 30876 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep454 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep886 := nat_lit 5035947934806690079297806821272336

noncomputable def ep887 := BSN.cos_dyadic_bound_f 266391466 1073741824 2 1 524288 157945 ep886 ep110 ep886 ep886 ep111 ep886 508235 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 266391466) qz284 0 1 ep886 ep110 ep886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 266391466) qz285 0 1 ep886 ep111 ep886 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115427027) qz38)

noncomputable def ep888 := @Enclosure.Real.IsNear.cos_image qz212 qz464 Bool.false 115427027 524288 507 524288 Bool.false 508235 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 991510616251581903 4503599627370496 380850000120188643 394475000000000000000 115427027 524288 507 524288 (ep885 rfl) rfl) (Enclosure.sfrac_false_div 115427027 524288) (BSN.cos_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18745632982913142226944) qz39) 226375608064910080 72057594037927936 Bool.false 508235 524288 35 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 115427027 524288 226375608064910080 72057594037927936 35 18745632982913142226944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 508235 524288 18745632982913142226944 75557863725914323419136 266391466 1073741824 157945 157790 (ep887 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep889 := BSN.sin_dyadic_bound_f 266391466 1073741824 2 1 524288 157945 ep886 ep64 ep886 ep886 ep65 ep886 128743 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 266391466) qz290 0 1 ep886 ep64 ep886 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 266391466) qz291 0 1 ep886 ep65 ep886 rfl rfl rfl rfl) rfl rfl

noncomputable def ep890 := @Enclosure.Real.IsNear.sin_image qz212 qz464 Bool.false 115427027 524288 507 524288 Bool.false 128743 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 991510616251581903 4503599627370496 380850000120188643 394475000000000000000 115427027 524288 507 524288 (ep885 rfl) rfl) (Enclosure.sfrac_false_div 115427027 524288) (BSN.sin_reduce0 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18745632982913142226944) qz39) 226375608064910080 72057594037927936 Bool.false 128743 524288 35 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q0 115427027 524288 226375608064910080 72057594037927936 35 18745632982913142226944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 128743 524288 18745632982913142226944 75557863725914323419136 266391466 1073741824 157945 157790 (ep889 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep891 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz131 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 62805140125 274877906944 5047897573853 21686492468346880 Bool.true 15909416225 274877906944 5017957552513 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ff qz131 (Real.cos qz212) 123575 524288 1 524288 508235 524288 40524053 41363701760 62805140125 274877906944 5047897573853 21686492468346880 qz406 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 508235 524288 40524053 41363701760 508235 524288 40524053 41363701760 (ep888 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz131 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 123575 524288 1 524288 128743 524288 40524053 41363701760 15909416225 274877906944 5017957552513 21686492468346880 qz406 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 128743 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 128743 524288 40524053 41363701760 128743 524288 40524053 41363701760 (ep890 rfl rfl) rfl)) rfl)

noncomputable def ep892 := @ep872 62805140125 274877906944 5047897573853 21686492468346880 Bool.true 15909416225 274877906944 5017957552513 21686492468346880 Bool.false 49487660291216572940288 22504382419 34359738368 65543944392359 10843246234173440 Bool.true 7141408244972505792512 3247536481 34359738368 65527799950719 10843246234173440 (ep873 (BSN.head_sum_c_succ qz145 17 18 rfl rfl) (ep883 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep884 ep891) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz268 qz423 qz411)

noncomputable def ep893 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 10696291191 137438953472 15768597425 69956427317248 Bool.false 59321241963 274877906944 31697702401 139912854634496 (BSN.cpow_neg_s_mk qz150 76170 1000 19 qz151 rfl)

noncomputable def ep894 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz138 76170 1000 0 1 3315141365800183 1125899906842624 50000000015779 3944750000000000000 25251431783299993911 112589990684262400 380850000120188643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 19 1 3315141365800183 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false 27809421382282341515264 9444732965739290427392 1000000000315580 78895000000000000000 3315141365800183 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 45049 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep895 := nat_lit 6686399791894222901199223856036496166549601798550727193399698201300172800000

noncomputable def ep896 := nat_lit 8941386335349207062010101278024665478339503057985940628169562521600000000

noncomputable def ep897 := nat_lit 20041316603011970289473651365553439168692126389536209698942755478857318400000

noncomputable def ep898 := BSN.cos_dyadic_bound_f 1314999560 1073741824 3 2 524288 157945 ep895 ep57 ep896 ep897 ep60 ep896 177858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1314999560) qz284 0 2 ep895 ep57 ep896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1314999560) qz285 0 2 ep897 ep60 ep896 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58793071) qz30)

noncomputable def ep899 := @Enclosure.Real.IsNear.cos_image qz213 qz465 Bool.false 58793071 262144 507 524288 Bool.true 177858 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 25251431783299993911 112589990684262400 380850000120188643 394475000000000000000 58793071 262144 507 524288 (ep894 rfl) rfl) (Enclosure.sfrac_false_div 58793071 262144) (BSN.cos_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46267433841521770627072) qz306) 226375608064910080 72057594037927936 Bool.false 177858 524288 35 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 58793071 262144 226375608064910080 72057594037927936 35 46267433841521770627072 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 177858 524288 46267433841521770627072 37778931862957161709568 1314999560 1073741824 157945 157790 (ep898 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep900 := nat_lit 12028366516341321856508994859843273367406611634944920195616921112323031040000

noncomputable def ep901 := nat_lit 31488388155398610907994589230853676027671433181809480417979661716763443200000

noncomputable def ep902 := BSN.sin_dyadic_bound_f 1314999560 1073741824 3 2 524288 157945 ep900 ep94 ep896 ep901 ep96 ep896 493197 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1314999560) qz290 0 2 ep900 ep94 ep896 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1314999560) qz291 0 2 ep901 ep96 ep896 rfl rfl rfl rfl) rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.sin_image qz213 qz465 Bool.false 58793071 262144 507 524288 Bool.true 493197 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 25251431783299993911 112589990684262400 380850000120188643 394475000000000000000 58793071 262144 507 524288 (ep894 rfl) rfl) (Enclosure.sfrac_false_div 58793071 262144) (BSN.sin_reduce2 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46267433841521770627072) qz306) 226375608064910080 72057594037927936 Bool.false 493197 524288 35 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q2 58793071 262144 226375608064910080 72057594037927936 35 46267433841521770627072 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493197 524288 46267433841521770627072 37778931862957161709568 1314999560 1073741824 157945 157790 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz135 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 10696291191 137438953472 15768597425 69956427317248 Bool.false 59321241963 274877906944 31697702401 139912854634496 (@Enclosure.Real.IsNear.mulLit_ft qz135 (Real.cos qz213) 120279 524288 1 524288 88929 262144 40524053 41363701760 10696291191 137438953472 15768597425 69956427317248 qz414 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 177858 524288 40524053 41363701760 88929 262144 40524053 41363701760 (ep899 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz135 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 120279 524288 1 524288 493197 524288 40524053 41363701760 59321241963 274877906944 31697702401 139912854634496 qz414 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 493197 524288 40524053 41363701760 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 493197 524288 40524053 41363701760 493197 524288 40524053 41363701760 (ep903 rfl rfl) rfl)) rfl)

noncomputable def ep905 := @ep870 10696291191 137438953472 15768597425 69956427317248 Bool.false 59321241963 274877906944 31697702401 139912854634496 Bool.false 2725457001370332692480 79321238485 137438953472 33994038496617 5421623117086720 Bool.false 1145586322891939512320 33340950115 274877906944 135968743773593 21686492468346880 (ep871 (BSN.head_sum_c_succ qz145 18 19 rfl rfl) (ep892 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep893 ep904) rfl rfl

noncomputable def ep906 := @Enclosure.Complex.IsNear.mul qz205 (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.true 2629543781825473910437 76553966355466734796800 ep863 ep745 Bool.true

noncomputable abbrev qz214 := (Complex.re qz461)

noncomputable abbrev qz215 := (Complex.im qz461)

noncomputable def ep907 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 69732418455797942663 1531079327109334695936 66567517113173345214127

noncomputable def ep908 := nat_lit 603972517561454804179353600

noncomputable def ep909 := nat_lit 10066208626024246736322560000

noncomputable def ep910 := nat_lit 1342013374693960598694742649638576763961344

noncomputable def ep911 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 25020410935 274877906944 4776965061523 21686492468346880 13935106549

noncomputable abbrev qz466 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz530 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz216 := (Real.cos qz466)

noncomputable abbrev qz217 := (Real.sin qz466)

noncomputable abbrev qz467 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz468 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep912 := @Enclosure.Complex.IsNear.of_eq qz205 (Complex.mk (@HMul.hMul Real Real Real qz0 qz467 qz216) (@HMul.hMul Real Real Real qz0 qz467 qz468)) Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (BSN.cpow_neg_s_mk qz150 76170 1000 20 qz151 rfl)

noncomputable abbrev qz469 := (Real.sqrt (@Nat.cast Real Real.instNatCast 20))

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz18)

noncomputable def ep913 := @Enclosure.Real.IsNear.inv_image qz469 2344687 524288 1 524288 58617 58618 262144 (@Enclosure.Real.IsNear.of_eq qz469 (Real.sqrt qz470) Bool.false 2344687 524288 1 524288 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz470) Bool.false 2344687 524288 1 524288 2344687 524288 1 524288 (BSN.sqrt_enclosure 20 1 1172343 1172344 262144 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep914 := BSN.log_dyadic_bound 4 36 3 2 25194240 262144 78895 104448 768 58495 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz471 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable def ep915 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz471 76170 1000 0 1 3372891496062199 1125899906842624 50000000015779 3944750000000000000 25691314525505769783 112589990684262400 380850000120188643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 20 1 3372891496062199 1125899906842624 50000000015779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz470) Bool.false 28293864586999331028992 9444732965739290427392 1000000000315580 78895000000000000000 3372891496062199 1125899906842624 50000000015779 3944750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 58495 262144 24973259072661432 36028797018963968 78895 1000000000000000 rfl rfl rfl rfl (ep914 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep916 := nat_lit 41063814781357998357845792688200625

noncomputable def ep917 := BSN.sin_dyadic_bound_f 450157845 1073741824 2 1 524288 157945 ep916 ep64 ep916 ep916 ep65 ep916 213421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 450157845) qz290 0 1 ep916 ep64 ep916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 450157845) qz291 0 1 ep916 ep65 ep916 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz466

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119634505) qz38)

noncomputable def ep918 := @Enclosure.Real.IsNear.cos_image qz218 qz472 Bool.false 119634505 524288 127 131072 Bool.true 213421 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 25691314525505769783 112589990684262400 380850000120188643 394475000000000000000 119634505 524288 127 131072 (ep915 rfl) rfl) (Enclosure.sfrac_false_div 119634505 524288) (BSN.cos_reduce1 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31677042272261174722560) qz39) 226375608064910080 72057594037927936 Bool.false 213421 524288 36 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 119634505 524288 226375608064910080 72057594037927936 36 31677042272261174722560 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 213421 524288 31677042272261174722560 75557863725914323419136 450157845 1073741824 157945 157790 (ep917 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep919 := BSN.cos_dyadic_bound_f 450157845 1073741824 2 1 524288 157945 ep916 ep110 ep916 ep916 ep111 ep916 478883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 450157845) qz284 0 1 ep916 ep110 ep916 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 450157845) qz285 0 1 ep916 ep111 ep916 rfl rfl rfl rfl) rfl rfl

noncomputable def ep920 := @Enclosure.Real.IsNear.sin_image qz218 qz472 Bool.false 119634505 524288 127 131072 Bool.false 478883 524288 1 78895 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 25691314525505769783 112589990684262400 380850000120188643 394475000000000000000 119634505 524288 127 131072 (ep915 rfl) rfl) (Enclosure.sfrac_false_div 119634505 524288) (BSN.sin_reduce1 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31677042272261174722560) qz39) 226375608064910080 72057594037927936 Bool.false 478883 524288 36 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q1 119634505 524288 226375608064910080 72057594037927936 36 31677042272261174722560 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 478883 524288 31677042272261174722560 75557863725914323419136 450157845 1073741824 157945 157790 (ep919 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep921 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz467 qz216) (@HMul.hMul Real Real Real qz0 qz467 qz468) Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (@Enclosure.Real.IsNear.mulLit_ft qz467 qz216 117235 524288 1 524288 213421 524288 10150737 10340925440 25020410935 274877906944 4776965061523 21686492468346880 (@Enclosure.Real.IsNear.recentre' qz467 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep913 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 213421 524288 10150737 10340925440 213421 524288 10150737 10340925440 (ep918 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz467 qz468 117235 524288 1 524288 478883 524288 10150737 10340925440 56141848505 274877906944 4797908686013 21686492468346880 (@Enclosure.Real.IsNear.recentre' qz467 Bool.false 117235 524288 1 524288 117235 524288 1 524288 (ep913 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 478883 524288 10150737 10340925440 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 478883 524288 10150737 10340925440 478883 524288 10150737 10340925440 (ep920 rfl rfl) rfl)) rfl)

noncomputable def ep922 := @ep911 27850170720 0 1 69732418455797942663 1531079327109334695936 66567517113173345214127 ep908 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (ep912 ep921))

noncomputable def ep923 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 13935106549 27850170720 0 1 Bool.false

noncomputable def ep924 := @Enclosure.Complex.IsNear.addLitP qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) Bool.false 57821189 116042378 0 1 Bool.true 15234000

noncomputable def ep925 := @ep924 58021189 0 1 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1 Bool.false 27870213098 13935106549 27850170720 0 1 Bool.false 25443798871 25443798871 464169512000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz366 qz462 (@HSub.hSub Complex Complex Complex qz358 qz416 (1 : Complex)))

noncomputable def ep926 := @Enclosure.Complex.IsNear.addLitP qz219 qz98 Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1

noncomputable def ep927 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 40000000 23208475600) (Enclosure.sfrac Bool.true 6093600000 23208475600)) Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1

noncomputable def ep928 := @ep926 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 23128475600 57821189 116042378 0 1 Bool.true 6093600000 15234000 58021189 0 1 (ep927 (BSN.N_div_s_sub_one_mk qz150 76170 1000 20 qz151 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 23208475600) (Enclosure.sfrac Bool.true 6093600000 23208475600) Bool.true 40000000 23208475600 0 1 Bool.true 6093600000 23208475600 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 23208475600) (Enclosure.Real.IsNear.const Bool.true 6093600000 23208475600))) qz99 rfl

noncomputable abbrev qz220 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz396 qz462 1))

noncomputable def ep929 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220)) Bool.false 1 480 0 1

noncomputable def ep930 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220) Bool.false 0 1 0 1 Bool.false

noncomputable def ep931 := @ep930 0 1 0 1 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1 Bool.false 1 1 480 0 1 Bool.false 2539 2539 8000 0

noncomputable def ep932 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep933 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz220 Bool.false 1 480 0 1 Bool.false 2539 8000 0 1

noncomputable def ep934 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) 1 480 0 1 0 1 0

noncomputable def ep935 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 1 24 0 1 1 20 0 1 1

noncomputable def ep936 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep937 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz145 Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 (BSN.ascPochhammer_one_eval qz145)

noncomputable def ep939 := ep938 (@Enclosure.Complex.IsNear.of_eq qz145 (Complex.mk qz93 qz150) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_crit_mk qz150 Bool.false 76170 1000 qz151) (@Enclosure.Complex.IsNear.mk qz93 qz150 Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 qz376 qz152))

noncomputable def ep940 := @ep937 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 76170 1000 0 1 0 1 0

noncomputable def ep942 := @ep941 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep943 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) 2539 400 0 1 0 1 0 1 2539

noncomputable def ep944 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 76170 1000 0 1 2539 400 0

noncomputable def ep945 := @ep944 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep946 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep947 := @ep946 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep497) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep948 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 (@ep936 1 24 0 1 (ep940 rfl) (ep942 rfl) rfl rfl) (@ep943 2539 400 0 1 (ep945 rfl) (ep947 rfl) rfl rfl)

noncomputable def ep949 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 ep948

noncomputable abbrev qz221 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz396 qz462 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz279) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow19.d13 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz279 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz293))

noncomputable def ep950 := @ep935 480 0 1 ep949 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep951 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 2539 400 0 1 0 1 0 1 0

noncomputable def ep952 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 2539 400 0 1 ep948

noncomputable def ep953 := @ep951 1 0 1 ep952 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep954 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220)) 0 1 0 1 2539 8000 0

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz220) 1 24 0 1 0 1 0 1 0

noncomputable def ep956 := @ep955 1 0 1 ep949 (@Enclosure.Complex.IsNear.im_isNear qz220 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep957 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz100)) ↑qz141) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz220) 2539 400 0 1 1 20 0 1 2539

noncomputable def ep958 := @ep957 8000 0 1 ep952 (@Enclosure.Complex.IsNear.re_isNear qz220 Bool.false 1 20 0 1 Bool.false 0 1 0 1 qz221)

noncomputable def ep959 := @ep931 1 (@ep932 0 1 0 1 (BSN.bern_sum_base qz145 20) qz114) (ep933 (@ep934 1 1 1 480 0 1 (ep950 rfl) (ep953 rfl) rfl rfl) (@ep954 1 2539 2539 8000 0 1 (ep956 rfl) (ep958 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep960 := ep925 (ep928 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep929 Bool.false 2539 8000 0 1 (BSN.bern_sum_succ qz145 20 0 1 1 rfl rfl) (ep959 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 56141848505 274877906944 4797908686013 21686492468346880 25443798871

noncomputable def ep962 := @ep961 464169512000 0 1 285692380321474407571 25517988785155578265600 122077023608338662891323 ep909 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (ep912 ep921))

noncomputable def ep963 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))) Bool.false 13935106549 27850170720 0 1 Bool.false

noncomputable def ep964 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1))))))) 127322860699981810877 25517988785155578265600 121544138239185352940533

noncomputable def ep965 := nat_lit 4187703546575209451138635247762232177590272

noncomputable def ep966 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 25020410935 274877906944 4776965061523 21686492468346880 25443798871

noncomputable def ep967 := @ep966 464169512000 0 1 127322860699981810877 25517988785155578265600 121544138239185352940533 ep909 (@Enclosure.Complex.IsNear.re_isNear qz205 Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (ep912 ep921))

noncomputable def ep968 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz206 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz79 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz79 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz125 qz207 (@HSub.hSub Nat Nat Nat qz124 (@HMul.hMul Nat Nat Nat qz79 2 k) 1)))))) 56141848505 274877906944 4797908686013 21686492468346880 13935106549

noncomputable def ep969 := @ep968 27850170720 0 1 156468528154998271849 1531079327109334695936 66859368751963740999137 ep908 (@Enclosure.Complex.IsNear.im_isNear qz205 Bool.true 25020410935 274877906944 4776965061523 21686492468346880 Bool.true 56141848505 274877906944 4797908686013 21686492468346880 (ep912 ep921))

noncomputable abbrev qz473 := (ep960 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep970 := @ep906 8205394989849859025081 76553966355466734796800 ep864 ep745 (@ep907 ep908 285692380321474407571 25517988785155578265600 122077023608338662891323 ep909 ep910 2629543781825473910437 76553966355466734796800 ep863 ep745 (ep922 (@ep923 25443798871 464169512000 0 1 qz473) rfl) (ep962 (@ep963 25443798871 464169512000 0 1 qz473) rfl) rfl rfl) (@ep964 ep909 156468528154998271849 1531079327109334695936 66859368751963740999137 ep908 ep965 8205394989849859025081 76553966355466734796800 ep864 ep745 (ep967 (@ep963 25443798871 464169512000 0 1 qz473) rfl) (ep969 (@ep923 25443798871 464169512000 0 1 qz473) rfl) rfl rfl)

noncomputable def ep971 := @ep867 ep860 ep745 (@ep868 21686492468346880 (BSN.head_sum_c_eq qz145 20) (ep869 (BSN.head_sum_c_succ qz145 19 20 rfl rfl) (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep970 rfl rfl rfl

noncomputable def ep972 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz145 1 20) Bool.false 41552656888756209273563 76553966355466734796800 ep744 ep745 Bool.false 1080116536847677302919 76553966355466734796800 ep860 ep745 (@ep861 ep745 Bool.false 1080116536847677302919 76553966355466734796800 ep860 ep745 (BSN.zetaApproximant_eq_folded' qz145 1 20 rfl) (ep971 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep973 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) (Complex.im (zetaApproximant qz145 1 20)) 305 524288 18591243

noncomputable def ep974 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177)) Bool.true 305 524288 18591243

noncomputable def ep975 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) qz443 Bool.false 14823741 262144 229

noncomputable def ep976 := nat_lit 18109687723878679669302898258783629110087761696285569155576425560836460994816

noncomputable def ep977 := nat_lit 54198477024972912803314579215286913914993640064000395461180129570229805342976

noncomputable def ep978 := BSN.cos_dyadic_bound_f 1686003178 1073741824 3 2 524288 157945 ep976 ep57 ep856 ep977 ep60 ep856 305 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686003178) qz284 0 2 ep976 ep57 ep856 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686003178) qz285 0 2 ep977 ep60 ep856 rfl rfl rfl rfl) rfl rfl

noncomputable def ep979 := @ep975 524288 Bool.true 305 524288 1 78895 (@ep749 14823741 262144 229 524288 ep854 rfl) (Enclosure.sfrac_false_div 14823741 262144) (BSN.sin_reduce3 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59320963182903219453952) qz306) 226375608064910080 72057594037927936 Bool.false 305 524288 8 1000000000000000 157790 78895 (BSN.sin_reduce_arg_pos_rat_q3 14823741 262144 226375608064910080 72057594037927936 8 59320963182903219453952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 305 524288 59320963182903219453952 37778931862957161709568 1686003178 1073741824 157945 157790 (ep978 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep980 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz145 1 20) Bool.false 41552656888756209273563 76553966355466734796800 ep744 ep745 Bool.false 1080116536847677302919 76553966355466734796800 ep860 ep745 (@ep861 ep745 Bool.false 1080116536847677302919 76553966355466734796800 ep860 ep745 (BSN.zetaApproximant_eq_folded' qz145 1 20 rfl) (ep971 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow19.d14 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz150) Bool.false ep729 ep730 ep731 ep732 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz150) ep733 Bool.false ep729 ep730 ep731 ep732 (@Eq.refl Real ep733) (@ep734 Bool.false ep729 ep730 ep731 ep732 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz361 (Complex.im (@HSub.hSub Complex Complex Complex qz72 qz175 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz176 (@Nat.cast Complex Complex.instNatCast j))))) qz177) (zetaApproximant qz145 1 20)) (@ep736 ep737 ep738 ep739 65887108747708315478059 ep740 ep741 ep739 ep742 ep729 ep730 ep731 ep732 (@ep743 41363701760 41552656888756209273563 76553966355466734796800 ep744 ep745 ep735 ep737 ep738 ep739 (@ep746 41363701760 524287 524288 18591243 41363701760 (ep859 rfl rfl) rfl) ep972 rfl) (@ep973 41363701760 1080116536847677302919 76553966355466734796800 ep860 ep745 65887108747708315478059 ep740 ep741 ep739 (@ep974 41363701760 305 524288 18591243 41363701760 (ep979 rfl rfl) rfl) ep980 rfl) rfl rfl))

theorem EMRow19.d15 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow19.d16 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow19.d17 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow19.d18 : @Eq Nat (Nat.pow 19 (Nat.succ (Nat.mul 2 3))) 893871739 := @Eq.refl Nat 893871739

noncomputable abbrev qz533 := (@HAdd.hAdd Complex Complex Complex qz537 qz536 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz474 := qz533

noncomputable abbrev qz222 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz474) (@HAdd.hAdd Real Real Real qz386 (Complex.re qz273) qz294))

noncomputable abbrev qz223 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz224 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz475 := (@HPow.hPow Complex Complex Complex qz514 (@Nat.cast Complex Complex.instNatCast 19) (@HSub.hSub Complex Complex Complex qz521 qz515 qz516))

noncomputable abbrev qz225 := qz475

noncomputable def ep981 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) 4200705041 77309411328 7311481 77309411328 12325284399274379 31525197391593472 2913228629

noncomputable def ep982 := nat_lit 1085288536959471099695857664

noncomputable def ep983 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19)) 4427 294912 1 884736 948883 262144 395 65536 4200705041 77309411328

noncomputable abbrev qz226 := qz272

noncomputable abbrev qz534 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz476 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz534 qz226 2))

noncomputable def ep984 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz476 96 162 0 1 13281 524288 1 524288 4427 294912 1 884736

noncomputable def ep985 := nat_lit 781950621441006189802102638025

noncomputable def ep986 := nat_lit 19807040628566084398385987584

noncomputable def ep987 := nat_lit 26986075409044041160201671

noncomputable def ep988 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz477 := (@HPow.hPow Real Nat Real qz534 qz226 1)

noncomputable def ep989 := @Enclosure.Real.IsNear.mulLit_ff qz477 qz226 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep985 ep986 ep987 ep988

noncomputable def ep990 := ep989 (@Enclosure.Real.IsNear.of_eq qz477 qz226 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz226) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270)) (@Enclosure.Real.IsNear.of_eq qz226 qz269 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz270) rfl

noncomputable abbrev qz478 := (@HPow.hPow Real Nat Real qz534 qz226 2)

noncomputable def ep991 := @Enclosure.Real.IsNear.inv_image qz478 ep985 ep986 ep987 ep988 6640 6641 262144 (@Enclosure.Real.IsNear.of_eq qz478 (@HMul.hMul Real Real Real qz0 qz477 qz226) Bool.false ep985 ep986 ep987 ep988 (BSN.pow_succ_r qz226 1 2 rfl) ep990) rfl rfl rfl

noncomputable def ep992 := ep984 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz476 Bool.false 13281 524288 1 524288 13281 524288 1 524288 (ep991 rfl rfl rfl) rfl)

noncomputable def ep993 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))))) Bool.false 948883 262144 395 65536

noncomputable def ep994 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))))) Bool.false 1897766 524288 3160 524288

noncomputable def ep995 := nat_lit 9921834378459425125098862969993145548513

noncomputable def ep996 := nat_lit 757260736344741425960618137959268352000

noncomputable def ep997 := nat_lit 80280886770717379686247548782536161762827743300554156223

noncomputable def ep998 := nat_lit 1840202019349504291992643285358380291004185454586101760000

noncomputable def ep999 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19)))) ep995 ep996 ep997 ep998 947303 950463

noncomputable def ep1000 := nat_lit 10759245378633275153491989218276984535705491411329

noncomputable def ep1001 := nat_lit 821228553698429366052583217907662651958231040000

noncomputable def ep1002 := nat_lit 79568385244573269647791018128346071443671961447139842323

noncomputable def ep1003 := nat_lit 178148256637159275857648321009412290094378889

noncomputable def ep1004 := nat_lit 205307138424607341513145804476915662989557760000

noncomputable def ep1005 := nat_lit 791668362382344487173922949100100354617535392682571

noncomputable def ep1006 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19))) ep1000 ep1001 ep1002 ep998 ep1003 ep1004 ep1005

noncomputable def ep1007 := nat_lit 2044668910388338102214048094842644767782428282873446400

noncomputable def ep1008 := nat_lit 2209096180730520681171115383178536773412301500365809601758849049109960017576764528611924377600000

noncomputable def ep1009 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 19)) (Complex.re (zetaApproximant qz5 1 19)) ep293 906216615218695582515200 ep294 ep295 ep293 906216615218695582515200 ep294 ep295 ep1000

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 19)) (Complex.im (zetaApproximant qz5 1 19)) 13347219060057389942083 453108307609347791257600 ep423 ep424 13347219060057389942083 453108307609347791257600 ep423 ep424 ep1003

noncomputable def ep1011 := @ep981 15762598695796736 ep982 126344214305220067 283726776524341248 13442845184509 141863388262170624 (@ep983 7311481 77309411328 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz476) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow19.d15 EMRow19.d16 rfl) (ep992 rfl)) (ep993 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 19)) (@ep994 948883 262144 395 65536 (@ep999 262144 (@ep1006 ep1007 ep1008 ep995 ep996 ep997 ep998 (@ep1009 ep1001 ep1002 ep998 ep533 ep533 rfl) (@ep1010 ep1004 ep1005 ep1007 ep541 ep541 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz227 := (@Norm.norm Complex Complex.instNorm qz474)

noncomputable abbrev qz479 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1012 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz227 qz479) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) Bool.false 12325284399274379 31525197391593472 2913228629 15762598695796736 (BSN.zrb_shape_eq qz227 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) qz16 3)

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz227 qz479) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) 38649533 1835008 1 1835008 318898663 17179869184 285 34359738368

noncomputable def ep1014 := @Enclosure.Real.IsNear.mulLit_ff qz227 qz479 38649533 524288 1 524288 2 7 0 1 38649533 1835008

noncomputable abbrev qz480 := (Complex.re qz533)

noncomputable abbrev qz481 := (Complex.im qz533)

noncomputable abbrev qz228 := (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz268 qz480 qz480) (@HMul.hMul Real Real Real qz268 qz481 qz481))

noncomputable abbrev qz229 := qz474

noncomputable def ep1015 := @Enclosure.Real.IsNear.of_eq qz227 (Real.sqrt qz228) Bool.false 38649533 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz229)

noncomputable def ep1016 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz228) Bool.false 38649533 524288 1 524288 38649533

noncomputable def ep1017 := @Enclosure.Real.IsNear.sqrt_image qz228 217374529 40000 0 1 19324766 19324767 262144

noncomputable abbrev qz230 := (@HMul.hMul Real Real Real qz268 qz480 qz480)

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz268 qz481 qz481)

noncomputable def ep1018 := @Enclosure.Real.IsNear.addLit_ff qz230 qz231 49 4 0 1 216884529 40000 0 1

noncomputable abbrev qz232 := qz480

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ff qz232 qz232 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz482 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1020 := @Enclosure.Complex.IsNear.of_eq qz229 (Complex.mk qz482 qz16) Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 73635 1000 3 qz17)

noncomputable abbrev qz483 := (ep1020 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz20))

noncomputable def ep1021 := @ep1019 0 1 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz483)

noncomputable def ep1022 := ep1021 (@Enclosure.Complex.IsNear.re_isNear qz229 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz483)

noncomputable abbrev qz233 := qz481

noncomputable def ep1023 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 73635 1000 0 1 73635 1000 0 1 216884529 40000

noncomputable def ep1024 := @ep1023 0 1 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz483)

noncomputable def ep1025 := ep1024 (@Enclosure.Complex.IsNear.im_isNear qz229 Bool.false 7 2 0 1 Bool.false 73635 1000 0 1 qz483)

noncomputable def ep1026 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 318898663 17179869184

noncomputable def ep1027 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))))) Bool.false 1275594652 68719476736

noncomputable def ep1028 := nat_lit 1133045932112164390656829413614295432402925738031357523413

noncomputable def ep1029 := nat_lit 3288378683994531565958290873611636794225848221696000000000000

noncomputable def ep1030 := nat_lit 890051707199081701213510028370747383666463336406642458774713507866601681

noncomputable def ep1031 := nat_lit 2896865602313741451411984724292574022707453081048609137366264709120000000000000000

noncomputable def ep1032 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) ep1028 ep1029 ep1030 ep1031

noncomputable def ep1033 := nat_lit 12438296736089438715956414325173913892199503553209802449

noncomputable def ep1034 := nat_lit 11145356485150628421567622298944562744400668575476139189440201445188253

noncomputable def ep1035 := nat_lit 280151908844018737985218249822280379627681558619536930241

noncomputable def ep1036 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225))) ep1033 ep1029 ep1034 ep1031 ep1035

noncomputable def ep1037 := nat_lit 822094670998632891489572718402909198556462055424000000000000

noncomputable def ep1038 := nat_lit 219726587678482768197985601517950705230515666957791579896318326605353357

noncomputable def ep1039 := nat_lit 724216400578435362852996181073143505676863270262152284341566177280000000000000000

noncomputable def ep1040 := nat_lit 931471022786089123098446098799931087026918598472159732787702196617969555978330312679759427617404183642112000000000000

noncomputable def ep1041 := nat_lit 3526796951355356765594262857

noncomputable def ep1042 := nat_lit 1813388729421943762059264000000

noncomputable def ep1043 := nat_lit 30736153222681566620989954298351

noncomputable def ep1044 := nat_lit 31074456832548398015406821657804800000000

noncomputable def ep1045 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1041 ep1042 ep1043 ep1044 ep1041 ep1042 ep1043

noncomputable def ep1046 := nat_lit 16737739060100642457536559329

noncomputable def ep1047 := nat_lit 906694364710971881029632000000

noncomputable def ep1048 := nat_lit 127679695212574075426452804845663

noncomputable def ep1049 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1041 ep1042 ep1043 ep1044 Bool.true ep1046 ep1047 ep1048

noncomputable def ep1050 := nat_lit 15537228416274199007703410828902400000000

noncomputable def ep1051 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225 Bool.true ep1041 ep1042 ep1043 ep1044 Bool.true ep1046 ep1047 ep1048 ep1050

noncomputable def ep1052 := nat_lit 3422149845480156186405931

noncomputable def ep1053 := nat_lit 3022314549036572936765440000

noncomputable def ep1054 := nat_lit 233462653740626847268742375513

noncomputable def ep1055 := nat_lit 466116852488225970231102324867072000000

noncomputable def ep1056 := nat_lit 1473507044067263053750704257

noncomputable def ep1057 := nat_lit 45515928919919330409221387792453

noncomputable abbrev qz234 := (Complex.re qz475)

noncomputable abbrev qz235 := (Complex.im qz475)

noncomputable def ep1058 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1052 ep1053 ep1054 ep1055 ep1056 ep1042 ep1057

noncomputable def ep1059 := nat_lit 93223370497645194046220464973414400000000

noncomputable def ep1060 := nat_lit 10659089737579125343627589298332096753092710713262080000

noncomputable def ep1061 := nat_lit 24276919400428435949536579420160

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 650603587 19200000 0 1 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 ep1052

noncomputable def ep1063 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 650603587 19200000 0 1 0 1 0 1 650603587

noncomputable def ep1064 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1951810761 80000 0 1 650603587 19200000 0

noncomputable def ep1065 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow19.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz484 := (@HAdd.hAdd Complex Complex Complex qz513 qz512 qz517)

noncomputable abbrev qz236 := qz484

noncomputable def ep1066 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1

noncomputable abbrev qz237 := (Complex.re qz484)

noncomputable abbrev qz238 := (Complex.im qz484)

noncomputable def ep1067 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 216854529 16000 0 1 216884529 20000 0 1

noncomputable def ep1068 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 216854529 40000 0 1 5 2 0 1 216854529 16000

noncomputable abbrev qz485 := (@HAdd.hAdd Complex Complex Complex qz513 qz512 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz239 := qz485

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1

noncomputable abbrev qz240 := (Complex.re qz485)

noncomputable abbrev qz241 := (Complex.im qz485)

noncomputable def ep1070 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 3 4 0 1 216884529 40000 0 1

noncomputable def ep1071 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1072 := @ep1071 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable abbrev qz486 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1073 := @Enclosure.Complex.IsNear.of_eq qz239 (Complex.mk qz486 qz16) Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 73635 1000 1 qz17)

noncomputable abbrev qz487 := (ep1073 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz20))

noncomputable def ep1074 := ep1072 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz487)

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 73635 1000 0 1 73635 1000 0 1 216884529 40000

noncomputable def ep1076 := @ep1075 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep1077 := ep1076 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz487)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz239 Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 (@ep1070 867418116 216854529 40000 0 1 (ep1074 rfl) (ep1077 rfl) rfl rfl)

noncomputable def ep1079 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240) 14727 400 0 1 44181 400 0 1

noncomputable def ep1080 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 73635 1000 0 1 14727 400

noncomputable def ep1081 := @ep1080 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep1082 := ep1081 (@Enclosure.Complex.IsNear.im_isNear qz239 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz487)

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz240 73635 1000 0 1 3 2 0 1 44181 400

noncomputable def ep1084 := @ep1083 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 73635 1000 0 1 ep499)

noncomputable def ep1085 := ep1084 (@Enclosure.Complex.IsNear.re_isNear qz239 Bool.false 3 2 0 1 Bool.false 73635 1000 0 1 qz487)

noncomputable abbrev qz242 := (ep1069 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1078 (@ep1079 23563200 14727 100 0 1 (ep1082 rfl) (ep1085 rfl) rfl rfl)))

noncomputable def ep1086 := @ep1068 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz242)

noncomputable abbrev qz488 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1087 := @Enclosure.Complex.IsNear.of_eq qz236 (Complex.mk qz488 qz16) Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 73635 1000 2 qz17)

noncomputable abbrev qz489 := (ep1087 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz20))

noncomputable def ep1088 := ep1086 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz489)

noncomputable def ep1089 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 14727 100 0 1 73635 1000 0 1 216884529 20000

noncomputable def ep1090 := @ep1089 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz242)

noncomputable def ep1091 := ep1090 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz489)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz236 Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 (@ep1067 7807243044000 1951810761 80000 0 1 (ep1088 rfl) (ep1091 rfl) rfl rfl)

noncomputable def ep1093 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237) 3193616648583 8000000 0 1 14727 40 0 1

noncomputable def ep1094 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 216854529 40000 0 1 73635 1000 0 1 3193616648583 8000000

noncomputable def ep1095 := @ep1094 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz242)

noncomputable def ep1096 := ep1095 (@Enclosure.Complex.IsNear.im_isNear qz236 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz489)

noncomputable def ep1097 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz237 14727 100 0 1 5 2 0 1 14727 40

noncomputable def ep1098 := @ep1097 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 216854529 40000 0 1 Bool.false 14727 100 0 1 qz242)

noncomputable def ep1099 := ep1098 (@Enclosure.Complex.IsNear.re_isNear qz236 Bool.false 5 2 0 1 Bool.false 73635 1000 0 1 qz489)

noncomputable abbrev qz243 := (ep1066 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1092 (@ep1093 127626849943320 3190671248583 8000000 0 1 (ep1096 rfl) (ep1099 rfl) rfl rfl)))

noncomputable def ep1100 := @ep1064 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz243)

noncomputable def ep1101 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3190671248583 8000000 0 1 0 1 0

noncomputable def ep1102 := @ep1101 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz243)

noncomputable def ep1103 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1063557082861 1920000000 0 1 0 1 0 1 1063557082861

noncomputable def ep1104 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3190671248583 8000000 0 1 1063557082861 1920000000 0

noncomputable def ep1105 := @ep1104 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz243)

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1951810761 80000 0 1 0 1 0

noncomputable def ep1107 := @ep1106 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1951810761 80000 0 1 Bool.true 3190671248583 8000000 0 1 qz243)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 (@ep1063 650603587 19200000 0 1 (ep1100 rfl) (ep1102 rfl) rfl rfl) (@ep1103 1063557082861 1920000000 0 1 (ep1105 rfl) (ep1107 rfl) rfl rfl)

noncomputable def ep1109 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 ep1108

noncomputable def ep1110 := nat_lit 48553838800856871899073158840320

noncomputable def ep1111 := @Enclosure.Complex.IsNear.re_isNear qz225 Bool.true 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 Bool.false 6927258855272185 4722366482869645213696 42795943587231007673 ep1110

noncomputable abbrev qz490 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 893871739)))

noncomputable def ep1112 := @Enclosure.Complex.IsNear.of_eq qz225 (Complex.mk (@HMul.hMul Real Real Real qz0 qz490 qz136) (@HMul.hMul Real Real Real qz0 qz490 qz409)) Bool.true 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 Bool.false 6927258855272185 4722366482869645213696 42795943587231007673

noncomputable abbrev qz491 := (Real.sqrt (@Nat.cast Real Real.instNatCast 893871739))

noncomputable abbrev qz492 := (@Nat.cast Real Real.instNatCast 893871739)

noncomputable def ep1113 := @Enclosure.Real.IsNear.inv_image qz491 2054553464925653 68719476736 1 68719476736 1149243 1149244 34359738368 (@Enclosure.Real.IsNear.of_eq qz491 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz492 qz18)) Bool.false 2054553464925653 68719476736 1 68719476736 (BSN.sqrt_natCast_div_one 893871739) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz492 qz18)) Bool.false 2054553464925653 68719476736 1 68719476736 2054553464925653 68719476736 1 68719476736 (BSN.sqrt_enclosure 893871739 1 1027276732462826 1027276732462827 34359738368 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1114 := nat_lit 102816752950000000000000000

noncomputable def ep1115 := nat_lit 3645038905525644730084360192

noncomputable def ep1116 := nat_lit 1237940039285380274899124224

noncomputable def ep1117 := nat_lit 10281675295000000000000000

noncomputable def ep1118 := BSN.log_dyadic_bound 3 35 5 4 2128022244140625 34359738368 10281675295 5234577362280 688905 5904729866 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 35) 0 4 5234577362280 2128022244140625 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz138 73635 1000 0 1 3315143572331767 1125899906842624 50002056335059 514083764750000000000000 48822119389729932609 225179981368524800 736380283646413893 ep1114 qz20 (BSN.isNear_log_sfrac 19 1 3315143572331767 1125899906842624 50002056335059 514083764750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz412 Bool.false ep1115 ep1116 1000041126701180 ep1117 3315143572331767 1125899906842624 50002056335059 514083764750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 5904729866 34359738368 24973259072661432 36028797018963968 10281675295 1000000000000000 rfl rfl rfl rfl (ep1118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1120 := nat_lit 434478648966522327701389312

noncomputable def ep1121 := nat_lit 9903520314283042199192993792

noncomputable def ep1122 := nat_lit 1453297595915154613186520798785389677376775989760000

noncomputable def ep1123 := nat_lit 9415652603080021145753684134811499624153533166696051769344

noncomputable def ep1124 := nat_lit 141234789046200317186305262022172494362302997500440776540160

noncomputable def ep1125 := BSN.cos_dyadic_bound_f 6174312957320 140737488355328 2 1 68719476736 20583431988 ep1122 ep1123 ep1122 ep1122 ep1124 ep1122 68653355970 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 6174312957320) (BSN.cosEvenQ 140737488355328) 0 1 ep1122 ep1123 ep1122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 6174312957320) (BSN.cosOddQ 140737488355328) 0 1 ep1122 ep1124 ep1122 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz493 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14899328427041) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1126 := @Enclosure.Real.IsNear.cos_image qz139 qz493 Bool.false 14899328427041 68719476736 493 68719476736 Bool.true 68653355970 68719476736 1 10281675295 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 48822119389729932609 225179981368524800 736380283646413893 ep1114 14899328427041 68719476736 493 68719476736 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 14899328427041 68719476736) (BSN.cos_reduce2 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1120) (@Nat.cast Real Real.instNatCast ep1121)) 226375608064910080 72057594037927936 Bool.false 68653355970 68719476736 34 1000000000000000 20563350590 10281675295 (BSN.sin_reduce_arg_pos_rat_q2 14899328427041 68719476736 226375608064910080 72057594037927936 34 ep1120 ep1121 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 68653355970 68719476736 ep1120 ep1121 6174312957320 140737488355328 20583431988 20563350590 (ep1125 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1127 := nat_lit 47078263015400105728768420674057498120767665833480258846720

noncomputable def ep1128 := nat_lit 329547841107800740101378944718402486845373660834361811927040

noncomputable def ep1129 := BSN.sin_dyadic_bound_f 6174312957320 140737488355328 2 1 68719476736 20583431988 ep1122 ep1127 ep1122 ep1122 ep1128 ep1122 3013834255 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 6174312957320) (BSN.sinEvenQ 140737488355328) 0 1 ep1122 ep1127 ep1122 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 6174312957320) (BSN.sinOddQ 140737488355328) 0 1 ep1122 ep1128 ep1122 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1130 := @Enclosure.Real.IsNear.sin_image qz139 qz493 Bool.false 14899328427041 68719476736 493 68719476736 Bool.true 3013834255 68719476736 1 10281675295 (@Enclosure.Real.IsNear.recentre' qz139 Bool.false 48822119389729932609 225179981368524800 736380283646413893 ep1114 14899328427041 68719476736 493 68719476736 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 14899328427041 68719476736) (BSN.sin_reduce2 qz493 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1120) (@Nat.cast Real Real.instNatCast ep1121)) 226375608064910080 72057594037927936 Bool.false 3013834255 68719476736 34 1000000000000000 20563350590 10281675295 (BSN.sin_reduce_arg_pos_rat_q2 14899328427041 68719476736 226375608064910080 72057594037927936 34 ep1120 ep1121 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 3013834255 68719476736 ep1120 ep1121 6174312957320 140737488355328 20583431988 20563350590 (ep1129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz490 qz136) (@HMul.hMul Real Real Real qz0 qz490 qz409) Bool.true 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 Bool.false 6927258855272185 4722366482869645213696 42795943587231007673 ep1110 (@Enclosure.Real.IsNear.mulLit_ft qz490 qz136 2298487 68719476736 1 68719476736 34326677985 34359738368 5137585397171 706551346241858437120 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 (@Enclosure.Real.IsNear.recentre' qz490 Bool.false 2298487 68719476736 1 68719476736 2298487 68719476736 1 68719476736 (ep1113 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz136 Bool.true 68653355970 68719476736 5137585397171 706551346241858437120 34326677985 34359738368 5137585397171 706551346241858437120 (ep1126 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz490 qz409 2298487 68719476736 1 68719476736 3013834255 68719476736 5137585397171 706551346241858437120 6927258855272185 4722366482869645213696 42795943587231007673 ep1110 (@Enclosure.Real.IsNear.recentre' qz490 Bool.false 2298487 68719476736 1 68719476736 2298487 68719476736 1 68719476736 (ep1113 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz137 Bool.true 3013834255 68719476736 5137585397171 706551346241858437120 (@Enclosure.Real.IsNear.recentre' qz137 Bool.true 3013834255 68719476736 5137585397171 706551346241858437120 3013834255 68719476736 5137585397171 706551346241858437120 (ep1130 rfl rfl) rfl)) rfl)

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 1063557082861 1920000000 0 1 6927258855272185 4722366482869645213696 42795943587231007673 ep1110 ep1056

noncomputable def ep1133 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 650603587 19200000 0 1 Bool.false 1063557082861 1920000000 0 1 ep1108

noncomputable def ep1134 := @Enclosure.Complex.IsNear.im_isNear qz225 Bool.true 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 Bool.false 6927258855272185 4722366482869645213696 42795943587231007673 ep1110

noncomputable def ep1135 := nat_lit 18133887294219437620592640000

noncomputable def ep1136 := nat_lit 27843194406902140989678323051

noncomputable def ep1137 := nat_lit 932233704976451940462204649734144000000

noncomputable def ep1138 := nat_lit 5594269351564606143919945093

noncomputable def ep1139 := nat_lit 302231454903657293676544000000

noncomputable def ep1140 := nat_lit 381646925917377119229874498384439

noncomputable def ep1141 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234) 901379891863519484465519 ep1135 ep1136 ep1137 ep1138 ep1139 ep1140

noncomputable def ep1142 := nat_lit 46611685248822597023110232486707200000000

noncomputable def ep1143 := nat_lit 101173424558639810751802707791520361371393007833579520000

noncomputable def ep1144 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 650603587 19200000 0 1 6927258855272185 4722366482869645213696 42795943587231007673 ep1110 901379891863519484465519

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz234 1063557082861 1920000000 0 1 78899423101708695 2361183241434822606848 358840096189981269299 ep1061 ep1138

noncomputable abbrev qz494 := (@ep1112 ep1110 (BSN.cpow_neg_s_sub_mk qz16 73635 1000 19 3 893871739 qz17 rfl EMRow19.d18) ep1131)

noncomputable def ep1146 := ep1051 (@ep1058 ep1059 ep1060 ep1041 ep1042 ep1043 ep1044 (@ep1062 ep1053 ep1054 ep1055 ep1109 (ep1111 qz494) rfl) (@ep1132 ep1042 ep1057 ep1059 ep1133 (ep1134 qz494) rfl) rfl rfl) (@ep1141 ep1142 ep1143 ep1046 ep1047 ep1048 ep1050 (@ep1144 ep1135 ep1136 ep1137 ep1109 (ep1134 qz494) rfl) (@ep1145 ep1139 ep1140 ep1142 ep1133 (ep1111 qz494) rfl) rfl rfl)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) ep1046 ep1047 ep1048 ep1050 ep1046 ep1047 ep1048

noncomputable def ep1148 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225) Bool.true ep1041 ep1042 ep1043 ep1044 Bool.true ep1046 ep1047 ep1048

noncomputable def ep1149 := @ep1013 12325284399274379 31525197391593472 2913228629 15762598695796736 (@ep1014 1 1835008 (ep1015 (@ep1016 524288 1 524288 (ep1017 (@ep1018 869498116 217374529 40000 0 1 (ep1022 rfl) (ep1025 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1026 285 34359738368 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)) (@ep1027 570 68719476736 318898663 17179869184 285 34359738368 (@ep1032 637797041 637797611 34359738368 (@ep1036 ep1037 ep1038 ep1039 ep1040 ep1028 ep1029 ep1030 ep1031 (@ep1045 ep1044 ep1033 ep1029 ep1034 ep1031 (@ep1049 ep1050 ep1146) (@ep1049 ep1050 ep1146) rfl) (@ep1147 ep1050 ep1035 ep1037 ep1038 ep1039 (@ep1148 ep1050 ep1146) (@ep1148 ep1050 ep1146) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow19.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 126344214305220067 283726776524341248 13442845184509 141863388262170624 := ep1011 (ep1012 ep1149) rfl rfl

theorem EMRow19.d20 : @Eq Nat (Nat.pow 20 (Nat.succ (Nat.mul 2 3))) 1280000000 := @Eq.refl Nat 1280000000

noncomputable abbrev qz535 := (@HAdd.hAdd Complex Complex Complex qz537 qz543 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz495 := qz535

noncomputable abbrev qz244 := (@HDiv.hDiv Real Real Real qz271 (@Norm.norm Complex Complex.instNorm qz495) (@HAdd.hAdd Real Real Real qz386 (Complex.re qz416) qz294))

noncomputable abbrev qz496 := (@HPow.hPow Complex Complex Complex qz514 (@Nat.cast Complex Complex.instNatCast 20) (@HSub.hSub Complex Complex Complex qz521 qz529 qz516))

noncomputable abbrev qz245 := qz496

noncomputable def ep1150 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) 35004289 4294967296 5809931 57982058496 11791614475496755 31525197391593472 6811234937

noncomputable def ep1151 := nat_lit 51748115659576140143525888

noncomputable def ep1152 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20)) 4427 294912 1 884736 71163 131072 1739 262144 35004289 4294967296

noncomputable def ep1153 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 20)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 20)) (Complex.im (zetaApproximant qz145 1 20))))) Bool.false 71163 131072 1739 262144

noncomputable def ep1154 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 20)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 20)) (Complex.im (zetaApproximant qz145 1 20))))) Bool.false 284652 524288 3478 524288

noncomputable def ep1155 := nat_lit 2977860288674661033480740857820688077

noncomputable def ep1156 := nat_lit 10100637139225004137517912231510016000

noncomputable def ep1157 := nat_lit 3283772593222930586348210044536767605269323486170022981

noncomputable def ep1158 := nat_lit 455978502461902289798905154482623370876945642291200000000

noncomputable def ep1159 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 20)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 20)) (Complex.im (zetaApproximant qz145 1 20)))) ep1155 ep1156 ep1157 ep1158 140587 144065

noncomputable def ep1160 := nat_lit 1726623294514698853504345988969310680170714969

noncomputable def ep1161 := nat_lit 5860509764753932785887087764698543937290240000

noncomputable def ep1162 := nat_lit 6365773690861078630676430180105796094908866012259068911

noncomputable def ep1163 := nat_lit 911957004923804579597810308965246741753891284582400000000

noncomputable def ep1164 := nat_lit 1166651733171819840867942747052030085920561

noncomputable def ep1165 := nat_lit 201771495584782542019989908967739115629780960080977051

noncomputable def ep1166 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz145 1 20)) (Complex.re (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz145 1 20)) (Complex.im (zetaApproximant qz145 1 20))) ep1160 ep1161 ep1162 ep1163 ep1164 ep1161 ep1165

noncomputable def ep1167 := nat_lit 10125729851429318732951239547853196325225692576380553772917501794954672496525167506227200000

noncomputable def ep1168 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz145 1 20)) (Complex.re (zetaApproximant qz145 1 20)) 41552656888756209273563 76553966355466734796800 ep744 ep745 41552656888756209273563 76553966355466734796800 ep744 ep745 ep1160

noncomputable def ep1169 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz145 1 20)) (Complex.im (zetaApproximant qz145 1 20)) 1080116536847677302919 76553966355466734796800 ep860 ep745 1080116536847677302919 76553966355466734796800 ep860 ep745 ep1164

noncomputable def ep1170 := @ep1150 31525197391593472 ep1151 12048547076894003 31525197391593472 85474062258883 851180329573023744 (@ep1152 5809931 57982058496 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz476) Bool.false 4427 294912 1 884736 (BSN.theta_err_eq 1 2 96 162 EMRow19.d15 EMRow19.d16 rfl) (ep992 rfl)) (ep1153 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz145 1 20)) (@ep1154 71163 131072 1739 262144 (@ep1159 262144 (@ep1166 ep1163 ep1167 ep1155 ep1156 ep1157 ep1158 (@ep1168 ep1161 ep1162 ep1163 ep972 ep972 rfl) (@ep1169 ep1161 ep1165 ep1163 ep980 ep980 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz246 := (@Norm.norm Complex Complex.instNorm qz495)

noncomputable def ep1171 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz246 qz479) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) Bool.false 11791614475496755 31525197391593472 6811234937 31525197391593472 (BSN.zrb_shape_eq qz246 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) qz150 3)

noncomputable def ep1172 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz246 qz479) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) 39977153 1835008 1 1835008 294958835 17179869184 163 17179869184

noncomputable def ep1173 := @Enclosure.Real.IsNear.mulLit_ff qz246 qz479 39977153 524288 1 524288 2 7 0 1 39977153 1835008

noncomputable abbrev qz497 := (Complex.re qz535)

noncomputable abbrev qz498 := (Complex.im qz535)

noncomputable abbrev qz247 := (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz268 qz497 qz497) (@HMul.hMul Real Real Real qz268 qz498 qz498))

noncomputable abbrev qz248 := qz495

noncomputable def ep1174 := @Enclosure.Real.IsNear.of_eq qz246 (Real.sqrt qz247) Bool.false 39977153 524288 1 524288 (BSN.norm_eq_sqrt_mul_add qz248)

noncomputable def ep1175 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz247) Bool.false 39977153 524288 1 524288 39977153

noncomputable def ep1176 := @Enclosure.Real.IsNear.sqrt_image qz247 58141189 10000 0 1 19988576 19988577 262144

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz268 qz497 qz497)

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz268 qz498 qz498)

noncomputable def ep1177 := @Enclosure.Real.IsNear.addLit_ff qz249 qz250 49 4 0 1 58018689 10000 0 1

noncomputable abbrev qz251 := qz497

noncomputable def ep1178 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1179 := @Enclosure.Complex.IsNear.of_eq qz248 (Complex.mk qz482 qz150) Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 76170 1000 3 qz151)

noncomputable abbrev qz499 := (ep1179 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz150 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz152))

noncomputable def ep1180 := @ep1178 0 1 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz499)

noncomputable def ep1181 := ep1180 (@Enclosure.Complex.IsNear.re_isNear qz248 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz499)

noncomputable abbrev qz252 := qz498

noncomputable def ep1182 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 76170 1000 0 1 76170 1000 0 1 58018689 10000

noncomputable def ep1183 := @ep1182 0 1 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz499)

noncomputable def ep1184 := ep1183 (@Enclosure.Complex.IsNear.im_isNear qz248 Bool.false 7 2 0 1 Bool.false 76170 1000 0 1 qz499)

noncomputable def ep1185 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 294958835 17179869184

noncomputable def ep1186 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))))) Bool.false 1179835340 68719476736

noncomputable def ep1187 := nat_lit 3029109408833544487847140442009345346220945963994404997

noncomputable def ep1188 := nat_lit 10276183387482911143619658980036364981955775692800000000000

noncomputable def ep1189 := nat_lit 338537975670836646756441167962131126341407260542664715954411945141

noncomputable def ep1190 := nat_lit 1041069204651763573413948567035618578422188734414848000000000000000000000000

noncomputable def ep1191 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) ep1187 ep1188 ep1189 ep1190

noncomputable def ep1192 := nat_lit 5179777031410518460132352900936723187144908606518449

noncomputable def ep1193 := nat_lit 22300745198530623141535718272648361505980416000000000000

noncomputable def ep1194 := nat_lit 50428849644627340040064625934800094011768027760962820555526647689

noncomputable def ep1195 := nat_lit 195200475872205670015115356319178483454160387702784000000000000000000000000

noncomputable def ep1196 := nat_lit 3211340763797887907090761126288516507922860390553518489

noncomputable def ep1197 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245))) ep1192 ep1193 ep1194 ep1195 ep1196

noncomputable def ep1198 := nat_lit 51380916937414555718098294900181824909778878464000000000000

noncomputable def ep1199 := nat_lit 208752332698472499628289488929591874835933337452589018974809472399

noncomputable def ep1200 := nat_lit 3123207613955290720241845701106855735266566203244544000000000000000000000000

noncomputable def ep1201 := nat_lit 337756985524343007846235721763196988084114474695308680996871759051521426771803241888349895272693760000000000000

noncomputable def ep1202 := nat_lit 71970667854414957208243143

noncomputable def ep1203 := nat_lit 4722366482869645213696000000

noncomputable def ep1204 := nat_lit 118416620882332184627715382367

noncomputable def ep1205 := nat_lit 13971416387475024717545472000000000000

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1202 ep1203 ep1204 ep1205 ep1202 ep1203 ep1204

noncomputable def ep1207 := nat_lit 1792021418342394675266522683

noncomputable def ep1208 := nat_lit 226673591177742970257408000000

noncomputable def ep1209 := nat_lit 236242770532130906729492826343

noncomputable def ep1210 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1202 ep1203 ep1204 ep1205 Bool.true ep1207 ep1208 ep1209

noncomputable def ep1211 := nat_lit 55885665549900098870181888000000000000

noncomputable def ep1212 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245 Bool.false ep1202 ep1203 ep1204 ep1205 Bool.true ep1207 ep1208 ep1209 ep1211

noncomputable def ep1213 := nat_lit 1871207554821514879032791

noncomputable def ep1214 := nat_lit 4533471823554859405148160000

noncomputable def ep1215 := nat_lit 247132574038750247752333811

noncomputable def ep1216 := nat_lit 1117713310998001977403637760000000000

noncomputable def ep1217 := nat_lit 1774076217376496844973655207

noncomputable def ep1218 := nat_lit 113336795588871485128704000000

noncomputable def ep1219 := nat_lit 230654927413695613061622419459

noncomputable abbrev qz253 := (Complex.re qz496)

noncomputable abbrev qz254 := (Complex.im qz496)

noncomputable def ep1220 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) ep1213 ep1214 ep1215 ep1216 ep1217 ep1218 ep1219

noncomputable def ep1221 := nat_lit 27942832774950049435090944000000000000

noncomputable def ep1222 := nat_lit 7830647876169976238571300385258465451526797257605120000

noncomputable def ep1223 := nat_lit 232856939791250411959091200000

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 174043567 4800000 0 1 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 ep1213

noncomputable def ep1225 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 174043567 4800000 0 1 0 1 0 1 174043567

noncomputable def ep1226 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 522130701 20000 0 1 174043567 4800000 0

noncomputable abbrev qz500 := (@HAdd.hAdd Complex Complex Complex qz513 qz528 qz517)

noncomputable abbrev qz255 := qz500

noncomputable def ep1227 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz255) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1

noncomputable abbrev qz256 := (Complex.re qz500)

noncomputable abbrev qz257 := (Complex.im qz500)

noncomputable def ep1228 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 58011189 4000 0 1 58018689 5000 0 1

noncomputable def ep1229 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 58011189 10000 0 1 5 2 0 1 58011189 4000

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex qz513 qz528 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz258 := qz501

noncomputable def ep1230 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz71 (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz258) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1

noncomputable abbrev qz259 := (Complex.re qz501)

noncomputable abbrev qz260 := (Complex.im qz501)

noncomputable def ep1231 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 3 4 0 1 58018689 10000 0 1

noncomputable def ep1232 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1233 := @ep1232 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep1234 := @Enclosure.Complex.IsNear.of_eq qz258 (Complex.mk qz486 qz150) Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 76170 1000 1 qz151)

noncomputable abbrev qz502 := (ep1234 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz150 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz152))

noncomputable def ep1235 := ep1233 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz502)

noncomputable def ep1236 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 76170 1000 0 1 76170 1000 0 1 58018689 10000

noncomputable def ep1237 := @ep1236 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep1238 := ep1237 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz502)

noncomputable def ep1239 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) qz258 Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 (@ep1231 232044756 58011189 10000 0 1 (ep1235 rfl) (ep1238 rfl) rfl rfl)

noncomputable def ep1240 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 7617 200 0 1 22851 200 0 1

noncomputable def ep1241 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 76170 1000 0 1 7617 200

noncomputable def ep1242 := @ep1241 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep1243 := ep1242 (@Enclosure.Complex.IsNear.im_isNear qz258 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz502)

noncomputable def ep1244 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 76170 1000 0 1 3 2 0 1 22851 200

noncomputable def ep1245 := @ep1244 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 76170 1000 0 1 ep939)

noncomputable def ep1246 := ep1245 (@Enclosure.Complex.IsNear.re_isNear qz258 Bool.false 3 2 0 1 Bool.false 76170 1000 0 1 qz502)

noncomputable abbrev qz261 := (ep1230 (BSN.ascPochhammer_succ_eval_c 1 2 qz416 rfl) (ep1239 (@ep1240 6093600 7617 50 0 1 (ep1243 rfl) (ep1246 rfl) rfl rfl)))

noncomputable def ep1247 := @ep1229 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz261)

noncomputable def ep1248 := @Enclosure.Complex.IsNear.of_eq qz255 (Complex.mk qz488 qz150) Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 (BSN.s_add_nat_mk qz150 Bool.false 76170 1000 2 qz151)

noncomputable abbrev qz503 := (ep1248 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz150 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz152))

noncomputable def ep1249 := ep1247 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz503)

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 7617 50 0 1 76170 1000 0 1 58018689 5000

noncomputable def ep1251 := @ep1250 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz261)

noncomputable def ep1252 := ep1251 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz503)

noncomputable def ep1253 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) qz255 Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 (@ep1228 522130701000 522130701 20000 0 1 (ep1249 rfl) (ep1252 rfl) rfl rfl)

noncomputable def ep1254 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 441871226613 1000000 0 1 7617 20 0 1

noncomputable def ep1255 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 58011189 10000 0 1 76170 1000 0 1 441871226613 1000000

noncomputable def ep1256 := @ep1255 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz261)

noncomputable def ep1257 := ep1256 (@Enclosure.Complex.IsNear.im_isNear qz255 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz503)

noncomputable def ep1258 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 7617 50 0 1 5 2 0 1 7617 20

noncomputable def ep1259 := @ep1258 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 58011189 10000 0 1 Bool.false 7617 50 0 1 qz261)

noncomputable def ep1260 := ep1259 (@Enclosure.Complex.IsNear.re_isNear qz255 Bool.false 5 2 0 1 Bool.false 76170 1000 0 1 qz503)

noncomputable abbrev qz262 := (ep1227 (BSN.ascPochhammer_succ_eval_c 2 3 qz416 rfl) (ep1253 (@ep1254 8829807532260 441490376613 1000000 0 1 (ep1257 rfl) (ep1260 rfl) rfl rfl)))

noncomputable def ep1261 := @ep1226 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz262)

noncomputable def ep1262 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 441490376613 1000000 0 1 0 1 0

noncomputable def ep1263 := @ep1262 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz262)

noncomputable def ep1264 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) 147163458871 240000000 0 1 0 1 0 1 147163458871

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 441490376613 1000000 0 1 147163458871 240000000 0

noncomputable def ep1266 := @ep1265 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz262)

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 522130701 20000 0 1 0 1 0

noncomputable def ep1268 := @ep1267 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1065) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 522130701 20000 0 1 Bool.true 441490376613 1000000 0 1 qz262)

noncomputable def ep1269 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 (@ep1225 174043567 4800000 0 1 (ep1261 rfl) (ep1263 rfl) rfl rfl) (@ep1264 147163458871 240000000 0 1 (ep1266 rfl) (ep1268 rfl) rfl rfl)

noncomputable def ep1270 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 ep1269

noncomputable def ep1271 := nat_lit 116428469895625205979545600000

noncomputable def ep1272 := @Enclosure.Complex.IsNear.re_isNear qz245 Bool.true 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 Bool.true 60275704002432085 2361183241434822606848 1567338313350478229 ep1271

noncomputable abbrev qz504 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 1280000000)))

noncomputable def ep1273 := @Enclosure.Complex.IsNear.of_eq qz245 (Complex.mk (@HMul.hMul Real Real Real qz0 qz504 qz216) (@HMul.hMul Real Real Real qz0 qz504 qz468)) Bool.true 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 Bool.true 60275704002432085 2361183241434822606848 1567338313350478229

noncomputable abbrev qz505 := (Real.sqrt (@Nat.cast Real Real.instNatCast 1280000000))

noncomputable abbrev qz506 := (@Nat.cast Real Real.instNatCast 1280000000)

noncomputable def ep1274 := @Enclosure.Real.IsNear.inv_image qz505 2458582741758581 68719476736 1 68719476736 960383 960384 34359738368 (@Enclosure.Real.IsNear.of_eq qz505 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz506 qz18)) Bool.false 2458582741758581 68719476736 1 68719476736 (BSN.sqrt_natCast_div_one 1280000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz506 qz18)) Bool.false 2458582741758581 68719476736 1 68719476736 2458582741758581 68719476736 1 68719476736 (BSN.sqrt_enclosure 1280000000 1 1229291370879290 1229291370879291 34359738368 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1275 := nat_lit 3708536928388034760741486592

noncomputable def ep1276 := nat_lit 12623200000000000000000000

noncomputable def ep1277 := BSN.log_dyadic_bound 4 36 6 5 38005766984454635520 34359738368 12623200000 157571184526884864 990904320 7667154041 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 36) 0 5 157571184526884864 38005766984454635520 990904320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_ff qz150 qz471 76170 1000 0 1 3372894687698167 1125899906842624 312515779 3944750000000000000 25691338836196938039 112589990684262400 2380432688643 394475000000000000000 qz152 (BSN.isNear_log_sfrac 20 1 3372894687698167 1125899906842624 312515779 3944750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz470) Bool.false ep1275 ep1116 1000050492800000 ep1276 3372894687698167 1125899906842624 312515779 3944750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 7667154041 34359738368 24973259072661432 36028797018963968 12623200000 1000000000000000 rfl rfl rfl rfl (ep1277 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1279 := nat_lit 4154129540333148102992068608

noncomputable def ep1280 := nat_lit 14408751664996540782413514403909921068151046336395070838407948271702961137751557480543224879858009588018082129289825

noncomputable def ep1281 := nat_lit 55852343783389174283405539341953572568700530415884770651816705900518310611097296041679722416299367920843395176259911680

noncomputable def ep1282 := nat_lit 147503347860969887420648617983291349761589878409968886935714417143317695838936995348220961407568170047243723361

noncomputable def ep1283 := nat_lit 37736967926713450955074809055334963182972174021231569389061016221594285227365577979620739470452508096343471944016481

noncomputable def ep1284 := nat_lit 1023959636028801528529101554602482163759509724291220795283306274842835694536783760764128244298821745215462244898098380800

noncomputable def ep1285 := BSN.sin_dyadic_bound_f 59033731365803 140737488355328 3 2 68719476736 25271054688 ep1280 ep1281 ep1282 ep1283 ep1284 ep1282 27987190595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 59033731365803) (BSN.sinEvenQ 140737488355328) 0 2 ep1280 ep1281 ep1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 59033731365803) (BSN.sinOddQ 140737488355328) 0 2 ep1283 ep1284 ep1282 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz507 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15680748801389) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1286 := @Enclosure.Real.IsNear.cos_image qz218 qz507 Bool.false 15680748801389 68719476736 13 2147483648 Bool.true 27987190595 68719476736 1 12623200000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 25691338836196938039 112589990684262400 2380432688643 394475000000000000000 15680748801389 68719476736 13 2147483648 (ep1278 rfl) rfl) (Enclosure.sfrac_false_div 15680748801389 68719476736) (BSN.cos_reduce1 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1279) (@Nat.cast Real Real.instNatCast ep1121)) 226375608064910080 72057594037927936 Bool.false 27987190595 68719476736 36 1000000000000000 25246400000 12623200000 (BSN.sin_reduce_arg_pos_rat_q1 15680748801389 68719476736 226375608064910080 72057594037927936 36 ep1279 ep1121 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 27987190595 68719476736 ep1279 ep1121 59033731365803 140737488355328 25271054688 25246400000 (ep1285 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1287 := nat_lit 8004927593152683087957472734891282056239364226832110451954164912909264328837904794521946364792853134752288846815841

noncomputable def ep1288 := nat_lit 6205815975932130475933948815772619174300058935098307850201856211168701179010810671297746935144374213427043908473323520

noncomputable def ep1289 := nat_lit 24014487772762327324097576907437879586018569500739511418088623309893506351122036509575142652455744267916772053000801

noncomputable def ep1290 := nat_lit 279261718916945871417027696709767862843502652079423853259083529502591553055486480208398612081496839604216975881299558400

noncomputable def ep1291 := BSN.cos_dyadic_bound_f 59033731365803 140737488355328 3 2 68719476736 25271054688 ep1287 ep1288 ep1282 ep1289 ep1290 ep1282 62762119510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 59033731365803) (BSN.cosEvenQ 140737488355328) 0 2 ep1287 ep1288 ep1282 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 59033731365803) (BSN.cosOddQ 140737488355328) 0 2 ep1289 ep1290 ep1282 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1292 := @Enclosure.Real.IsNear.sin_image qz218 qz507 Bool.false 15680748801389 68719476736 13 2147483648 Bool.false 62762119510 68719476736 1 12623200000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 25691338836196938039 112589990684262400 2380432688643 394475000000000000000 15680748801389 68719476736 13 2147483648 (ep1278 rfl) rfl) (Enclosure.sfrac_false_div 15680748801389 68719476736) (BSN.sin_reduce1 qz507 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1279) (@Nat.cast Real Real.instNatCast ep1121)) 226375608064910080 72057594037927936 Bool.false 62762119510 68719476736 36 1000000000000000 25246400000 12623200000 (BSN.sin_reduce_arg_pos_rat_q1 15680748801389 68719476736 226375608064910080 72057594037927936 36 ep1279 ep1121 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 62762119510 68719476736 ep1279 ep1121 59033731365803 140737488355328 25271054688 25246400000 (ep1291 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1293 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz504 qz216) (@HMul.hMul Real Real Real qz0 qz504 qz468) Bool.true 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 Bool.true 60275704002432085 2361183241434822606848 1567338313350478229 ep1271 (@Enclosure.Real.IsNear.mulLit_ft qz504 qz216 1920767 68719476736 1 68719476736 27987190595 68719476736 649410483 105891076505600000 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 (@Enclosure.Real.IsNear.recentre' qz504 Bool.false 1920767 68719476736 1 68719476736 1920767 68719476736 1 68719476736 (ep1274 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 27987190595 68719476736 166249083648 27108115585433600000 27987190595 68719476736 649410483 105891076505600000 (ep1286 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz504 qz468 1920767 68719476736 1 68719476736 31381059755 34359738368 649410483 105891076505600000 60275704002432085 2361183241434822606848 1567338313350478229 ep1271 (@Enclosure.Real.IsNear.recentre' qz504 Bool.false 1920767 68719476736 1 68719476736 1920767 68719476736 1 68719476736 (ep1274 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz217 Bool.false 31381059755 34359738368 649410483 105891076505600000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 62762119510 68719476736 166249083648 27108115585433600000 31381059755 34359738368 649410483 105891076505600000 (ep1292 rfl rfl) rfl)) rfl)

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 147163458871 240000000 0 1 60275704002432085 2361183241434822606848 1567338313350478229 ep1271 ep1217

noncomputable def ep1295 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 174043567 4800000 0 1 Bool.false 147163458871 240000000 0 1 ep1269

noncomputable def ep1296 := @Enclosure.Complex.IsNear.im_isNear qz245 Bool.true 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 Bool.true 60275704002432085 2361183241434822606848 1567338313350478229 ep1271

noncomputable def ep1297 := nat_lit 2098119705603891349729439

noncomputable def ep1298 := nat_lit 2266735911777429702574080000

noncomputable def ep1299 := nat_lit 272785150751280952131002843

noncomputable def ep1300 := nat_lit 558856655499000988701818880000000000

noncomputable def ep1301 := nat_lit 1582209447782005540293578783

noncomputable def ep1302 := nat_lit 208964255457002811516392542043

noncomputable def ep1303 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1297 ep1298 ep1299 ep1300 ep1301 ep1208 ep1302

noncomputable def ep1304 := nat_lit 4062039303631030782430119343853010648197935807856640000

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 174043567 4800000 0 1 60275704002432085 2361183241434822606848 1567338313350478229 ep1271 ep1297

noncomputable def ep1306 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 147163458871 240000000 0 1 53756872117586365 4722366482869645213696 1419946616232878333 ep1223 ep1301

noncomputable abbrev qz508 := (@ep1273 ep1271 (BSN.cpow_neg_s_sub_mk qz150 76170 1000 20 3 1280000000 qz151 rfl EMRow19.d20) ep1293)

noncomputable def ep1307 := ep1212 (@ep1220 ep1221 ep1222 ep1202 ep1203 ep1204 ep1205 (@ep1224 ep1214 ep1215 ep1216 ep1270 (ep1272 qz508) rfl) (@ep1294 ep1218 ep1219 ep1221 ep1295 (ep1296 qz508) rfl) rfl rfl) (@ep1303 ep1211 ep1304 ep1207 ep1208 ep1209 ep1211 (@ep1305 ep1298 ep1299 ep1300 ep1270 (ep1296 qz508) rfl) (@ep1306 ep1208 ep1302 ep1211 ep1295 (ep1272 qz508) rfl) rfl rfl)

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (Complex.im (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) ep1207 ep1208 ep1209 ep1211 ep1207 ep1208 ep1209

noncomputable def ep1309 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245) Bool.false ep1202 ep1203 ep1204 ep1205 Bool.true ep1207 ep1208 ep1209

noncomputable def ep1310 := @ep1172 11791614475496755 31525197391593472 6811234937 31525197391593472 (@ep1173 1 1835008 (ep1174 (@ep1175 524288 1 524288 (ep1176 (@ep1177 232564756 58141189 10000 0 1 (ep1181 rfl) (ep1184 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1185 163 17179869184 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)) (@ep1186 652 68719476736 294958835 17179869184 163 17179869184 (@ep1191 589917344 589917996 34359738368 (@ep1197 ep1198 ep1199 ep1200 ep1201 ep1187 ep1188 ep1189 ep1190 (@ep1206 ep1205 ep1192 ep1193 ep1194 ep1195 (@ep1210 ep1211 ep1307) (@ep1210 ep1211 ep1307) rfl) (@ep1308 ep1211 ep1196 ep1198 ep1199 ep1200 (@ep1309 ep1211 ep1307) (@ep1309 ep1211 ep1307) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow19.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 12048547076894003 31525197391593472 85474062258883 851180329573023744 := ep1170 (ep1171 ep1310) rfl rfl

noncomputable def EMRow19.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz509 := (EMRow19.d3 qz518 qz530 (@Enclosure.dec_le_dec qz518 qz530 73635 1000 76170 1000 (@Eq.refl Real qz518) (@Eq.refl Real qz530) rfl rfl rfl) 19 20 1 1)

noncomputable abbrev qz263 := qz509

noncomputable def ep1311 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz263 (@Enclosure.dec_nonneg qz16 73635 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 19 rfl)

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.fstVal qz509)

noncomputable def ep1312 := @Enclosure.Real.IsNear.neg_val qz264 ep278 ep279

noncomputable def ep1313 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 19 qz16) Bool.true

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.sndVal qz509)

noncomputable def ep1314 := BSN.mul_neg_of_neg_pos_r qz264 qz265 (@ep1312 ep280 ep281 (@ep1313 ep278 ep279 ep280 ep281 (@Eq.refl Real (hardyZApproximantEM 1 19 qz16)) EMRow19.d10) rfl rfl rfl)

noncomputable def ep1315 := @Enclosure.Real.IsNear.pos_val qz265 ep729 ep730

noncomputable def ep1316 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 20 qz150) Bool.false

noncomputable def ep1317 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 19 qz16)

noncomputable def ep1318 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 19 qz16) Bool.true

noncomputable def ep1319 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 19 qz16) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))) Bool.false 126344214305220067 283726776524341248 13442845184509 141863388262170624 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 19))) (@HMul.hMul Real Real Real qz0 qz222 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz225)))))

noncomputable def ep1320 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 20 qz150)

noncomputable def ep1321 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 20 qz150) Bool.false

noncomputable def ep1322 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz150) (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))) Bool.false 12048547076894003 31525197391593472 85474062258883 851180329573023744 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz386 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz145 1 20))) (@HMul.hMul Real Real Real qz0 qz244 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz71 (@HMul.hMul Complex Complex Complex qz71 (@HDiv.hDiv Complex Complex Complex qz78 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz223)) ↑qz224) (@Polynomial.eval Complex Complex.instSemiring qz145 (@ascPochhammer Complex Complex.instSemiring 3))) qz245)))))

noncomputable def ep1323 := @List.cons EMRow19.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz263 (ep1311 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl) (ep1314 (@ep1315 ep731 ep732 (@ep1316 ep729 ep730 ep731 ep732 (@Eq.refl Real (hardyZApproximantEM 1 20 qz150)) EMRow19.d14) rfl rfl rfl)) (ep1317 (hardyZErrorBoundEM 1 19 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 19 qz16 rfl) (@ep1318 Bool.false ep278 ep279 ep280 ep281 126344214305220067 283726776524341248 13442845184509 141863388262170624 (@ep1313 ep278 ep279 ep280 ep281 (@Eq.refl Real (hardyZApproximantEM 1 19 qz16)) EMRow19.d10) (ep1319 EMRow19.d19) rfl rfl rfl rfl rfl)) (ep1320 (hardyZErrorBoundEM 1 20 qz150) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz150 rfl) (@ep1321 Bool.false ep729 ep730 ep731 ep732 12048547076894003 31525197391593472 85474062258883 851180329573023744 (@ep1316 ep729 ep730 ep731 ep732 (@Eq.refl Real (hardyZApproximantEM 1 20 qz150)) EMRow19.d14) (ep1322 EMRow19.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow19.d0)

noncomputable abbrev qz510 := (@Enclosure.dec_le_dec qz518 qz530 73635 1000 76170 1000 (@Eq.refl Real qz518) (@Eq.refl Real qz530) rfl rfl rfl)

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1323 (@List.IsChain.singleton EMRow19.d1 EMRow19.d22 (EMRow19.d2 qz281 qz423 qz510))))

noncomputable abbrev qz511 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1324 := And (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 qz266)) (@Option.some Real qz16))

noncomputable def ep1325 := ep1324 (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 qz266)) (@Option.some Real qz150))

noncomputable def ep1326 := @And.intro (@Eq Nat (@List.length qz511 qz266) 1) ep1325

noncomputable def ep1327 := @And.intro (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 qz266)) (@Option.some Real qz16))

noncomputable def ep1328 := @ep1327 (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 qz266)) (@Option.some Real qz150))

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1323 (@List.IsChain.singleton EMRow19.d1 EMRow19.d22 (EMRow19.d2 qz281 qz423 qz510)))

theorem EMRow19.d23 : Zeta.Certificates.BatchSpec 1 73635 1000 76170 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz511 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz511 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz150)))) qz267 (ep1326 (@Eq.refl Nat 1) (ep1328 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz150))))

theorem solution : Zeta.Certificates.BatchSpec 1 73635 1000 76170 1000 := EMRow19.d23
#print axioms solution
#check solution
