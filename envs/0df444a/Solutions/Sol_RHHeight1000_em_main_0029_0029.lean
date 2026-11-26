-- Prove2me | solution 1 for RHHeight1000.em_main_0029_0029
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:58:57.691435+00:00
-- url     : https://prove2.me/submissions/c4e2bd74-8b4f-4ef9-8235-3404da807ac2

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow29.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow29.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow29.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow29.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow29.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000131521 65760500000000000000 4138529546116343 2251799813685248 250000000131521 65760500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 263042 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000526084 263042000000000000000 4138529546116343 2251799813685248 250000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 263042 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000526084 263042000000000000000 4138529546116343 2251799813685248 250000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz271 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) (2 : Real) Real.pi)

noncomputable abbrev qz2 := (Real.log qz271)

theorem EMRow29.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 263042 1200336 1048576 1 263042 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 263042 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 263042 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 263042 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 263042 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 263042 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 263042 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow29.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 97714 1000)))

noncomputable abbrev qz509 := qz536

noncomputable abbrev qz272 := qz509

noncomputable abbrev qz3 := (BSN.headSumC qz272 9)

noncomputable abbrev qz537 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz510 := qz537

noncomputable abbrev qz273 := qz510

noncomputable abbrev qz4 := qz273

noncomputable abbrev qz5 := qz272

noncomputable abbrev qz511 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz274 := qz511

noncomputable abbrev qz512 := (@Neg.neg Complex Complex.instNeg qz536)

noncomputable abbrev qz275 := qz512

noncomputable abbrev qz6 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 8) qz275)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz6) Bool.false 1819287146775 1099511627776 2430483476009 957674627792896 Bool.false 71158512921 549755813888 1215429530395 478837313896448

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz6 Bool.false 2025060651033 1099511627776 328460865134969 144608868796727296 Bool.false 472123550309 1099511627776 328473575850493 144608868796727296 Bool.true

noncomputable abbrev qz7 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 7) qz275)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz7) Bool.false 2025060651033 1099511627776 328460865134969 144608868796727296 Bool.false 472123550309 1099511627776 328473575850493 144608868796727296

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz7 Bool.false 2056676288933 1099511627776 287377145870101 144608868796727296 Bool.false 443248000917 549755813888 71815709551765 36152217199181824 Bool.true

noncomputable abbrev qz8 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 6) qz275)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz8) Bool.false 2056676288933 1099511627776 287377145870101 144608868796727296 Bool.false 443248000917 549755813888 71815709551765 36152217199181824

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz8 Bool.false 880095028885 549755813888 583947122249 347617473069056 Bool.false 17171106195 34359738368 9338278523099 5561879569104896 Bool.false

noncomputable abbrev qz9 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 5) qz275)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz9) Bool.false 880095028885 549755813888 583947122249 347617473069056 Bool.false 17171106195 34359738368 9338278523099 5561879569104896

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz9 Bool.false 159605796907 137438953472 97094036135347 72304434398363648 Bool.false 639827834715 1099511627776 194171531795171 144608868796727296 Bool.false

noncomputable abbrev qz10 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 4) qz275)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz10) Bool.false 159605796907 137438953472 97094036135347 72304434398363648 Bool.false 639827834715 1099511627776 194171531795171 144608868796727296

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz10 Bool.false 1789040695601 1099511627776 10748078537787 11123759138209792 Bool.false 440111187805 1099511627776 10752835976101 11123759138209792 Bool.true

noncomputable def ep48 := nat_lit 1403907436477609888710656

noncomputable abbrev qz513 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz276 := qz513

noncomputable abbrev qz11 := (@HPow.hPow Complex Complex Complex qz274 qz276 qz275)

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) qz11) Bool.false 1789040695601 1099511627776 10748078537787 11123759138209792 Bool.false 440111187805 1099511627776 10752835976101 11123759138209792

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) qz11 Bool.false 1243136651461 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 8589934592 1202754625141 2259513574948864 Bool.false

noncomputable abbrev qz514 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz277 := qz514

noncomputable abbrev qz12 := (@HPow.hPow Complex Complex Complex qz274 qz277 qz275)

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) qz12) Bool.false 1243136651461 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 8589934592 1202754625141 2259513574948864

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) qz12 Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz13 := qz278

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz279 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz14 := (@Inv.inv Real Real.instInv (Real.sqrt qz279))

noncomputable abbrev qz538 := (Enclosure.sfrac Bool.false 97714 1000)

noncomputable abbrev qz515 := qz538

noncomputable abbrev qz280 := qz515

noncomputable abbrev qz281 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz15 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log qz281))

noncomputable abbrev qz16 := qz280

noncomputable abbrev qz282 := (@Eq.refl Real qz515)

noncomputable abbrev qz17 := qz282

noncomputable def ep54 := @Enclosure.Complex.IsNear.of_eq qz12 (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)))) Bool.false 143625023685 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 8589934592 1202754625141 2259513574948864 (BSN.cpow_neg_s_mk qz16 97714 1000 2 qz17 rfl)

noncomputable abbrev qz18 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep55 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz279) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz279) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz279 qz18)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep56 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 131521 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep57 := nat_lit 25346325404850593077749490291360000

noncomputable def ep58 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep59 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz283 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz284 := (BSN.sinOddQ 2147483648)

noncomputable def ep60 := BSN.sin_dyadic_bound_f 399005380 2147483648 2 1 1048576 263299 ep57 ep58 ep57 ep57 ep59 ep57 193707 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 399005380) qz283 0 1 ep57 ep58 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 399005380) qz284 0 1 ep57 ep59 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz19 := (Real.log qz281)

noncomputable abbrev qz20 := (Enclosure.Real.IsNear.const Bool.false 97714 1000)

noncomputable abbrev qz516 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz285 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35510049) qz516)

noncomputable abbrev qz286 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 131521 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 131521 rfl rfl rfl (ep56 rfl)))

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable def ep61 := @Enclosure.Real.IsNear.cos_image qz15 qz285 Bool.false 35510049 524288 195 262144 Bool.false 193707 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 1109689041 16384000 48857 65760500 35510049 524288 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz19 97714 1000 0 1 363408 524288 1 131521 1109689041 16384000 48857 65760500 qz20 qz286 rfl) rfl) (Enclosure.sfrac_false_div 35510049 524288) (BSN.cos_reduce3 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14038753769027962667008) qz287) 226375608064910080 72057594037927936 Bool.false 193707 1048576 10 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 35510049 524288 226375608064910080 72057594037927936 10 14038753769027962667008 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 193707 1048576 14038753769027962667008 75557863725914323419136 399005380 2147483648 263299 263042 (ep60 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep62 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep63 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz288 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz289 := (BSN.cosOddQ 2147483648)

noncomputable def ep64 := BSN.cos_dyadic_bound_f 399005380 2147483648 2 1 1048576 263299 ep57 ep62 ep57 ep57 ep63 ep57 1030528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 399005380) qz288 0 1 ep57 ep62 ep57 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 399005380) qz289 0 1 ep57 ep63 ep57 rfl rfl rfl rfl) rfl rfl

noncomputable def ep65 := @Enclosure.Real.IsNear.sin_image qz15 qz285 Bool.false 35510049 524288 195 262144 Bool.true 1030528 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz15 Bool.false 1109689041 16384000 48857 65760500 35510049 524288 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz19 97714 1000 0 1 363408 524288 1 131521 1109689041 16384000 48857 65760500 qz20 qz286 rfl) rfl) (Enclosure.sfrac_false_div 35510049 524288) (BSN.sin_reduce3 qz285 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14038753769027962667008) qz287) 226375608064910080 72057594037927936 Bool.false 1030528 1048576 10 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 35510049 524288 226375608064910080 72057594037927936 10 14038753769027962667008 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030528 1048576 14038753769027962667008 75557863725914323419136 399005380 2147483648 263299 263042 (ep64 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz290 := (@Enclosure.Real.IsNear.recentre' qz14 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep55 rfl rfl) rfl)

noncomputable def ep66 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz15)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15))) Bool.false 143625023685 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 8589934592 1202754625141 2259513574948864 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz15) 741455 1048576 1 1048576 193707 1048576 25908739 34477441024 143625023685 1099511627776 76866236474283 144608868796727296 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz15) Bool.false 193707 1048576 25908739 34477441024 193707 1048576 25908739 34477441024 (ep61 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz14 (@Neg.neg Real Real.instNeg (Real.sin qz15)) 741455 1048576 1 1048576 8051 8192 25908739 34477441024 5969454205 8589934592 1202754625141 2259513574948864 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz15) Bool.true 8051 8192 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz15) Bool.true 1030528 1048576 25908739 34477441024 8051 8192 25908739 34477441024 (ep65 rfl rfl) rfl)) rfl)

noncomputable abbrev qz291 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz291

noncomputable def ep67 := @ep52 143625023685 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 8589934592 1202754625141 2259513574948864 Bool.false 1243136651461 1243136651461 1099511627776 76866236474283 144608868796727296 Bool.false 5969454205 5969454205 8589934592 1202754625141 2259513574948864 (ep53 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep54 ep66) rfl rfl

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz22 := (@Inv.inv Real Real.instInv (Real.sqrt qz292))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep68 := @Enclosure.Complex.IsNear.of_eq qz11 (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 136476011035 274877906944 15714696129237 36152217199181824 Bool.true 323978950435 1099511627776 62810571680289 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 3 qz17 rfl)

noncomputable def ep69 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz292) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz292) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz292 qz18)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz292 qz18)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep70 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 131521 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep71 := nat_lit 1750254717496134025811969861047456321

noncomputable def ep72 := BSN.cos_dyadic_bound_f 1150205167 2147483648 2 1 1048576 263299 ep71 ep62 ep71 ep71 ep63 ep71 901732 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1150205167) qz288 0 1 ep71 ep62 ep71 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1150205167) qz289 0 1 ep71 ep63 ep71 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56282189) qz516)

noncomputable abbrev qz294 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 131521 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 131521 rfl rfl rfl (ep70 rfl)))

noncomputable def ep73 := @Enclosure.Real.IsNear.cos_image qz23 qz293 Bool.false 56282189 524288 195 262144 Bool.false 901732 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 28141094573 262144000 48857 65760500 56282189 524288 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz24 97714 1000 0 1 575989 524288 1 131521 28141094573 262144000 48857 65760500 qz20 qz294 rfl) rfl) (Enclosure.sfrac_false_div 56282189 524288) (BSN.cos_reduce0 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40469246578647355097088) qz287) 226375608064910080 72057594037927936 Bool.false 901732 1048576 17 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 56282189 524288 226375608064910080 72057594037927936 17 40469246578647355097088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 901732 1048576 40469246578647355097088 75557863725914323419136 1150205167 2147483648 263299 263042 (ep72 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep74 := BSN.sin_dyadic_bound_f 1150205167 2147483648 2 1 1048576 263299 ep71 ep58 ep71 ep71 ep59 ep71 535153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1150205167) qz283 0 1 ep71 ep58 ep71 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1150205167) qz284 0 1 ep71 ep59 ep71 rfl rfl rfl rfl) rfl rfl

noncomputable def ep75 := @Enclosure.Real.IsNear.sin_image qz23 qz293 Bool.false 56282189 524288 195 262144 Bool.false 535153 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 28141094573 262144000 48857 65760500 56282189 524288 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz24 97714 1000 0 1 575989 524288 1 131521 28141094573 262144000 48857 65760500 qz20 qz294 rfl) rfl) (Enclosure.sfrac_false_div 56282189 524288) (BSN.sin_reduce0 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40469246578647355097088) qz287) 226375608064910080 72057594037927936 Bool.false 535153 1048576 17 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 56282189 524288 226375608064910080 72057594037927936 17 40469246578647355097088 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 535153 1048576 40469246578647355097088 75557863725914323419136 1150205167 2147483648 263299 263042 (ep74 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz295 := (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep69 rfl rfl) rfl)

noncomputable def ep76 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 136476011035 274877906944 15714696129237 36152217199181824 Bool.true 323978950435 1099511627776 62810571680289 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz22 (Real.cos qz23) 605395 1048576 1 1048576 225433 262144 25908739 34477441024 136476011035 274877906944 15714696129237 36152217199181824 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 901732 1048576 25908739 34477441024 225433 262144 25908739 34477441024 (ep73 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 535153 1048576 25908739 34477441024 323978950435 1099511627776 62810571680289 144608868796727296 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 535153 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 535153 1048576 25908739 34477441024 535153 1048576 25908739 34477441024 (ep75 rfl rfl) rfl)) rfl)

noncomputable def ep77 := @ep50 136476011035 274877906944 15714696129237 36152217199181824 Bool.true 323978950435 1099511627776 62810571680289 144608868796727296 Bool.false 491767761844440708153344 1789040695601 1099511627776 10748078537787 11123759138209792 Bool.false 3780526316452378050560 440111187805 1099511627776 10752835976101 11123759138209792 (ep51 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep67 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep68 ep76) rfl rfl

noncomputable abbrev qz296 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz25 := (@Inv.inv Real Real.instInv (Real.sqrt qz296))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep78 := @Enclosure.Complex.IsNear.of_eq qz10 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 512194320345 1099511627776 54463051279463 144608868796727296 Bool.false 99858323455 549755813888 27192332052929 72304434398363648 (BSN.cpow_neg_s_mk qz16 97714 1000 4 qz17 rfl)

noncomputable def ep79 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz296) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz296) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz18)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz296 qz18)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep80 := nat_lit 318077276165597140789031982421875

noncomputable def ep81 := nat_lit 49379992292270016474244603430625

noncomputable def ep82 := nat_lit 20095619060363156210525625

noncomputable def ep83 := BSN.log_dyadic_bound 3 5 14 13 ep80 524288 131521 ep81 ep82 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep81 ep80 ep82 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep84 := nat_lit 406357788708096090413880936286130176

noncomputable def ep85 := BSN.cos_dyadic_bound_f 798412168 2147483648 2 1 1048576 263299 ep84 ep62 ep84 ep84 ep63 ep84 976935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 798412168) qz288 0 1 ep84 ep62 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 798412168) qz289 0 1 ep84 ep63 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz27 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz297 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17755049) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz298 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 131521 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 131521 rfl rfl rfl (ep83 rfl)))

noncomputable abbrev qz299 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep86 := @Enclosure.Real.IsNear.cos_image qz26 qz297 Bool.false 17755049 131072 195 262144 Bool.true 976935 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 35510098169 262144000 48857 65760500 17755049 131072 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 97714 1000 0 1 726817 524288 1 131521 35510098169 262144000 48857 65760500 qz20 qz298 rfl) rfl) (Enclosure.sfrac_false_div 17755049 131072) (BSN.cos_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7022907706621839802368) qz299) 226375608064910080 72057594037927936 Bool.false 976935 1048576 21 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 17755049 131072 226375608064910080 72057594037927936 21 7022907706621839802368 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 976935 1048576 7022907706621839802368 18889465931478580854784 798412168 2147483648 263299 263042 (ep85 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep87 := BSN.sin_dyadic_bound_f 798412168 2147483648 2 1 1048576 263299 ep84 ep58 ep84 ep84 ep59 ep84 380930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 798412168) qz283 0 1 ep84 ep58 ep84 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 798412168) qz284 0 1 ep84 ep59 ep84 rfl rfl rfl rfl) rfl rfl

noncomputable def ep88 := @Enclosure.Real.IsNear.sin_image qz26 qz297 Bool.false 17755049 131072 195 262144 Bool.true 380930 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 35510098169 262144000 48857 65760500 17755049 131072 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz27 97714 1000 0 1 726817 524288 1 131521 35510098169 262144000 48857 65760500 qz20 qz298 rfl) rfl) (Enclosure.sfrac_false_div 17755049 131072) (BSN.sin_reduce2 qz297 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7022907706621839802368) qz299) 226375608064910080 72057594037927936 Bool.false 380930 1048576 21 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 17755049 131072 226375608064910080 72057594037927936 21 7022907706621839802368 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 380930 1048576 7022907706621839802368 18889465931478580854784 798412168 2147483648 263299 263042 (ep87 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep79 rfl rfl) rfl)

noncomputable def ep89 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 512194320345 1099511627776 54463051279463 144608868796727296 Bool.false 99858323455 549755813888 27192332052929 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ft qz25 (Real.cos qz26) 524287 1048576 1 1048576 976935 1048576 25908739 34477441024 512194320345 1099511627776 54463051279463 144608868796727296 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 976935 1048576 25908739 34477441024 976935 1048576 25908739 34477441024 (ep86 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz25 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 524287 1048576 1 1048576 190465 524288 25908739 34477441024 99858323455 549755813888 27192332052929 72304434398363648 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 190465 524288 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 380930 1048576 25908739 34477441024 190465 524288 25908739 34477441024 (ep88 rfl rfl) rfl)) rfl)

noncomputable def ep90 := @ep47 512194320345 1099511627776 54463051279463 144608868796727296 Bool.false 99858323455 549755813888 27192332052929 72304434398363648 Bool.false ep48 159605796907 137438953472 97094036135347 72304434398363648 Bool.false 351749072021941565521920 639827834715 1099511627776 194171531795171 144608868796727296 (ep49 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep77 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep78 ep89) rfl rfl

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz28 := (@Inv.inv Real Real.instInv (Real.sqrt qz301))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep91 := @Enclosure.Complex.IsNear.of_eq qz9 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 241671841257 549755813888 24366965292445 72304434398363648 Bool.true 90352436475 1099511627776 48623709805403 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 5 qz17 rfl)

noncomputable def ep92 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz301) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz301) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz18)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz18)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep93 := nat_lit 11734546589655452485523914939250625

noncomputable def ep94 := nat_lit 2429970938528035899633153341031900

noncomputable def ep95 := nat_lit 824199001261152424427520000

noncomputable def ep96 := BSN.log_dyadic_bound 2 3 17 16 ep93 524288 131521 ep94 ep95 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep94 ep93 ep95 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep97 := nat_lit 24803930198396711098573299276860176

noncomputable def ep98 := BSN.cos_dyadic_bound_f 396853418 2147483648 2 1 1048576 263299 ep97 ep62 ep97 ep97 ep63 ep97 1030722 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 396853418) qz288 0 1 ep97 ep62 ep97 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 396853418) qz289 0 1 ep97 ep63 ep97 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz31 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164903709) qz30)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 131521 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 131521 rfl rfl rfl (ep96 rfl)))

noncomputable def ep99 := @Enclosure.Real.IsNear.cos_image qz29 qz302 Bool.false 164903709 1048576 195 262144 Bool.false 1030722 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1288310233 8192000 48857 65760500 164903709 1048576 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz31 97714 1000 0 1 843808 524288 1 131521 1288310233 8192000 48857 65760500 qz20 qz303 rfl) rfl) (Enclosure.sfrac_false_div 164903709 1048576) (BSN.cos_reduce0 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27926076714091437621248) qz32) 226375608064910080 72057594037927936 Bool.false 1030722 1048576 25 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 164903709 1048576 226375608064910080 72057594037927936 25 27926076714091437621248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030722 1048576 27926076714091437621248 151115727451828646838272 396853418 2147483648 263299 263042 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep100 := BSN.sin_dyadic_bound_f 396853418 2147483648 2 1 1048576 263299 ep97 ep58 ep97 ep97 ep59 ep97 192675 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 396853418) qz283 0 1 ep97 ep58 ep97 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 396853418) qz284 0 1 ep97 ep59 ep97 rfl rfl rfl rfl) rfl rfl

noncomputable def ep101 := @Enclosure.Real.IsNear.sin_image qz29 qz302 Bool.false 164903709 1048576 195 262144 Bool.false 192675 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 1288310233 8192000 48857 65760500 164903709 1048576 195 262144 (@Enclosure.Real.IsNear.mulLit_ff qz16 qz31 97714 1000 0 1 843808 524288 1 131521 1288310233 8192000 48857 65760500 qz20 qz303 rfl) rfl) (Enclosure.sfrac_false_div 164903709 1048576) (BSN.sin_reduce0 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27926076714091437621248) qz32) 226375608064910080 72057594037927936 Bool.false 192675 1048576 25 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 164903709 1048576 226375608064910080 72057594037927936 25 27926076714091437621248 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 192675 1048576 27926076714091437621248 151115727451828646838272 396853418 2147483648 263299 263042 (ep100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep92 rfl rfl) rfl)

noncomputable def ep102 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 241671841257 549755813888 24366965292445 72304434398363648 Bool.true 90352436475 1099511627776 48623709805403 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz28 (Real.cos qz29) 468937 1048576 1 1048576 515361 524288 25908739 34477441024 241671841257 549755813888 24366965292445 72304434398363648 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 1030722 1048576 25908739 34477441024 515361 524288 25908739 34477441024 (ep99 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz28 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 468937 1048576 1 1048576 192675 1048576 25908739 34477441024 90352436475 1099511627776 48623709805403 144608868796727296 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 192675 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 192675 1048576 25908739 34477441024 192675 1048576 25908739 34477441024 (ep101 rfl rfl) rfl)) rfl)

noncomputable def ep103 := @ep45 241671841257 549755813888 24366965292445 72304434398363648 Bool.true 90352436475 1099511627776 48623709805403 144608868796727296 Bool.false 120959339725864011038720 880095028885 549755813888 583947122249 347617473069056 Bool.false 604154589541728245514240 17171106195 34359738368 9338278523099 5561879569104896 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep90 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep91 ep102) rfl rfl

noncomputable abbrev qz305 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz305))

noncomputable abbrev qz306 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz267 qz280 qz306)

noncomputable def ep104 := @Enclosure.Complex.IsNear.of_eq qz8 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 296486231163 1099511627776 44455143014517 144608868796727296 Bool.false 168510301797 549755813888 22233798303243 72304434398363648 (BSN.cpow_neg_s_mk qz16 97714 1000 6 qz17 rfl)

noncomputable abbrev qz307 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz18)

noncomputable def ep105 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz305) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz305) (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz307) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep106 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 131521 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz306 97714 1000 0 1 4034681531866359 2251799813685248 500000000131521 65760500000000000000 197122435602394701663 1125899906842624000 24428500006425721497 32880250000000000000000 qz20 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000263042 131521000000000000000 4034681531866359 2251799813685248 500000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep106 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep108 := nat_lit 5763241534610277776050013847675770001

noncomputable def ep109 := BSN.sin_dyadic_bound_f 1549411251 2147483648 2 1 1048576 263299 ep108 ep58 ep108 ep108 ep59 ep108 692597 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1549411251) qz283 0 1 ep108 ep58 ep108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1549411251) qz284 0 1 ep108 ep59 ep108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91792287) qz516)

noncomputable def ep110 := @Enclosure.Real.IsNear.cos_image qz34 qz308 Bool.false 91792287 524288 195 262144 Bool.false 692597 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 197122435602394701663 1125899906842624000 24428500006425721497 32880250000000000000000 91792287 524288 195 262144 (ep107 rfl) rfl) (Enclosure.sfrac_false_div 91792287 524288) (BSN.cos_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54515061991891034701824) qz287) 226375608064910080 72057594037927936 Bool.false 692597 1048576 27 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 91792287 524288 226375608064910080 72057594037927936 27 54515061991891034701824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 692597 1048576 54515061991891034701824 75557863725914323419136 1549411251 2147483648 263299 263042 (ep109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep111 := nat_lit 205951809359082193395008540278458141314647032078417289346006618579324131342881

noncomputable def ep112 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep113 := nat_lit 33214952986257029608789619500340844925848887823554930676331072788251540001

noncomputable def ep114 := nat_lit 617788998171274066125808041596373742254089398459604758176667193592395890948641

noncomputable def ep115 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep116 := BSN.cos_dyadic_bound_f 1549411251 2147483648 3 2 1048576 263299 ep111 ep112 ep113 ep114 ep115 ep113 787286 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1549411251) qz288 0 2 ep111 ep112 ep113 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1549411251) qz289 0 2 ep114 ep115 ep113 rfl rfl rfl rfl) rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.sin_image qz34 qz308 Bool.false 91792287 524288 195 262144 Bool.true 787286 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 197122435602394701663 1125899906842624000 24428500006425721497 32880250000000000000000 91792287 524288 195 262144 (ep107 rfl) rfl) (Enclosure.sfrac_false_div 91792287 524288) (BSN.sin_reduce3 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54515061991891034701824) qz287) 226375608064910080 72057594037927936 Bool.false 787286 1048576 27 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 91792287 524288 226375608064910080 72057594037927936 27 54515061991891034701824 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 787286 1048576 54515061991891034701824 75557863725914323419136 1549411251 2147483648 263299 263042 (ep116 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep105 rfl rfl) rfl)

noncomputable def ep118 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 296486231163 1099511627776 44455143014517 144608868796727296 Bool.false 168510301797 549755813888 22233798303243 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 428079 1048576 1 1048576 692597 1048576 25908739 34477441024 296486231163 1099511627776 44455143014517 144608868796727296 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 692597 1048576 25908739 34477441024 692597 1048576 25908739 34477441024 (ep110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 428079 1048576 1 1048576 393643 524288 25908739 34477441024 168510301797 549755813888 22233798303243 72304434398363648 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 393643 524288 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 787286 1048576 25908739 34477441024 393643 524288 25908739 34477441024 (ep117 rfl rfl) rfl)) rfl)

noncomputable def ep119 := @ep43 296486231163 1099511627776 44455143014517 144608868796727296 Bool.false 168510301797 549755813888 22233798303243 72304434398363648 Bool.false 1130669747126512862101504 2056676288933 1099511627776 287377145870101 144608868796727296 Bool.false 15229885343647144083456 443248000917 549755813888 71815709551765 36152217199181824 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep103 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep104 ep118) rfl rfl

noncomputable abbrev qz310 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt qz310))

noncomputable abbrev qz311 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz267 qz280 qz311)

noncomputable def ep120 := @Enclosure.Complex.IsNear.of_eq qz7 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.true 7903909475 274877906944 10270929816217 36152217199181824 Bool.true 414372451525 1099511627776 41210737643433 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 7 qz17 rfl)

noncomputable abbrev qz312 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz18)

noncomputable def ep121 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz310) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz310) (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz312) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep122 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 131521 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz311 97714 1000 0 1 4381796493761783 2251799813685248 500000000131521 65760500000000000000 214081431295719432031 1125899906842624000 24428500006425721497 32880250000000000000000 qz20 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000263042 131521000000000000000 4381796493761783 2251799813685248 500000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep124 := BSN.sin_dyadic_bound_f 163533150 2147483648 1 0 1048576 263299 0 1 1 0 1 1 79772 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 163533150) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 163533150) qz284 0 0 rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199378869) qz30)

noncomputable def ep125 := @Enclosure.Real.IsNear.cos_image qz36 qz313 Bool.false 199378869 1048576 195 262144 Bool.true 79772 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 214081431295719432031 1125899906842624000 24428500006425721497 32880250000000000000000 199378869 1048576 195 262144 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 199378869 1048576) (BSN.cos_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11507622411620568793088) qz32) 226375608064910080 72057594037927936 Bool.false 79772 1048576 30 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 199378869 1048576 226375608064910080 72057594037927936 30 11507622411620568793088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 79772 1048576 11507622411620568793088 151115727451828646838272 163533150 2147483648 263299 263042 (ep124 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep126 := nat_lit 715192924199576961072911006250000

noncomputable def ep127 := BSN.cos_dyadic_bound_f 163533150 2147483648 2 1 1048576 263299 ep126 ep62 ep126 ep126 ep63 ep126 1045537 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 163533150) qz288 0 1 ep126 ep62 ep126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 163533150) qz289 0 1 ep126 ep63 ep126 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz36 qz313 Bool.false 199378869 1048576 195 262144 Bool.false 1045537 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 214081431295719432031 1125899906842624000 24428500006425721497 32880250000000000000000 199378869 1048576 195 262144 (ep123 rfl) rfl) (Enclosure.sfrac_false_div 199378869 1048576) (BSN.sin_reduce1 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11507622411620568793088) qz32) 226375608064910080 72057594037927936 Bool.false 1045537 1048576 30 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 199378869 1048576 226375608064910080 72057594037927936 30 11507622411620568793088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1045537 1048576 11507622411620568793088 151115727451828646838272 163533150 2147483648 263299 263042 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep121 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.true 7903909475 274877906944 10270929816217 36152217199181824 Bool.true 414372451525 1099511627776 41210737643433 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz36) 396325 1048576 1 1048576 19943 262144 25908739 34477441024 7903909475 274877906944 10270929816217 36152217199181824 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.true 79772 1048576 25908739 34477441024 19943 262144 25908739 34477441024 (ep125 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 396325 1048576 1 1048576 1045537 1048576 25908739 34477441024 414372451525 1099511627776 41210737643433 144608868796727296 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.false 1045537 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.false 1045537 1048576 25908739 34477441024 1045537 1048576 25908739 34477441024 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep41 7903909475 274877906944 10270929816217 36152217199181824 Bool.true 414372451525 1099511627776 41210737643433 144608868796727296 Bool.false 556644433190605031473152 2025060651033 1099511627776 328460865134969 144608868796727296 Bool.false 259552666655816408891392 472123550309 1099511627776 328473575850493 144608868796727296 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep119 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep120 ep129) rfl rfl

noncomputable abbrev qz315 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz315))

noncomputable abbrev qz316 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz267 qz280 qz316)

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz6 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 102886752129 549755813888 19271069871195 72304434398363648 Bool.true 329806524467 1099511627776 38586142328797 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 8 qz17 rfl)

noncomputable abbrev qz317 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz18)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz315) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz315) (Real.sqrt qz317) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz317) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 0 16 1 0 1 524288 131521 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz316 97714 1000 0 1 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 457544444442382343709 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 39279540158062550581248 18889465931478580854784 1000000000394563 131521000000000000000 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := nat_lit 2059241543292225908993870771385578641

noncomputable def ep136 := BSN.sin_dyadic_bound_f 1197917261 2147483648 2 1 1048576 263299 ep135 ep58 ep135 ep135 ep59 ep135 555054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1197917261) qz283 0 1 ep135 ep58 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1197917261) qz284 0 1 ep135 ep59 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106530367) qz516)

noncomputable def ep137 := @Enclosure.Real.IsNear.cos_image qz38 qz318 Bool.false 106530367 524288 781 1048576 Bool.true 555054 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 457544444442382343709 2251799813685248000 48857000019277164491 65760500000000000000000 106530367 524288 781 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 106530367 524288) (BSN.cos_reduce1 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42147966648460576292864) qz287) 226375608064910080 72057594037927936 Bool.false 555054 1048576 32 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 106530367 524288 226375608064910080 72057594037927936 32 42147966648460576292864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 555054 1048576 42147966648460576292864 75557863725914323419136 1197917261 2147483648 263299 263042 (ep136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep138 := BSN.cos_dyadic_bound_f 1197917261 2147483648 2 1 1048576 263299 ep135 ep62 ep135 ep135 ep63 ep135 889621 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1197917261) qz288 0 1 ep135 ep62 ep135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1197917261) qz289 0 1 ep135 ep63 ep135 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz38 qz318 Bool.false 106530367 524288 781 1048576 Bool.false 889621 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 457544444442382343709 2251799813685248000 48857000019277164491 65760500000000000000000 106530367 524288 781 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 106530367 524288) (BSN.sin_reduce1 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 42147966648460576292864) qz287) 226375608064910080 72057594037927936 Bool.false 889621 1048576 32 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 106530367 524288 226375608064910080 72057594037927936 32 42147966648460576292864 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 889621 1048576 42147966648460576292864 75557863725914323419136 1197917261 2147483648 263299 263042 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 102886752129 549755813888 19271069871195 72304434398363648 Bool.true 329806524467 1099511627776 38586142328797 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 370727 1048576 1 1048576 277527 524288 103766477 137909764096 102886752129 549755813888 19271069871195 72304434398363648 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 555054 1048576 103766477 137909764096 277527 524288 103766477 137909764096 (ep137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 370727 1048576 1 1048576 889621 1048576 103766477 137909764096 329806524467 1099511627776 38586142328797 144608868796727296 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 889621 1048576 103766477 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 889621 1048576 103766477 137909764096 889621 1048576 103766477 137909764096 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep39 102886752129 549755813888 19271069871195 72304434398363648 Bool.true 329806524467 1099511627776 38586142328797 144608868796727296 Bool.false 1000163686071267439411200 1819287146775 1099511627776 2430483476009 957674627792896 Bool.false 156479224743776476987392 71158512921 549755813888 1215429530395 478837313896448 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep140) rfl rfl

theorem EMRow29.d6 : Enclosure.Complex.IsNear qz3 Bool.false 1819287146775 1099511627776 2430483476009 957674627792896 Bool.false 71158512921 549755813888 1215429530395 478837313896448 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz39 := (BSN.headSumC qz272 17)

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz275)

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz39 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz40) Bool.false 2773894499761 1099511627776 616848707222851 144608868796727296 Bool.true 179680209653 1099511627776 617025042951433 144608868796727296

noncomputable def ep143 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz40 Bool.false 2571606086665 1099511627776 589545456803051 144608868796727296 Bool.false 6428737483 1099511627776 589729910007753 144608868796727296 Bool.false

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz275)

noncomputable def ep144 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz41) Bool.false 2571606086665 1099511627776 589545456803051 144608868796727296 Bool.false 6428737483 1099511627776 589729910007753 144608868796727296

noncomputable def ep145 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz41 Bool.false 2358258929773 1099511627776 561383481419447 144608868796727296 Bool.false 96859754897 549755813888 280790296168355 72304434398363648 Bool.false

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz275)

noncomputable def ep146 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz42) Bool.false 2358258929773 1099511627776 561383481419447 144608868796727296 Bool.false 96859754897 549755813888 280790296168355 72304434398363648

noncomputable def ep147 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz42 Bool.false 32413094803 17179869184 66525900835197 18076108599590912 Bool.false 134929084989 549755813888 266250892524999 72304434398363648 Bool.false

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz275)

noncomputable def ep148 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz43) Bool.false 32413094803 17179869184 66525900835197 18076108599590912 Bool.false 134929084989 549755813888 266250892524999 72304434398363648

noncomputable def ep149 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz43 Bool.false 1840439845831 1099511627776 501961851520585 144608868796727296 Bool.false 37154974035 549755813888 251136909205969 72304434398363648 Bool.false

noncomputable def ep150 := nat_lit 2280868776198677507080192

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz275)

noncomputable def ep151 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz44) Bool.false 1840439845831 1099511627776 501961851520585 144608868796727296 Bool.false 37154974035 549755813888 251136909205969 72304434398363648

noncomputable def ep152 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz44 Bool.false 2035883428609 1099511627776 470506837919143 144608868796727296 Bool.true 175779826815 1099511627776 470795061192845 144608868796727296 Bool.true

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz275)

noncomputable def ep153 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz45) Bool.false 2035883428609 1099511627776 470506837919143 144608868796727296 Bool.true 175779826815 1099511627776 470795061192845 144608868796727296

noncomputable def ep154 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz45 Bool.false 265106525393 137438953472 109426617643435 36152217199181824 Bool.false 72330392189 549755813888 54737092224471 18076108599590912 Bool.true

noncomputable abbrev qz46 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz275)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz46) Bool.false 265106525393 137438953472 109426617643435 36152217199181824 Bool.false 72330392189 549755813888 54737092224471 18076108599590912

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz46 Bool.false 498712427375 274877906944 3877809404421 1390469892276224 Bool.true 179400813733 1099511627776 31031068261073 11123759138209792 Bool.false

noncomputable abbrev qz47 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 9) qz275)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz47) Bool.false 498712427375 274877906944 3877809404421 1390469892276224 Bool.true 179400813733 1099511627776 31031068261073 11123759138209792

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP qz3 qz47 Bool.false 1819287146775 1099511627776 2430483476009 957674627792896 Bool.false 71158512921 549755813888 1215429530395 478837313896448 Bool.false

noncomputable def ep159 := nat_lit 2193360451260825731072000

noncomputable abbrev qz320 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz320))

noncomputable abbrev qz321 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz280 qz321)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq qz47 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 175562562725 1099511627776 36289173182425 144608868796727296 Bool.true 321717839575 1099511627776 36344169214659 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 9 qz17 rfl)

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz18)

noncomputable def ep161 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz320) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz320) (Real.sqrt qz322) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz322) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep162 := BSN.log_dyadic_bound 1 17 2 1 867 524288 131521 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep163 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz321 97714 1000 0 1 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 483460427121064058397 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 41504390431577613533184 18889465931478580854784 1000000000394563 131521000000000000000 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep162 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep164 := nat_lit 1001531312962843306019871502985220007628252005779895095583391999878367158763776

noncomputable def ep165 := nat_lit 784496384534055600519576455372906322747670324151905966937845958135988388096

noncomputable def ep166 := nat_lit 3003024946119461806858575356044914210239260676691381474816300307718829499515136

noncomputable def ep167 := BSN.cos_dyadic_bound_f 2300508638 2147483648 3 2 1048576 263299 ep164 ep112 ep165 ep166 ep115 ep165 502289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2300508638) qz288 0 2 ep164 ep112 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2300508638) qz289 0 2 ep166 ep115 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56282201) (@Nat.cast Real Real.instNatCast 262144))

noncomputable abbrev qz324 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep168 := @Enclosure.Real.IsNear.cos_image qz49 qz323 Bool.false 56282201 262144 195 262144 Bool.false 502289 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 483460427121064058397 2251799813685248000 48857000019277164491 65760500000000000000000 56282201 262144 195 262144 (ep163 rfl) rfl) (Enclosure.sfrac_false_div 56282201 262144) (BSN.cos_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40470975960904265367552) qz324) 226375608064910080 72057594037927936 Bool.false 502289 1048576 34 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 56282201 262144 226375608064910080 72057594037927936 34 40470975960904265367552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 502289 1048576 40470975960904265367552 37778931862957161709568 2300508638 2147483648 263299 263042 (ep167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep169 := nat_lit 1802128766225490706355353044209097688672655474144489647276555323014552095064320

noncomputable def ep170 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep171 := nat_lit 4718590917396563379006035801524652098191553823186941228444507428724940077302016

noncomputable def ep172 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep173 := BSN.sin_dyadic_bound_f 2300508638 2147483648 3 2 1048576 263299 ep169 ep170 ep165 ep171 ep172 ep165 920443 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2300508638) qz283 0 2 ep169 ep170 ep165 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2300508638) qz284 0 2 ep171 ep172 ep165 rfl rfl rfl rfl) rfl rfl

noncomputable def ep174 := @Enclosure.Real.IsNear.sin_image qz49 qz323 Bool.false 56282201 262144 195 262144 Bool.false 920443 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 483460427121064058397 2251799813685248000 48857000019277164491 65760500000000000000000 56282201 262144 195 262144 (ep163 rfl) rfl) (Enclosure.sfrac_false_div 56282201 262144) (BSN.sin_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40470975960904265367552) qz324) 226375608064910080 72057594037927936 Bool.false 920443 1048576 34 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 56282201 262144 226375608064910080 72057594037927936 34 40470975960904265367552 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 920443 1048576 40470975960904265367552 37778931862957161709568 2300508638 2147483648 263299 263042 (ep173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep161 rfl rfl) rfl)

noncomputable def ep175 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 175562562725 1099511627776 36289173182425 144608868796727296 Bool.true 321717839575 1099511627776 36344169214659 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 349525 1048576 1 1048576 502289 1048576 25908739 34477441024 175562562725 1099511627776 36289173182425 144608868796727296 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 502289 1048576 25908739 34477441024 502289 1048576 25908739 34477441024 (ep168 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 349525 1048576 1 1048576 920443 1048576 25908739 34477441024 321717839575 1099511627776 36344169214659 144608868796727296 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 920443 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 920443 1048576 25908739 34477441024 920443 1048576 25908739 34477441024 (ep174 rfl rfl) rfl)) rfl)

noncomputable def ep176 := @ep158 175562562725 1099511627776 36289173182425 144608868796727296 Bool.true 321717839575 1099511627776 36344169214659 144608868796727296 Bool.false ep159 498712427375 274877906944 3877809404421 1390469892276224 Bool.true 98626640365954902523904 179400813733 1099511627776 31031068261073 11123759138209792 EMRow29.d6 (ep160 ep175) rfl rfl

noncomputable abbrev qz326 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz326))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep177 := @Enclosure.Complex.IsNear.of_eq qz46 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 31500623411 274877906944 8603573128489 36152217199181824 Bool.false 324061598111 1099511627776 34492850401819 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 10 qz17 rfl)

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz18)

noncomputable def ep178 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz326) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz326) (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz327) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep179 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 131521 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz52 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable def ep180 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz52 97714 1000 0 1 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 506643044156750339613 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000394563 131521000000000000000 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep181 := nat_lit 402197133585438147677464360686135361

noncomputable def ep182 := BSN.sin_dyadic_bound_f 796360559 2147483648 2 1 1048576 263299 ep181 ep58 ep181 ep181 ep59 ep181 379996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 796360559) qz283 0 1 ep181 ep58 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 796360559) qz284 0 1 ep181 ep59 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58981013) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep183 := @Enclosure.Real.IsNear.cos_image qz51 qz328 Bool.false 58981013 262144 195 262144 Bool.false 379996 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 506643044156750339613 2251799813685248000 48857000019277164491 65760500000000000000000 58981013 262144 195 262144 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 58981013 262144) (BSN.cos_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14009723118306486910976) qz324) 226375608064910080 72057594037927936 Bool.false 379996 1048576 35 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 58981013 262144 226375608064910080 72057594037927936 35 14009723118306486910976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379996 1048576 14009723118306486910976 37778931862957161709568 796360559 2147483648 263299 263042 (ep182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep184 := BSN.cos_dyadic_bound_f 796360559 2147483648 2 1 1048576 263299 ep181 ep62 ep181 ep181 ep63 ep181 977299 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 796360559) qz288 0 1 ep181 ep62 ep181 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 796360559) qz289 0 1 ep181 ep63 ep181 rfl rfl rfl rfl) rfl rfl

noncomputable def ep185 := @Enclosure.Real.IsNear.sin_image qz51 qz328 Bool.false 58981013 262144 195 262144 Bool.true 977299 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 506643044156750339613 2251799813685248000 48857000019277164491 65760500000000000000000 58981013 262144 195 262144 (ep180 rfl) rfl) (Enclosure.sfrac_false_div 58981013 262144) (BSN.sin_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14009723118306486910976) qz324) 226375608064910080 72057594037927936 Bool.false 977299 1048576 35 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 58981013 262144 226375608064910080 72057594037927936 35 14009723118306486910976 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977299 1048576 14009723118306486910976 37778931862957161709568 796360559 2147483648 263299 263042 (ep184 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep178 rfl rfl) rfl)

noncomputable def ep186 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 31500623411 274877906944 8603573128489 36152217199181824 Bool.false 324061598111 1099511627776 34492850401819 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 331589 1048576 1 1048576 94999 262144 25908739 34477441024 31500623411 274877906944 8603573128489 36152217199181824 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 379996 1048576 25908739 34477441024 94999 262144 25908739 34477441024 (ep183 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 331589 1048576 1 1048576 977299 1048576 25908739 34477441024 324061598111 1099511627776 34492850401819 144608868796727296 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.true 977299 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.true 977299 1048576 25908739 34477441024 977299 1048576 25908739 34477441024 (ep185 rfl rfl) rfl)) rfl)

noncomputable def ep187 := @ep156 31500623411 274877906944 8603573128489 36152217199181824 Bool.false 324061598111 1099511627776 34492850401819 144608868796727296 Bool.false 145743853634448454057984 265106525393 137438953472 109426617643435 36152217199181824 Bool.false 159056214506807731683328 72330392189 549755813888 54737092224471 18076108599590912 (ep157 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep176 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep177 ep186) rfl rfl

noncomputable abbrev qz330 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz330))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz267 qz280 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep188 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.true 84968774535 1099511627776 32800367345403 144608868796727296 Bool.true 320440611193 1099511627776 32898323397077 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 11 qz17 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz18)

noncomputable def ep189 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz330) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz330) (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep190 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 131521 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz55 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable def ep191 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz55 97714 1000 0 1 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 527614375521786699293 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000394563 131521000000000000000 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep190 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep192 := nat_lit 95994647635416852518258883525104656

noncomputable def ep193 := BSN.sin_dyadic_bound_f 556623778 2147483648 2 1 1048576 263299 ep192 ep58 ep192 ep192 ep59 ep192 268755 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 556623778) qz283 0 1 ep192 ep58 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 556623778) qz284 0 1 ep192 ep59 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 245689589) qz30)

noncomputable def ep194 := @Enclosure.Real.IsNear.cos_image qz54 qz332 Bool.false 245689589 1048576 195 262144 Bool.true 268755 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 527614375521786699293 2251799813685248000 48857000019277164491 65760500000000000000000 245689589 1048576 195 262144 (ep191 rfl) rfl) (Enclosure.sfrac_false_div 245689589 1048576) (BSN.cos_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39168916276328360050688) qz32) 226375608064910080 72057594037927936 Bool.false 268755 1048576 37 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 245689589 1048576 226375608064910080 72057594037927936 37 39168916276328360050688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 268755 1048576 39168916276328360050688 151115727451828646838272 556623778 2147483648 263299 263042 (ep193 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep195 := BSN.cos_dyadic_bound_f 556623778 2147483648 2 1 1048576 263299 ep192 ep62 ep192 ep192 ep63 ep192 1013549 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 556623778) qz288 0 1 ep192 ep62 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 556623778) qz289 0 1 ep192 ep63 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.sin_image qz54 qz332 Bool.false 245689589 1048576 195 262144 Bool.false 1013549 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 527614375521786699293 2251799813685248000 48857000019277164491 65760500000000000000000 245689589 1048576 195 262144 (ep191 rfl) rfl) (Enclosure.sfrac_false_div 245689589 1048576) (BSN.sin_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39168916276328360050688) qz32) 226375608064910080 72057594037927936 Bool.false 1013549 1048576 37 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 245689589 1048576 226375608064910080 72057594037927936 37 39168916276328360050688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1013549 1048576 39168916276328360050688 151115727451828646838272 556623778 2147483648 263299 263042 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep189 rfl rfl) rfl)

noncomputable def ep197 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.true 84968774535 1099511627776 32800367345403 144608868796727296 Bool.true 320440611193 1099511627776 32898323397077 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz54) 316157 1048576 1 1048576 268755 1048576 25908739 34477441024 84968774535 1099511627776 32800367345403 144608868796727296 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.true 268755 1048576 25908739 34477441024 268755 1048576 25908739 34477441024 (ep194 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 316157 1048576 1 1048576 1013549 1048576 25908739 34477441024 320440611193 1099511627776 32898323397077 144608868796727296 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.false 1013549 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.false 1013549 1048576 25908739 34477441024 1013549 1048576 25908739 34477441024 (ep196 rfl rfl) rfl)) rfl)

noncomputable def ep198 := @ep154 84968774535 1099511627776 32800367345403 144608868796727296 Bool.true 320440611193 1099511627776 32898323397077 144608868796727296 Bool.false 279809687819008184680448 2035883428609 1099511627776 470506837919143 144608868796727296 Bool.true 96635981755772011806720 175779826815 1099511627776 470795061192845 144608868796727296 (ep155 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep187 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep188 ep197) rfl rfl

noncomputable abbrev qz334 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz334))

noncomputable abbrev qz335 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz280 qz335)

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.true 97721791389 549755813888 15727506800721 72304434398363648 Bool.false 250089774885 1099511627776 31478757219093 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 12 qz17 rfl)

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz18)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz334) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz334) (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz336) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 131521 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz335 97714 1000 0 1 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 546759686018916851229 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000394563 131521000000000000000 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep203 := nat_lit 515465619503196454347436534246613143495008035760915520272877600340581987771201

noncomputable def ep204 := nat_lit 207965557871157110506127701644700477389491500690989836595821032841663603521

noncomputable def ep205 := nat_lit 1545980927393847048821297347336550029530245124281364581145441158956062636106561

noncomputable def ep206 := BSN.cos_dyadic_bound_f 1948717687 2147483648 3 2 1048576 263299 ep203 ep112 ep204 ep205 ep115 ep204 645674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1948717687) qz288 0 2 ep203 ep112 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1948717687) qz289 0 2 ep205 ep115 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 254604819) qz30)

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz57 qz337 Bool.false 254604819 1048576 195 262144 Bool.true 645674 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 546759686018916851229 2251799813685248000 48857000019277164491 65760500000000000000000 254604819 1048576 195 262144 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 254604819 1048576) (BSN.cos_reduce2 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137128816454485145550848) qz32) 226375608064910080 72057594037927936 Bool.false 645674 1048576 38 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 254604819 1048576 226375608064910080 72057594037927936 38 137128816454485145550848 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 645674 1048576 137128816454485145550848 151115727451828646838272 1948717687 2147483648 263299 263042 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := nat_lit 927671742659456692136980859482587897909102871169095144621903023786774247105345

noncomputable def ep209 := nat_lit 2429279762728690415513178044270781646131876914441749490464781352055046048965441

noncomputable def ep210 := BSN.sin_dyadic_bound_f 1948717687 2147483648 3 2 1048576 263299 ep208 ep170 ep204 ep209 ep172 ep204 826205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1948717687) qz283 0 2 ep208 ep170 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1948717687) qz284 0 2 ep209 ep172 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable def ep211 := @Enclosure.Real.IsNear.sin_image qz57 qz337 Bool.false 254604819 1048576 195 262144 Bool.true 826205 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 546759686018916851229 2251799813685248000 48857000019277164491 65760500000000000000000 254604819 1048576 195 262144 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 254604819 1048576) (BSN.sin_reduce2 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137128816454485145550848) qz32) 226375608064910080 72057594037927936 Bool.false 826205 1048576 38 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 254604819 1048576 226375608064910080 72057594037927936 38 137128816454485145550848 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 826205 1048576 137128816454485145550848 151115727451828646838272 1948717687 2147483648 263299 263042 (ep210 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep200 rfl rfl) rfl)

noncomputable def ep212 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.true 97721791389 549755813888 15727506800721 72304434398363648 Bool.false 250089774885 1099511627776 31478757219093 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz57) 302697 1048576 1 1048576 322837 524288 25908739 34477441024 97721791389 549755813888 15727506800721 72304434398363648 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.true 645674 1048576 25908739 34477441024 322837 524288 25908739 34477441024 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 302697 1048576 1 1048576 826205 1048576 25908739 34477441024 250089774885 1099511627776 31478757219093 144608868796727296 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.true 826205 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.true 826205 1048576 25908739 34477441024 826205 1048576 25908739 34477441024 (ep211 rfl rfl) rfl)) rfl)

noncomputable def ep213 := @ep152 97721791389 549755813888 15727506800721 72304434398363648 Bool.false 250089774885 1099511627776 31478757219093 144608868796727296 Bool.false 1011792505356726648700928 1840439845831 1099511627776 501961851520585 144608868796727296 Bool.false 81704651962395729592320 37154974035 549755813888 251136909205969 72304434398363648 (ep153 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep198 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep199 ep212) rfl rfl

noncomputable abbrev qz339 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz339))

noncomputable abbrev qz340 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz280 qz340)

noncomputable def ep214 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 233998221561 1099511627776 30245355160991 144608868796727296 Bool.false 48887055477 274877906944 7556991659515 36152217199181824 (BSN.cpow_neg_s_mk qz16 97714 1000 13 qz17 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz18)

noncomputable def ep215 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz339) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz339) (Real.sqrt qz341) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep216 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 131521 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep217 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz340 97714 1000 0 1 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 564371491516890652189 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 48450490295254733815808 18889465931478580854784 1000000000394563 131521000000000000000 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep218 := nat_lit 12448108952570970254663850909607700625

noncomputable def ep219 := BSN.sin_dyadic_bound_f 1878347085 2147483648 2 1 1048576 263299 ep218 ep58 ep218 ep218 ep59 ep218 804607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1878347085) qz283 0 1 ep218 ep58 ep218 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1878347085) qz284 0 1 ep218 ep59 ep218 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 262805955) qz30)

noncomputable def ep220 := @Enclosure.Real.IsNear.cos_image qz59 qz342 Bool.false 262805955 1048576 195 262144 Bool.false 804607 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 564371491516890652189 2251799813685248000 48857000019277164491 65760500000000000000000 262805955 1048576 195 262144 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 262805955 1048576) (BSN.cos_reduce3 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132176925518801707991040) qz32) 226375608064910080 72057594037927936 Bool.false 804607 1048576 39 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 262805955 1048576 226375608064910080 72057594037927936 39 132176925518801707991040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 804607 1048576 132176925518801707991040 151115727451828646838272 1878347085 2147483648 263299 263042 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep221 := nat_lit 444921513113905334200873719052769231985498998677113843621293406584698678190625

noncomputable def ep222 := nat_lit 154955416495077538181139611549072824677791367762611389005981536299625390625

noncomputable def ep223 := nat_lit 1334454628508725847526258877935209550307141413295816308085868256681496783790625

noncomputable def ep224 := BSN.cos_dyadic_bound_f 1878347085 2147483648 3 2 1048576 263299 ep221 ep112 ep222 ep223 ep115 ep222 672396 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1878347085) qz288 0 2 ep221 ep112 ep222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1878347085) qz289 0 2 ep223 ep115 ep222 rfl rfl rfl rfl) rfl rfl

noncomputable def ep225 := @Enclosure.Real.IsNear.sin_image qz59 qz342 Bool.false 262805955 1048576 195 262144 Bool.true 672396 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 564371491516890652189 2251799813685248000 48857000019277164491 65760500000000000000000 262805955 1048576 195 262144 (ep217 rfl) rfl) (Enclosure.sfrac_false_div 262805955 1048576) (BSN.sin_reduce3 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132176925518801707991040) qz32) 226375608064910080 72057594037927936 Bool.false 672396 1048576 39 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 262805955 1048576 226375608064910080 72057594037927936 39 132176925518801707991040 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 672396 1048576 132176925518801707991040 151115727451828646838272 1878347085 2147483648 263299 263042 (ep224 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep215 rfl rfl) rfl)

noncomputable def ep226 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 233998221561 1099511627776 30245355160991 144608868796727296 Bool.false 48887055477 274877906944 7556991659515 36152217199181824 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 290823 1048576 1 1048576 804607 1048576 25908739 34477441024 233998221561 1099511627776 30245355160991 144608868796727296 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 804607 1048576 25908739 34477441024 804607 1048576 25908739 34477441024 (ep220 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 290823 1048576 1 1048576 168099 262144 25908739 34477441024 48887055477 274877906944 7556991659515 36152217199181824 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.true 168099 262144 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.true 672396 1048576 25908739 34477441024 168099 262144 25908739 34477441024 (ep225 rfl rfl) rfl)) rfl)

noncomputable def ep227 := @ep149 233998221561 1099511627776 30245355160991 144608868796727296 Bool.false 48887055477 274877906944 7556991659515 36152217199181824 Bool.false ep150 32413094803 17179869184 66525900835197 18076108599590912 Bool.false 37089024467645409263616 134929084989 549755813888 266250892524999 72304434398363648 (ep151 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep213 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep214 ep226) rfl rfl

noncomputable abbrev qz344 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz344))

noncomputable abbrev qz345 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz280 qz345)

noncomputable def ep228 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 283820862381 1099511627776 29176274737871 144608868796727296 Bool.true 9517332523 137438953472 3634850910839 18076108599590912 (BSN.cpow_neg_s_mk qz16 97714 1000 14 qz17 rfl)

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz18)

noncomputable def ep229 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz344) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz344) (Real.sqrt qz346) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz346) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep230 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 131521 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz345 97714 1000 0 1 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 116135535481113262393 450359962737049600 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 49850353174629559828480 18889465931478580854784 1000000000394563 131521000000000000000 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep232 := nat_lit 100354890101267531979274418172748816

noncomputable def ep233 := BSN.cos_dyadic_bound_f 562839586 2147483648 2 1 1048576 263299 ep232 ep62 ep232 ep232 ep63 ep232 1012767 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 562839586) qz288 0 1 ep232 ep62 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 562839586) qz289 0 1 ep232 ep63 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135199557) qz516)

noncomputable def ep234 := @Enclosure.Real.IsNear.cos_image qz61 qz347 Bool.false 135199557 524288 195 262144 Bool.false 1012767 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 116135535481113262393 450359962737049600 48857000019277164491 65760500000000000000000 135199557 524288 195 262144 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 135199557 524288) (BSN.cos_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19803157441161822470144) qz287) 226375608064910080 72057594037927936 Bool.false 1012767 1048576 41 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 135199557 524288 226375608064910080 72057594037927936 41 19803157441161822470144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012767 1048576 19803157441161822470144 75557863725914323419136 562839586 2147483648 263299 263042 (ep233 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep235 := BSN.sin_dyadic_bound_f 562839586 2147483648 2 1 1048576 263299 ep232 ep58 ep232 ep232 ep59 ep232 271688 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 562839586) qz283 0 1 ep232 ep58 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 562839586) qz284 0 1 ep232 ep59 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable def ep236 := @Enclosure.Real.IsNear.sin_image qz61 qz347 Bool.false 135199557 524288 195 262144 Bool.false 271688 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 116135535481113262393 450359962737049600 48857000019277164491 65760500000000000000000 135199557 524288 195 262144 (ep231 rfl) rfl) (Enclosure.sfrac_false_div 135199557 524288) (BSN.sin_reduce0 qz347 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19803157441161822470144) qz287) 226375608064910080 72057594037927936 Bool.false 271688 1048576 41 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 135199557 524288 226375608064910080 72057594037927936 41 19803157441161822470144 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 271688 1048576 19803157441161822470144 75557863725914323419136 562839586 2147483648 263299 263042 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz348 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep229 rfl rfl) rfl)

noncomputable def ep237 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 283820862381 1099511627776 29176274737871 144608868796727296 Bool.true 9517332523 137438953472 3634850910839 18076108599590912 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz61) 280243 1048576 1 1048576 1012767 1048576 25908739 34477441024 283820862381 1099511627776 29176274737871 144608868796727296 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 1012767 1048576 25908739 34477441024 1012767 1048576 25908739 34477441024 (ep234 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 280243 1048576 1 1048576 33961 131072 25908739 34477441024 9517332523 137438953472 3634850910839 18076108599590912 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 33961 131072 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 271688 1048576 25908739 34477441024 33961 131072 25908739 34477441024 (ep236 rfl rfl) rfl)) rfl)

noncomputable def ep238 := @ep147 283820862381 1099511627776 29176274737871 144608868796727296 Bool.true 9517332523 137438953472 3634850910839 18076108599590912 Bool.false 40514579915499982815232 2358258929773 1099511627776 561383481419447 144608868796727296 Bool.false 13312303346598107152384 96859754897 549755813888 280790296168355 72304434398363648 (ep148 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep227 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep228 ep237) rfl rfl

noncomputable abbrev qz349 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz62 := (@Inv.inv Real Real.instInv (Real.sqrt qz349))

noncomputable abbrev qz350 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz63 := (@HMul.hMul Real Real Real qz267 qz280 qz350)

noncomputable def ep239 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)))) Bool.false 53336789223 274877906944 7040493845901 36152217199181824 Bool.true 187290772311 1099511627776 28149317671043 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 15 qz17 rfl)

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz18)

noncomputable def ep240 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz349) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz349) (Real.sqrt qz351) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz351) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep241 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 131521 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz350 97714 1000 0 1 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 595858285733284847133 2251799813685248000 48857000019277164491 65760500000000000000000 qz20 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 51153586820399524478976 18889465931478580854784 1000000000394563 131521000000000000000 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep243 := nat_lit 204756693023072302123875699882338777339992576624885206649146647043505337016576

noncomputable def ep244 := nat_lit 32830647248569333400874466622994793336565145856072064601371105529713008896

noncomputable def ep245 := nat_lit 614204417774719767704825350713770342433304599582943475818237198919456585031936

noncomputable def ep246 := BSN.cos_dyadic_bound_f 1547158938 2147483648 3 2 1048576 263299 ep243 ep112 ep244 ep245 ep115 ep244 788012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1547158938) qz288 0 2 ep243 ep112 ep244 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1547158938) qz289 0 2 ep245 ep115 ep244 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34683517) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep247 := @Enclosure.Real.IsNear.cos_image qz63 qz352 Bool.false 34683517 131072 195 262144 Bool.false 788012 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 595858285733284847133 2251799813685248000 48857000019277164491 65760500000000000000000 34683517 131072 195 262144 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 34683517 131072) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13608953939450233094144) qz299) 226375608064910080 72057594037927936 Bool.false 788012 1048576 42 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 34683517 131072 226375608064910080 72057594037927936 42 13608953939450233094144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 788012 1048576 13608953939450233094144 18889465931478580854784 1547158938 2147483648 263299 263042 (ep246 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep248 := nat_lit 5729803421459529740615799307758168336

noncomputable def ep249 := BSN.sin_dyadic_bound_f 1547158938 2147483648 2 1 1048576 263299 ep248 ep58 ep248 ep248 ep59 ep248 691771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1547158938) qz283 0 1 ep248 ep58 ep248 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1547158938) qz284 0 1 ep248 ep59 ep248 rfl rfl rfl rfl) rfl rfl

noncomputable def ep250 := @Enclosure.Real.IsNear.sin_image qz63 qz352 Bool.false 34683517 131072 195 262144 Bool.false 691771 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 595858285733284847133 2251799813685248000 48857000019277164491 65760500000000000000000 34683517 131072 195 262144 (ep242 rfl) rfl) (Enclosure.sfrac_false_div 34683517 131072) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13608953939450233094144) qz299) 226375608064910080 72057594037927936 Bool.false 691771 1048576 42 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 34683517 131072 226375608064910080 72057594037927936 42 13608953939450233094144 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 691771 1048576 13608953939450233094144 18889465931478580854784 1547158938 2147483648 263299 263042 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep240 rfl rfl) rfl)

noncomputable def ep251 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz63)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63))) Bool.false 53336789223 274877906944 7040493845901 36152217199181824 Bool.true 187290772311 1099511627776 28149317671043 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz63) 270741 1048576 1 1048576 197003 262144 25908739 34477441024 53336789223 274877906944 7040493845901 36152217199181824 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz63) Bool.false 788012 1048576 25908739 34477441024 197003 262144 25908739 34477441024 (ep247 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz63)) 270741 1048576 1 1048576 691771 1048576 25908739 34477441024 187290772311 1099511627776 28149317671043 144608868796727296 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz63) Bool.false 691771 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz63) Bool.false 691771 1048576 25908739 34477441024 691771 1048576 25908739 34477441024 (ep250 rfl rfl) rfl)) rfl)

noncomputable def ep252 := @ep145 53336789223 274877906944 7040493845901 36152217199181824 Bool.true 187290772311 1099511627776 28149317671043 144608868796727296 Bool.false 706877698586925869301760 2571606086665 1099511627776 589545456803051 144608868796727296 Bool.false 3534235807238957563904 6428737483 1099511627776 589729910007753 144608868796727296 (ep146 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep238 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep239 ep251) rfl rfl

noncomputable abbrev qz354 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt qz354))

noncomputable abbrev qz355 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz267 qz280 qz355)

noncomputable def ep253 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.false 25286051637 137438953472 3412906302475 18076108599590912 Bool.true 2907952299 17179869184 426486452245 2259513574948864 (BSN.cpow_neg_s_mk qz16 97714 1000 16 qz17 rfl)

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz18)

noncomputable def ep254 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz354) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz354) (Real.sqrt qz356) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz356) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep255 := BSN.log_dyadic_bound 0 32 1 0 1 524288 131521 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep256 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz355 97714 1000 0 1 3121657384082679 1125899906842624 250000000131521 32880250000000000000 152514814814127447903 562949953421312000 12214250006425721497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 52372720210750067441664 18889465931478580854784 1000000000526084 131521000000000000000 3121657384082679 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep257 := nat_lit 232579174220602483119817097452135545857275190764476720832094267914586334016641

noncomputable def ep258 := nat_lit 42357074751347725136292231703542545304873886097391379974743179597326431361

noncomputable def ep259 := nat_lit 697652808512304753909178707892999552481215824521235379736333317384564349187201

noncomputable def ep260 := BSN.cos_dyadic_bound_f 1597223697 2147483648 3 2 1048576 263299 ep257 ep112 ep258 ep259 ep115 ep258 771672 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1597223697) qz288 0 2 ep257 ep112 ep258 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1597223697) qz289 0 2 ep259 ep115 ep258 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 284080979) qz30)

noncomputable def ep261 := @Enclosure.Real.IsNear.cos_image qz65 qz357 Bool.false 284080979 1048576 781 1048576 Bool.false 771672 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 152514814814127447903 562949953421312000 12214250006425721497 16440125000000000000000 284080979 1048576 781 1048576 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 284080979 1048576) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112394625767624228732928) qz32) 226375608064910080 72057594037927936 Bool.false 771672 1048576 43 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 284080979 1048576 226375608064910080 72057594037927936 43 112394625767624228732928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 771672 1048576 112394625767624228732928 151115727451828646838272 1597223697 2147483648 263299 263042 (ep260 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep262 := nat_lit 6508231307455791797128000074415100481

noncomputable def ep263 := BSN.sin_dyadic_bound_f 1597223697 2147483648 2 1 1048576 263299 ep262 ep58 ep262 ep262 ep59 ep262 709952 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1597223697) qz283 0 1 ep262 ep58 ep262 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1597223697) qz284 0 1 ep262 ep59 ep262 rfl rfl rfl rfl) rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.sin_image qz65 qz357 Bool.false 284080979 1048576 781 1048576 Bool.false 709952 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 152514814814127447903 562949953421312000 12214250006425721497 16440125000000000000000 284080979 1048576 781 1048576 (ep256 rfl) rfl) (Enclosure.sfrac_false_div 284080979 1048576) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 112394625767624228732928) qz32) 226375608064910080 72057594037927936 Bool.false 709952 1048576 43 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 284080979 1048576 226375608064910080 72057594037927936 43 112394625767624228732928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 709952 1048576 112394625767624228732928 151115727451828646838272 1597223697 2147483648 263299 263042 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz358 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep254 rfl rfl) rfl)

noncomputable def ep265 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.false 25286051637 137438953472 3412906302475 18076108599590912 Bool.true 2907952299 17179869184 426486452245 2259513574948864 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz65) 262143 1048576 1 1048576 96459 131072 103766477 137909764096 25286051637 137438953472 3412906302475 18076108599590912 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.false 771672 1048576 103766477 137909764096 96459 131072 103766477 137909764096 (ep261 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 262143 1048576 1 1048576 11093 16384 103766477 137909764096 2907952299 17179869184 426486452245 2259513574948864 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.false 11093 16384 103766477 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.false 709952 1048576 103766477 137909764096 11093 16384 103766477 137909764096 (ep264 rfl rfl) rfl)) rfl)

noncomputable def ep266 := @ep143 25286051637 137438953472 3412906302475 18076108599590912 Bool.true 2907952299 17179869184 426486452245 2259513574948864 Bool.false 381241157088888794120192 2773894499761 1099511627776 616848707222851 144608868796727296 Bool.true 3086882496792234033152 179680209653 1099511627776 617025042951433 144608868796727296 (ep144 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep252 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep253 ep265) rfl rfl

theorem EMRow29.d7 : Enclosure.Complex.IsNear qz39 Bool.false 2773894499761 1099511627776 616848707222851 144608868796727296 Bool.true 179680209653 1099511627776 617025042951433 144608868796727296 := ep142 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow29.d8 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow29.d9 : @Eq Nat (Nat.pow 20 1) 20 := @Eq.refl Nat 20

noncomputable def ep267 := nat_lit 1732334455917454224036411737703

noncomputable def ep268 := nat_lit 595049324168943755503599616000

noncomputable def ep269 := nat_lit 2217627267772515841549905753189484582669

noncomputable def ep270 := nat_lit 380842050640698523565999631649076150272000

noncomputable abbrev qz539 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz517 := qz539

noncomputable abbrev qz359 := qz517

noncomputable abbrev qz66 := qz359

noncomputable abbrev qz518 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz360 := qz518

noncomputable abbrev qz67 := qz360

noncomputable abbrev qz540 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz541 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz519 := (@HAdd.hAdd Complex Complex Complex qz537 (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz538) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz361 := qz519

noncomputable abbrev qz68 := (Complex.Stirling.logGammaStirling 1 qz361)

noncomputable abbrev qz520 := (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz538) (2 : Complex))))

noncomputable abbrev qz362 := qz520

noncomputable abbrev qz69 := qz362

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz363 := (@instHSub Real Real.instSub)

noncomputable def ep271 := Complex.re (@HMul.hMul Complex Complex Complex qz66 (Complex.exp (@HMul.hMul Complex Complex Complex qz66 Complex.I ↑(@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70))) (zetaApproximant qz5 1 20))

noncomputable def ep272 := @Enclosure.Real.IsNear.of_eq ep271 (@HSub.hSub Real Real Real qz363 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20))))

noncomputable def ep273 := nat_lit 346461941104871196028041556059

noncomputable def ep274 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20))) ep273

noncomputable def ep275 := nat_lit 119009864833788751100719923200

noncomputable def ep276 := nat_lit 2208761160058799119642738539705726562861

noncomputable def ep277 := nat_lit 18595291380279492359487488000

noncomputable def ep278 := nat_lit 277065866053647559598975421367438119

noncomputable def ep279 := nat_lit 11901314082521828861437488489033629696000

noncomputable def ep280 := nat_lit 6442652795176600153654943808367231208674592599313272012800

noncomputable def ep281 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.re (zetaApproximant qz5 1 20)) 1048575 1048576 41688565

noncomputable def ep282 := nat_lit 8260304248739269866915613

noncomputable def ep283 := nat_lit 2837416287274092462080000

noncomputable def ep284 := nat_lit 67908400246024009437848598091

noncomputable def ep285 := nat_lit 13807653618187308844093276160000

noncomputable def ep286 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) Bool.true 1048575 1048576 41688565

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11117831) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep287 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) qz364 Bool.false 11117831 131072 309

noncomputable def ep288 := nat_lit 30357597672445391341020997

noncomputable def ep289 := nat_lit 103432323072000000000000000000

noncomputable def ep290 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) Bool.false 2292034597629886239391 27021597764222976000 ep288 ep289

noncomputable def ep291 := nat_lit 11080433181445391341020997

noncomputable def ep292 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70 3803299997192560874143 27021597764222976000 ep291 ep289 3665300997 65536000

noncomputable def ep293 := nat_lit 150210779390272224584728576000

noncomputable def ep294 := nat_lit 3374094232915061911384267

noncomputable def ep295 := nat_lit 17238720512000000000000000000

noncomputable def ep296 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 69173231018454923469 900719925474099200 ep294 ep295 Bool.false 3803299997192560874143 27021597764222976000

noncomputable def ep297 := nat_lit 3308558232725435985752267

noncomputable def ep298 := nat_lit 10294001181341959017948997

noncomputable def ep299 := @Enclosure.Complex.IsNear.subLitP qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 62167309589868498469 900719925474099200 ep297 ep295 Bool.false 3887361423312567818143 27021597764222976000 ep298

noncomputable def ep300 := nat_lit 311528537438726828850715421388570624

noncomputable def ep301 := nat_lit 1070533778133414102232816486142967808

noncomputable abbrev qz542 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz521 := qz542

noncomputable abbrev qz365 := (@HSub.hSub Complex Complex Complex qz518 qz519 qz521)

noncomputable abbrev qz366 := (Complex.log qz519)

noncomputable abbrev qz71 := (@HSub.hSub Complex Complex Complex qz360 (@HMul.hMul Complex Complex Complex qz359 qz365 qz366) qz361)

noncomputable abbrev qz367 := qz521

noncomputable abbrev qz72 := (@HMul.hMul Complex Complex Complex qz359 qz367 ↑(Real.log qz271))

noncomputable abbrev qz522 := qz541

noncomputable abbrev qz368 := qz522

noncomputable abbrev qz73 := qz368

noncomputable abbrev qz74 := (@instHMul Nat instMulNat)

noncomputable abbrev qz523 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz369 := qz523

noncomputable abbrev qz75 := qz369

noncomputable abbrev qz76 := qz361

noncomputable abbrev qz370 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz77 := qz370

noncomputable abbrev qz371 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz78 := qz371

noncomputable abbrev qz372 := (@instHSub Int Int.instSub)

noncomputable abbrev qz373 := (@instHMul Int Int.instMul)

noncomputable def ep302 := @Enclosure.Complex.IsNear.of_eq qz68 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz71 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k)))))) Bool.true 62167309589868498469

noncomputable def ep303 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz71 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) Bool.true 62167380191879941669 900719925474099200

noncomputable def ep304 := nat_lit 2136052492550338990919848558592

noncomputable def ep305 := nat_lit 1335687214468759261176500836106240

noncomputable def ep306 := @ep303 100969138415131798369 526084000000000000000000 Bool.false 51832098871273896317 360287970189639680 26178500070913098217 263042000000000000000000 Bool.false 2693253 34359738368 3 34359738368 Bool.true 43861420607 25769803776000 48857 25769803776000 Bool.true ep304 62167309589868498469 900719925474099200 ep297 ep295 Bool.false ep305

noncomputable def ep307 := @Enclosure.Complex.IsNear.addLitP qz71 qz72 Bool.true 62995085673322040869 900719925474099200 49732000008957500747 263042000000000000000000

noncomputable def ep308 := nat_lit 8148402856510087714439168

noncomputable def ep309 := @ep307 Bool.false 51832098871273896317 360287970189639680 26178500070913098217 263042000000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep308 62167380191879941669 900719925474099200 100969138415131798369 526084000000000000000000 Bool.false 51832098871273896317 51832098871273896317 360287970189639680

noncomputable abbrev qz79 := (@HMul.hMul Complex Complex Complex qz359 qz365 qz366)

noncomputable def ep310 := @Enclosure.Complex.IsNear.subLitP qz79 qz76 Bool.true 60968465841005317669 900719925474099200 49732000008957500747 263042000000000000000000 Bool.false 1735867205770728054069

noncomputable def ep311 := nat_lit 5183209887127389631700000

noncomputable def ep312 := @ep310 9007199254740992000 26178500070913098217 263042000000000000000000 Bool.false 9000 4000 0 1 Bool.false 195428 4000 0 1 Bool.true 251980342693288163476000 62995085673322040869 900719925474099200 49732000008957500747 263042000000000000000000 Bool.false ep311 51832098871273896317 360287970189639680 26178500070913098217 263042000000000000000000

noncomputable abbrev qz80 := qz365

noncomputable abbrev qz81 := qz366

noncomputable def ep313 := @Enclosure.Complex.IsNear.mul qz80 qz81 Bool.true 60968465841005317669 900719925474099200 49732000008957500747 263042000000000000000000 Bool.false 1735867205770728054069 9007199254740992000 26178500070913098217

noncomputable abbrev qz82 := (Complex.re qz365)

noncomputable abbrev qz83 := (Complex.re qz366)

noncomputable abbrev qz84 := (Complex.im qz365)

noncomputable abbrev qz85 := (Complex.im qz366)

noncomputable def ep314 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz82 qz83) (@HMul.hMul Real Real Real qz0 qz84 qz85) 245263305766188619 36028797018963968 3500000010127117 1052168000000000000000 8387506060645004143 112589990684262400

noncomputable def ep315 := nat_lit 274577560042902362679354015638093824

noncomputable def ep316 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz83 7000 4000 0 1 35037615109455517 9007199254740992 500000001446731 263042000000000000000

noncomputable def ep317 := @Enclosure.Complex.IsNear.re_isNear qz80 Bool.false 7000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable abbrev qz374 := (Enclosure.sfrac Bool.false 195428 4000)

noncomputable abbrev qz86 := qz374

noncomputable def ep318 := @Enclosure.Complex.IsNear.of_eq qz80 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz86) Bool.false 7000 4000 0 1 Bool.false 195428 4000 0

noncomputable abbrev qz375 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz87 := qz375

noncomputable abbrev qz376 := (Complex.log (Complex.mk qz87 qz86))

noncomputable def ep319 := @Enclosure.Complex.IsNear.of_eq qz81 qz376 Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep320 := nat_lit 382058658693617442584662624042157102728151040

noncomputable def ep321 := nat_lit 767506868480980504927670159888922287013888

noncomputable def ep322 := nat_lit 2755390195763546071627123612402817630208

noncomputable def ep323 := BSN.log_dyadic_bound 5505103184 71041103184 3 2 ep320 1048576 263042 ep321 ep322 162838 76546206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5505103184) (BSN.artanhQ 71041103184) 0 2 ep321 ep320 ep322 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz88 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz377 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz524 := (Real.log (Enclosure.sfrac Bool.false 38273103184 16000000))

noncomputable def ep324 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz524 1 2 0 1 35037615109455517 4503599627370496 500000001446731 131521000000000000000 35037615109455517 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 38273103184 16000000 35037615109455517 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38273103184) qz378)) Bool.false 293916818408099425550336 37778931862957161709568 1000000002893462 263042000000000000000 35037615109455517 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 38273103184 16000000 11 76546206368 65536000000 162838 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep323 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep325 := BSN.arctan_dyadic_bound_f 9000 195428 1 0 1048576 263042 0 1 1 0 1 1 48255 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz89 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz90 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz377 BSN.pi_near_15 rfl)

noncomputable abbrev qz379 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 195428)))

noncomputable def ep326 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz379 884279719003555 562949953421312 1 2000000000000000 48255 1048576 1 263042 900069340631526277120 858373013144995 562949953421312 1000000000131521 263042000000000000000 qz90 (ep325 rfl) rfl rfl

noncomputable abbrev qz380 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195428) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep327 := @Enclosure.Complex.IsNear.re_isNear qz81 Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (ep319 (@congrArg Complex Complex qz76 (Complex.mk qz87 qz86) Complex.log (BSN.w_shift_mk qz16 Bool.false 97714 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz376 Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz376) (@HMul.hMul Real Real Real qz0 qz88 qz524) Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 9000 195428 4000 38273103184 16000000 rfl rfl rfl) (ep324 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz376) qz380 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 9000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz380 (@HSub.hSub Real Real Real qz363 qz89 qz379) Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 195428 9000 rfl rfl) ep326))))

noncomputable def ep328 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz85 195428 4000 0 1 858373013144995 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep329 := @Enclosure.Complex.IsNear.im_isNear qz80 Bool.false 7000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable def ep330 := @Enclosure.Complex.IsNear.im_isNear qz81 Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (ep319 (@congrArg Complex Complex qz76 (Complex.mk qz87 qz86) Complex.log (BSN.w_shift_mk qz16 Bool.false 97714 1000 2 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz376 Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz376) (@HMul.hMul Real Real Real qz0 qz88 qz524) Bool.false 35037615109455517 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 9000 195428 4000 38273103184 16000000 rfl rfl rfl) (ep324 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz376) qz380 Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 9000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz380 (@HSub.hSub Real Real Real qz363 qz89 qz379) Bool.false 858373013144995 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 195428 9000 rfl rfl) ep326))))

noncomputable abbrev qz381 := (Enclosure.Real.IsNear.const Bool.false 195428 4000)

noncomputable abbrev qz91 := (@ep318 1 (BSN.w_sub_half_mk qz280 Bool.false 97714 1000 2 qz282 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz374 Bool.false 7000 4000 0 1 Bool.false 195428 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz381))

noncomputable def ep331 := @ep314 48857000006425721497 263042000000000000000000 ep315 60968465841005317669 900719925474099200 49732000008957500747 263042000000000000000000 (@ep316 245263305766188619 36028797018963968 3500000010127117 1052168000000000000000 (ep317 qz91) ep327 rfl) (@ep328 8387506060645004143 112589990684262400 48857000006425721497 263042000000000000000000 (ep329 qz91) ep330 rfl) rfl

noncomputable def ep332 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz82 qz85) (@HMul.hMul Real Real Real qz0 qz84 qz83) 6008611092014965 2251799813685248 7000000000920647 1052168000000000000000 1711832761402668194069 9007199254740992000

noncomputable def ep333 := nat_lit 3908825450536857484046407946691674112

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz82 qz85 7000 4000 0 1 858373013144995 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep335 := @Enclosure.Real.IsNear.mulLit_ff qz84 qz83 195428 4000 0 1 35037615109455517 9007199254740992 500000001446731 263042000000000000000

noncomputable def ep336 := @ep332 24428500070682936467 263042000000000000000000 ep333 1735867205770728054069 9007199254740992000 26178500070913098217 263042000000000000000000 (@ep334 6008611092014965 2251799813685248 7000000000920647 1052168000000000000000 (ep317 qz91) ep330 rfl) (@ep335 1711832761402668194069 9007199254740992000 24428500070682936467 263042000000000000000000 (ep329 qz91) ep327 rfl) rfl

noncomputable def ep337 := @Enclosure.Complex.IsNear.of_eq qz76 (Complex.mk qz87 qz86) Bool.false 9000 4000 0 1 Bool.false 195428 4000 0 1 (BSN.w_shift_mk qz16 Bool.false 97714 1000 2 qz17 rfl)

noncomputable abbrev qz382 := (ep337 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 195428 4000) Bool.false 9000 4000 0 1 Bool.false 195428 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 195428 4000)))

noncomputable abbrev qz92 := qz382

noncomputable def ep338 := ep312 (@ep313 263042000000000000000000 (ep331 rfl) (ep336 rfl)) qz92 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz93 := qz367

noncomputable def ep339 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz93) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz93) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep340 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz93) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz94 := (@Enclosure.Complex.IsNear.of_eq qz367 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz278) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz278 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz377 qz291))

noncomputable def ep341 := ep340 (@Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow29.d4)

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz93) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep343 := ep342 (@Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep344 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz93) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz93) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz93) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep346 := ep345 (@Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz13 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz13 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep347 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz93) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep348 := ep347 (@Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz94) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMRow29.d4)

noncomputable def ep349 := @ep309 26178500070913098217 263042000000000000000000 (ep338 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz93 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep339 131072 3 1048576 (ep341 rfl) (ep343 rfl) rfl rfl) (@ep344 1 0 1 (ep346 rfl) (ep348 rfl) rfl rfl))

noncomputable abbrev qz95 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz383 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz96 := (@HMul.hMul Complex Complex Complex qz359 (@HMul.hMul Complex Complex Complex qz359 (2 : Complex) qz383) (@HSub.hSub Complex Complex Complex qz360 (@HMul.hMul Complex Complex Complex qz359 (2 : Complex) qz383) (1 : Complex)))

noncomputable abbrev qz384 := (@HPow.hPow Complex Int Complex qz523 qz519 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz97 := qz384

noncomputable def ep350 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97)) Bool.false 2693253 34359738368 3 34359738368

noncomputable def ep351 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97) Bool.false 0 1 0 1 Bool.false

noncomputable def ep352 := @ep351 0 1 0 1 Bool.false 2693253 34359738368 3 34359738368 Bool.true 43861420607 25769803776000 48857 25769803776000 Bool.false 2693253 2693253 34359738368 3 34359738368 Bool.true 43861420607 43861420607 25769803776000 48857

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz76 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep354 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz97 Bool.false 2693253 34359738368 3 34359738368 Bool.true 43861420607 25769803776000 48857 25769803776000

noncomputable abbrev qz98 := (Complex.re qz384)

noncomputable abbrev qz99 := (Complex.im qz384)

noncomputable def ep355 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99) 2693253 34359738368 3 34359738368 0 1 0

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98 1 12 0 1 8079759 8589934592 9 8589934592 2693253

noncomputable def ep357 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz385 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz13 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep358 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep357 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz385)

noncomputable def ep359 := @Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 8079759 8589934592 9 8589934592 Bool.true 43861420607 2147483648000 48857 2147483648000

noncomputable abbrev qz525 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz386 := (@HPow.hPow Complex Nat Complex qz525 qz519 1)

noncomputable abbrev qz100 := (@Inv.inv Complex Complex.instInv qz386)

noncomputable def ep360 := @Enclosure.Complex.IsNear.of_eq qz97 qz100 Bool.false 8079759 8589934592 9 8589934592 Bool.true 43861420607 2147483648000 48857

noncomputable def ep361 := @Enclosure.Complex.IsNear.of_parts qz100 Bool.false 8079759 8589934592 9 8589934592 Bool.true 43861420607 2147483648000 48857

noncomputable abbrev qz101 := (Complex.re qz386)

noncomputable abbrev qz102 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz103 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz104 := qz386

noncomputable def ep362 := @Enclosure.Real.IsNear.mulLit_ff qz101 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) 9000 4000 0 1 897751 2147483648 1 2147483648

noncomputable def ep363 := @Enclosure.Complex.IsNear.re_isNear qz104 Bool.false 9000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable def ep364 := @Enclosure.Complex.IsNear.of_eq qz104 qz76 Bool.false 9000 4000 0 1 Bool.false 195428 4000 0

noncomputable def ep365 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) Bool.false 897751 2147483648 1 2147483648 897751 2147483648 1

noncomputable abbrev qz105 := (Complex.im qz386)

noncomputable abbrev qz387 := (@instHAdd Real Real.instAdd)

noncomputable def ep366 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104) (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 qz101 qz101) (@HMul.hMul Real Real Real qz0 qz105 qz105)) Bool.false 2392068949 1000000 0 1

noncomputable def ep367 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz101 qz101) (@HMul.hMul Real Real Real qz0 qz105 qz105) 81 16 0 1 2387006449 1000000

noncomputable def ep368 := @Enclosure.Real.IsNear.mulLit_ff qz101 qz101 9000 4000 0 1 9000 4000 0 1

noncomputable def ep369 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 195428 4000 0 1 195428 4000 0 1

noncomputable def ep370 := @Enclosure.Complex.IsNear.im_isNear qz104 Bool.false 9000 4000 0 1 Bool.false 195428 4000 0 1

noncomputable abbrev qz106 := (ep363 (@ep364 1 (BSN.pow_one_c qz361) qz382))

noncomputable abbrev qz107 := (ep370 (@ep364 1 (BSN.pow_one_c qz361) qz382))

noncomputable def ep371 := @ep367 0 1 38273103184 2392068949 1000000 0 1 (@ep368 81 16 0 1 qz106 qz106 rfl) (@ep369 2387006449 1000000 0 1 qz107 qz107 rfl)

noncomputable def ep372 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104) 2392068949 1000000 0 1 448875 448876 1073741824 (ep366 (Enclosure.Complex.normSq_eq_mul_add_mul qz104) (ep371 rfl rfl)) rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.of_eq (Complex.re qz100) (@HMul.hMul Real Real Real qz0 qz101 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104))) Bool.false 8079759 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz104) (@ep362 8079759 8589934592 9 8589934592 qz106 (@ep365 2147483648 (ep372 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep374 := @Enclosure.Real.IsNear.of_eq (Complex.im qz100) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz105) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104))) Bool.true 43861420607 2147483648000 48857 2147483648000 (Enclosure.Complex.inv_im_eq_mul qz104)

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz105) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz104)) 195428 4000 0 1 897751 2147483648 1

noncomputable def ep376 := @ep375 2147483648 43861420607 2147483648000 48857 2147483648000 (@Enclosure.Real.IsNear.neg qz105 Bool.false 195428 4000 0 1 qz107) (@ep365 2147483648 (ep372 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99 0 1 0 1 43861420607 2147483648000 48857 2147483648000 0

noncomputable def ep378 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep357 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz385)

noncomputable def ep379 := @Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 8079759 8589934592 9 8589934592 Bool.true 43861420607 2147483648000 48857 2147483648000

noncomputable abbrev qz108 := (@ep360 2147483648000 (BSN.zpow_one_sub_two_mul qz361 1 1 rfl rfl) (@ep361 2147483648000 ep373 (ep374 ep376)))

noncomputable def ep380 := @ep355 1 2693253 2693253 34359738368 3 34359738368 (@ep356 34359738368 3 34359738368 ep358 (ep359 qz108) rfl) (@ep377 1 0 1 ep378 (ep379 qz108) rfl) rfl

noncomputable def ep381 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98) 43861420607 25769803776000 48857 25769803776000 0 1 0

noncomputable def ep382 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz99 1 12 0 1 43861420607 2147483648000 48857 2147483648000 43861420607

noncomputable def ep383 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz98 0 1 0 1 8079759 8589934592 9 8589934592 0

noncomputable def ep384 := @ep381 1 43861420607 43861420607 25769803776000 48857 25769803776000 (@ep382 25769803776000 48857 25769803776000 ep358 (ep379 qz108) rfl) (@ep383 1 0 1 ep378 (ep359 qz108) rfl) rfl

noncomputable abbrev qz109 := (@Enclosure.Complex.IsNear.mk qz278 qz278 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz291 qz291)

noncomputable def ep385 := @ep352 25769803776000 (@ep353 0 1 0 1 (BSN.stirling_sum_base qz76) qz109) (ep354 (ep380 rfl) (ep384 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep386 := @ep306 3887361423312567818143 27021597764222976000 ep298 ep289 (ep349 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep350 Bool.true 43861420607 25769803776000 48857 25769803776000 (BSN.stirling_sum_succ qz76 0 1 rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep387 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz16 2) Bool.false 35029607142932125 4503599627370496 500000001446731 131521000000000000000 Bool.false 875639855416739 281474976710656

noncomputable abbrev qz110 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz362 qz383))

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 1) qz110) Bool.false 35029607142932125 4503599627370496 500000001446731 131521000000000000000 Bool.false 875639855416739 281474976710656 1000000000131521 131521000000000000000

noncomputable def ep389 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 1) qz110 Bool.false 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000 Bool.false

noncomputable def ep390 := nat_lit 631037302703375932657380622336000

noncomputable def ep391 := nat_lit 985882831641395188457208283136

noncomputable abbrev qz111 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz362 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep392 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz16 0) qz111) Bool.false 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep393 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz16 0) qz111 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz388 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz86))

noncomputable def ep394 := @Enclosure.Complex.IsNear.of_eq qz111 qz388 Bool.false 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep395 := nat_lit 380340605266516854014639895064236283528151040

noncomputable def ep396 := nat_lit 743613218150638736155534746811152047013888

noncomputable def ep397 := nat_lit 2598682763013786156674078108238977630208

noncomputable def ep398 := BSN.log_dyadic_bound 5425103184 70961103184 3 2 ep395 1048576 263042 ep396 ep397 160644 76386206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5425103184) (BSN.artanhQ 70961103184) 0 2 ep396 ep395 ep397 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 38193103184 16000000)) 1 2 0 1 35028191951208093 4503599627370496 500000001446731 131521000000000000000 35028191951208093 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 38193103184 16000000 35028191951208093 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38193103184) qz378)) Bool.false 293837771227439818604544 37778931862957161709568 1000000002893462 263042000000000000000 35028191951208093 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 38193103184 16000000 11 76386206368 65536000000 160644 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep400 := BSN.arctan_dyadic_bound_f 1000 195428 1 0 1048576 263042 0 1 1 0 1 1 5365 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz390 := (@Nat.cast Real Real.instNatCast 195428)

noncomputable def ep401 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz390)) 884279719003555 562949953421312 1 2000000000000000 5365 1048576 1 263042 924214264133766348800 881399406560675 562949953421312 1000000000131521 263042000000000000000 qz90 (ep400 rfl) rfl rfl

noncomputable abbrev qz112 := (@HAdd.hAdd Complex Complex Complex qz273 qz362 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz391 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz86)

noncomputable def ep402 := @ep393 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000 Bool.false 35028191951208093 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 881399406560675 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz16 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz16) qz109) (ep394 (@congrArg Complex Complex qz112 qz391 Complex.log (BSN.w_shift_mk qz16 Bool.false 97714 1000 0 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz388 Bool.false 35028191951208093 9007199254740992 500000001446731 263042000000000000000 Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz388) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 38193103184 16000000))) Bool.false 35028191951208093 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 1000 195428 4000 38193103184 16000000 rfl rfl rfl) (ep399 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz388) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz390 qz389)) Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 1000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz390 qz389)) (@HSub.hSub Real Real Real qz363 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz390))) Bool.false 881399406560675 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 195428 1000 rfl rfl) ep401)))) rfl rfl

noncomputable abbrev qz392 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz86))

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq qz110 qz392 Bool.false 35031022334656157 9007199254740992 500000001446731 263042000000000000000 Bool.false 869880304272803 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep404 := nat_lit 380855411607909288384763990695852529288151040

noncomputable def ep405 := nat_lit 750736101048832415598352404462483119013888

noncomputable def ep406 := nat_lit 2644973844615046290231379407488129630208

noncomputable def ep407 := BSN.log_dyadic_bound 5449103184 70985103184 3 2 ep404 1048576 263042 ep405 ep406 161303 76434206368 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5449103184) (BSN.artanhQ 70985103184) 0 2 ep405 ep404 ep406 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep408 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 38217103184 16000000)) 1 2 0 1 35031022334656157 4503599627370496 500000001446731 131521000000000000000 35031022334656157 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 38217103184 16000000 35031022334656157 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38217103184) qz378)) Bool.false 293861514204675315859456 37778931862957161709568 1000000002893462 263042000000000000000 35031022334656157 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 38217103184 16000000 11 76434206368 65536000000 161303 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep407 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep409 := BSN.arctan_dyadic_bound_f 5000 195428 1 0 1048576 263042 0 1 1 0 1 1 26821 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 195428) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 195428) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep410 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz393 qz390)) 884279719003555 562949953421312 1 2000000000000000 26821 1048576 1 263042 912135609933158678528 869880304272803 562949953421312 1000000000131521 263042000000000000000 qz90 (ep409 rfl) rfl rfl

noncomputable abbrev qz113 := (@HAdd.hAdd Complex Complex Complex qz273 qz362 qz383)

noncomputable abbrev qz394 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz86)

noncomputable def ep411 := @ep389 35031022334656157 9007199254740992 500000001446731 263042000000000000000 Bool.false 869880304272803 562949953421312 1000000000131521 263042000000000000000 Bool.false ep390 35029607142932125 4503599627370496 500000001446731 131521000000000000000 Bool.false ep391 875639855416739 281474976710656 1000000000131521 131521000000000000000 (ep392 (BSN.log_sum_c_succ qz16 0 1 rfl) (ep402 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep403 (@congrArg Complex Complex qz113 qz394 Complex.log (BSN.w_shift_mk qz16 Bool.false 97714 1000 1 qz17 rfl)) (@Enclosure.Complex.IsNear.of_parts qz392 Bool.false 35031022334656157 9007199254740992 500000001446731 263042000000000000000 Bool.false 869880304272803 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz392) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 38217103184 16000000))) Bool.false 35031022334656157 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 5000 195428 4000 38217103184 16000000 rfl rfl rfl) (ep408 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz392) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz390 qz393)) Bool.false 869880304272803 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 5000 195428 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz390 qz393)) (@HSub.hSub Real Real Real qz363 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz393 qz390))) Bool.false 869880304272803 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 195428 5000 rfl rfl) ep410)))) rfl rfl

noncomputable def ep412 := @ep299 ep289 Bool.false 35029607142932125 4503599627370496 500000001446731 131521000000000000000 Bool.false 875639855416739 281474976710656 1000000000131521 131521000000000000000 Bool.true ep300 69173231018454923469 900719925474099200 ep294 ep295 Bool.false ep301 3803299997192560874143 27021597764222976000 ep291 ep289 (@ep302 900719925474099200 ep297 ep295 Bool.false 3887361423312567818143 27021597764222976000 ep298 ep289 (BSN.logGammaStirling_unfold 1 qz76) (ep386 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep387 1000000000131521 131521000000000000000 (BSN.log_sum_c_eq qz16 2) (ep388 (BSN.log_sum_c_succ qz16 1 2 rfl) (ep411 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz114 := (@HDiv.hDiv Real Real Real qz270 qz280 (2 : Real))

noncomputable def ep413 := @Enclosure.Real.IsNear.mulLit_ff qz114 (Real.log Real.pi) 97714 2000 0 1 75021 65536 1 262144 3665300997 65536000 48857 262144000 (@Enclosure.Real.IsNear.of_eq qz114 (Enclosure.sfrac Bool.false 97714 2000) Bool.false 97714 2000 0 1 (BSN.t_half_eq qz16 Bool.false 97714 1000 qz17) (Enclosure.Real.IsNear.const Bool.false 97714 2000)) EMRow29.d5 rfl

noncomputable def ep414 := @ep292 48857 262144000 ep293 2292034597629886239391 27021597764222976000 ep288 ep289 (@ep296 ep291 ep289 (ep412 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep413 rfl rfl

noncomputable def ep415 := nat_lit 8329464546849436028407222082400943876981133444491658792463802745407228196223105

noncomputable def ep416 := nat_lit 16706588377569694798516776694490628974881987110392523095094407708112157735041

noncomputable def ep417 := nat_lit 21788215527232457711392744958306630088038873899299423228584568625491511306156161

noncomputable def ep418 := BSN.sin_dyadic_bound_f 3371793519 2147483648 3 2 1048576 263299 ep415 ep170 ep416 ep417 ep172 ep416 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3371793519) qz283 0 2 ep415 ep170 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3371793519) qz284 0 2 ep417 ep172 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable def ep419 := @ep287 1048576 Bool.true 1048575 1048576 1 131521 (@ep290 11117831 131072 309 1048576 ep414 rfl) (Enclosure.sfrac_false_div 11117831 131072) (BSN.cos_reduce1 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29658609445534382948352) qz299) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 13 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 11117831 131072 226375608064910080 72057594037927936 13 29658609445534382948352 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 29658609445534382948352 18889465931478580854784 3371793519 2147483648 263299 263042 (ep418 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep420 := nat_lit 16979407142760569751225629493

noncomputable def ep421 := nat_lit 3451913404546827211023319040000

noncomputable abbrev qz115 := qz274

noncomputable abbrev qz116 := qz275

noncomputable abbrev qz526 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable abbrev qz395 := (@HPow.hPow Complex Complex Complex qz511 qz526 qz512)

noncomputable abbrev qz117 := qz395

noncomputable abbrev qz396 := qz526

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz368 qz396 (@HSub.hSub Complex Complex Complex qz360 qz272 (1 : Complex))) qz367)

noncomputable abbrev qz119 := (@instHSub Nat instSubNat)

noncomputable abbrev qz397 := qz525

noncomputable abbrev qz120 := qz397

noncomputable abbrev qz121 := qz396

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (@HMul.hMul Complex Complex Complex qz66 qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) Bool.false ep282 ep283 ep284

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (@HMul.hMul Complex Complex Complex qz66 qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) Bool.false 3331789338615 1099511627776 53387928084031 11123759138209792

noncomputable def ep424 := nat_lit 1639254247989568754070718091

noncomputable def ep425 := nat_lit 409498535397303165273159493

noncomputable def ep426 := nat_lit 9082300570456323407186132538058866688

noncomputable def ep427 := nat_lit 5946972247278413942803670665003008

noncomputable def ep428 := @ep423 Bool.false 44232552545 1099511627776 53396377802431 11123759138209792 Bool.true 337761561873825447284387 ep283 ep424 ep285 Bool.false 1841639996599131351433 88669258977315389440000 ep425 ep421 Bool.false ep426 ep282 ep283 ep284 ep285 Bool.false ep427 5408739750490361932683 88669258977315389440000

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz116) (BSN.headSumC qz5 20) Bool.false 3331789338615 1099511627776 53387928084031 11123759138209792 Bool.false 44232552545 1099511627776 53396377802431

noncomputable abbrev qz122 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz275)

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz122) Bool.false 3331789338615 1099511627776 53387928084031 11123759138209792 Bool.false 44232552545 1099511627776 53396377802431 11123759138209792

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz122 Bool.false 3267630809961 1099511627776 669077562637217 144608868796727296 Bool.true 199715923765 1099511627776 669089112285353 144608868796727296 Bool.false

noncomputable def ep432 := nat_lit 1831670559553650551685120

noncomputable abbrev qz123 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz275)

noncomputable def ep433 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz123) Bool.false 3267630809961 1099511627776 669077562637217 144608868796727296 Bool.true 199715923765 1099511627776 669089112285353 144608868796727296

noncomputable def ep434 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz123 Bool.false 1510556628987 549755813888 160833198020057 36152217199181824 Bool.true 279660869131 1099511627776 643432983068255 144608868796727296 Bool.false

noncomputable def ep435 := nat_lit 1796399035415614212538368

noncomputable abbrev qz124 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz275)

noncomputable def ep436 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz39 qz124) Bool.false 1510556628987 549755813888 160833198020057 36152217199181824 Bool.true 279660869131 1099511627776 643432983068255 144608868796727296

noncomputable def ep437 := @Enclosure.Complex.IsNear.addLitP qz39 qz124 Bool.false 2773894499761 1099511627776 616848707222851 144608868796727296 Bool.true 179680209653 1099511627776 617025042951433 144608868796727296 Bool.false

noncomputable def ep438 := nat_lit 3321749155970647351885824

noncomputable abbrev qz398 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz125 := (@Inv.inv Real Real.instInv (Real.sqrt qz398))

noncomputable abbrev qz399 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz280 qz399)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz124 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 247218758213 1099511627776 26484084857377 144608868796727296 Bool.true 49990329739 549755813888 13203970058411 72304434398363648 (BSN.cpow_neg_s_mk qz16 97714 1000 17 qz17 rfl)

noncomputable abbrev qz400 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz18)

noncomputable def ep440 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz398) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz398) (Real.sqrt qz400) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz400) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep441 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 131521 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz399 97714 1000 0 1 3189913004350711 1125899906842624 250000000131521 32880250000000000000 155849579653562687327 562949953421312000 12214250006425721497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 53517859495200818200576 18889465931478580854784 1000000000526084 131521000000000000000 3189913004350711 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep443 := nat_lit 463936325596953385145284305375390625

noncomputable def ep444 := BSN.cos_dyadic_bound_f 825305225 2147483648 2 1 1048576 263299 ep443 ep62 ep443 ep443 ep63 ep443 972089 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 825305225) qz288 0 1 ep443 ep62 ep443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 825305225) qz289 0 1 ep443 ep63 ep443 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz401 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290292463) qz30)

noncomputable def ep445 := @Enclosure.Real.IsNear.cos_image qz126 qz401 Bool.false 290292463 1048576 195 262144 Bool.false 972089 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 155849579653562687327 562949953421312000 12214250006425721497 16440125000000000000000 290292463 1048576 195 262144 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 290292463 1048576) (BSN.cos_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58075692248709155782656) qz32) 226375608064910080 72057594037927936 Bool.false 972089 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 290292463 1048576 226375608064910080 72057594037927936 44 58075692248709155782656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 972089 1048576 58075692248709155782656 151115727451828646838272 825305225 2147483648 263299 263042 (ep444 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep446 := BSN.sin_dyadic_bound_f 825305225 2147483648 2 1 1048576 263299 ep443 ep58 ep443 ep443 ep59 ep443 393134 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 825305225) qz283 0 1 ep443 ep58 ep443 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 825305225) qz284 0 1 ep443 ep59 ep443 rfl rfl rfl rfl) rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.sin_image qz126 qz401 Bool.false 290292463 1048576 195 262144 Bool.false 393134 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 155849579653562687327 562949953421312000 12214250006425721497 16440125000000000000000 290292463 1048576 195 262144 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 290292463 1048576) (BSN.sin_reduce0 qz401 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58075692248709155782656) qz32) 226375608064910080 72057594037927936 Bool.false 393134 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 290292463 1048576 226375608064910080 72057594037927936 44 58075692248709155782656 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 393134 1048576 58075692248709155782656 151115727451828646838272 825305225 2147483648 263299 263042 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz402 := (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep440 rfl rfl) rfl)

noncomputable def ep448 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 247218758213 1099511627776 26484084857377 144608868796727296 Bool.true 49990329739 549755813888 13203970058411 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz126) 254317 1048576 1 1048576 972089 1048576 25908739 34477441024 247218758213 1099511627776 26484084857377 144608868796727296 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 972089 1048576 25908739 34477441024 972089 1048576 25908739 34477441024 (ep445 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 254317 1048576 1 1048576 196567 524288 25908739 34477441024 49990329739 549755813888 13203970058411 72304434398363648 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.false 196567 524288 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.false 393134 1048576 25908739 34477441024 196567 524288 25908739 34477441024 (ep447 rfl rfl) rfl)) rfl)

noncomputable def ep449 := @ep437 247218758213 1099511627776 26484084857377 144608868796727296 Bool.true 49990329739 549755813888 13203970058411 72304434398363648 Bool.false ep438 1510556628987 549755813888 160833198020057 36152217199181824 Bool.true 153745188721738360291328 279660869131 1099511627776 643432983068255 144608868796727296 EMRow29.d7 (ep439 ep448) rfl rfl

noncomputable abbrev qz403 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz127 := (@Inv.inv Real Real.instInv (Real.sqrt qz403))

noncomputable abbrev qz404 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz267 qz280 qz404)

noncomputable def ep450 := @Enclosure.Complex.IsNear.of_eq qz123 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 246517551987 1099511627776 25744770556989 144608868796727296 Bool.false 39972472683 549755813888 12828064608549 72304434398363648 (BSN.cpow_neg_s_mk qz16 97714 1000 18 qz17 rfl)

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz18)

noncomputable def ep451 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz403) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz403) (Real.sqrt qz405) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz405) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep452 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 131521 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep453 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz404 97714 1000 0 1 3254268794313975 1125899906842624 250000000131521 32880250000000000000 6359752419351915063 22517998136852480 12214250006425721497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz405) Bool.false 54597570484265130393600 18889465931478580854784 1000000000526084 131521000000000000000 3254268794313975 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep454 := nat_lit 3419762493593854416404714628855966618285877176741915196322169255583365944213760

noncomputable def ep455 := nat_lit 2822748222706155900360721173232323236866306459426691694760729061369864683776

noncomputable def ep456 := nat_lit 8951950652766189695316525717485155476936656681008801346671306869952311977738496

noncomputable def ep457 := BSN.sin_dyadic_bound_f 2699815074 2147483648 3 2 1048576 263299 ep454 ep170 ep455 ep456 ep172 ep455 997437 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2699815074) qz283 0 2 ep454 ep170 ep455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2699815074) qz284 0 2 ep456 ep172 ep455 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz406 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 296149049) qz30)

noncomputable def ep458 := @Enclosure.Real.IsNear.cos_image qz128 qz406 Bool.false 296149049 1048576 195 262144 Bool.false 997437 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 6359752419351915063 22517998136852480 12214250006425721497 16440125000000000000000 296149049 1048576 195 262144 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 296149049 1048576) (BSN.cos_reduce3 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189982596314320137617408) qz32) 226375608064910080 72057594037927936 Bool.false 997437 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 296149049 1048576 226375608064910080 72057594037927936 44 189982596314320137617408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 997437 1048576 189982596314320137617408 151115727451828646838272 2699815074 2147483648 263299 263042 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep459 := nat_lit 1901122606762232967291668447663640264930761234394142527598876577129145464422656

noncomputable def ep460 := nat_lit 5697722323841286590074283900644456148318551090263574199407108273264696663900416

noncomputable def ep461 := BSN.cos_dyadic_bound_f 2699815074 2147483648 3 2 1048576 263299 ep459 ep112 ep455 ep460 ep115 ep455 323466 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2699815074) qz288 0 2 ep459 ep112 ep455 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2699815074) qz289 0 2 ep460 ep115 ep455 rfl rfl rfl rfl) rfl rfl

noncomputable def ep462 := @Enclosure.Real.IsNear.sin_image qz128 qz406 Bool.false 296149049 1048576 195 262144 Bool.true 323466 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 6359752419351915063 22517998136852480 12214250006425721497 16440125000000000000000 296149049 1048576 195 262144 (ep453 rfl) rfl) (Enclosure.sfrac_false_div 296149049 1048576) (BSN.sin_reduce3 qz406 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 189982596314320137617408) qz32) 226375608064910080 72057594037927936 Bool.false 323466 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 296149049 1048576 226375608064910080 72057594037927936 44 189982596314320137617408 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 323466 1048576 189982596314320137617408 151115727451828646838272 2699815074 2147483648 263299 263042 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz407 := (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep451 rfl rfl) rfl)

noncomputable def ep463 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 246517551987 1099511627776 25744770556989 144608868796727296 Bool.false 39972472683 549755813888 12828064608549 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz128) 247151 1048576 1 1048576 997437 1048576 25908739 34477441024 246517551987 1099511627776 25744770556989 144608868796727296 qz407 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 997437 1048576 25908739 34477441024 997437 1048576 25908739 34477441024 (ep458 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 247151 1048576 1 1048576 161733 524288 25908739 34477441024 39972472683 549755813888 12828064608549 72304434398363648 qz407 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.true 161733 524288 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.true 323466 1048576 25908739 34477441024 161733 524288 25908739 34477441024 (ep462 rfl rfl) rfl)) rfl)

noncomputable def ep464 := @ep434 246517551987 1099511627776 25744770556989 144608868796727296 Bool.false 39972472683 549755813888 12828064608549 72304434398363648 Bool.false ep435 3267630809961 1099511627776 669077562637217 144608868796727296 Bool.true 109794990215821336248320 199715923765 1099511627776 669089112285353 144608868796727296 (ep436 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep449 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep450 ep463) rfl rfl

noncomputable abbrev qz408 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz129 := (@Inv.inv Real Real.instInv (Real.sqrt qz408))

noncomputable abbrev qz409 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz280 qz409)

noncomputable def ep465 := @Enclosure.Complex.IsNear.of_eq qz122 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.false 32079264327 549755813888 12482751227593 72304434398363648 Bool.false 121974238155 549755813888 12531899573125 72304434398363648 (BSN.cpow_neg_s_mk qz16 97714 1000 19 qz17 rfl)

noncomputable abbrev qz410 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz18)

noncomputable def ep466 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz408) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz408) (Real.sqrt qz410) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz410) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep467 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 131521 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep468 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz409 97714 1000 0 1 3315143513283831 1125899906842624 250000000131521 32880250000000000000 161967966628508131167 562949953421312000 12214250006425721497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 55618878793361701994496 18889465931478580854784 1000000000526084 131521000000000000000 3315143513283831 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep467 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep469 := nat_lit 93035526803621450855200320793852176

noncomputable def ep470 := BSN.sin_dyadic_bound_f 552283674 2147483648 2 1 1048576 263299 ep469 ep58 ep469 ep469 ep59 ep469 266706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 552283674) qz283 0 1 ep469 ep58 ep469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 552283674) qz284 0 1 ep469 ep59 ep469 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz411 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 301688847) qz30)

noncomputable def ep471 := @Enclosure.Real.IsNear.cos_image qz130 qz411 Bool.false 301688847 1048576 195 262144 Bool.false 266706 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 161967966628508131167 562949953421312000 12214250006425721497 16440125000000000000000 301688847 1048576 195 262144 (ep468 rfl) rfl) (Enclosure.sfrac_false_div 301688847 1048576) (BSN.cos_reduce3 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38863508577485737426944) qz32) 226375608064910080 72057594037927936 Bool.false 266706 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 301688847 1048576 226375608064910080 72057594037927936 45 38863508577485737426944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 266706 1048576 38863508577485737426944 151115727451828646838272 552283674 2147483648 263299 263042 (ep470 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep472 := BSN.cos_dyadic_bound_f 552283674 2147483648 2 1 1048576 263299 ep469 ep62 ep469 ep469 ep63 ep469 1014090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 552283674) qz288 0 1 ep469 ep62 ep469 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 552283674) qz289 0 1 ep469 ep63 ep469 rfl rfl rfl rfl) rfl rfl

noncomputable def ep473 := @Enclosure.Real.IsNear.sin_image qz130 qz411 Bool.false 301688847 1048576 195 262144 Bool.true 1014090 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 161967966628508131167 562949953421312000 12214250006425721497 16440125000000000000000 301688847 1048576 195 262144 (ep468 rfl) rfl) (Enclosure.sfrac_false_div 301688847 1048576) (BSN.sin_reduce3 qz411 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38863508577485737426944) qz32) 226375608064910080 72057594037927936 Bool.false 1014090 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 301688847 1048576 226375608064910080 72057594037927936 45 38863508577485737426944 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1014090 1048576 38863508577485737426944 151115727451828646838272 552283674 2147483648 263299 263042 (ep472 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz412 := (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep466 rfl rfl) rfl)

noncomputable def ep474 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.false 32079264327 549755813888 12482751227593 72304434398363648 Bool.false 121974238155 549755813888 12531899573125 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz130) 240559 1048576 1 1048576 133353 524288 25908739 34477441024 32079264327 549755813888 12482751227593 72304434398363648 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 266706 1048576 25908739 34477441024 133353 524288 25908739 34477441024 (ep471 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 240559 1048576 1 1048576 507045 524288 25908739 34477441024 121974238155 549755813888 12531899573125 72304434398363648 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 507045 524288 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 1014090 1048576 25908739 34477441024 507045 524288 25908739 34477441024 (ep473 rfl rfl) rfl)) rfl)

noncomputable def ep475 := @ep431 32079264327 549755813888 12482751227593 72304434398363648 Bool.false 121974238155 549755813888 12531899573125 72304434398363648 Bool.false ep432 3331789338615 1099511627776 53387928084031 11123759138209792 Bool.false 24317102924720200744960 44232552545 1099511627776 53396377802431 11123759138209792 (ep433 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep465 ep474) rfl rfl

noncomputable def ep476 := @Enclosure.Complex.IsNear.mul qz117 (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.true 337761561873825447284387 ep283 ep424 ep285 Bool.false

noncomputable def ep477 := nat_lit 7008518536276569210550229

noncomputable abbrev qz131 := (Complex.re qz395)

noncomputable abbrev qz132 := (Complex.im qz395)

noncomputable def ep478 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 539754380316194254411 5674832574548184924160 ep477

noncomputable def ep479 := nat_lit 82845921709123853064559656960

noncomputable def ep480 := nat_lit 21097066803439129208015519

noncomputable def ep481 := nat_lit 618253147083013828839997440000

noncomputable def ep482 := nat_lit 1916740313751856922419525339530807765547089920

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 104362386369 549755813888 12208184195281 72304434398363648 574083616709

noncomputable abbrev qz413 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz133 := (@Inv.inv Real Real.instInv (Real.sqrt qz413))

noncomputable abbrev qz414 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz515 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz134 := (Real.cos qz414)

noncomputable abbrev qz135 := (Real.sin qz414)

noncomputable abbrev qz415 := (@Neg.neg Real Real.instNeg qz135)

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq qz117 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz415)) Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (BSN.cpow_neg_s_mk qz16 97714 1000 20 qz17 rfl)

noncomputable abbrev qz416 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz18)

noncomputable def ep485 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz413) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz413) (Real.sqrt qz416) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz416) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep486 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 131521 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz417 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz136 := qz417

noncomputable abbrev qz418 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz18))

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz136 97714 1000 0 1 3372893643545847 1125899906842624 250000000131521 32880250000000000000 164789464742719446879 562949953421312000 12214250006425721497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 56587765202795681021952 18889465931478580854784 1000000000526084 131521000000000000000 3372893643545847 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep488 := nat_lit 2043812094718826328829137375516500625

noncomputable def ep489 := BSN.cos_dyadic_bound_f 1195666995 2147483648 2 1 1048576 263299 ep488 ep62 ep488 ep488 ep63 ep488 890202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1195666995) qz288 0 1 ep488 ep62 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1195666995) qz289 0 1 ep488 ep63 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz137 := qz414

noncomputable abbrev qz419 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 306944297) qz30)

noncomputable def ep490 := @Enclosure.Real.IsNear.cos_image qz137 qz419 Bool.false 306944297 1048576 195 262144 Bool.true 890202 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 164789464742719446879 562949953421312000 12214250006425721497 16440125000000000000000 306944297 1048576 195 262144 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 306944297 1048576) (BSN.cos_reduce2 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84137584943929023791104) qz32) 226375608064910080 72057594037927936 Bool.false 890202 1048576 46 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 306944297 1048576 226375608064910080 72057594037927936 46 84137584943929023791104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 890202 1048576 84137584943929023791104 151115727451828646838272 1195666995 2147483648 263299 263042 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := BSN.sin_dyadic_bound_f 1195666995 2147483648 2 1 1048576 263299 ep488 ep58 ep488 ep488 ep59 ep488 554121 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1195666995) qz283 0 1 ep488 ep58 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1195666995) qz284 0 1 ep488 ep59 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.sin_image qz137 qz419 Bool.false 306944297 1048576 195 262144 Bool.true 554121 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 164789464742719446879 562949953421312000 12214250006425721497 16440125000000000000000 306944297 1048576 195 262144 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 306944297 1048576) (BSN.sin_reduce2 qz419 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84137584943929023791104) qz32) 226375608064910080 72057594037927936 Bool.false 554121 1048576 46 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 306944297 1048576 226375608064910080 72057594037927936 46 84137584943929023791104 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 554121 1048576 84137584943929023791104 151115727451828646838272 1195666995 2147483648 263299 263042 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz420 := (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep485 rfl rfl) rfl)

noncomputable def ep493 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 qz134) (@HMul.hMul Real Real Real qz0 qz133 qz415) Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz133 qz134 234469 1048576 1 1048576 445101 524288 25908739 34477441024 104362386369 549755813888 12208184195281 72304434398363648 qz420 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 890202 1048576 25908739 34477441024 445101 524288 25908739 34477441024 (ep490 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 qz415 234469 1048576 1 1048576 554121 1048576 25908739 34477441024 129924196749 1099511627776 24372166681361 144608868796727296 qz420 (@Enclosure.Real.IsNear.neg qz135 Bool.true 554121 1048576 25908739 34477441024 (@Enclosure.Real.IsNear.recentre' qz135 Bool.true 554121 1048576 25908739 34477441024 554121 1048576 25908739 34477441024 (ep492 rfl rfl) rfl)) rfl)

noncomputable def ep494 := @ep483 1145793095520 0 1 539754380316194254411 5674832574548184924160 ep477 ep479 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (ep484 ep493))

noncomputable def ep495 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 574083616709 1145793095520 0 1 Bool.false

noncomputable def ep496 := @Enclosure.Complex.IsNear.addLitP qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) Bool.false 2382068949 4774137898 0 1 Bool.true 488570000

noncomputable def ep497 := @ep496 2387068949 0 1 Bool.false 1 480 0 1 Bool.false 48857 120000 0 1 Bool.false 1148167233418 574083616709 1145793095520 0 1 Bool.false 57996627641293 57996627641293 286448273880000 0 1

noncomputable abbrev qz138 := (@HDiv.hDiv Complex Complex Complex qz368 qz396 (@HSub.hSub Complex Complex Complex qz360 qz272 (1 : Complex)))

noncomputable def ep498 := @Enclosure.Complex.IsNear.addLitP qz138 qz93 Bool.true 40000000 38193103184 0 1 Bool.true 7817120000 38193103184 0 1

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq qz138 (Complex.mk (Enclosure.sfrac Bool.true 40000000 38193103184) (Enclosure.sfrac Bool.true 7817120000 38193103184)) Bool.true 40000000 38193103184 0 1 Bool.true 7817120000 38193103184 0 1

noncomputable def ep500 := @ep498 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 38113103184 2382068949 4774137898 0 1 Bool.true 7817120000 488570000 2387068949 0 1 (ep499 (BSN.N_div_s_sub_one_mk qz16 97714 1000 20 qz17 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 38193103184) (Enclosure.sfrac Bool.true 7817120000 38193103184) Bool.true 40000000 38193103184 0 1 Bool.true 7817120000 38193103184 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 38193103184) (Enclosure.Real.IsNear.const Bool.true 7817120000 38193103184))) qz94 rfl

noncomputable abbrev qz139 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz421 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz525 qz526 1))

noncomputable abbrev qz140 := qz421

noncomputable def ep501 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 480 0 1

noncomputable def ep502 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep503 := @ep502 0 1 0 1 Bool.false 1 480 0 1 Bool.false 48857 120000 0 1 Bool.false 1 1 480 0 1 Bool.false 48857 48857 120000 0

noncomputable def ep504 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep505 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 480 0 1 Bool.false 48857 120000 0 1

noncomputable abbrev qz141 := (Complex.re qz421)

noncomputable abbrev qz142 := (Complex.im qz421)

noncomputable def ep506 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 480 0 1 0 1 0

noncomputable def ep507 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 20 0 1 1

noncomputable def ep508 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz13) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow29.d8 rfl) qz385

noncomputable def ep511 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep512 := ep511 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz88 qz16) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_crit_mk qz16 Bool.false 97714 1000 qz17) (@Enclosure.Complex.IsNear.mk qz88 qz16 Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 qz377 qz20))

noncomputable def ep513 := @ep509 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep514 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 97714 1000 0 1 0 1 0

noncomputable def ep515 := @ep514 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep516 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 48857 6000 0 1 0 1 0 1 48857

noncomputable def ep517 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 97714 1000 0 1 48857 6000 0

noncomputable def ep518 := @ep517 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep519 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep520 := @ep519 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep521 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 (@ep508 1 24 0 1 (ep513 rfl) (ep515 rfl) rfl rfl) (@ep516 48857 6000 0 1 (ep518 rfl) (ep520 rfl) rfl rfl)

noncomputable def ep522 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 ep521

noncomputable abbrev qz143 := (@Enclosure.Complex.IsNear.re_isNear qz421 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz421 (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz278) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow29.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz278 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz291)))

noncomputable def ep523 := @ep507 480 0 1 ep522 qz143

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 48857 6000 0 1 0 1 0 1 0

noncomputable def ep525 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 48857 6000 0 1 ep521

noncomputable abbrev qz144 := (@Enclosure.Complex.IsNear.im_isNear qz421 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz421 (Complex.mk (Enclosure.sfrac Bool.false 1 20) qz278) Bool.false 1 20 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 20 1 20 EMRow29.d9 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 20) qz278 Bool.false 1 20 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 20) qz291)))

noncomputable def ep526 := @ep524 1 0 1 ep525 qz144

noncomputable def ep527 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 48857 120000 0

noncomputable def ep528 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep529 := @ep528 1 0 1 ep522 qz144

noncomputable def ep530 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 48857 6000 0 1 1 20 0 1 48857

noncomputable def ep531 := @ep530 120000 0 1 ep525 qz143

noncomputable def ep532 := @ep503 1 (@ep504 0 1 0 1 (BSN.bern_sum_base qz5 20) qz109) (ep505 (@ep506 1 1 1 480 0 1 (ep523 rfl) (ep526 rfl) rfl rfl) (@ep527 1 48857 48857 120000 0 1 (ep529 rfl) (ep531 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep533 := ep497 (ep500 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep501 Bool.false 48857 120000 0 1 (BSN.bern_sum_succ qz5 20 0 1 1 rfl rfl) (ep532 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep534 := @Enclosure.Real.IsNear.mulLit_ff qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 129924196749 1099511627776 24372166681361 144608868796727296 57996627641293

noncomputable def ep535 := @ep534 286448273880000 0 1 67884371715728320078887 ep283 ep480 ep481 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (ep484 ep493))

noncomputable def ep536 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 574083616709 1145793095520 0 1 Bool.false

noncomputable def ep537 := nat_lit 1418708143637046231040000

noncomputable def ep538 := nat_lit 10567664372388513198975199

noncomputable def ep539 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 54528526684681488330947 ep537 ep538

noncomputable def ep540 := nat_lit 309126573541506914419998720000

noncomputable def ep541 := nat_lit 13991661595470308858460949

noncomputable def ep542 := nat_lit 165691843418247706129119313920

noncomputable def ep543 := nat_lit 334431956585329891042635118603173677194280960

noncomputable def ep544 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 104362386369 549755813888 12208184195281 72304434398363648 57996627641293

noncomputable def ep545 := @ep544 286448273880000 0 1 54528526684681488330947 ep537 ep538 ep540 (@Enclosure.Complex.IsNear.re_isNear qz117 Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (ep484 ep493))

noncomputable def ep546 := @Enclosure.Real.IsNear.mulLit_ff qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz118 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 129924196749 1099511627776 24372166681361 144608868796727296 574083616709

noncomputable def ep547 := @ep546 1145793095520 0 1 671958133042140719631 11349665149096369848320 ep541 ep542 (@Enclosure.Complex.IsNear.im_isNear qz117 Bool.true 104362386369 549755813888 12208184195281 72304434398363648 Bool.false 129924196749 1099511627776 24372166681361 144608868796727296 (ep484 ep493))

noncomputable abbrev qz422 := (ep533 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep548 := @ep476 1841639996599131351433 88669258977315389440000 ep425 ep421 (@ep478 ep479 67884371715728320078887 ep283 ep480 ep481 ep482 337761561873825447284387 ep283 ep424 ep285 (ep494 (@ep495 57996627641293 286448273880000 0 1 qz422) rfl) (ep535 (@ep536 57996627641293 286448273880000 0 1 qz422) rfl) rfl rfl) (@ep539 ep540 671958133042140719631 11349665149096369848320 ep541 ep542 ep543 1841639996599131351433 88669258977315389440000 ep425 ep421 (ep545 (@ep536 57996627641293 286448273880000 0 1 qz422) rfl) (ep547 (@ep495 57996627641293 286448273880000 0 1 qz422) rfl) rfl rfl)

noncomputable def ep549 := @ep428 ep420 ep421 (@ep429 11123759138209792 (BSN.head_sum_c_eq qz5 20) (ep430 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep475 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep548 rfl rfl rfl

noncomputable def ep550 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 20) Bool.false ep282 ep283 ep284 ep285 Bool.false 5408739750490361932683 88669258977315389440000 ep420 ep421 (@ep422 ep285 Bool.false 5408739750490361932683 88669258977315389440000 ep420 ep421 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep551 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) (Complex.im (zetaApproximant qz5 1 20)) 715 1048576 41688565

noncomputable def ep552 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70)) Bool.false 715 1048576 41688565

noncomputable def ep553 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) qz364 Bool.false 11117831 131072 309

noncomputable def ep554 := nat_lit 4634905454195273213470019724309186877867243907877762672744376817540954401339521

noncomputable def ep555 := nat_lit 13871303185830680250813025619538579375651967749412502972042941637206638888548481

noncomputable def ep556 := BSN.cos_dyadic_bound_f 3371793519 2147483648 3 2 1048576 263299 ep554 ep112 ep416 ep555 ep115 ep416 715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3371793519) qz288 0 2 ep554 ep112 ep416 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3371793519) qz289 0 2 ep555 ep115 ep416 rfl rfl rfl rfl) rfl rfl

noncomputable def ep557 := @ep553 1048576 Bool.false 715 1048576 1 131521 (@ep290 11117831 131072 309 1048576 ep414 rfl) (Enclosure.sfrac_false_div 11117831 131072) (BSN.sin_reduce1 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29658609445534382948352) qz299) 226375608064910080 72057594037927936 Bool.false 715 1048576 13 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 11117831 131072 226375608064910080 72057594037927936 13 29658609445534382948352 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 715 1048576 29658609445534382948352 18889465931478580854784 3371793519 2147483648 263299 263042 (ep556 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep558 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 20) Bool.false ep282 ep283 ep284 ep285 Bool.false 5408739750490361932683 88669258977315389440000 ep420 ep421 (@ep422 ep285 Bool.false 5408739750490361932683 88669258977315389440000 ep420 ep421 (BSN.zetaApproximant_eq_folded' qz5 1 20 rfl) (ep549 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow29.d10 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz16) Bool.true ep267 ep268 ep269 ep270 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz16) ep271 Bool.true ep267 ep268 ep269 ep270 (@Eq.refl Real ep271) (@ep272 Bool.true ep267 ep268 ep269 ep270 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz68 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz69 (@Nat.cast Complex Complex.instNatCast j))))) qz70) (zetaApproximant qz5 1 20)) (@ep274 ep275 ep276 ep270 773449784320121756373669 ep277 ep278 ep279 ep280 ep267 ep268 ep269 ep270 (@ep281 137909764096 ep282 ep283 ep284 ep285 ep273 ep275 ep276 ep270 (@ep286 137909764096 1048575 1048576 41688565 137909764096 (ep419 rfl rfl) rfl) ep550 rfl) (@ep551 137909764096 5408739750490361932683 88669258977315389440000 ep420 ep421 773449784320121756373669 ep277 ep278 ep279 (@ep552 137909764096 715 1048576 41688565 137909764096 (ep557 rfl rfl) rfl) ep558 rfl) rfl rfl))

noncomputable abbrev qz543 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 99995 1000)))

noncomputable abbrev qz527 := qz543

noncomputable abbrev qz423 := qz527

noncomputable abbrev qz145 := (BSN.headSumC qz423 9)

noncomputable abbrev qz146 := qz423

noncomputable abbrev qz528 := (@Neg.neg Complex Complex.instNeg qz543)

noncomputable abbrev qz424 := qz528

noncomputable abbrev qz147 := qz424

noncomputable abbrev qz425 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 8) qz147)

noncomputable def ep559 := @Enclosure.Complex.IsNear.of_eq qz145 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 8) qz425) Bool.false 1650932987253 1099511627776 2489140275951 957674627792896 Bool.true 48526812689 274877906944 1242614140679 478837313896448

noncomputable def ep560 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 8) qz425 Bool.false 331905956047 274877906944 168223724791477 72304434398363648 Bool.false 10865375049 549755813888 41986858177083 18076108599590912 Bool.false

noncomputable abbrev qz426 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 7) qz147)

noncomputable def ep561 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 7) qz426) Bool.false 331905956047 274877906944 168223724791477 72304434398363648 Bool.false 10865375049 549755813888 41986858177083 18076108599590912

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 7) qz426 Bool.false 920135537913 1099511627776 294300743006063 144608868796727296 Bool.true 59861866627 1099511627776 293856307768947 144608868796727296 Bool.false

noncomputable def ep563 := nat_lit 1459737832007145921445888

noncomputable abbrev qz427 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 6) qz147)

noncomputable def ep564 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 6) qz427) Bool.false 920135537913 1099511627776 294300743006063 144608868796727296 Bool.true 59861866627 1099511627776 293856307768947 144608868796727296

noncomputable def ep565 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 6) qz427 Bool.false 1366937001057 1099511627776 19137383897299 11123759138209792 Bool.true 102937744081 1099511627776 19112738015237 11123759138209792 Bool.true

noncomputable abbrev qz428 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 5) qz147)

noncomputable def ep566 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 5) qz428) Bool.false 1366937001057 1099511627776 19137383897299 11123759138209792 Bool.true 102937744081 1099511627776 19112738015237 11123759138209792

noncomputable def ep567 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 5) qz428 Bool.false 1738443898441 1099511627776 198911597824025 144608868796727296 Bool.true 425066513239 1099511627776 198605050255477 144608868796727296 Bool.true

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 4) qz147)

noncomputable def ep568 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 4) qz429) Bool.false 1738443898441 1099511627776 198911597824025 144608868796727296 Bool.true 425066513239 1099511627776 198605050255477 144608868796727296

noncomputable def ep569 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 4) qz429 Bool.false 615229801353 549755813888 688170480285 695234946138112 Bool.true 53717735515 274877906944 343527919905 347617473069056 Bool.false

noncomputable abbrev qz148 := qz276

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz115 qz148 qz147)) Bool.false 615229801353 549755813888 688170480285 695234946138112 Bool.true 53717735515 274877906944 343527919905 347617473069056

noncomputable def ep571 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 3) (@HPow.hPow Complex Complex Complex qz115 qz148 qz147) Bool.false 1862086973451 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 1099511627776 78720450571239 144608868796727296 Bool.true

noncomputable def ep572 := nat_lit 1352904640683884314361856

noncomputable abbrev qz149 := qz277

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz115 qz149 qz147)) Bool.false 1862086973451 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 1099511627776 78720450571239 144608868796727296

noncomputable def ep574 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 2) (@HPow.hPow Complex Complex Complex qz115 qz149 qz147) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep575 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz13) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz146)

noncomputable abbrev qz544 := (Enclosure.sfrac Bool.false 99995 1000)

noncomputable abbrev qz529 := qz544

noncomputable abbrev qz430 := qz529

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log qz281))

noncomputable abbrev qz151 := qz430

noncomputable abbrev qz431 := (@Eq.refl Real qz529)

noncomputable abbrev qz152 := qz431

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz115 qz149 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 762575345675 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 1099511627776 78720450571239 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 2 qz152 rfl)

noncomputable def ep577 := nat_lit 31431558745104694503745582164010000

noncomputable def ep578 := BSN.cos_dyadic_bound_f 421057570 2147483648 2 1 1048576 263299 ep577 ep62 ep577 ep577 ep63 ep577 1028485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 421057570) qz288 0 1 ep577 ep62 ep577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 421057570) qz289 0 1 ep577 ep63 ep577 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz153 := (Enclosure.Real.IsNear.const Bool.false 99995 1000)

noncomputable abbrev qz432 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72677965) qz30)

noncomputable def ep579 := @Enclosure.Real.IsNear.cos_image qz150 qz432 Bool.false 72677965 1048576 799 1048576 Bool.false 1028485 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 454237287 6553600 19999 26304200 72677965 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz19 99995 1000 0 1 363408 524288 1 131521 454237287 6553600 19999 26304200 qz153 qz286 rfl) rfl) (Enclosure.sfrac_false_div 72677965 1048576) (BSN.cos_reduce0 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29629292445539720232960) qz32) 226375608064910080 72057594037927936 Bool.false 1028485 1048576 11 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 72677965 1048576 226375608064910080 72057594037927936 11 29629292445539720232960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1028485 1048576 29629292445539720232960 151115727451828646838272 421057570 2147483648 263299 263042 (ep578 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep580 := BSN.sin_dyadic_bound_f 421057570 2147483648 2 1 1048576 263299 ep577 ep58 ep577 ep577 ep59 ep577 204279 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 421057570) qz283 0 1 ep577 ep58 ep577 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 421057570) qz284 0 1 ep577 ep59 ep577 rfl rfl rfl rfl) rfl rfl

noncomputable def ep581 := @Enclosure.Real.IsNear.sin_image qz150 qz432 Bool.false 72677965 1048576 799 1048576 Bool.false 204279 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 454237287 6553600 19999 26304200 72677965 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz19 99995 1000 0 1 363408 524288 1 131521 454237287 6553600 19999 26304200 qz153 qz286 rfl) rfl) (Enclosure.sfrac_false_div 72677965 1048576) (BSN.sin_reduce0 qz432 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29629292445539720232960) qz32) 226375608064910080 72057594037927936 Bool.false 204279 1048576 11 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 72677965 1048576 226375608064910080 72057594037927936 11 29629292445539720232960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 204279 1048576 29629292445539720232960 151115727451828646838272 421057570 2147483648 263299 263042 (ep580 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep582 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz14 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 762575345675 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 1099511627776 78720450571239 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz14 (Real.cos qz150) 741455 1048576 1 1048576 1028485 1048576 106133855 137909764096 762575345675 1099511627776 78828850968565 144608868796727296 qz290 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 1028485 1048576 106133855 137909764096 1028485 1048576 106133855 137909764096 (ep579 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz14 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 741455 1048576 1 1048576 204279 1048576 106133855 137909764096 151463685945 1099511627776 78720450571239 144608868796727296 qz290 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 204279 1048576 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 204279 1048576 106133855 137909764096 204279 1048576 106133855 137909764096 (ep581 rfl rfl) rfl)) rfl)

noncomputable def ep583 := @ep574 762575345675 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 1099511627776 78720450571239 144608868796727296 Bool.false 1862086973451 1862086973451 1099511627776 78828850968565 144608868796727296 Bool.true 151463685945 151463685945 1099511627776 78720450571239 144608868796727296 (ep575 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz13 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep576 ep582) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep584 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz115 qz148 qz147) (Complex.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.true 631627370745 1099511627776 64310608930715 144608868796727296 Bool.true 63407256115 1099511627776 64187164109241 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 3 qz152 rfl)

noncomputable def ep585 := nat_lit 6409731802828591806083668951596874756253795097383734706914466692438088833105920

noncomputable def ep586 := nat_lit 9902259775832757625776439949299038831800324611338816257032015163866229047296

noncomputable def ep587 := nat_lit 16771360586818773122634542541883425917794167586634280434645551408024925430153216

noncomputable def ep588 := BSN.sin_dyadic_bound_f 3158397516 2147483648 3 2 1048576 263299 ep585 ep170 ep586 ep587 ep172 ep586 1043331 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3158397516) qz283 0 2 ep585 ep170 ep586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3158397516) qz284 0 2 ep587 ep172 ep586 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14399005) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep589 := @Enclosure.Real.IsNear.cos_image qz154 qz433 Bool.false 14399005 131072 399 524288 Bool.true 1043331 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 11519204011 104857600 19999 26304200 14399005 131072 399 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz24 99995 1000 0 1 575989 524288 1 131521 11519204011 104857600 19999 26304200 qz153 qz294 rfl) rfl) (Enclosure.sfrac_false_div 14399005 131072) (BSN.cos_reduce1 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27781558360600393809920) qz299) 226375608064910080 72057594037927936 Bool.false 1043331 1048576 17 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 14399005 131072 226375608064910080 72057594037927936 17 27781558360600393809920 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1043331 1048576 27781558360600393809920 18889465931478580854784 3158397516 2147483648 263299 263042 (ep588 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep590 := nat_lit 3565363117027365562324605613086841104066241865040447644400051280316212120190976

noncomputable def ep591 := nat_lit 10676284831530431171722263959361925234535124945898665300686089810620903902478336

noncomputable def ep592 := BSN.cos_dyadic_bound_f 3158397516 2147483648 3 2 1048576 263299 ep590 ep112 ep586 ep591 ep115 ep586 104737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3158397516) qz288 0 2 ep590 ep112 ep586 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3158397516) qz289 0 2 ep591 ep115 ep586 rfl rfl rfl rfl) rfl rfl

noncomputable def ep593 := @Enclosure.Real.IsNear.sin_image qz154 qz433 Bool.false 14399005 131072 399 524288 Bool.false 104737 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 11519204011 104857600 19999 26304200 14399005 131072 399 524288 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz24 99995 1000 0 1 575989 524288 1 131521 11519204011 104857600 19999 26304200 qz153 qz294 rfl) rfl) (Enclosure.sfrac_false_div 14399005 131072) (BSN.sin_reduce1 qz433 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27781558360600393809920) qz299) 226375608064910080 72057594037927936 Bool.false 104737 1048576 17 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q1 14399005 131072 226375608064910080 72057594037927936 17 27781558360600393809920 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 104737 1048576 27781558360600393809920 18889465931478580854784 3158397516 2147483648 263299 263042 (ep592 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep594 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz22 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz22 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.true 631627370745 1099511627776 64310608930715 144608868796727296 Bool.true 63407256115 1099511627776 64187164109241 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz22 (Real.cos qz154) 605395 1048576 1 1048576 1043331 1048576 53001167 68954882048 631627370745 1099511627776 64310608930715 144608868796727296 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.true 1043331 1048576 53001167 68954882048 1043331 1048576 53001167 68954882048 (ep589 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz22 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 605395 1048576 1 1048576 104737 1048576 53001167 68954882048 63407256115 1099511627776 64187164109241 144608868796727296 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 104737 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 104737 1048576 53001167 68954882048 104737 1048576 53001167 68954882048 (ep593 rfl rfl) rfl)) rfl)

noncomputable def ep595 := @ep571 631627370745 1099511627776 64310608930715 144608868796727296 Bool.true 63407256115 1099511627776 64187164109241 144608868796727296 Bool.false ep572 615229801353 549755813888 688170480285 695234946138112 Bool.true 236253099266153182658560 53717735515 274877906944 343527919905 347617473069056 (ep573 (BSN.head_sum_c_succ qz146 2 3 rfl rfl) (ep583 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep584 ep594) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq qz429 (Complex.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 507984295735 1099511627776 55772137924745 144608868796727296 Bool.true 210195571179 1099511627776 55697435574997 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 4 qz152 rfl)

noncomputable def ep597 := nat_lit 503888993751966306973519262678139136

noncomputable def ep598 := BSN.cos_dyadic_bound_f 842526788 2147483648 2 1 1048576 263299 ep597 ep62 ep597 ep597 ep63 ep597 968905 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 842526788) qz288 0 1 ep597 ep62 ep597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 842526788) qz289 0 1 ep597 ep63 ep597 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz434 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145356131) qz30)

noncomputable def ep599 := @Enclosure.Real.IsNear.cos_image qz155 qz434 Bool.false 145356131 1048576 799 1048576 Bool.false 968905 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 14535613183 104857600 19999 26304200 145356131 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz27 99995 1000 0 1 726817 524288 1 131521 14535613183 104857600 19999 26304200 qz153 qz298 rfl) rfl) (Enclosure.sfrac_false_div 145356131 1048576) (BSN.cos_reduce0 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59287552043882687496192) qz32) 226375608064910080 72057594037927936 Bool.false 968905 1048576 22 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 145356131 1048576 226375608064910080 72057594037927936 22 59287552043882687496192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 968905 1048576 59287552043882687496192 151115727451828646838272 842526788 2147483648 263299 263042 (ep598 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep600 := BSN.sin_dyadic_bound_f 842526788 2147483648 2 1 1048576 263299 ep597 ep58 ep597 ep597 ep59 ep597 400917 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 842526788) qz283 0 1 ep597 ep58 ep597 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 842526788) qz284 0 1 ep597 ep59 ep597 rfl rfl rfl rfl) rfl rfl

noncomputable def ep601 := @Enclosure.Real.IsNear.sin_image qz155 qz434 Bool.false 145356131 1048576 799 1048576 Bool.false 400917 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 14535613183 104857600 19999 26304200 145356131 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz27 99995 1000 0 1 726817 524288 1 131521 14535613183 104857600 19999 26304200 qz153 qz298 rfl) rfl) (Enclosure.sfrac_false_div 145356131 1048576) (BSN.sin_reduce0 qz434 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59287552043882687496192) qz32) 226375608064910080 72057594037927936 Bool.false 400917 1048576 22 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 145356131 1048576 226375608064910080 72057594037927936 22 59287552043882687496192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 400917 1048576 59287552043882687496192 151115727451828646838272 842526788 2147483648 263299 263042 (ep600 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep602 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz25 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz25 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 507984295735 1099511627776 55772137924745 144608868796727296 Bool.true 210195571179 1099511627776 55697435574997 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz25 (Real.cos qz155) 524287 1048576 1 1048576 968905 1048576 106133855 137909764096 507984295735 1099511627776 55772137924745 144608868796727296 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 968905 1048576 106133855 137909764096 968905 1048576 106133855 137909764096 (ep599 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz25 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 524287 1048576 1 1048576 400917 1048576 106133855 137909764096 210195571179 1099511627776 55697435574997 144608868796727296 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 400917 1048576 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 400917 1048576 106133855 137909764096 400917 1048576 106133855 137909764096 (ep601 rfl rfl) rfl)) rfl)

noncomputable def ep603 := @ep569 507984295735 1099511627776 55772137924745 144608868796727296 Bool.true 210195571179 1099511627776 55697435574997 144608868796727296 Bool.false 955719640286059569348608 1738443898441 1099511627776 198911597824025 144608868796727296 Bool.true 116841393471120386031616 425066513239 1099511627776 198605050255477 144608868796727296 (ep570 (BSN.head_sum_c_succ qz146 3 4 rfl rfl) (ep595 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep596 ep602) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz428 (Complex.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.true 46438362173 137438953472 24937196420431 72304434398363648 Bool.false 161064384579 549755813888 12465135985651 36152217199181824 (BSN.cpow_neg_s_mk qz151 99995 1000 5 qz152 rfl)

noncomputable def ep605 := nat_lit 197884315051888319513900798529481888171960023827031692303609815330368749445376

noncomputable def ep606 := nat_lit 30664130109941367960215281206583524118460418843550092749854831168495165696

noncomputable def ep607 := nat_lit 593591616895445075805781965026032497467643150643407976725329736328769258004736

noncomputable def ep608 := BSN.cos_dyadic_bound_f 1534012262 2147483648 3 2 1048576 263299 ep605 ep112 ep606 ep607 ep115 ep606 792232 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1534012262) qz288 0 2 ep605 ep112 ep606 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1534012262) qz289 0 2 ep607 ep115 ep606 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168753161) qz30)

noncomputable def ep609 := @Enclosure.Real.IsNear.cos_image qz156 qz435 Bool.false 168753161 1048576 799 1048576 Bool.true 792232 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 527353631 3276800 19999 26304200 168753161 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz31 99995 1000 0 1 843808 524288 1 131521 527353631 3276800 19999 26304200 qz153 qz303 rfl) rfl) (Enclosure.sfrac_false_div 168753161 1048576) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107946516478528671711232) qz32) 226375608064910080 72057594037927936 Bool.false 792232 1048576 25 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 168753161 1048576 226375608064910080 72057594037927936 25 107946516478528671711232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 792232 1048576 107946516478528671711232 151115727451828646838272 1534012262 2147483648 263299 263042 (ep608 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep610 := nat_lit 5537520213050365738611954435402942736

noncomputable def ep611 := BSN.sin_dyadic_bound_f 1534012262 2147483648 2 1 1048576 263299 ep610 ep58 ep610 ep610 ep59 ep610 686934 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1534012262) qz283 0 1 ep610 ep58 ep610 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1534012262) qz284 0 1 ep610 ep59 ep610 rfl rfl rfl rfl) rfl rfl

noncomputable def ep612 := @Enclosure.Real.IsNear.sin_image qz156 qz435 Bool.false 168753161 1048576 799 1048576 Bool.true 686934 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 527353631 3276800 19999 26304200 168753161 1048576 799 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz151 qz31 99995 1000 0 1 843808 524288 1 131521 527353631 3276800 19999 26304200 qz153 qz303 rfl) rfl) (Enclosure.sfrac_false_div 168753161 1048576) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107946516478528671711232) qz32) 226375608064910080 72057594037927936 Bool.false 686934 1048576 25 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 168753161 1048576 226375608064910080 72057594037927936 25 107946516478528671711232 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 686934 1048576 107946516478528671711232 151115727451828646838272 1534012262 2147483648 263299 263042 (ep611 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep613 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz28 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.true 46438362173 137438953472 24937196420431 72304434398363648 Bool.false 161064384579 549755813888 12465135985651 36152217199181824 (@Enclosure.Real.IsNear.mulLit_ft qz28 (Real.cos qz156) 468937 1048576 1 1048576 99029 131072 106133855 137909764096 46438362173 137438953472 24937196420431 72304434398363648 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.true 792232 1048576 106133855 137909764096 99029 131072 106133855 137909764096 (ep609 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz28 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 468937 1048576 1 1048576 343467 524288 106133855 137909764096 161064384579 549755813888 12465135985651 36152217199181824 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 343467 524288 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 686934 1048576 106133855 137909764096 343467 524288 106133855 137909764096 (ep612 rfl rfl) rfl)) rfl)

noncomputable def ep614 := @ep567 46438362173 137438953472 24937196420431 72304434398363648 Bool.false 161064384579 549755813888 12465135985651 36152217199181824 Bool.false 187870390887428237819904 1366937001057 1099511627776 19137383897299 11123759138209792 Bool.true 56590623277044809596928 102937744081 1099511627776 19112738015237 11123759138209792 (ep568 (BSN.head_sum_c_succ qz146 4 5 rfl rfl) (ep603 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep604 ep613) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz430 qz306)

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq qz427 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 55850182893 137438953472 5689344042647 18076108599590912 Bool.false 21537938727 549755813888 22695356785433 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 6 qz152 rfl)

noncomputable def ep616 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz306 99995 1000 0 1 4034681531866359 2251799813685248 500000000131521 65760500000000000000 80689595955795313641 450359962737049600 9999500002630288479 13152100000000000000000 qz153 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz307) Bool.false 33845361775666394038272 18889465931478580854784 1000000000263042 131521000000000000000 4034681531866359 2251799813685248 500000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep106 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep617 := nat_lit 1814858006969459208606837798775441

noncomputable def ep618 := BSN.cos_dyadic_bound_f 206400461 2147483648 2 1 1048576 263299 ep617 ep62 ep617 ep617 ep63 ep617 1043736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 206400461) qz288 0 1 ep617 ep62 ep617 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 206400461) qz289 0 1 ep617 ep63 ep617 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187870105) qz30)

noncomputable def ep619 := @Enclosure.Real.IsNear.cos_image qz157 qz436 Bool.false 187870105 1048576 399 524288 Bool.true 1043736 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 80689595955795313641 450359962737049600 9999500002630288479 13152100000000000000000 187870105 1048576 399 524288 (ep616 rfl) rfl) (Enclosure.sfrac_false_div 187870105 1048576) (BSN.cos_reduce2 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14524141246879304253440) qz32) 226375608064910080 72057594037927936 Bool.false 1043736 1048576 28 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 187870105 1048576 226375608064910080 72057594037927936 28 14524141246879304253440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043736 1048576 14524141246879304253440 151115727451828646838272 206400461 2147483648 263299 263042 (ep618 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep620 := BSN.sin_dyadic_bound_f 206400461 2147483648 1 0 1048576 263299 0 1 1 0 1 1 100626 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 206400461) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 206400461) qz284 0 0 rfl) rfl rfl

noncomputable def ep621 := @Enclosure.Real.IsNear.sin_image qz157 qz436 Bool.false 187870105 1048576 399 524288 Bool.true 100626 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 80689595955795313641 450359962737049600 9999500002630288479 13152100000000000000000 187870105 1048576 399 524288 (ep616 rfl) rfl) (Enclosure.sfrac_false_div 187870105 1048576) (BSN.sin_reduce2 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14524141246879304253440) qz32) 226375608064910080 72057594037927936 Bool.false 100626 1048576 28 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 187870105 1048576 226375608064910080 72057594037927936 28 14524141246879304253440 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 100626 1048576 14524141246879304253440 151115727451828646838272 206400461 2147483648 263299 263042 (ep620 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep622 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 55850182893 137438953472 5689344042647 18076108599590912 Bool.false 21537938727 549755813888 22695356785433 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz157) 428079 1048576 1 1048576 130467 131072 53001167 68954882048 55850182893 137438953472 5689344042647 18076108599590912 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 1043736 1048576 53001167 68954882048 130467 131072 53001167 68954882048 (ep619 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 428079 1048576 1 1048576 50313 524288 53001167 68954882048 21537938727 549755813888 22695356785433 72304434398363648 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 50313 524288 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 100626 1048576 53001167 68954882048 50313 524288 53001167 68954882048 (ep621 rfl rfl) rfl)) rfl)

noncomputable def ep623 := @ep565 55850182893 137438953472 5689344042647 18076108599590912 Bool.false 21537938727 549755813888 22695356785433 72304434398363648 Bool.false 126462465383158498983936 920135537913 1099511627776 294300743006063 144608868796727296 Bool.true 32909409208381290315776 59861866627 1099511627776 293856307768947 144608868796727296 (ep566 (BSN.head_sum_c_succ qz146 5 6 rfl rfl) (ep614 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep615 ep622) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz430 qz311)

noncomputable def ep624 := @Enclosure.Complex.IsNear.of_eq qz426 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 407488286275 1099511627776 42146706576891 144608868796727296 Bool.false 81592616725 1099511627776 42038557647717 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 7 qz152 rfl)

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz311 99995 1000 0 1 4381796493761783 2251799813685248 500000000131521 65760500000000000000 87631548078741898217 450359962737049600 9999500002630288479 13152100000000000000000 qz153 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000131521 65760500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz312) Bool.false 36757173121942042968064 18889465931478580854784 1000000000263042 131521000000000000000 4381796493761783 2251799813685248 500000000131521 65760500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep122 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep626 := nat_lit 4868957669086194840032399564169294447944111499651016845540462436945412569386945

noncomputable def ep627 := nat_lit 5718061689581162077495315903939061733651801479906495864197169944428703862721

noncomputable def ep628 := nat_lit 12742774176299759842435577870884631739903903391928052649778225250185100732616641

noncomputable def ep629 := BSN.sin_dyadic_bound_f 2948873241 2147483648 3 2 1048576 263299 ep626 ep170 ep627 ep628 ep172 ep627 1028167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2948873241) qz283 0 2 ep626 ep170 ep627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2948873241) qz284 0 2 ep628 ep172 ep627 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz437 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204033097) qz30)

noncomputable def ep630 := @Enclosure.Real.IsNear.cos_image qz158 qz437 Bool.false 204033097 1048576 399 524288 Bool.false 1028167 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 87631548078741898217 450359962737049600 9999500002630288479 13152100000000000000000 204033097 1048576 399 524288 (ep625 rfl) rfl) (Enclosure.sfrac_false_div 204033097 1048576) (BSN.cos_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207508506774992788127744) qz32) 226375608064910080 72057594037927936 Bool.false 1028167 1048576 30 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 204033097 1048576 226375608064910080 72057594037927936 30 207508506774992788127744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1028167 1048576 207508506774992788127744 151115727451828646838272 2948873241 2147483648 263299 263042 (ep629 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep631 := nat_lit 2707517843576588760941331009384692054072796078241634467906566762722753073598401

noncomputable def ep632 := nat_lit 8111117407350603958669002396346198038751084631765090411991305948279401813069761

noncomputable def ep633 := BSN.cos_dyadic_bound_f 2948873241 2147483648 3 2 1048576 263299 ep631 ep112 ep627 ep632 ep115 ep627 205873 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2948873241) qz288 0 2 ep631 ep112 ep627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2948873241) qz289 0 2 ep632 ep115 ep627 rfl rfl rfl rfl) rfl rfl

noncomputable def ep634 := @Enclosure.Real.IsNear.sin_image qz158 qz437 Bool.false 204033097 1048576 399 524288 Bool.true 205873 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 87631548078741898217 450359962737049600 9999500002630288479 13152100000000000000000 204033097 1048576 399 524288 (ep625 rfl) rfl) (Enclosure.sfrac_false_div 204033097 1048576) (BSN.sin_reduce3 qz437 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207508506774992788127744) qz32) 226375608064910080 72057594037927936 Bool.false 205873 1048576 30 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 204033097 1048576 226375608064910080 72057594037927936 30 207508506774992788127744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 205873 1048576 207508506774992788127744 151115727451828646838272 2948873241 2147483648 263299 263042 (ep633 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep635 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 407488286275 1099511627776 42146706576891 144608868796727296 Bool.false 81592616725 1099511627776 42038557647717 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz35 (Real.cos qz158) 396325 1048576 1 1048576 1028167 1048576 53001167 68954882048 407488286275 1099511627776 42146706576891 144608868796727296 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 1028167 1048576 53001167 68954882048 1028167 1048576 53001167 68954882048 (ep630 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 396325 1048576 1 1048576 205873 1048576 53001167 68954882048 81592616725 1099511627776 42038557647717 144608868796727296 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 205873 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 205873 1048576 53001167 68954882048 205873 1048576 53001167 68954882048 (ep634 rfl rfl) rfl)) rfl)

noncomputable def ep636 := @ep562 407488286275 1099511627776 42146706576891 144608868796727296 Bool.false 81592616725 1099511627776 42038557647717 144608868796727296 Bool.false ep563 331905956047 274877906944 168223724791477 72304434398363648 Bool.false 23893212413045451522048 10865375049 549755813888 41986858177083 18076108599590912 (ep564 (BSN.head_sum_c_succ qz146 6 7 rfl rfl) (ep623 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep624 ep635) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz430 qz316)

noncomputable def ep637 := @Enclosure.Complex.IsNear.of_eq qz425 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 323309163065 1099511627776 39412732085647 144608868796727296 Bool.true 107919000427 549755813888 19687302534197 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 8 qz152 rfl)

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz316 99995 1000 0 1 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 187290078072808491963 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz317) Bool.false 39279540158062550581248 18889465931478580854784 1000000000394563 131521000000000000000 9364972152248037 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep639 := nat_lit 2553427520094606397600749274109978896

noncomputable def ep640 := BSN.cos_dyadic_bound_f 1264098406 2147483648 2 1 1048576 263299 ep639 ep62 ep639 ep639 ep63 ep639 872095 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1264098406) qz288 0 1 ep639 ep62 ep639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1264098406) qz289 0 1 ep639 ep63 ep639 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz438 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 218034347) qz30)

noncomputable def ep641 := @Enclosure.Real.IsNear.cos_image qz159 qz438 Bool.false 218034347 1048576 399 524288 Bool.false 872095 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 187290078072808491963 900719925474099200 19999000007890865437 26304200000000000000000 218034347 1048576 399 524288 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 218034347 1048576) (BSN.cos_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88953017401629447553024) qz32) 226375608064910080 72057594037927936 Bool.false 872095 1048576 33 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 218034347 1048576 226375608064910080 72057594037927936 33 88953017401629447553024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 872095 1048576 88953017401629447553024 151115727451828646838272 1264098406 2147483648 263299 263042 (ep640 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep642 := BSN.sin_dyadic_bound_f 1264098406 2147483648 2 1 1048576 263299 ep639 ep58 ep639 ep639 ep59 ep639 582202 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1264098406) qz283 0 1 ep639 ep58 ep639 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1264098406) qz284 0 1 ep639 ep59 ep639 rfl rfl rfl rfl) rfl rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.sin_image qz159 qz438 Bool.false 218034347 1048576 399 524288 Bool.false 582202 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 187290078072808491963 900719925474099200 19999000007890865437 26304200000000000000000 218034347 1048576 399 524288 (ep638 rfl) rfl) (Enclosure.sfrac_false_div 218034347 1048576) (BSN.sin_reduce0 qz438 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88953017401629447553024) qz32) 226375608064910080 72057594037927936 Bool.false 582202 1048576 33 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 218034347 1048576 226375608064910080 72057594037927936 33 88953017401629447553024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 582202 1048576 88953017401629447553024 151115727451828646838272 1264098406 2147483648 263299 263042 (ep642 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep644 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 323309163065 1099511627776 39412732085647 144608868796727296 Bool.true 107919000427 549755813888 19687302534197 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz159) 370727 1048576 1 1048576 872095 1048576 53001167 68954882048 323309163065 1099511627776 39412732085647 144608868796727296 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 872095 1048576 53001167 68954882048 872095 1048576 53001167 68954882048 (ep641 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 370727 1048576 1 1048576 291101 524288 53001167 68954882048 107919000427 549755813888 19687302534197 72304434398363648 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 291101 524288 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 582202 1048576 53001167 68954882048 291101 524288 53001167 68954882048 (ep643 rfl rfl) rfl)) rfl)

noncomputable def ep645 := @ep560 323309163065 1099511627776 39412732085647 144608868796727296 Bool.true 107919000427 549755813888 19687302534197 72304434398363648 Bool.false 453805004040910072184832 1650932987253 1099511627776 2489140275951 957674627792896 Bool.true 53355794810463441649664 48526812689 274877906944 1242614140679 478837313896448 (ep561 (BSN.head_sum_c_succ qz146 7 8 rfl rfl) (ep636 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep637 ep644) rfl rfl

theorem EMRow29.d11 : Enclosure.Complex.IsNear qz145 Bool.false 1650932987253 1099511627776 2489140275951 957674627792896 Bool.true 48526812689 274877906944 1242614140679 478837313896448 := ep559 (BSN.head_sum_c_succ qz146 8 9 rfl rfl) (ep645 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz160 := (BSN.headSumC qz423 17)

noncomputable abbrev qz161 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 16) qz424)

noncomputable def ep646 := @Enclosure.Complex.IsNear.of_eq qz160 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 16) qz161) Bool.false 2518279435067 1099511627776 631547995803945 144608868796727296 Bool.true 118881239681 1099511627776 630720849976307 144608868796727296

noncomputable def ep647 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 16) qz161 Bool.false 580951703879 274877906944 75453509093041 18076108599590912 Bool.false 18845023153 274877906944 75350129115327 18076108599590912 Bool.false

noncomputable abbrev qz162 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 15) qz424)

noncomputable def ep648 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 15) qz162) Bool.false 580951703879 274877906944 75453509093041 18076108599590912 Bool.false 18845023153 274877906944 75350129115327 18076108599590912

noncomputable def ep649 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 15) qz162 Bool.false 522955191305 274877906944 143704023568631 36152217199181824 Bool.false 119508788729 549755813888 287011128464631 72304434398363648 Bool.false

noncomputable abbrev qz163 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 14) qz424)

noncomputable def ep650 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 14) qz163) Bool.false 522955191305 274877906944 143704023568631 36152217199181824 Bool.false 119508788729 549755813888 287011128464631 72304434398363648

noncomputable def ep651 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 14) qz163 Bool.false 898982620869 549755813888 272485833341987 72304434398363648 Bool.false 238604779519 1099511627776 544315545109333 144608868796727296 Bool.false

noncomputable abbrev qz164 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 13) qz424)

noncomputable def ep652 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 13) qz164) Bool.false 898982620869 549755813888 272485833341987 72304434398363648 Bool.false 238604779519 1099511627776 544315545109333 144608868796727296

noncomputable def ep653 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 13) qz164 Bool.false 833743460571 549755813888 257042318370533 72304434398363648 Bool.true 4627658077 137438953472 128340718488993 36152217199181824 Bool.false

noncomputable abbrev qz165 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 12) qz424)

noncomputable def ep654 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 12) qz165) Bool.false 833743460571 549755813888 257042318370533 72304434398363648 Bool.true 4627658077 137438953472 128340718488993 36152217199181824

noncomputable def ep655 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 12) qz165 Bool.false 1971422254569 1099511627776 481865883191523 144608868796727296 Bool.true 128489941379 1099511627776 481236436574581 144608868796727296 Bool.true

noncomputable def ep656 := nat_lit 1833421258960030968840192

noncomputable abbrev qz166 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 11) qz424)

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 11) qz166) Bool.false 1971422254569 1099511627776 481865883191523 144608868796727296 Bool.true 128489941379 1099511627776 481236436574581 144608868796727296

noncomputable def ep658 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 11) qz166 Bool.false 1796904855197 1099511627776 448279798212835 144608868796727296 Bool.false 76685331709 549755813888 27975356058023 9038054299795456 Bool.false

noncomputable abbrev qz167 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 10) qz424)

noncomputable def ep659 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 10) qz167) Bool.false 1796904855197 1099511627776 448279798212835 144608868796727296 Bool.false 76685331709 549755813888 27975356058023 9038054299795456

noncomputable def ep660 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 10) qz167 Bool.false 1005063099139 549755813888 15886381248641 5561879569104896 Bool.true 15159153907 137438953472 15859517254797 5561879569104896 Bool.true

noncomputable abbrev qz439 := (@HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast 9) qz147)

noncomputable def ep661 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 10) (@HAdd.hAdd Complex Complex Complex qz4 qz145 qz439) Bool.false 1005063099139 549755813888 15886381248641 5561879569104896 Bool.true 15159153907 137438953472 15859517254797 5561879569104896

noncomputable def ep662 := @Enclosure.Complex.IsNear.addLitP qz145 qz439 Bool.false 1650932987253 1099511627776 2489140275951 957674627792896 Bool.true 48526812689 274877906944 1242614140679 478837313896448 Bool.false

noncomputable def ep663 := nat_lit 2210157128303826308169728

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz430 qz321)

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz439 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 359193211025 1099511627776 37185730796065 144608868796727296 Bool.false 18208504875 274877906944 2317373633729 9038054299795456 (BSN.cpow_neg_s_mk qz151 99995 1000 9 qz152 rfl)

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz321 99995 1000 0 1 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 197898460445671246779 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 41504390431577613533184 18889465931478580854784 1000000000394563 131521000000000000000 9895417793173221 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep162 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep666 := nat_lit 4834419857360376028867127779093146397021577759133671848238188091529194584590145

noncomputable def ep667 := nat_lit 5637321407430835819286174253175333654832167498322961707426274774148162701121

noncomputable def ep668 := nat_lit 12652448725093715865230299901215004309139165859876617664526088175799269743839041

noncomputable def ep669 := BSN.sin_dyadic_bound_f 2943635959 2147483648 3 2 1048576 263299 ep666 ep170 ep667 ep668 ep172 ep667 1027661 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2943635959) qz283 0 2 ep666 ep170 ep667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2943635959) qz284 0 2 ep668 ep172 ep667 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz440 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230384129) qz30)

noncomputable def ep670 := @Enclosure.Real.IsNear.cos_image qz168 qz440 Bool.false 230384129 1048576 399 524288 Bool.false 1027661 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 197898460445671246779 900719925474099200 19999000007890865437 26304200000000000000000 230384129 1048576 399 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 230384129 1048576) (BSN.cos_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207139965811550865850368) qz32) 226375608064910080 72057594037927936 Bool.false 1027661 1048576 34 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 230384129 1048576 226375608064910080 72057594037927936 34 207139965811550865850368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1027661 1048576 207139965811550865850368 151115727451828646838272 2943635959 2147483648 263299 263042 (ep669 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep671 := nat_lit 2688294285825733720845864843608714813303024162851294565335627284082507285972801

noncomputable def ep672 := nat_lit 8053608214662339490899022182319793772599408153557237772592029302699225532516161

noncomputable def ep673 := BSN.cos_dyadic_bound_f 2943635959 2147483648 3 2 1048576 263299 ep671 ep112 ep667 ep672 ep115 ep667 208380 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2943635959) qz288 0 2 ep671 ep112 ep667 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2943635959) qz289 0 2 ep672 ep115 ep667 rfl rfl rfl rfl) rfl rfl

noncomputable def ep674 := @Enclosure.Real.IsNear.sin_image qz168 qz440 Bool.false 230384129 1048576 399 524288 Bool.true 208380 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 197898460445671246779 900719925474099200 19999000007890865437 26304200000000000000000 230384129 1048576 399 524288 (ep665 rfl) rfl) (Enclosure.sfrac_false_div 230384129 1048576) (BSN.sin_reduce3 qz440 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207139965811550865850368) qz32) 226375608064910080 72057594037927936 Bool.false 208380 1048576 34 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 230384129 1048576 226375608064910080 72057594037927936 34 207139965811550865850368 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 208380 1048576 207139965811550865850368 151115727451828646838272 2943635959 2147483648 263299 263042 (ep673 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep675 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 359193211025 1099511627776 37185730796065 144608868796727296 Bool.false 18208504875 274877906944 2317373633729 9038054299795456 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz168) 349525 1048576 1 1048576 1027661 1048576 53001167 68954882048 359193211025 1099511627776 37185730796065 144608868796727296 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 1027661 1048576 53001167 68954882048 1027661 1048576 53001167 68954882048 (ep670 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 349525 1048576 1 1048576 52095 262144 53001167 68954882048 18208504875 274877906944 2317373633729 9038054299795456 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 52095 262144 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 208380 1048576 53001167 68954882048 52095 262144 53001167 68954882048 (ep674 rfl rfl) rfl)) rfl)

noncomputable def ep676 := @ep662 359193211025 1099511627776 37185730796065 144608868796727296 Bool.false 18208504875 274877906944 2317373633729 9038054299795456 Bool.false ep663 1005063099139 549755813888 15886381248641 5561879569104896 Bool.true 8333832993996240060416 15159153907 137438953472 15859517254797 5561879569104896 EMRow29.d11 (ep664 ep675) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log (Enclosure.sfrac Bool.false 10 1)))

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq qz167 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.true 213221343081 1099511627776 35233885748169 144608868796727296 Bool.false 137321947337 549755813888 17629124151823 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 10 qz152 rfl)

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz52 99995 1000 0 1 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 207387973884824079291 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz327) Bool.false 43494585150108164161536 18889465931478580854784 1000000000394563 131521000000000000000 10369917190100709 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep179 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := nat_lit 522771946055104902198918468958901754998151236584797783325867420263959756800000

noncomputable def ep680 := nat_lit 213900396456072958457763137234160692888323582191947115800067840409600000000

noncomputable def ep681 := nat_lit 1567888037372402560679839880602236943608677062590009455746002125111060070400000

noncomputable def ep682 := BSN.cos_dyadic_bound_f 1955583880 2147483648 3 2 1048576 263299 ep679 ep112 ep680 ep681 ep115 ep680 643029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1955583880) qz288 0 2 ep679 ep112 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1955583880) qz289 0 2 ep681 ep115 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 241431377) qz30)

noncomputable def ep683 := @Enclosure.Real.IsNear.cos_image qz169 qz441 Bool.false 241431377 1048576 399 524288 Bool.true 643029 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 207387973884824079291 900719925474099200 19999000007890865437 26304200000000000000000 241431377 1048576 399 524288 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 241431377 1048576) (BSN.cos_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137611981836275431768064) qz32) 226375608064910080 72057594037927936 Bool.false 643029 1048576 36 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 241431377 1048576 226375608064910080 72057594037927936 36 137611981836275431768064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 643029 1048576 137611981836275431768064 151115727451828646838272 1955583880 2147483648 263299 263042 (ep682 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep684 := nat_lit 940818382582023965591287033616235830442361566986882452293921302202799882240000

noncomputable def ep685 := nat_lit 2463701829930086267949201090582238533846270627737333746391831872122860339200000

noncomputable def ep686 := BSN.sin_dyadic_bound_f 1955583880 2147483648 3 2 1048576 263299 ep684 ep170 ep680 ep685 ep172 ep680 828266 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1955583880) qz283 0 2 ep684 ep170 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1955583880) qz284 0 2 ep685 ep172 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable def ep687 := @Enclosure.Real.IsNear.sin_image qz169 qz441 Bool.false 241431377 1048576 399 524288 Bool.true 828266 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 207387973884824079291 900719925474099200 19999000007890865437 26304200000000000000000 241431377 1048576 399 524288 (ep678 rfl) rfl) (Enclosure.sfrac_false_div 241431377 1048576) (BSN.sin_reduce2 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137611981836275431768064) qz32) 226375608064910080 72057594037927936 Bool.false 828266 1048576 36 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 241431377 1048576 226375608064910080 72057594037927936 36 137611981836275431768064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 828266 1048576 137611981836275431768064 151115727451828646838272 1955583880 2147483648 263299 263042 (ep686 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep688 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.true 213221343081 1099511627776 35233885748169 144608868796727296 Bool.false 137321947337 549755813888 17629124151823 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ft qz50 (Real.cos qz169) 331589 1048576 1 1048576 643029 1048576 53001167 68954882048 213221343081 1099511627776 35233885748169 144608868796727296 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.true 643029 1048576 53001167 68954882048 643029 1048576 53001167 68954882048 (ep683 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 331589 1048576 1 1048576 414133 524288 53001167 68954882048 137321947337 549755813888 17629124151823 72304434398363648 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 414133 524288 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 828266 1048576 53001167 68954882048 414133 524288 53001167 68954882048 (ep687 rfl rfl) rfl)) rfl)

noncomputable def ep689 := @ep660 213221343081 1099511627776 35233885748169 144608868796727296 Bool.false 137321947337 549755813888 17629124151823 72304434398363648 Bool.false 987858891148125521575936 1796904855197 1099511627776 448279798212835 144608868796727296 Bool.false 10539551736738137243648 76685331709 549755813888 27975356058023 9038054299795456 (ep661 (BSN.head_sum_c_succ qz146 9 10 rfl rfl) (ep676 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep677 ep688) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz430 (Real.log (Enclosure.sfrac Bool.false 11 1)))

noncomputable def ep690 := @Enclosure.Complex.IsNear.of_eq qz166 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 43629349843 274877906944 4099863889 17652449804288 Bool.true 281860604797 1099511627776 33630739646213 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 11 qz152 rfl)

noncomputable def ep691 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz55 99995 1000 0 1 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 215972325277037317051 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 45294944137145793642496 18889465931478580854784 1000000000394563 131521000000000000000 10799156221662949 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep190 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep692 := nat_lit 811508253899012185520298137242061022568204213139343712005168840063892712390656

noncomputable def ep693 := nat_lit 515201097797425861477647637830328610713168102504974273097237187351795531776

noncomputable def ep694 := nat_lit 2433494359501441704837939116450522410483186303213021187469312045816974546108416

noncomputable def ep695 := BSN.cos_dyadic_bound_f 2182715324 2147483648 3 2 1048576 263299 ep692 ep112 ep693 ep694 ep115 ep693 551996 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2182715324) qz288 0 2 ep692 ep112 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2182715324) qz289 0 2 ep694 ep115 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz442 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 251424877) qz30)

noncomputable def ep696 := @Enclosure.Real.IsNear.cos_image qz170 qz442 Bool.false 251424877 1048576 399 524288 Bool.false 551996 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 215972325277037317051 900719925474099200 19999000007890865437 26304200000000000000000 251424877 1048576 399 524288 (ep691 rfl) rfl) (Enclosure.sfrac_false_div 251424877 1048576) (BSN.cos_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153594936258714176323584) qz32) 226375608064910080 72057594037927936 Bool.false 551996 1048576 38 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 251424877 1048576 226375608064910080 72057594037927936 38 153594936258714176323584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 551996 1048576 153594936258714176323584 151115727451828646838272 2182715324 2147483648 263299 263042 (ep695 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep697 := nat_lit 1460302696139983993247354528925445577734197049168814702190826122365125445877760

noncomputable def ep698 := nat_lit 3823768164303524149967345670057775028696028094704744737867149079319616117866496

noncomputable def ep699 := BSN.sin_dyadic_bound_f 2182715324 2147483648 3 2 1048576 263299 ep697 ep170 ep693 ep698 ep172 ep693 891521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2182715324) qz283 0 2 ep697 ep170 ep693 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2182715324) qz284 0 2 ep698 ep172 ep693 rfl rfl rfl rfl) rfl rfl

noncomputable def ep700 := @Enclosure.Real.IsNear.sin_image qz170 qz442 Bool.false 251424877 1048576 399 524288 Bool.false 891521 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 215972325277037317051 900719925474099200 19999000007890865437 26304200000000000000000 251424877 1048576 399 524288 (ep691 rfl) rfl) (Enclosure.sfrac_false_div 251424877 1048576) (BSN.sin_reduce0 qz442 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153594936258714176323584) qz32) 226375608064910080 72057594037927936 Bool.false 891521 1048576 38 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 251424877 1048576 226375608064910080 72057594037927936 38 153594936258714176323584 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 891521 1048576 153594936258714176323584 151115727451828646838272 2182715324 2147483648 263299 263042 (ep699 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep701 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 43629349843 274877906944 4099863889 17652449804288 Bool.true 281860604797 1099511627776 33630739646213 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz170) 316157 1048576 1 1048576 137999 262144 53001167 68954882048 43629349843 274877906944 4099863889 17652449804288 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 551996 1048576 53001167 68954882048 137999 262144 53001167 68954882048 (ep696 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 316157 1048576 1 1048576 891521 1048576 53001167 68954882048 281860604797 1099511627776 33630739646213 144608868796727296 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 891521 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 891521 1048576 53001167 68954882048 891521 1048576 53001167 68954882048 (ep700 rfl rfl) rfl)) rfl)

noncomputable def ep702 := @ep658 43629349843 274877906944 4099863889 17652449804288 Bool.true 281860604797 1099511627776 33630739646213 144608868796727296 Bool.false 541900423038748260827136 1971422254569 1099511627776 481865883191523 144608868796727296 Bool.true 70638092299233554071552 128489941379 1099511627776 481236436574581 144608868796727296 (ep659 (BSN.head_sum_c_succ qz146 10 11 rfl rfl) (ep689 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep690 ep701) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz430 qz335)

noncomputable def ep703 := @Enclosure.Complex.IsNear.of_eq qz165 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.true 303935333427 1099511627776 32218753549543 144608868796727296 Bool.false 91468676763 1099511627776 32126437381391 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 12 qz152 rfl)

noncomputable def ep704 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz335 99995 1000 0 1 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 223809217935860124603 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz336) Bool.false 46938541828353910898688 18889465931478580854784 1000000000394563 131521000000000000000 11191020447815397 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep705 := nat_lit 155308312606724842259553034681673281

noncomputable def ep706 := BSN.cos_dyadic_bound_f 627767279 2147483648 2 1 1048576 263299 ep705 ep62 ep705 ep705 ep63 ep705 1004091 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 627767279) qz288 0 1 ep705 ep62 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 627767279) qz289 0 1 ep705 ep63 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz443 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 260548221) qz30)

noncomputable def ep707 := @Enclosure.Real.IsNear.cos_image qz171 qz443 Bool.false 260548221 1048576 399 524288 Bool.true 1004091 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 223809217935860124603 900719925474099200 19999000007890865437 26304200000000000000000 260548221 1048576 399 524288 (ep704 rfl) rfl) (Enclosure.sfrac_false_div 260548221 1048576) (BSN.cos_reduce2 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44175195085818478723072) qz32) 226375608064910080 72057594037927936 Bool.false 1004091 1048576 39 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 260548221 1048576 226375608064910080 72057594037927936 39 44175195085818478723072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1004091 1048576 44175195085818478723072 151115727451828646838272 627767279 2147483648 263299 263042 (ep706 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep708 := BSN.sin_dyadic_bound_f 627767279 2147483648 2 1 1048576 263299 ep705 ep58 ep705 ep705 ep59 ep705 302179 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 627767279) qz283 0 1 ep705 ep58 ep705 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 627767279) qz284 0 1 ep705 ep59 ep705 rfl rfl rfl rfl) rfl rfl

noncomputable def ep709 := @Enclosure.Real.IsNear.sin_image qz171 qz443 Bool.false 260548221 1048576 399 524288 Bool.true 302179 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 223809217935860124603 900719925474099200 19999000007890865437 26304200000000000000000 260548221 1048576 399 524288 (ep704 rfl) rfl) (Enclosure.sfrac_false_div 260548221 1048576) (BSN.sin_reduce2 qz443 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44175195085818478723072) qz32) 226375608064910080 72057594037927936 Bool.false 302179 1048576 39 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 260548221 1048576 226375608064910080 72057594037927936 39 44175195085818478723072 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 302179 1048576 44175195085818478723072 151115727451828646838272 627767279 2147483648 263299 263042 (ep708 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep710 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.true 303935333427 1099511627776 32218753549543 144608868796727296 Bool.false 91468676763 1099511627776 32126437381391 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ft qz56 (Real.cos qz171) 302697 1048576 1 1048576 1004091 1048576 53001167 68954882048 303935333427 1099511627776 32218753549543 144608868796727296 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.true 1004091 1048576 53001167 68954882048 1004091 1048576 53001167 68954882048 (ep707 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 302697 1048576 1 1048576 302179 1048576 53001167 68954882048 91468676763 1099511627776 32126437381391 144608868796727296 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 302179 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 302179 1048576 53001167 68954882048 302179 1048576 53001167 68954882048 (ep709 rfl rfl) rfl)) rfl)

noncomputable def ep711 := @ep655 303935333427 1099511627776 32218753549543 144608868796727296 Bool.false 91468676763 1099511627776 32126437381391 144608868796727296 Bool.false ep656 833743460571 549755813888 257042318370533 72304434398363648 Bool.true 40705310920264191574016 4627658077 137438953472 128340718488993 36152217199181824 (ep657 (BSN.head_sum_c_succ qz146 11 12 rfl rfl) (ep702 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep703 ep710) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz430 qz340)

noncomputable def ep712 := @Enclosure.Complex.IsNear.of_eq qz164 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 32619580149 274877906944 7721757485727 36152217199181824 Bool.false 275626044135 1099511627776 30952671153361 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 13 qz152 rfl)

noncomputable def ep713 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz340 99995 1000 0 1 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 231018389562320571323 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 48450490295254733815808 18889465931478580854784 1000000000394563 131521000000000000000 11551497052968677 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep216 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep714 := nat_lit 812703789561918457414442533299732736

noncomputable def ep715 := BSN.sin_dyadic_bound_f 949473988 2147483648 2 1 1048576 263299 ep714 ep58 ep714 ep714 ep59 ep714 448652 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 949473988) qz283 0 1 ep714 ep58 ep714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 949473988) qz284 0 1 ep714 ep59 ep714 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz444 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268940801) qz30)

noncomputable def ep716 := @Enclosure.Real.IsNear.cos_image qz172 qz444 Bool.false 268940801 1048576 399 524288 Bool.false 448652 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 231018389562320571323 900719925474099200 19999000007890865437 26304200000000000000000 268940801 1048576 399 524288 (ep713 rfl) rfl) (Enclosure.sfrac_false_div 268940801 1048576) (BSN.cos_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66813292216129192722432) qz32) 226375608064910080 72057594037927936 Bool.false 448652 1048576 40 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 268940801 1048576 226375608064910080 72057594037927936 40 66813292216129192722432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 448652 1048576 66813292216129192722432 151115727451828646838272 949473988 2147483648 263299 263042 (ep715 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep717 := BSN.cos_dyadic_bound_f 949473988 2147483648 2 1 1048576 263299 ep714 ep62 ep714 ep714 ep63 ep714 947745 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 949473988) qz288 0 1 ep714 ep62 ep714 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 949473988) qz289 0 1 ep714 ep63 ep714 rfl rfl rfl rfl) rfl rfl

noncomputable def ep718 := @Enclosure.Real.IsNear.sin_image qz172 qz444 Bool.false 268940801 1048576 399 524288 Bool.true 947745 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 231018389562320571323 900719925474099200 19999000007890865437 26304200000000000000000 268940801 1048576 399 524288 (ep713 rfl) rfl) (Enclosure.sfrac_false_div 268940801 1048576) (BSN.sin_reduce3 qz444 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 66813292216129192722432) qz32) 226375608064910080 72057594037927936 Bool.false 947745 1048576 40 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 268940801 1048576 226375608064910080 72057594037927936 40 66813292216129192722432 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 947745 1048576 66813292216129192722432 151115727451828646838272 949473988 2147483648 263299 263042 (ep717 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep719 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 32619580149 274877906944 7721757485727 36152217199181824 Bool.false 275626044135 1099511627776 30952671153361 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz172) 290823 1048576 1 1048576 112163 262144 53001167 68954882048 32619580149 274877906944 7721757485727 36152217199181824 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 448652 1048576 53001167 68954882048 112163 262144 53001167 68954882048 (ep716 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz58 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 290823 1048576 1 1048576 947745 1048576 53001167 68954882048 275626044135 1099511627776 30952671153361 144608868796727296 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 947745 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 947745 1048576 53001167 68954882048 947745 1048576 53001167 68954882048 (ep718 rfl rfl) rfl)) rfl)

noncomputable def ep720 := @ep653 32619580149 274877906944 7721757485727 36152217199181824 Bool.false 275626044135 1099511627776 30952671153361 144608868796727296 Bool.false 247110461203502214414336 898982620869 549755813888 272485833341987 72304434398363648 Bool.false 32793591190508659539968 238604779519 1099511627776 544315545109333 144608868796727296 (ep654 (BSN.head_sum_c_succ qz146 12 13 rfl rfl) (ep711 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep712 ep719) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz430 qz345)

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq qz163 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 146927761741 549755813888 14922213795275 72304434398363648 Bool.false 412797939 1099511627776 29706711819929 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 14 qz152 rfl)

noncomputable def ep722 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz345 99995 1000 0 1 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 47538624436350658751 180143985094819840 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz346) Bool.false 49850353174629559828480 18889465931478580854784 1000000000394563 131521000000000000000 11885250371606245 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep230 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep723 := nat_lit 8314094175688719787814587360159960203475670858678687142007164841122144624640000

noncomputable def ep724 := nat_lit 16645110855728759939350604940994298415693987560846523638774117339161600000000

noncomputable def ep725 := nat_lit 21748059328275467166279256392419238335477538173821857666984559346294593331200000

noncomputable def ep726 := BSN.sin_dyadic_bound_f 3370240060 2147483648 3 2 1048576 263299 ep723 ep170 ep724 ep725 ep172 ep724 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3370240060) qz283 0 2 ep723 ep170 ep724 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3370240060) qz284 0 2 ep725 ep172 ep724 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 276711213) qz30)

noncomputable def ep727 := @Enclosure.Real.IsNear.cos_image qz173 qz445 Bool.false 276711213 1048576 399 524288 Bool.false 1048574 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 47538624436350658751 180143985094819840 19999000007890865437 26304200000000000000000 276711213 1048576 399 524288 (ep722 rfl) rfl) (Enclosure.sfrac_false_div 276711213 1048576) (BSN.cos_reduce3 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237159560613931962597376) qz32) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 41 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 276711213 1048576 226375608064910080 72057594037927936 41 237159560613931962597376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048574 1048576 237159560613931962597376 151115727451828646838272 3370240060 2147483648 263299 263042 (ep726 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep728 := nat_lit 4626339035762945997647815468951530912337903360404091311621213408329707724800000

noncomputable def ep729 := nat_lit 13845726885577380473064745196972604140182322106090580887586091990310799974400000

noncomputable def ep730 := BSN.cos_dyadic_bound_f 3370240060 2147483648 3 2 1048576 263299 ep728 ep112 ep724 ep729 ep115 ep724 1473 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3370240060) qz288 0 2 ep728 ep112 ep724 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3370240060) qz289 0 2 ep729 ep115 ep724 rfl rfl rfl rfl) rfl rfl

noncomputable def ep731 := @Enclosure.Real.IsNear.sin_image qz173 qz445 Bool.false 276711213 1048576 399 524288 Bool.true 1473 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 47538624436350658751 180143985094819840 19999000007890865437 26304200000000000000000 276711213 1048576 399 524288 (ep722 rfl) rfl) (Enclosure.sfrac_false_div 276711213 1048576) (BSN.sin_reduce3 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237159560613931962597376) qz32) 226375608064910080 72057594037927936 Bool.false 1473 1048576 41 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 276711213 1048576 226375608064910080 72057594037927936 41 237159560613931962597376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1473 1048576 237159560613931962597376 151115727451828646838272 3370240060 2147483648 263299 263042 (ep730 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep732 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 146927761741 549755813888 14922213795275 72304434398363648 Bool.false 412797939 1099511627776 29706711819929 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz60 (Real.cos qz173) 280243 1048576 1 1048576 524287 524288 53001167 68954882048 146927761741 549755813888 14922213795275 72304434398363648 qz348 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1048574 1048576 53001167 68954882048 524287 524288 53001167 68954882048 (ep727 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 280243 1048576 1 1048576 1473 1048576 53001167 68954882048 412797939 1099511627776 29706711819929 144608868796727296 qz348 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 1473 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 1473 1048576 53001167 68954882048 1473 1048576 53001167 68954882048 (ep731 rfl rfl) rfl)) rfl)

noncomputable def ep733 := @ep651 146927761741 549755813888 14922213795275 72304434398363648 Bool.false 412797939 1099511627776 29706711819929 144608868796727296 Bool.false 574995313645670031687680 522955191305 274877906944 143704023568631 36152217199181824 Bool.false 262802605657921744273408 119508788729 549755813888 287011128464631 72304434398363648 (ep652 (BSN.head_sum_c_succ qz146 13 14 rfl rfl) (ep720 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep721 ep732) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz430 qz350)

noncomputable def ep734 := @Enclosure.Complex.IsNear.of_eq qz162 (Complex.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 28998256287 137438953472 7202994617451 36152217199181824 Bool.true 81818742423 549755813888 14389387996677 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 15 qz152 rfl)

noncomputable def ep735 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz350 99995 1000 0 1 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 243907113747875711931 900719925474099200 19999000007890865437 26304200000000000000000 qz153 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz351) Bool.false 51153586820399524478976 18889465931478580854784 1000000000394563 131521000000000000000 12195965485668069 4503599627370496 1000000000394563 131521000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep241 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep736 := nat_lit 3029089018552656279309059963606422081

noncomputable def ep737 := BSN.cos_dyadic_bound_f 1319252753 2147483648 2 1 1048576 263299 ep736 ep62 ep736 ep736 ep63 ep736 856856 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1319252753) qz288 0 1 ep736 ep62 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1319252753) qz289 0 1 ep736 ep63 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 283945251) qz30)

noncomputable def ep738 := @Enclosure.Real.IsNear.cos_image qz174 qz446 Bool.false 283945251 1048576 399 524288 Bool.false 856856 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 243907113747875711931 900719925474099200 19999000007890865437 26304200000000000000000 283945251 1048576 399 524288 (ep735 rfl) rfl) (Enclosure.sfrac_false_div 283945251 1048576) (BSN.cos_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92834159520464462938112) qz32) 226375608064910080 72057594037927936 Bool.false 856856 1048576 43 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 283945251 1048576 226375608064910080 72057594037927936 43 92834159520464462938112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 856856 1048576 92834159520464462938112 151115727451828646838272 1319252753 2147483648 263299 263042 (ep737 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep739 := BSN.sin_dyadic_bound_f 1319252753 2147483648 2 1 1048576 263299 ep736 ep58 ep736 ep736 ep59 ep736 604406 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1319252753) qz283 0 1 ep736 ep58 ep736 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1319252753) qz284 0 1 ep736 ep59 ep736 rfl rfl rfl rfl) rfl rfl

noncomputable def ep740 := @Enclosure.Real.IsNear.sin_image qz174 qz446 Bool.false 283945251 1048576 399 524288 Bool.false 604406 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 243907113747875711931 900719925474099200 19999000007890865437 26304200000000000000000 283945251 1048576 399 524288 (ep735 rfl) rfl) (Enclosure.sfrac_false_div 283945251 1048576) (BSN.sin_reduce0 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92834159520464462938112) qz32) 226375608064910080 72057594037927936 Bool.false 604406 1048576 43 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 283945251 1048576 226375608064910080 72057594037927936 43 92834159520464462938112 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 604406 1048576 92834159520464462938112 151115727451828646838272 1319252753 2147483648 263299 263042 (ep739 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep741 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz62 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 28998256287 137438953472 7202994617451 36152217199181824 Bool.true 81818742423 549755813888 14389387996677 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz62 (Real.cos qz174) 270741 1048576 1 1048576 107107 131072 53001167 68954882048 28998256287 137438953472 7202994617451 36152217199181824 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 856856 1048576 53001167 68954882048 107107 131072 53001167 68954882048 (ep738 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz62 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 270741 1048576 1 1048576 302203 524288 53001167 68954882048 81818742423 549755813888 14389387996677 72304434398363648 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 302203 524288 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 604406 1048576 53001167 68954882048 302203 524288 53001167 68954882048 (ep740 rfl rfl) rfl)) rfl)

noncomputable def ep742 := @ep649 28998256287 137438953472 7202994617451 36152217199181824 Bool.true 81818742423 549755813888 14389387996677 72304434398363648 Bool.false 79845394198905002917888 580951703879 274877906944 75453509093041 18076108599590912 Bool.false 20720322082431437897728 18845023153 274877906944 75350129115327 18076108599590912 (ep650 (BSN.head_sum_c_succ qz146 14 15 rfl rfl) (ep733 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep734 ep741) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz430 qz355)

noncomputable def ep743 := @Enclosure.Complex.IsNear.of_eq qz161 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 194472619551 1099511627776 27919923059617 144608868796727296 Bool.true 194261332293 1099511627776 27919817053691 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 16 qz152 rfl)

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz355 99995 1000 0 1 3121657384082679 1125899906842624 250000000131521 32880250000000000000 62430026024269497321 225179981368524800 4999750002630288479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 52372720210750067441664 18889465931478580854784 1000000000526084 131521000000000000000 3121657384082679 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep745 := nat_lit 288405740061333826878258642133644121196920811119783993645436358011596146916161

noncomputable def ep746 := nat_lit 65125961780627615860142935727909475382866941471479678662971032265572662081

noncomputable def ep747 := nat_lit 865086968260440225403055640529476544639996699476409021578983131970257295424321

noncomputable def ep748 := BSN.cos_dyadic_bound_f 1685463177 2147483648 3 2 1048576 263299 ep745 ep112 ep746 ep747 ep115 ep746 741857 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685463177) qz288 0 2 ep745 ep112 ep746 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685463177) qz289 0 2 ep747 ep115 ep746 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145356231) qz516)

noncomputable def ep749 := @Enclosure.Real.IsNear.cos_image qz175 qz447 Bool.false 145356231 524288 799 1048576 Bool.false 741857 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 62430026024269497321 225179981368524800 4999750002630288479 6576050000000000000000 145356231 524288 799 1048576 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 145356231 524288) (BSN.cos_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59301963562690273083392) qz287) 226375608064910080 72057594037927936 Bool.false 741857 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 145356231 524288 226375608064910080 72057594037927936 44 59301963562690273083392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741857 1048576 59301963562690273083392 75557863725914323419136 1685463177 2147483648 263299 263042 (ep748 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep750 := nat_lit 8070065785396524006463579555579022241

noncomputable def ep751 := BSN.sin_dyadic_bound_f 1685463177 2147483648 2 1 1048576 263299 ep750 ep58 ep750 ep750 ep59 ep750 741051 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685463177) qz283 0 1 ep750 ep58 ep750 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685463177) qz284 0 1 ep750 ep59 ep750 rfl rfl rfl rfl) rfl rfl

noncomputable def ep752 := @Enclosure.Real.IsNear.sin_image qz175 qz447 Bool.false 145356231 524288 799 1048576 Bool.false 741051 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 62430026024269497321 225179981368524800 4999750002630288479 6576050000000000000000 145356231 524288 799 1048576 (ep744 rfl) rfl) (Enclosure.sfrac_false_div 145356231 524288) (BSN.sin_reduce0 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59301963562690273083392) qz287) 226375608064910080 72057594037927936 Bool.false 741051 1048576 44 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 145356231 524288 226375608064910080 72057594037927936 44 59301963562690273083392 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741051 1048576 59301963562690273083392 75557863725914323419136 1685463177 2147483648 263299 263042 (ep751 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep753 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 194472619551 1099511627776 27919923059617 144608868796727296 Bool.true 194261332293 1099511627776 27919817053691 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz175) 262143 1048576 1 1048576 741857 1048576 106133855 137909764096 194472619551 1099511627776 27919923059617 144608868796727296 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 741857 1048576 106133855 137909764096 741857 1048576 106133855 137909764096 (ep749 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz64 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 262143 1048576 1 1048576 741051 1048576 106133855 137909764096 194261332293 1099511627776 27919817053691 144608868796727296 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 741051 1048576 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 741051 1048576 106133855 137909764096 741051 1048576 106133855 137909764096 (ep752 rfl rfl) rfl)) rfl)

noncomputable def ep754 := @ep647 194472619551 1099511627776 27919923059617 144608868796727296 Bool.true 194261332293 1099511627776 27919817053691 144608868796727296 Bool.false 692219380211335716405248 2518279435067 1099511627776 631547995803945 144608868796727296 Bool.true 32677826338421278244864 118881239681 1099511627776 630720849976307 144608868796727296 (ep648 (BSN.head_sum_c_succ qz146 15 16 rfl rfl) (ep742 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep743 ep753) rfl rfl

theorem EMRow29.d12 : Enclosure.Complex.IsNear qz160 Bool.false 2518279435067 1099511627776 631547995803945 144608868796727296 Bool.true 118881239681 1099511627776 630720849976307 144608868796727296 := ep646 (BSN.head_sum_c_succ qz146 16 17 rfl rfl) (ep754 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep755 := nat_lit 5134592455540199781226977180043

noncomputable def ep756 := nat_lit 1844536061402088358390267904000

noncomputable def ep757 := nat_lit 1131373319437066999963884190409622630937

noncomputable def ep758 := nat_lit 191438201363326735366190793976115625984000

noncomputable abbrev qz530 := (@HAdd.hAdd Complex Complex Complex qz537 (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz544) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz448 := qz530

noncomputable abbrev qz176 := (Complex.Stirling.logGammaStirling 1 qz448)

noncomputable abbrev qz531 := (@HAdd.hAdd Complex Complex Complex qz537 qz540 (@HMul.hMul Complex Complex Complex qz539 Complex.I (@HDiv.hDiv Complex Complex Complex qz541 (↑qz544) (2 : Complex))))

noncomputable abbrev qz449 := qz531

noncomputable abbrev qz177 := qz449

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz430 (2 : Real)) (Real.log Real.pi))

noncomputable def ep759 := Complex.re (@HMul.hMul Complex Complex Complex qz66 (Complex.exp (@HMul.hMul Complex Complex Complex qz66 Complex.I ↑(@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178))) (zetaApproximant qz146 1 20))

noncomputable def ep760 := @Enclosure.Real.IsNear.of_eq ep759 (@HSub.hSub Real Real Real qz363 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20))))

noncomputable def ep761 := nat_lit 51346145310881089948506293869

noncomputable def ep762 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20))) ep761

noncomputable def ep763 := nat_lit 18445360614020883583902679040

noncomputable def ep764 := nat_lit 1129355385764187824149916687063577501973

noncomputable def ep765 := nat_lit 22075547909213623652206857

noncomputable def ep766 := nat_lit 168161139406597984497291945503760747

noncomputable def ep767 := nat_lit 15953183446943894613849232831342968832000

noncomputable def ep768 := nat_lit 94709409448469975830686838031568044666106711717052122398720

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.re (zetaApproximant qz146 1 20)) 1048575 1048576 10652303

noncomputable def ep770 := nat_lit 3672566004640661608504849

noncomputable def ep771 := nat_lit 1319315000583235043328000

noncomputable def ep772 := nat_lit 2331016185570313794353785349

noncomputable def ep773 := nat_lit 462713675177887083022778368000

noncomputable def ep774 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 1048575 1048576 10652303

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92238237) qz30)

noncomputable def ep775 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz450 Bool.false 92238237 1048576 79

noncomputable def ep776 := nat_lit 12412733110488710072368979

noncomputable def ep777 := nat_lit 41372929228800000000000000000

noncomputable def ep778 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) Bool.false 316928171021768863811 3602879701896396800 ep776 ep777

noncomputable def ep779 := nat_lit 4521867673488710072368979

noncomputable def ep780 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178 523134014782498680899 3602879701896396800 ep779 ep777 1500344979 26214400

noncomputable def ep781 := nat_lit 8308081846433057703487078400

noncomputable def ep782 := nat_lit 3447744102400000000000000000

noncomputable def ep783 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 70792050070621880393 900719925474099200 689767608184978458351247 ep782 Bool.false 523134014782498680899 3602879701896396800

noncomputable def ep784 := nat_lit 4207294873447337143140179

noncomputable def ep785 := @Enclosure.Complex.IsNear.subLitP qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 63744573974453196193 900719925474099200 676660408147053273224847 ep782 Bool.false 534344723500655314499 3602879701896396800 ep784

noncomputable def ep786 := nat_lit 318819050318846195578918537609084928

noncomputable def ep787 := nat_lit 147249134627455787835349065996959744

noncomputable abbrev qz451 := (@HSub.hSub Complex Complex Complex qz518 qz530 qz521)

noncomputable abbrev qz452 := (Complex.log qz530)

noncomputable abbrev qz179 := (@HSub.hSub Complex Complex Complex qz360 (@HMul.hMul Complex Complex Complex qz359 qz451 qz452) qz448)

noncomputable abbrev qz180 := qz448

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq qz176 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k)))))) Bool.true 63744573974453196193

noncomputable def ep789 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz179 qz72) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) Bool.true 63744641398650213793 900719925474099200

noncomputable def ep790 := nat_lit 2190246884141833737052853633024

noncomputable def ep791 := nat_lit 1835994489780381768273439699763200

noncomputable def ep792 := @ep789 10325013841543179777 52608400000000000000000 Bool.false 534350716462949336643 3602879701896396800 10699500029025237969 105216800000000000000000 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400 Bool.true ep790 63744573974453196193 900719925474099200 676660408147053273224847 ep782 Bool.false ep791

noncomputable def ep793 := @Enclosure.Complex.IsNear.addLitP qz179 qz72 Bool.true 64572346880092312993 900719925474099200 20349000003643000179 105216800000000000000000

noncomputable def ep794 := nat_lit 8355137637403880822276096

noncomputable def ep795 := @ep793 Bool.false 534350716462949336643 3602879701896396800 10699500029025237969 105216800000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep794 63744641398650213793 900719925474099200 10325013841543179777 52608400000000000000000 Bool.false 534350716462949336643 534350716462949336643 3602879701896396800

noncomputable abbrev qz181 := (@HMul.hMul Complex Complex Complex qz359 qz451 qz452)

noncomputable def ep796 := @Enclosure.Complex.IsNear.subLitP qz181 qz180 Bool.true 62545727047775589793 900719925474099200 20349000003643000179 105216800000000000000000 Bool.false 714485694358514435651

noncomputable def ep797 := nat_lit 2137402865851797346572000

noncomputable def ep798 := @ep796 3602879701896396800 10699500029025237969 105216800000000000000000 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 Bool.true 258289387520369251972000 64572346880092312993 900719925474099200 20349000003643000179 105216800000000000000000 Bool.false ep797 534350716462949336643 3602879701896396800 10699500029025237969 105216800000000000000000

noncomputable abbrev qz182 := qz451

noncomputable abbrev qz183 := qz452

noncomputable def ep799 := @Enclosure.Complex.IsNear.mul qz182 qz183 Bool.true 62545727047775589793 900719925474099200 20349000003643000179 105216800000000000000000 Bool.false 714485694358514435651 3602879701896396800 10699500029025237969

noncomputable abbrev qz184 := (Complex.re qz451)

noncomputable abbrev qz185 := (Complex.re qz452)

noncomputable abbrev qz186 := (Complex.im qz451)

noncomputable abbrev qz187 := (Complex.im qz452)

noncomputable def ep800 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz184 qz185) (@HMul.hMul Real Real Real qz0 qz186 qz187) 246715193690797643 36028797018963968 3500000010127117 1052168000000000000000 17178401722511382717 225179981368524800

noncomputable def ep801 := nat_lit 563361826051957798119504944253894656

noncomputable def ep802 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz185 7000 4000 0 1 35245027670113949 9007199254740992 500000001446731 263042000000000000000

noncomputable def ep803 := @Enclosure.Complex.IsNear.re_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable abbrev qz453 := (Enclosure.sfrac Bool.false 199990 4000)

noncomputable abbrev qz188 := qz453

noncomputable def ep804 := @Enclosure.Complex.IsNear.of_eq qz182 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz188) Bool.false 7000 4000 0 1 Bool.false 199990 4000 0

noncomputable abbrev qz454 := (Complex.log (Complex.mk qz87 qz188))

noncomputable def ep805 := @Enclosure.Complex.IsNear.of_eq qz183 qz454 Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep806 := nat_lit 422367265547601150657504626870700001500000000

noncomputable def ep807 := nat_lit 1425938744966426429816263769248000800000000

noncomputable def ep808 := nat_lit 8561564365249218170666667708000300000000

noncomputable def ep809 := BSN.log_dyadic_bound 7309000100 72845000100 3 2 ep806 1048576 263042 ep807 ep808 211130 80154000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7309000100) (BSN.artanhQ 72845000100) 0 2 ep807 ep806 ep808 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz532 := (Real.log (Enclosure.sfrac Bool.false 40077000100 16000000))

noncomputable def ep810 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz532 1 2 0 1 35245027670113949 4503599627370496 500000001446731 131521000000000000000 35245027670113949 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 40077000100 16000000 35245027670113949 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40077000100) qz378)) Bool.false 295656721073739233492992 37778931862957161709568 1000000002893462 263042000000000000000 35245027670113949 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 40077000100 16000000 11 80154000200 65536000000 211130 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep809 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep811 := BSN.arctan_dyadic_bound_f 9000 199990 1 0 1048576 263042 0 1 1 0 1 1 47156 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz455 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 199990)))

noncomputable def ep812 := @Enclosure.Real.IsNear.subLit_ff_p qz89 qz455 884279719003555 562949953421312 1 2000000000000000 47156 1048576 1 263042 900688022630336299008 858963034277283 562949953421312 1000000000131521 263042000000000000000 qz90 (ep811 rfl) rfl rfl

noncomputable abbrev qz456 := (Complex.mk qz87 qz188)

noncomputable abbrev qz457 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199990) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep813 := @Enclosure.Complex.IsNear.re_isNear qz183 Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (ep805 (@congrArg Complex Complex qz180 qz456 Complex.log (BSN.w_shift_mk qz151 Bool.false 99995 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz454 Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz454) (@HMul.hMul Real Real Real qz0 qz88 qz532) Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 9000 199990 4000 40077000100 16000000 rfl rfl rfl) (ep810 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz454) qz457 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 9000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz457 (@HSub.hSub Real Real Real qz363 qz89 qz455) Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 199990 9000 rfl rfl) ep812))))

noncomputable def ep814 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz187 199990 4000 0 1 858963034277283 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep815 := @Enclosure.Complex.IsNear.im_isNear qz182 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable def ep816 := @Enclosure.Complex.IsNear.im_isNear qz183 Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (ep805 (@congrArg Complex Complex qz180 qz456 Complex.log (BSN.w_shift_mk qz151 Bool.false 99995 1000 2 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz454 Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz454) (@HMul.hMul Real Real Real qz0 qz88 qz532) Bool.false 35245027670113949 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 9000 199990 4000 40077000100 16000000 rfl rfl rfl) (ep810 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz454) qz457 Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 9000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz457 (@HSub.hSub Real Real Real qz363 qz89 qz455) Bool.false 858963034277283 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 199990 9000 rfl rfl) ep812))))

noncomputable abbrev qz458 := (Enclosure.Real.IsNear.const Bool.false 199990 4000)

noncomputable abbrev qz189 := (@ep804 1 (BSN.w_sub_half_mk qz430 Bool.false 99995 1000 2 qz431 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz453 Bool.false 7000 4000 0 1 Bool.false 199990 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) qz458))

noncomputable def ep817 := @ep800 19999000002630288479 105216800000000000000000 ep801 62545727047775589793 900719925474099200 20349000003643000179 105216800000000000000000 (@ep802 246715193690797643 36028797018963968 3500000010127117 1052168000000000000000 (ep803 qz189) ep813 rfl) (@ep814 17178401722511382717 225179981368524800 19999000002630288479 105216800000000000000000 (ep815 qz189) ep816 rfl) rfl

noncomputable def ep818 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz184 qz187) (@HMul.hMul Real Real Real qz0 qz186 qz185) 6012741239940981 2251799813685248 7000000000920647 1052168000000000000000 704865308374608866051 3602879701896396800

noncomputable def ep819 := nat_lit 1608878753437277854244505633263976448

noncomputable def ep820 := @Enclosure.Real.IsNear.mulLit_ff qz184 qz187 7000 4000 0 1 858963034277283 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_ff qz186 qz185 199990 4000 0 1 35245027670113949 9007199254740992 500000001446731 263042000000000000000

noncomputable def ep822 := @ep818 9999500028933173269 105216800000000000000000 ep819 714485694358514435651 3602879701896396800 10699500029025237969 105216800000000000000000 (@ep820 6012741239940981 2251799813685248 7000000000920647 1052168000000000000000 (ep803 qz189) ep816 rfl) (@ep821 704865308374608866051 3602879701896396800 9999500028933173269 105216800000000000000000 (ep815 qz189) ep813 rfl) rfl

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq qz180 qz456 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 (BSN.w_shift_mk qz151 Bool.false 99995 1000 2 qz152 rfl)

noncomputable abbrev qz459 := (ep823 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 199990 4000) Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 199990 4000)))

noncomputable abbrev qz190 := qz459

noncomputable def ep824 := ep798 (@ep799 105216800000000000000000 (ep817 rfl) (ep822 rfl)) qz190 rfl rfl rfl rfl rfl rfl

noncomputable def ep825 := @ep795 10699500029025237969 105216800000000000000000 (ep824 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz93 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep339 131072 3 1048576 (ep341 rfl) (ep343 rfl) rfl rfl) (@ep344 1 0 1 (ep346 rfl) (ep348 rfl) rfl rfl))

noncomputable abbrev qz460 := (@HPow.hPow Complex Int Complex qz523 qz530 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz191 := qz460

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191)) Bool.false 2572029 34359738368 3 34359738368

noncomputable def ep827 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191) Bool.false 0 1 0 1 Bool.false

noncomputable def ep828 := @ep827 0 1 0 1 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400 Bool.false 2572029 2572029 34359738368 3 34359738368 Bool.true 5715334219 5715334219 3435973836800 19999

noncomputable def ep829 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz67 (@HMul.hMul Complex Complex Complex qz66 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz75 qz180 (@HSub.hSub Int Int Int qz372 qz77 (@HMul.hMul Int Int Int qz373 qz78 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep830 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96) qz191 Bool.false 2572029 34359738368 3 34359738368 Bool.true 5715334219 3435973836800 19999 10307921510400

noncomputable abbrev qz192 := (Complex.re qz460)

noncomputable abbrev qz193 := (Complex.im qz460)

noncomputable def ep831 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193) 2572029 34359738368 3 34359738368 0 1 0

noncomputable def ep832 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192 1 12 0 1 7716087 8589934592 9 8589934592 2572029

noncomputable def ep833 := @Enclosure.Complex.IsNear.re_isNear qz191 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999 858993459200

noncomputable abbrev qz461 := (@HPow.hPow Complex Nat Complex qz525 qz530 1)

noncomputable abbrev qz194 := (@Inv.inv Complex Complex.instInv qz461)

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq qz191 qz194 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_parts qz194 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999

noncomputable abbrev qz195 := (Complex.re qz461)

noncomputable abbrev qz196 := qz461

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) 9000 4000 0 1 857343 2147483648 1 2147483648

noncomputable def ep837 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq qz196 qz180 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0

noncomputable def ep839 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) Bool.false 857343 2147483648 1 2147483648 857343 2147483648 1

noncomputable abbrev qz197 := (Complex.im qz461)

noncomputable def ep840 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196) (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197)) Bool.false 400770001 160000 0 1

noncomputable def ep841 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz195 qz195) (@HMul.hMul Real Real Real qz0 qz197 qz197) 81 16 0 1 399960001 160000

noncomputable def ep842 := @Enclosure.Real.IsNear.mulLit_ff qz195 qz195 9000 4000 0 1 9000 4000 0 1

noncomputable def ep843 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 199990 4000 0 1 199990 4000 0 1

noncomputable def ep844 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 9000 4000 0 1 Bool.false 199990 4000 0 1

noncomputable abbrev qz198 := (ep837 (@ep838 1 (BSN.pow_one_c qz448) qz459))

noncomputable abbrev qz199 := (ep844 (@ep838 1 (BSN.pow_one_c qz448) qz459))

noncomputable def ep845 := @ep841 0 1 6412320016 400770001 160000 0 1 (@ep842 81 16 0 1 qz198 qz198 rfl) (@ep843 399960001 160000 0 1 qz199 qz199 rfl)

noncomputable def ep846 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196) 400770001 160000 0 1 428671 428672 1073741824 (ep840 (Enclosure.Complex.normSq_eq_mul_add_mul qz196) (ep845 rfl rfl)) rfl

noncomputable def ep847 := @Enclosure.Real.IsNear.of_eq (Complex.re qz194) (@HMul.hMul Real Real Real qz0 qz195 (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196))) Bool.false 7716087 8589934592 9 8589934592 (Enclosure.Complex.inv_re_eq_mul qz196) (@ep836 7716087 8589934592 9 8589934592 qz198 (@ep839 2147483648 (ep846 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep848 := @Enclosure.Real.IsNear.of_eq (Complex.im qz194) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196))) Bool.true 17146002657 858993459200 19999 858993459200 (Enclosure.Complex.inv_im_eq_mul qz196)

noncomputable def ep849 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz197) (@Inv.inv Real Real.instInv (@DFunLike.coe qz102 Complex (fun (x : Complex) => Real) qz103 Complex.normSq qz196)) 199990 4000 0 1 857343 2147483648 1

noncomputable def ep850 := @ep849 2147483648 17146002657 858993459200 19999 858993459200 (@Enclosure.Real.IsNear.neg qz197 Bool.false 199990 4000 0 1 qz199) (@ep839 2147483648 (ep846 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep851 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193 0 1 0 1 17146002657 858993459200 19999 858993459200 0

noncomputable def ep852 := @Enclosure.Complex.IsNear.im_isNear qz191 Bool.false 7716087 8589934592 9 8589934592 Bool.true 17146002657 858993459200 19999 858993459200

noncomputable abbrev qz200 := (@ep834 858993459200 (BSN.zpow_one_sub_two_mul qz448 1 1 rfl rfl) (@ep835 858993459200 ep847 (ep848 ep850)))

noncomputable def ep853 := @ep831 1 2572029 2572029 34359738368 3 34359738368 (@ep832 34359738368 3 34359738368 ep358 (ep833 qz200) rfl) (@ep851 1 0 1 ep378 (ep852 qz200) rfl) rfl

noncomputable def ep854 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192) 5715334219 3435973836800 19999 10307921510400 0 1 0

noncomputable def ep855 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz193 1 12 0 1 17146002657 858993459200 19999 858993459200 5715334219

noncomputable def ep856 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 (@Rat.cast Complex Complex.instRatCast (bernoulli qz95)) qz96)) qz192 0 1 0 1 7716087 8589934592 9 8589934592 0

noncomputable def ep857 := @ep854 1 5715334219 5715334219 3435973836800 19999 10307921510400 (@ep855 3435973836800 19999 10307921510400 ep358 (ep852 qz200) rfl) (@ep856 1 0 1 ep378 (ep833 qz200) rfl) rfl

noncomputable def ep858 := @ep828 10307921510400 (@ep829 0 1 0 1 (BSN.stirling_sum_base qz180) qz109) (ep830 (ep853 rfl) (ep857 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep859 := @ep792 534344723500655314499 3602879701896396800 ep784 ep777 (ep825 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep826 Bool.true 5715334219 3435973836800 19999 10307921510400 (BSN.stirling_sum_succ qz180 0 1 rfl) (ep858 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep860 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz151 2) Bool.false 35237380480843421 4503599627370496 500000001446731 131521000000000000000 Bool.false 875836618605987 281474976710656

noncomputable abbrev qz201 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz449 qz383))

noncomputable def ep861 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 1) qz201) Bool.false 35237380480843421 4503599627370496 500000001446731 131521000000000000000 Bool.false 875836618605987 281474976710656 1000000000131521 131521000000000000000

noncomputable def ep862 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 1) qz201 Bool.false 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000 Bool.false

noncomputable def ep863 := nat_lit 634780214412155279918538124427264

noncomputable def ep864 := nat_lit 986104367297839569253473189888

noncomputable abbrev qz202 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz273 qz449 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz151 0) qz202) Bool.false 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz151 0) qz202 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz462 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188))

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq qz202 qz462 Bool.false 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep868 := nat_lit 420514907276537331923020706865900001500000000

noncomputable def ep869 := nat_lit 1391668531252353164837140566688000800000000

noncomputable def ep870 := nat_lit 8192834420582976393319466748000300000000

noncomputable def ep871 := BSN.log_dyadic_bound 7229000100 72765000100 3 2 ep868 1048576 263042 ep869 ep870 209035 79994000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7229000100) (BSN.artanhQ 72765000100) 0 2 ep869 ep868 ep870 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep872 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 39997000100 16000000)) 1 2 0 1 35236029713628829 4503599627370496 500000001446731 131521000000000000000 35236029713628829 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 39997000100 16000000 35236029713628829 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39997000100) qz378)) Bool.false 295581240743984503980032 37778931862957161709568 1000000002893462 263042000000000000000 35236029713628829 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 39997000100 16000000 11 79994000200 65536000000 209035 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep871 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep873 := BSN.arctan_dyadic_bound_f 1000 199990 1 0 1048576 263042 0 1 1 0 1 1 5243 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz463 := (@Nat.cast Real Real.instNatCast 199990)

noncomputable def ep874 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz463)) 884279719003555 562949953421312 1 2000000000000000 5243 1048576 1 263042 924282944028083748864 881464904811939 562949953421312 1000000000131521 263042000000000000000 qz90 (ep873 rfl) rfl rfl

noncomputable abbrev qz203 := (@HAdd.hAdd Complex Complex Complex qz273 qz449 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz464 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz188)

noncomputable def ep875 := @ep866 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000 Bool.false 35236029713628829 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 881464904811939 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz151 0) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz151) qz109) (ep867 (@congrArg Complex Complex qz203 qz464 Complex.log (BSN.w_shift_mk qz151 Bool.false 99995 1000 0 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz462 Bool.false 35236029713628829 9007199254740992 500000001446731 263042000000000000000 Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz462) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 39997000100 16000000))) Bool.false 35236029713628829 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 1000 199990 4000 39997000100 16000000 rfl rfl rfl) (ep872 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz462) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz463 qz389)) Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 1000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz463 qz389)) (@HSub.hSub Real Real Real qz363 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz389 qz463))) Bool.false 881464904811939 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 199990 1000 rfl rfl) ep874)))) rfl rfl

noncomputable abbrev qz465 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188))

noncomputable def ep876 := @Enclosure.Complex.IsNear.of_eq qz201 qz465 Bool.false 35238731248058013 9007199254740992 500000001446731 263042000000000000000 Bool.false 870208332400035 562949953421312 1000000000131521 263042000000000000000

noncomputable def ep877 := nat_lit 421069973695044918613828673267340001500000000

noncomputable def ep878 := nat_lit 1401898135863212512445432407456000800000000

noncomputable def ep879 := nat_lit 8302177006585912401481707036000300000000

noncomputable def ep880 := BSN.log_dyadic_bound 7253000100 72789000100 3 2 ep877 1048576 263042 ep878 ep879 209664 80042000200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 7253000100) (BSN.artanhQ 72789000100) 0 2 ep878 ep877 ep879 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep881 := @Enclosure.Real.IsNear.mulLit_ff qz88 (Real.log (Enclosure.sfrac Bool.false 40021000100 16000000)) 1 2 0 1 35238731248058013 4503599627370496 500000001446731 131521000000000000000 35238731248058013 9007199254740992 500000001446731 263042000000000000000 qz377 (BSN.isNear_log_sfrac 40021000100 16000000 35238731248058013 4503599627370496 500000001446731 131521000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40021000100) qz378)) Bool.false 295603902857309432315904 37778931862957161709568 1000000002893462 263042000000000000000 35238731248058013 4503599627370496 500000001446731 131521000000000000000 (BSN.log_rat_reduce_isNear 40021000100 16000000 11 80042000200 65536000000 209664 1048576 24973259072661432 36028797018963968 263042 1000000000000000 rfl rfl rfl rfl (ep880 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep882 := BSN.arctan_dyadic_bound_f 5000 199990 1 0 1048576 263042 0 1 1 0 1 1 26210 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 199990) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 199990) 0 0 rfl) rfl rfl rfl

noncomputable def ep883 := @Enclosure.Real.IsNear.subLit_ff_p qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz393 qz463)) 884279719003555 562949953421312 1 2000000000000000 26210 1048576 1 263042 912479572354699100160 870208332400035 562949953421312 1000000000131521 263042000000000000000 qz90 (ep882 rfl) rfl rfl

noncomputable abbrev qz204 := (@HAdd.hAdd Complex Complex Complex qz273 qz449 qz383)

noncomputable abbrev qz466 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz188)

noncomputable def ep884 := @ep862 35238731248058013 9007199254740992 500000001446731 263042000000000000000 Bool.false 870208332400035 562949953421312 1000000000131521 263042000000000000000 Bool.false ep863 35237380480843421 4503599627370496 500000001446731 131521000000000000000 Bool.false ep864 875836618605987 281474976710656 1000000000131521 131521000000000000000 (ep865 (BSN.log_sum_c_succ qz151 0 1 rfl) (ep875 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep876 (@congrArg Complex Complex qz204 qz466 Complex.log (BSN.w_shift_mk qz151 Bool.false 99995 1000 1 qz152 rfl)) (@Enclosure.Complex.IsNear.of_parts qz465 Bool.false 35238731248058013 9007199254740992 500000001446731 263042000000000000000 Bool.false 870208332400035 562949953421312 1000000000131521 263042000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz465) (@HMul.hMul Real Real Real qz0 qz88 (Real.log (Enclosure.sfrac Bool.false 40021000100 16000000))) Bool.false 35238731248058013 9007199254740992 500000001446731 263042000000000000000 (Enclosure.clog_re_eq 5000 199990 4000 40021000100 16000000 rfl rfl rfl) (ep881 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz465) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz463 qz393)) Bool.false 870208332400035 562949953421312 1000000000131521 263042000000000000000 (Enclosure.clog_im_eq 5000 199990 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz463 qz393)) (@HSub.hSub Real Real Real qz363 qz89 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz393 qz463))) Bool.false 870208332400035 562949953421312 1000000000131521 263042000000000000000 (BSN.arctan_recip 199990 5000 rfl rfl) ep883)))) rfl rfl

noncomputable def ep885 := @ep785 ep777 Bool.false 35237380480843421 4503599627370496 500000001446731 131521000000000000000 Bool.false 875836618605987 281474976710656 1000000000131521 131521000000000000000 Bool.true ep786 70792050070621880393 900719925474099200 689767608184978458351247 ep782 Bool.false ep787 523134014782498680899 3602879701896396800 ep779 ep777 (@ep788 900719925474099200 676660408147053273224847 ep782 Bool.false 534344723500655314499 3602879701896396800 ep784 ep777 (BSN.logGammaStirling_unfold 1 qz180) (ep859 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep860 1000000000131521 131521000000000000000 (BSN.log_sum_c_eq qz151 2) (ep861 (BSN.log_sum_c_succ qz151 1 2 rfl) (ep884 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz205 := (@HDiv.hDiv Real Real Real qz270 qz430 (2 : Real))

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff qz205 (Real.log Real.pi) 99995 2000 0 1 75021 65536 1 262144 1500344979 26214400 19999 104857600 (@Enclosure.Real.IsNear.of_eq qz205 (Enclosure.sfrac Bool.false 99995 2000) Bool.false 99995 2000 0 1 (BSN.t_half_eq qz151 Bool.false 99995 1000 qz152) (Enclosure.Real.IsNear.const Bool.false 99995 2000)) EMRow29.d5 rfl

noncomputable def ep887 := @ep780 19999 104857600 ep781 316928171021768863811 3602879701896396800 ep776 ep777 (@ep783 ep779 ep777 (ep885 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep886 rfl rfl

noncomputable def ep888 := BSN.cos_dyadic_bound_f 1381512 2147483648 1 0 1048576 263299 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1381512) qz288 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1381512) qz289 0 0 rfl) rfl rfl

noncomputable def ep889 := @ep775 262144 Bool.false 1048575 1048576 1 131521 (@ep778 92238237 1048576 79 262144 ep887 rfl) (Enclosure.sfrac_false_div 92238237 1048576) (BSN.cos_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97215313183384797184) qz32) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 14 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 92238237 1048576 226375608064910080 72057594037927936 14 97215313183384797184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 97215313183384797184 151115727451828646838272 1381512 2147483648 263299 263042 (ep888 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep890 := nat_lit 3518173334888626782208000

noncomputable def ep891 := nat_lit 290988509395940391717743547

noncomputable def ep892 := nat_lit 57839209397235885377847296000

noncomputable abbrev qz467 := (@HPow.hPow Complex Complex Complex qz511 qz526 qz528)

noncomputable abbrev qz206 := qz467

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz273 (@HDiv.hDiv Complex Complex Complex qz368 qz396 (@HSub.hSub Complex Complex Complex qz360 qz423 (1 : Complex))) qz367)

noncomputable def ep893 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz146 1 20) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz66 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) Bool.false ep770 ep771 ep772

noncomputable def ep894 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (@HMul.hMul Complex Complex Complex qz66 qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) Bool.false 197716330307 68719476736 27329955422135 5561879569104896

noncomputable def ep895 := nat_lit 57334427685885188949705349

noncomputable def ep896 := nat_lit 7173813926653214191789547

noncomputable def ep897 := nat_lit 252376814117328413445297310598692864

noncomputable def ep898 := nat_lit 18006173305420285467324492162269184

noncomputable def ep899 := @ep894 Bool.true 16466753761 274877906944 27291921390229 5561879569104896 Bool.true 123302835228480166231151 ep771 ep895 ep773 Bool.false 276264717466065096411961 ep890 ep896 ep892 Bool.false ep897 ep770 ep771 ep772 ep773 Bool.false ep898 65506076881939536059961 ep890

noncomputable def ep900 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 20, @HPow.hPow Complex Complex Complex qz115 (@Nat.cast Complex Complex.instNatCast n) qz147) (BSN.headSumC qz146 20) Bool.false 197716330307 68719476736 27329955422135 5561879569104896 Bool.true 16466753761 274877906944 27291921390229

noncomputable abbrev qz208 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 19) qz424)

noncomputable def ep901 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 19) qz208) Bool.false 197716330307 68719476736 27329955422135 5561879569104896 Bool.true 16466753761 274877906944 27291921390229 5561879569104896

noncomputable def ep902 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 19) qz208 Bool.false 46919510949 17179869184 342479734489883 72304434398363648 Bool.true 130184053893 549755813888 85494007032607 18076108599590912 Bool.false

noncomputable abbrev qz209 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 18) qz424)

noncomputable def ep903 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz146 18) qz209) Bool.false 46919510949 17179869184 342479734489883 72304434398363648 Bool.true 130184053893 549755813888 85494007032607 18076108599590912

noncomputable def ep904 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz146 18) qz209 Bool.false 342961758871 137438953472 329311435707535 72304434398363648 Bool.true 261364373467 1099511627776 657752837246937 144608868796727296 Bool.false

noncomputable abbrev qz210 := (@HPow.hPow Complex Complex Complex qz274 (@Nat.cast Complex Complex.instNatCast 17) qz424)

noncomputable def ep905 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz146 18) (@HAdd.hAdd Complex Complex Complex qz4 qz160 qz210) Bool.false 342961758871 137438953472 329311435707535 72304434398363648 Bool.true 261364373467 1099511627776 657752837246937 144608868796727296

noncomputable def ep906 := @Enclosure.Complex.IsNear.addLitP qz160 qz210 Bool.false 2518279435067 1099511627776 631547995803945 144608868796727296 Bool.true 118881239681 1099511627776 630720849976307 144608868796727296 Bool.false

noncomputable def ep907 := nat_lit 3016723534089385744007168

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz430 qz399)

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq qz210 (Complex.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 225414635901 1099511627776 27074875611125 144608868796727296 Bool.true 71241566893 549755813888 13515993635315 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 17 qz152 rfl)

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz399 99995 1000 0 1 3189913004350711 1125899906842624 250000000131521 32880250000000000000 63795070174009869289 225179981368524800 4999750002630288479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz400) Bool.false 53517859495200818200576 18889465931478580854784 1000000000526084 131521000000000000000 3189913004350711 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep910 := nat_lit 2147152973222687543807757849928400896

noncomputable def ep911 := BSN.cos_dyadic_bound_f 1210502656 2147483648 2 1 1048576 263299 ep910 ep62 ep910 ep910 ep63 ep910 886353 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1210502656) qz288 0 1 ep910 ep62 ep910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1210502656) qz289 0 1 ep910 ep63 ep910 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297068945) qz30)

noncomputable def ep912 := @Enclosure.Real.IsNear.cos_image qz211 qz468 Bool.false 297068945 1048576 399 524288 Bool.false 886353 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 63795070174009869289 225179981368524800 4999750002630288479 6576050000000000000000 297068945 1048576 399 524288 (ep909 rfl) rfl) (Enclosure.sfrac_false_div 297068945 1048576) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85181551762276498800640) qz32) 226375608064910080 72057594037927936 Bool.false 886353 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 297068945 1048576 226375608064910080 72057594037927936 45 85181551762276498800640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 886353 1048576 85181551762276498800640 151115727451828646838272 1210502656 2147483648 263299 263042 (ep911 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep913 := BSN.sin_dyadic_bound_f 1210502656 2147483648 2 1 1048576 263299 ep910 ep58 ep910 ep910 ep59 ep910 560258 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1210502656) qz283 0 1 ep910 ep58 ep910 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1210502656) qz284 0 1 ep910 ep59 ep910 rfl rfl rfl rfl) rfl rfl

noncomputable def ep914 := @Enclosure.Real.IsNear.sin_image qz211 qz468 Bool.false 297068945 1048576 399 524288 Bool.false 560258 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 63795070174009869289 225179981368524800 4999750002630288479 6576050000000000000000 297068945 1048576 399 524288 (ep909 rfl) rfl) (Enclosure.sfrac_false_div 297068945 1048576) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85181551762276498800640) qz32) 226375608064910080 72057594037927936 Bool.false 560258 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 297068945 1048576 226375608064910080 72057594037927936 45 85181551762276498800640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 560258 1048576 85181551762276498800640 151115727451828646838272 1210502656 2147483648 263299 263042 (ep913 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep915 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz125 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 225414635901 1099511627776 27074875611125 144608868796727296 Bool.true 71241566893 549755813888 13515993635315 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz125 (Real.cos qz211) 254317 1048576 1 1048576 886353 1048576 53001167 68954882048 225414635901 1099511627776 27074875611125 144608868796727296 qz402 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 886353 1048576 53001167 68954882048 886353 1048576 53001167 68954882048 (ep912 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz125 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 254317 1048576 1 1048576 280129 524288 53001167 68954882048 71241566893 549755813888 13515993635315 72304434398363648 qz402 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 280129 524288 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 560258 1048576 53001167 68954882048 280129 524288 53001167 68954882048 (ep914 rfl rfl) rfl)) rfl)

noncomputable def ep916 := @ep906 225414635901 1099511627776 27074875611125 144608868796727296 Bool.true 71241566893 549755813888 13515993635315 72304434398363648 Bool.false ep907 342961758871 137438953472 329311435707535 72304434398363648 Bool.true 143686583856677777309696 261364373467 1099511627776 657752837246937 144608868796727296 EMRow29.d12 (ep908 ep915) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz430 qz404)

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 32394328721 137438953472 3292074695587 18076108599590912 Bool.false 996265681 1099511627776 26199219013919 144608868796727296 (BSN.cpow_neg_s_mk qz151 99995 1000 18 qz152 rfl)

noncomputable def ep918 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz404 99995 1000 0 1 3254268794313975 1125899906842624 250000000131521 32880250000000000000 2603284864699407441 9007199254740992 4999750002630288479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz405) Bool.false 54597570484265130393600 18889465931478580854784 1000000000526084 131521000000000000000 3254268794313975 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep452 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep919 := nat_lit 8262432222890305884326189225268336343980595333127261363706435008325014000247040

noncomputable def ep920 := nat_lit 16439303626513672083064287468776843422214876343003942458476342702771641262336

noncomputable def ep921 := nat_lit 21613087425507874227957915315039051725837020834587487664774558562189596867174656

noncomputable def ep922 := BSN.sin_dyadic_bound_f 3365002778 2147483648 3 2 1048576 263299 ep919 ep170 ep920 ep921 ep172 ep920 1048568 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3365002778) qz283 0 2 ep919 ep170 ep920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3365002778) qz284 0 2 ep921 ep172 ep920 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 303062245) qz30)

noncomputable def ep923 := @Enclosure.Real.IsNear.cos_image qz212 qz469 Bool.false 303062245 1048576 399 524288 Bool.false 1048568 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 2603284864699407441 9007199254740992 4999750002630288479 6576050000000000000000 303062245 1048576 399 524288 (ep918 rfl) rfl) (Enclosure.sfrac_false_div 303062245 1048576) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236791019650490040320000) qz32) 226375608064910080 72057594037927936 Bool.false 1048568 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 303062245 1048576 226375608064910080 72057594037927936 45 236791019650490040320000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048568 1048576 236791019650490040320000 151115727451828646838272 3365002778 2147483648 263299 263042 (ep922 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep924 := nat_lit 4597546480995287123329244808468532121510204019000924732040675601381795174031616

noncomputable def ep925 := nat_lit 13759760835732834025821605850468042677686182304316766311205074118739842239570176

noncomputable def ep926 := BSN.cos_dyadic_bound_f 3365002778 2147483648 3 2 1048576 263299 ep924 ep112 ep920 ep925 ep115 ep920 4031 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3365002778) qz288 0 2 ep924 ep112 ep920 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3365002778) qz289 0 2 ep925 ep115 ep920 rfl rfl rfl rfl) rfl rfl

noncomputable def ep927 := @Enclosure.Real.IsNear.sin_image qz212 qz469 Bool.false 303062245 1048576 399 524288 Bool.true 4031 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 2603284864699407441 9007199254740992 4999750002630288479 6576050000000000000000 303062245 1048576 399 524288 (ep918 rfl) rfl) (Enclosure.sfrac_false_div 303062245 1048576) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236791019650490040320000) qz32) 226375608064910080 72057594037927936 Bool.false 4031 1048576 45 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 303062245 1048576 226375608064910080 72057594037927936 45 236791019650490040320000 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 4031 1048576 236791019650490040320000 151115727451828646838272 3365002778 2147483648 263299 263042 (ep926 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep928 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz127 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 32394328721 137438953472 3292074695587 18076108599590912 Bool.false 996265681 1099511627776 26199219013919 144608868796727296 (@Enclosure.Real.IsNear.mulLit_ff qz127 (Real.cos qz212) 247151 1048576 1 1048576 131071 131072 53001167 68954882048 32394328721 137438953472 3292074695587 18076108599590912 qz407 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 1048568 1048576 53001167 68954882048 131071 131072 53001167 68954882048 (ep923 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz127 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 247151 1048576 1 1048576 4031 1048576 53001167 68954882048 996265681 1099511627776 26199219013919 144608868796727296 qz407 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 4031 1048576 53001167 68954882048 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 4031 1048576 53001167 68954882048 4031 1048576 53001167 68954882048 (ep927 rfl rfl) rfl)) rfl)

noncomputable def ep929 := @ep904 32394328721 137438953472 3292074695587 18076108599590912 Bool.false 996265681 1099511627776 26199219013919 144608868796727296 Bool.false 51588547857988844519424 46919510949 17179869184 342479734489883 72304434398363648 Bool.true 286277762012741879463936 130184053893 549755813888 85494007032607 18076108599590912 (ep905 (BSN.head_sum_c_succ qz146 17 18 rfl rfl) (ep916 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep917 ep928) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz430 qz409)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 10038286511 68719476736 800605374867 4519027149897728 Bool.false 97250546371 549755813888 12818949942549 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 19 qz152 rfl)

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz409 99995 1000 0 1 3315143513283831 1125899906842624 250000000131521 32880250000000000000 66299555122163336169 225179981368524800 4999750002630288479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz410) Bool.false 55618878793361701994496 18889465931478580854784 1000000000526084 131521000000000000000 3315143513283831 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep467 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep932 := nat_lit 4827936983383764795979851924016772161

noncomputable def ep933 := BSN.sin_dyadic_bound_f 1482314641 2147483648 2 1 1048576 263299 ep932 ep58 ep932 ep932 ep59 ep932 667664 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1482314641) qz283 0 1 ep932 ep58 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1482314641) qz284 0 1 ep932 ep59 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 308731361) qz30)

noncomputable def ep934 := @Enclosure.Real.IsNear.cos_image qz213 qz470 Bool.false 308731361 1048576 799 1048576 Bool.false 667664 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 66299555122163336169 225179981368524800 4999750002630288479 6576050000000000000000 308731361 1048576 799 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 308731361 1048576) (BSN.cos_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104308619805249169784832) qz32) 226375608064910080 72057594037927936 Bool.false 667664 1048576 46 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 308731361 1048576 226375608064910080 72057594037927936 46 104308619805249169784832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 667664 1048576 104308619805249169784832 151115727451828646838272 1482314641 2147483648 263299 263042 (ep933 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep935 := nat_lit 172523800500866643710384153985766494970113194936657974033652025958461702633601

noncomputable def ep936 := nat_lit 23308975515524726791716429072282017828214874608855114234451256833384609921

noncomputable def ep937 := nat_lit 517524783551568881677569029099154920874683155060756211872487175361718338680961

noncomputable def ep938 := BSN.cos_dyadic_bound_f 1482314641 2147483648 3 2 1048576 263299 ep935 ep112 ep936 ep937 ep115 ep936 808538 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1482314641) qz288 0 2 ep935 ep112 ep936 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1482314641) qz289 0 2 ep937 ep115 ep936 rfl rfl rfl rfl) rfl rfl

noncomputable def ep939 := @Enclosure.Real.IsNear.sin_image qz213 qz470 Bool.false 308731361 1048576 799 1048576 Bool.true 808538 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 66299555122163336169 225179981368524800 4999750002630288479 6576050000000000000000 308731361 1048576 799 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 308731361 1048576) (BSN.sin_reduce3 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 104308619805249169784832) qz32) 226375608064910080 72057594037927936 Bool.false 808538 1048576 46 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q3 308731361 1048576 226375608064910080 72057594037927936 46 104308619805249169784832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 808538 1048576 104308619805249169784832 151115727451828646838272 1482314641 2147483648 263299 263042 (ep938 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep940 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz129 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 10038286511 68719476736 800605374867 4519027149897728 Bool.false 97250546371 549755813888 12818949942549 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ff qz129 (Real.cos qz213) 240559 1048576 1 1048576 41729 65536 106133855 137909764096 10038286511 68719476736 800605374867 4519027149897728 qz412 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 667664 1048576 106133855 137909764096 41729 65536 106133855 137909764096 (ep934 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz129 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 240559 1048576 1 1048576 404269 524288 106133855 137909764096 97250546371 549755813888 12818949942549 72304434398363648 qz412 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 404269 524288 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 808538 1048576 106133855 137909764096 404269 524288 106133855 137909764096 (ep939 rfl rfl) rfl)) rfl)

noncomputable def ep941 := @ep902 10038286511 68719476736 800605374867 4519027149897728 Bool.false 97250546371 549755813888 12818949942549 72304434398363648 Bool.false 3396740690214794559488 197716330307 68719476736 27329955422135 5561879569104896 Bool.true 18105387231943680065536 16466753761 274877906944 27291921390229 5561879569104896 (ep903 (BSN.head_sum_c_succ qz146 18 19 rfl rfl) (ep929 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep930 ep940) rfl rfl

noncomputable def ep942 := @Enclosure.Complex.IsNear.mul qz206 (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.true 123302835228480166231151 ep771 ep895 ep773 Bool.false

noncomputable abbrev qz214 := (Complex.re qz467)

noncomputable abbrev qz215 := (Complex.im qz467)

noncomputable def ep943 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 5291818576774430462603 105545200046658803466240 99996357506757768986621

noncomputable def ep944 := nat_lit 1156784187944717707556945920

noncomputable def ep945 := nat_lit 2638630001166470086656000

noncomputable def ep946 := nat_lit 17335884683182081355056949

noncomputable def ep947 := nat_lit 26028044821020295193311816975426239351729684480

noncomputable def ep948 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 55008068683 549755813888 3118364559543 18076108599590912 96200770241

noncomputable abbrev qz471 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz529 (Real.log (Enclosure.sfrac Bool.false 20 1)))

noncomputable abbrev qz216 := (Real.cos qz471)

noncomputable abbrev qz217 := (Real.sin qz471)

noncomputable abbrev qz472 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep949 := @Enclosure.Complex.IsNear.of_eq qz206 (Complex.mk (@HMul.hMul Real Real Real qz0 qz133 qz216) (@HMul.hMul Real Real Real qz0 qz133 qz472)) Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (BSN.cpow_neg_s_mk qz151 99995 1000 20 qz152 rfl)

noncomputable def ep950 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz136 99995 1000 0 1 3372893643545847 1125899906842624 250000000131521 32880250000000000000 67454499977273394153 225179981368524800 4999750002630288479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000131521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false 56587765202795681021952 18889465931478580854784 1000000000526084 131521000000000000000 3372893643545847 1125899906842624 250000000131521 32880250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 131521 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep951 := nat_lit 1141552193233618004134629081577993187532075966817937212781666569417513806570081

noncomputable def ep952 := nat_lit 1018962962483632078497518456385335775856927891583201043967361177837803119201

noncomputable def ep953 := nat_lit 3422618653775886748246892207821208891044514044670645236257064985896865813471841

noncomputable def ep954 := BSN.cos_dyadic_bound_f 2376948651 2147483648 3 2 1048576 263299 ep951 ep112 ep952 ep953 ep115 ep952 469214 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2376948651) qz288 0 2 ep951 ep112 ep952 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2376948651) qz289 0 2 ep953 ep115 ep952 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz471

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 78527373) (@Nat.cast Real Real.instNatCast 262144))

noncomputable def ep955 := @Enclosure.Real.IsNear.cos_image qz218 qz473 Bool.false 78527373 262144 799 1048576 Bool.true 469214 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 67454499977273394153 225179981368524800 4999750002630288479 6576050000000000000000 78527373 262144 799 1048576 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 78527373 262144) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41815722890006632595456) qz324) 226375608064910080 72057594037927936 Bool.false 469214 1048576 47 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 78527373 262144 226375608064910080 72057594037927936 47 41815722890006632595456 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 469214 1048576 41815722890006632595456 37778931862957161709568 2376948651 2147483648 263299 263042 (ep954 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep956 := nat_lit 2053978777450525501779534332075279468937051197959020422171825936009254609330785

noncomputable def ep957 := nat_lit 5377818477097831386057403458886822351198032397115823542093120771450596105101921

noncomputable def ep958 := BSN.sin_dyadic_bound_f 2376948651 2147483648 3 2 1048576 263299 ep956 ep170 ep952 ep957 ep172 ep952 937736 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2376948651) qz283 0 2 ep956 ep170 ep952 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2376948651) qz284 0 2 ep957 ep172 ep952 rfl rfl rfl rfl) rfl rfl

noncomputable def ep959 := @Enclosure.Real.IsNear.sin_image qz218 qz473 Bool.false 78527373 262144 799 1048576 Bool.true 937736 1048576 1 131521 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 67454499977273394153 225179981368524800 4999750002630288479 6576050000000000000000 78527373 262144 799 1048576 (ep950 rfl) rfl) (Enclosure.sfrac_false_div 78527373 262144) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41815722890006632595456) qz324) 226375608064910080 72057594037927936 Bool.false 937736 1048576 47 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q2 78527373 262144 226375608064910080 72057594037927936 47 41815722890006632595456 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 937736 1048576 41815722890006632595456 37778931862957161709568 2376948651 2147483648 263299 263042 (ep958 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep960 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz133 qz216) (@HMul.hMul Real Real Real qz0 qz133 qz472) Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (@Enclosure.Real.IsNear.mulLit_ft qz133 qz216 234469 1048576 1 1048576 234607 524288 106133855 137909764096 55008068683 549755813888 3118364559543 18076108599590912 qz420 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 469214 1048576 106133855 137909764096 234607 524288 106133855 137909764096 (ep955 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz133 qz472 234469 1048576 1 1048576 117217 131072 106133855 137909764096 27483752773 137438953472 12504268479153 72304434398363648 qz420 (@Enclosure.Real.IsNear.neg qz217 Bool.true 117217 131072 106133855 137909764096 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 937736 1048576 106133855 137909764096 117217 131072 106133855 137909764096 (ep959 rfl rfl) rfl)) rfl)

noncomputable def ep961 := @ep948 191985600480 0 1 5291818576774430462603 105545200046658803466240 99996357506757768986621 ep944 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (ep949 ep960))

noncomputable def ep962 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 96200770241 191985600480 0 1 Bool.false

noncomputable def ep963 := @Enclosure.Complex.IsNear.addLitP qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) Bool.false 399170001 799940002 0 1 Bool.true 79996000

noncomputable def ep964 := @ep963 399970001 0 1 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1 Bool.false 192401540482 96200770241 191985600480 0 1 Bool.false 4159192049999 4159192049999 19198560048000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz368 qz396 (@HSub.hSub Complex Complex Complex qz360 qz423 (1 : Complex)))

noncomputable def ep965 := @Enclosure.Complex.IsNear.addLitP qz219 qz93 Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1

noncomputable def ep966 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 40000000 39997000100) (Enclosure.sfrac Bool.true 7999600000 39997000100)) Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1

noncomputable def ep967 := @ep965 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 39917000100 399170001 799940002 0 1 Bool.true 7999600000 79996000 399970001 0 1 (ep966 (BSN.N_div_s_sub_one_mk qz151 99995 1000 20 qz152 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 40000000 39997000100) (Enclosure.sfrac Bool.true 7999600000 39997000100) Bool.true 40000000 39997000100 0 1 Bool.true 7999600000 39997000100 0 1 (Enclosure.Real.IsNear.const Bool.true 40000000 39997000100) (Enclosure.Real.IsNear.const Bool.true 7999600000 39997000100))) qz94 rfl

noncomputable def ep968 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140)) Bool.false 1 480 0 1

noncomputable def ep969 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140) Bool.false 0 1 0 1 Bool.false

noncomputable def ep970 := @ep969 0 1 0 1 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1 Bool.false 1 1 480 0 1 Bool.false 19999 19999 48000 0

noncomputable def ep971 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (Complex.mk qz13 qz13) Bool.false 0 1 0 1 Bool.false

noncomputable def ep972 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz140 Bool.false 1 480 0 1 Bool.false 19999 48000 0 1

noncomputable def ep973 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) 1 480 0 1 0 1 0

noncomputable def ep974 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 1 24 0 1 1 20 0 1 1

noncomputable def ep975 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep976 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep977 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz146 Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 (BSN.ascPochhammer_one_eval qz146)

noncomputable def ep978 := ep977 (@Enclosure.Complex.IsNear.of_eq qz146 (Complex.mk qz88 qz151) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_crit_mk qz151 Bool.false 99995 1000 qz152) (@Enclosure.Complex.IsNear.mk qz88 qz151 Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 qz377 qz153))

noncomputable def ep979 := @ep976 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep980 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 99995 1000 0 1 0 1 0

noncomputable def ep981 := @ep980 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep982 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) 19999 2400 0 1 0 1 0 1 19999

noncomputable def ep983 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 99995 1000 0 1 19999 2400 0

noncomputable def ep984 := @ep983 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep985 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep986 := @ep985 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep510) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep987 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 (@ep975 1 24 0 1 (ep979 rfl) (ep981 rfl) rfl rfl) (@ep982 19999 2400 0 1 (ep984 rfl) (ep986 rfl) rfl rfl)

noncomputable def ep988 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 ep987

noncomputable def ep989 := @ep974 480 0 1 ep988 qz143

noncomputable def ep990 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 19999 2400 0 1 0 1 0 1 0

noncomputable def ep991 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 19999 2400 0 1 ep987

noncomputable def ep992 := @ep990 1 0 1 ep991 qz144

noncomputable def ep993 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141) 0 1 0 1 19999 48000 0

noncomputable def ep994 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz142 1 24 0 1 0 1 0 1 0

noncomputable def ep995 := @ep994 1 0 1 ep988 qz144

noncomputable def ep996 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz95)) ↑qz139) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)))) qz141 19999 2400 0 1 1 20 0 1 19999

noncomputable def ep997 := @ep996 48000 0 1 ep991 qz143

noncomputable def ep998 := @ep970 1 (@ep971 0 1 0 1 (BSN.bern_sum_base qz146 20) qz109) (ep972 (@ep973 1 1 1 480 0 1 (ep989 rfl) (ep992 rfl) rfl rfl) (@ep993 1 19999 19999 48000 0 1 (ep995 rfl) (ep997 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep999 := ep964 (ep967 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep968 Bool.false 19999 48000 0 1 (BSN.bern_sum_succ qz146 20 0 1 1 rfl rfl) (ep998 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1000 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 27483752773 137438953472 12504268479153 72304434398363648 4159192049999

noncomputable def ep1001 := @ep1000 19198560048000 0 1 114310206037599570897227 ep945 ep946 ep773 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (ep949 ep960))

noncomputable def ep1002 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))) Bool.false 96200770241 191985600480 0 1 Bool.false

noncomputable def ep1003 := nat_lit 10554520004665880346624000

noncomputable def ep1004 := nat_lit 4323292361683292956196819

noncomputable def ep1005 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1))))))) 228789121952132562081317 ep1003 ep1004

noncomputable def ep1006 := nat_lit 115678418794471770755694592000

noncomputable def ep1007 := nat_lit 4627136751778870830227783680

noncomputable def ep1008 := nat_lit 21868811153092136228043868895429914270346772480

noncomputable def ep1009 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 55008068683 549755813888 3118364559543 18076108599590912 4159192049999

noncomputable def ep1010 := @ep1009 19198560048000 0 1 228789121952132562081317 ep1003 ep1004 ep1006 (@Enclosure.Complex.IsNear.re_isNear qz206 Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (ep949 ep960))

noncomputable def ep1011 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz207 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz74 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz74 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz120 qz121 (@HSub.hSub Nat Nat Nat qz119 (@HMul.hMul Nat Nat Nat qz74 2 k) 1)))))) 27483752773 137438953472 12504268479153 72304434398363648 96200770241

noncomputable def ep1012 := @ep1011 191985600480 0 1 2643958185875819628293 26386300011664700866560 400973419664925417095291 ep1007 (@Enclosure.Complex.IsNear.im_isNear qz206 Bool.true 55008068683 549755813888 3118364559543 18076108599590912 Bool.false 27483752773 137438953472 12504268479153 72304434398363648 (ep949 ep960))

noncomputable abbrev qz474 := (ep999 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1013 := @ep942 276264717466065096411961 ep890 ep896 ep892 (@ep943 ep944 114310206037599570897227 ep945 ep946 ep773 ep947 123302835228480166231151 ep771 ep895 ep773 (ep961 (@ep962 4159192049999 19198560048000 0 1 qz474) rfl) (ep1001 (@ep1002 4159192049999 19198560048000 0 1 qz474) rfl) rfl rfl) (@ep1005 ep1006 2643958185875819628293 26386300011664700866560 400973419664925417095291 ep1007 ep1008 276264717466065096411961 ep890 ep896 ep892 (ep1010 (@ep1002 4159192049999 19198560048000 0 1 qz474) rfl) (ep1012 (@ep962 4159192049999 19198560048000 0 1 qz474) rfl) rfl rfl)

noncomputable def ep1014 := @ep899 ep891 ep892 (@ep900 5561879569104896 (BSN.head_sum_c_eq qz146 20) (ep901 (BSN.head_sum_c_succ qz146 19 20 rfl rfl) (ep941 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1013 rfl rfl rfl

noncomputable def ep1015 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz146 1 20) Bool.false ep770 ep771 ep772 ep773 Bool.false 65506076881939536059961 ep890 ep891 ep892 (@ep893 ep773 Bool.false 65506076881939536059961 ep890 ep891 ep892 (BSN.zetaApproximant_eq_folded' qz146 1 20 rfl) (ep1014 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1016 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) (Complex.im (zetaApproximant qz146 1 20)) 337 524288 10652303

noncomputable def ep1017 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178)) Bool.false 674 1048576 10652303

noncomputable def ep1018 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) qz450 Bool.false 92238237 1048576 79

noncomputable def ep1019 := BSN.sin_dyadic_bound_f 1381512 2147483648 1 0 1048576 263299 0 1 1 0 1 1 674 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1381512) qz283 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1381512) qz284 0 0 rfl) rfl rfl

noncomputable def ep1020 := @ep1018 262144 Bool.false 674 1048576 1 131521 (@ep778 92238237 1048576 79 262144 ep887 rfl) (Enclosure.sfrac_false_div 92238237 1048576) (BSN.sin_reduce0 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 97215313183384797184) qz32) 226375608064910080 72057594037927936 Bool.false 674 1048576 14 1000000000000000 263042 131521 (BSN.sin_reduce_arg_pos_rat_q0 92238237 1048576 226375608064910080 72057594037927936 14 97215313183384797184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 674 1048576 97215313183384797184 151115727451828646838272 1381512 2147483648 263299 263042 (ep1019 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz146 1 20) Bool.false ep770 ep771 ep772 ep773 Bool.false 65506076881939536059961 ep890 ep891 ep892 (@ep893 ep773 Bool.false 65506076881939536059961 ep890 ep891 ep892 (BSN.zetaApproximant_eq_folded' qz146 1 20 rfl) (ep1014 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow29.d13 : Enclosure.Real.IsNear (hardyZApproximantEM 1 20 qz151) Bool.false ep755 ep756 ep757 ep758 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 20 qz151) ep759 Bool.false ep755 ep756 ep757 ep758 (@Eq.refl Real ep759) (@ep760 Bool.false ep755 ep756 ep757 ep758 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz363 (Complex.im (@HSub.hSub Complex Complex Complex qz67 qz176 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz177 (@Nat.cast Complex Complex.instNatCast j))))) qz178) (zetaApproximant qz146 1 20)) (@ep762 ep763 ep764 ep758 ep765 ep756 ep766 ep767 ep768 ep755 ep756 ep757 ep758 (@ep769 34477441024 ep770 ep771 ep772 ep773 ep761 ep763 ep764 ep758 (@ep774 34477441024 1048575 1048576 10652303 34477441024 (ep889 rfl rfl) rfl) ep1015 rfl) (@ep1016 34477441024 65506076881939536059961 ep890 ep891 ep892 ep765 ep756 ep766 ep767 (@ep1017 34477441024 337 524288 10652303 34477441024 (ep1020 rfl rfl) rfl) ep1021 rfl) rfl rfl))

theorem EMRow29.d14 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow29.d15 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow29.d16 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow29.d17 : @Eq Nat (Nat.pow 20 (Nat.succ (Nat.mul 2 3))) 1280000000 := @Eq.refl Nat 1280000000

noncomputable abbrev qz533 := (@HAdd.hAdd Complex Complex Complex qz537 qz536 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz475 := qz533

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz475) (@HAdd.hAdd Real Real Real qz387 (Complex.re qz272) qz292))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz476 := (@HPow.hPow Complex Complex Complex qz511 qz526 (@HSub.hSub Complex Complex Complex qz518 qz512 qz513))

noncomputable abbrev qz223 := qz476

noncomputable def ep1022 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 4505462747 103079215104 7952293 103079215104 72942174637795539 72057594037927936 146773963883

noncomputable def ep1023 := nat_lit 7843474915219193273671221248

noncomputable def ep1024 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) 26561 1769472 1 1769472 1526643 524288 2637 524288 4505462747 103079215104

noncomputable abbrev qz224 := qz271

noncomputable abbrev qz534 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz477 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz534 qz224 2))

noncomputable def ep1025 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz477 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1026 := nat_lit 781950621441006189802102638025

noncomputable def ep1027 := nat_lit 19807040628566084398385987584

noncomputable def ep1028 := nat_lit 26986075409044041160201671

noncomputable def ep1029 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz478 := (@HPow.hPow Real Nat Real qz534 qz224 1)

noncomputable def ep1030 := @Enclosure.Real.IsNear.mulLit_ff qz478 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1026 ep1027 ep1028 ep1029

noncomputable def ep1031 := ep1030 (@Enclosure.Real.IsNear.of_eq qz478 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz479 := (@HPow.hPow Real Nat Real qz534 qz224 2)

noncomputable def ep1032 := @Enclosure.Real.IsNear.inv_image qz479 ep1026 ep1027 ep1028 ep1029 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz479 (@HMul.hMul Real Real Real qz0 qz478 qz224) Bool.false ep1026 ep1027 ep1028 ep1029 (BSN.pow_succ_r qz224 1 2 rfl) ep1031) rfl rfl rfl

noncomputable def ep1033 := ep1025 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz477 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1032 rfl rfl rfl) rfl)

noncomputable def ep1034 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 1526643 524288 2637 524288

noncomputable def ep1035 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))))) Bool.false 3053286 1048576 5274 1048576

noncomputable def ep1036 := nat_lit 211616473556699801724564720211731120641413

noncomputable def ep1037 := nat_lit 24958177605590974694837698837872640000000

noncomputable def ep1038 := nat_lit 223322012890755217373282550075894491038188982755262000969623

noncomputable def ep1039 := nat_lit 7626051937593643248067637184130794119816536740880973824000000

noncomputable def ep1040 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)))) ep1036 ep1037 ep1038 ep1039 1524006 1529280

noncomputable def ep1041 := nat_lit 68232626281740033548749385378977476156474063165769

noncomputable def ep1042 := nat_lit 8050931187288295201174570471689076237926400000000

noncomputable def ep1043 := nat_lit 5464029779982523578144232587910966851149811690943244518710063

noncomputable def ep1044 := nat_lit 190651298439841081201690929603269852995413418522024345600000000

noncomputable def ep1045 := nat_lit 29254465688534542654619187323524607023578489

noncomputable def ep1046 := nat_lit 7862237487586225782397041476258863513600000000

noncomputable def ep1047 := nat_lit 7438783892897303511739447749149714050307054871144094095657

noncomputable def ep1048 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20))) ep1041 ep1042 ep1043 ep1044 ep1045 ep1046 ep1047

noncomputable def ep1049 := nat_lit 11915706152490067575105683100204365812213338657626521600000000

noncomputable def ep1050 := nat_lit 536696637918936918182488831870625525683027525292113737629375032651388678563824211591168000000000

noncomputable def ep1051 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 20)) (Complex.re (zetaApproximant qz5 1 20)) ep282 ep283 ep284 ep285 ep282 ep283 ep284 ep285 ep1041

noncomputable def ep1052 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 20)) (Complex.im (zetaApproximant qz5 1 20)) 5408739750490361932683 88669258977315389440000 ep420 ep421 5408739750490361932683 88669258977315389440000 ep420 ep421 ep1045

noncomputable def ep1053 := @ep1022 504403158265495552 ep1023 228275164124183161 216172782113783808 117180492078401 1513209474796486656 (@ep1024 7952293 103079215104 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz477) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow29.d14 EMRow29.d15 rfl) (ep1033 rfl)) (ep1034 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 20)) (@ep1035 1526643 524288 2637 524288 (@ep1040 524288 (@ep1048 ep1049 ep1050 ep1036 ep1037 ep1038 ep1039 (@ep1051 ep1042 ep1043 ep1044 ep550 ep550 rfl) (@ep1052 ep1046 ep1047 ep1049 ep558 ep558 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz475)

noncomputable abbrev qz480 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1054 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz480) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 72942174637795539 72057594037927936 146773963883 504403158265495552 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz16 3)

noncomputable def ep1055 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz480) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 14646609 524288 1 3670016 4980140771 137438953472 1383 137438953472

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz480 102526263 1048576 1 1048576 2 7 0 1 14646609 524288

noncomputable abbrev qz481 := (Complex.re qz533)

noncomputable abbrev qz482 := (Complex.im qz533)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz267 qz481 qz481) (@HMul.hMul Real Real Real qz267 qz482 qz482))

noncomputable abbrev qz227 := qz475

noncomputable def ep1057 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 102526263 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1058 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 102526263 1048576 1 1048576 102526263

noncomputable def ep1059 := @Enclosure.Real.IsNear.sqrt_image qz226 2390068949 250000 0 1 51263131 51263132 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz481 qz481)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz482 qz482)

noncomputable def ep1060 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 2387006449 250000 0 1

noncomputable abbrev qz230 := qz481

noncomputable def ep1061 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz483 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1062 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz483 qz16) Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 97714 1000 3 qz17)

noncomputable abbrev qz484 := (ep1062 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz16 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz20))

noncomputable def ep1063 := @ep1061 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz484)

noncomputable def ep1064 := ep1063 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz484)

noncomputable abbrev qz231 := qz482

noncomputable def ep1065 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 97714 1000 0 1 97714 1000 0 1 2387006449 250000

noncomputable def ep1066 := @ep1065 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz484)

noncomputable def ep1067 := ep1066 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 97714 1000 0 1 qz484)

noncomputable def ep1068 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 4980140771 137438953472

noncomputable def ep1069 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 4980140771 137438953472

noncomputable def ep1070 := nat_lit 1517916658166300132976085115678775591559248874642347123017789

noncomputable def ep1071 := nat_lit 1156070631091827503657211635254091060470024765440000000000000000

noncomputable def ep1072 := nat_lit 3558762240390952816921421299176171517495667667472555660431628155807280963

noncomputable def ep1073 := nat_lit 4882189418559649078348399851663670808689921719785226240000000000000000000000000000

noncomputable def ep1074 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1070 ep1071 ep1072 ep1073

noncomputable def ep1075 := nat_lit 488069058902851388092895456474770243568051192891707240824889

noncomputable def ep1076 := nat_lit 1108827796780854265117941540293645777636156238149379373481456880314188919

noncomputable def ep1077 := nat_lit 10298475992634487448831896592040053479911976817506398821929

noncomputable def ep1078 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1075 ep1071 ep1076 ep1073 ep1077

noncomputable def ep1079 := nat_lit 11560706310918275036572116352540910604700247654400000000000000

noncomputable def ep1080 := nat_lit 612483610902524637950869939720631434964877857330794071737542818873273011

noncomputable def ep1081 := nat_lit 1220547354639912269587099962915917702172480429946306560000000000000000000000000000

noncomputable def ep1082 := nat_lit 17548188689511123951441550166451312120020688261165823820766907852842317445776485403169085762538350996724121600000000000000

noncomputable def ep1083 := nat_lit 698619394880253369632370570667

noncomputable def ep1084 := nat_lit 34001038676661445538611200000000

noncomputable def ep1085 := nat_lit 386169779292812815112405171470013

noncomputable def ep1086 := nat_lit 69872665746768593416932556800000000000000

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1083 ep1084 ep1085 ep1086 ep1083 ep1084 ep1085

noncomputable def ep1088 := nat_lit 101481407127781232046299147827

noncomputable def ep1089 := nat_lit 3400103867666144553861120000000

noncomputable def ep1090 := nat_lit 293692463544657669725052152467819

noncomputable def ep1091 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090

noncomputable def ep1092 := nat_lit 34936332873384296708466278400000000000000

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090 ep1092

noncomputable def ep1094 := nat_lit 3209481862643545472833829

noncomputable def ep1095 := nat_lit 2266735911777429702574080000

noncomputable def ep1096 := nat_lit 8767245886478126286753046463

noncomputable def ep1097 := nat_lit 23290888582256197805644185600000000000

noncomputable def ep1098 := nat_lit 650477166940600187539863135667

noncomputable def ep1099 := nat_lit 359868041633378436252146032081013

noncomputable abbrev qz232 := (Complex.re qz476)

noncomputable abbrev qz233 := (Complex.im qz476)

noncomputable def ep1100 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1094 ep1095 ep1096 ep1097 ep1098 ep1084 ep1099

noncomputable def ep1101 := nat_lit 1583585671039287326098690365641097679382767048442511360000

noncomputable def ep1102 := nat_lit 194090738185468315047034880000

noncomputable def ep1103 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 7160706847 120000000 0 1 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 ep1094

noncomputable def ep1104 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 7160706847 120000000 0 1 0 1 0 1 7160706847

noncomputable def ep1105 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 21482120541 500000 0 1 7160706847 120000000 0

noncomputable def ep1106 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz13) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow29.d16 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz13 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz485 := (@HAdd.hAdd Complex Complex Complex qz510 qz509 qz514)

noncomputable abbrev qz234 := qz485

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1

noncomputable abbrev qz235 := (Complex.re qz485)

noncomputable abbrev qz236 := (Complex.im qz485)

noncomputable def ep1108 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 2386818949 100000 0 1 2387006449 125000 0 1

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 2386818949 250000 0 1 5 2 0 1 2386818949 100000

noncomputable abbrev qz486 := (@HAdd.hAdd Complex Complex Complex qz510 qz509 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz486

noncomputable def ep1110 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1

noncomputable abbrev qz238 := (Complex.re qz486)

noncomputable abbrev qz239 := (Complex.im qz486)

noncomputable def ep1111 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 2387006449 250000 0 1

noncomputable def ep1112 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1113 := @ep1112 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable abbrev qz487 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1114 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz487 qz16) Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 97714 1000 1 qz17)

noncomputable abbrev qz488 := (ep1114 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz16 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz20))

noncomputable def ep1115 := ep1113 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz488)

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 97714 1000 0 1 97714 1000 0 1 2387006449 250000

noncomputable def ep1117 := @ep1116 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep1118 := ep1117 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz488)

noncomputable def ep1119 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 (@ep1111 9547275796 2386818949 250000 0 1 (ep1115 rfl) (ep1118 rfl) rfl rfl)

noncomputable def ep1120 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 48857 1000 0 1 146571 1000 0 1

noncomputable def ep1121 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 97714 1000 0 1 48857 1000

noncomputable def ep1122 := @ep1121 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep1123 := ep1122 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz488)

noncomputable def ep1124 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 97714 1000 0 1 3 2 0 1 146571 1000

noncomputable def ep1125 := @ep1124 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 97714 1000 0 1 ep512)

noncomputable def ep1126 := ep1125 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 97714 1000 0 1 qz488)

noncomputable abbrev qz240 := (ep1110 (BSN.ascPochhammer_succ_eval_c 1 2 qz272 rfl) (ep1119 (@ep1120 195428000 48857 250 0 1 (ep1123 rfl) (ep1126 rfl) rfl rfl)))

noncomputable def ep1127 := @ep1109 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz240)

noncomputable abbrev qz489 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1128 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz489 qz16) Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 (BSN.s_add_nat_mk qz16 Bool.false 97714 1000 2 qz17)

noncomputable abbrev qz490 := (ep1128 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz16 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz20))

noncomputable def ep1129 := ep1127 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz490)

noncomputable def ep1130 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 48857 250 0 1 97714 1000 0 1 2387006449 125000

noncomputable def ep1131 := @ep1130 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz240)

noncomputable def ep1132 := ep1131 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz490)

noncomputable def ep1133 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 (@ep1108 537053013525000 21482120541 500000 0 1 (ep1129 rfl) (ep1132 rfl) rfl rfl)

noncomputable def ep1134 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 116612813391293 125000000 0 1 48857 100 0 1

noncomputable def ep1135 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 2386818949 250000 0 1 97714 1000 0 1 116612813391293 125000000

noncomputable def ep1136 := @ep1135 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz240)

noncomputable def ep1137 := ep1136 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz490)

noncomputable def ep1138 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 48857 250 0 1 5 2 0 1 48857 100

noncomputable def ep1139 := @ep1138 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 2386818949 250000 0 1 Bool.false 48857 250 0 1 qz240)

noncomputable def ep1140 := ep1139 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 97714 1000 0 1 qz490)

noncomputable abbrev qz241 := (ep1107 (BSN.ascPochhammer_succ_eval_c 2 3 qz272 rfl) (ep1133 (@ep1134 11655174214129300 116551742141293 125000000 0 1 (ep1137 rfl) (ep1140 rfl) rfl rfl)))

noncomputable def ep1141 := @ep1105 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz241)

noncomputable def ep1142 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 116551742141293 125000000 0 1 0 1 0

noncomputable def ep1143 := @ep1142 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz241)

noncomputable def ep1144 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 116551742141293 90000000000 0 1 0 1 0 1 116551742141293

noncomputable def ep1145 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 116551742141293 125000000 0 1 116551742141293 90000000000 0

noncomputable def ep1146 := @ep1145 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz241)

noncomputable def ep1147 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 21482120541 500000 0 1 0 1 0

noncomputable def ep1148 := @ep1147 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 21482120541 500000 0 1 Bool.true 116551742141293 125000000 0 1 qz241)

noncomputable def ep1149 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 (@ep1104 7160706847 120000000 0 1 (ep1141 rfl) (ep1143 rfl) rfl rfl) (@ep1144 116551742141293 90000000000 0 1 (ep1146 rfl) (ep1148 rfl) rfl rfl)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 ep1149

noncomputable def ep1151 := nat_lit 776362952741873260188139520000

noncomputable def ep1152 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 Bool.false 139525406268067975 9444732965739290427392 3087624732345216041 ep1151

noncomputable abbrev qz491 := (@Nat.cast Real Real.instNatCast 1280000000)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz491))

noncomputable def ep1153 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz134) (@HMul.hMul Real Real Real qz0 qz242 qz415)) Bool.true 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 Bool.false 139525406268067975 9444732965739290427392 3087624732345216041

noncomputable def ep1154 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz491) 4917165483517163 137438953472 1 137438953472 1920767 1920768 68719476736 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz491) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz491 qz18)) Bool.false 4917165483517163 137438953472 1 137438953472 (BSN.sqrt_natCast_div_one 1280000000) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz491 qz18)) Bool.false 4917165483517163 137438953472 1 137438953472 4917165483517163 137438953472 1 137438953472 (BSN.sqrt_enclosure 1280000000 1 2458582741758581 2458582741758582 68719476736 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1155 := nat_lit 7417073856812098318501937152

noncomputable def ep1156 := nat_lit 2475880078570760549798248448

noncomputable def ep1157 := nat_lit 21043360000000000000000000

noncomputable def ep1158 := BSN.log_dyadic_bound 4 36 6 5 38005766984454635520 68719476736 21043360000 157571184526884864 990904320 15334308083 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 4) (BSN.artanhQ 36) 0 5 157571184526884864 38005766984454635520 990904320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1159 := @Enclosure.Real.IsNear.mulLit_ff qz16 qz136 97714 1000 0 1 3372894687714551 1125899906842624 1562631521 32880250000000000000 164789515757669818207 562949953421312000 76345488221497 16440125000000000000000 qz20 (BSN.isNear_log_sfrac 20 1 3372894687714551 1125899906842624 1562631521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false ep1155 ep1156 1000084173440000 ep1157 3372894687714551 1125899906842624 1562631521 32880250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 15334308083 68719476736 24973259072661432 36028797018963968 21043360000 1000000000000000 rfl rfl rfl rfl (ep1158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1160 := nat_lit 2757469811700712390778683392

noncomputable def ep1161 := nat_lit 4951760157141521099596496896

noncomputable def ep1162 := nat_lit 6365860782646505441833992284208553016219037579252144120563927545473587005206793096428923538046495747786005666534344001

noncomputable def ep1163 := nat_lit 1588688889838625401839090896837790508620815087385166809651675190059187501826767531852223215396959798637323240569170821120

noncomputable def ep1164 := nat_lit 364357454019424437623506142263820236133813766627005972528769850589244376158116024234951802836343211273823833113921

noncomputable def ep1165 := nat_lit 19096853633031477476626729840341131408184845110223178349746725096719582526868063057238300710533814556935469351936804161

noncomputable def ep1166 := nat_lit 71491000042738143082759090357700572887936678932332506434325383552663437582204538933350044692863190938679545825612686950400

noncomputable def ep1167 := BSN.cos_dyadic_bound_f 156744011502537 281474976710656 3 2 137438953472 42127820313 ep1162 ep1163 ep1164 ep1165 ep1166 ep1164 116674040200 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 156744011502537) (BSN.cosEvenQ 281474976710656) 0 2 ep1162 ep1163 ep1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 156744011502537) (BSN.cosOddQ 281474976710656) 0 2 ep1165 ep1166 ep1164 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10057953842631) (@Nat.cast Real Real.instNatCast 34359738368))

noncomputable def ep1168 := @Enclosure.Real.IsNear.cos_image qz137 qz492 Bool.false 10057953842631 34359738368 5 1073741824 Bool.true 116674040200 137438953472 1 21043360000 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 164789515757669818207 562949953421312000 76345488221497 16440125000000000000000 10057953842631 34359738368 5 1073741824 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 10057953842631 34359738368) (BSN.cos_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1160) (@Nat.cast Real Real.instNatCast ep1161)) 226375608064910080 72057594037927936 Bool.false 116674040200 137438953472 46 1000000000000000 42086720000 21043360000 (BSN.sin_reduce_arg_pos_rat_q2 10057953842631 34359738368 226375608064910080 72057594037927936 46 ep1160 ep1161 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 116674040200 137438953472 ep1160 ep1161 156744011502537 281474976710656 42127820313 42086720000 (ep1167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1169 := nat_lit 11458257922800494255751087306661584373005360591640557812237046565971985213871301080752674407041423271445791140695328065

noncomputable def ep1170 := nat_lit 14298200008547628616551818071540114577587335786466501286865076710532687516440907786670008938572638187735909165122537390080

noncomputable def ep1171 := nat_lit 30009133219075739220734790602740484315584108708198350546189122997787578688292008737932052572665802107635009653710341441

noncomputable def ep1172 := nat_lit 262133666823373191303449997978235433922434489418552523592526406359765937801416642755616830540498366775158334693913185484800

noncomputable def ep1173 := BSN.sin_dyadic_bound_f 156744011502537 281474976710656 3 2 137438953472 42127820313 ep1169 ep1170 ep1164 ep1171 ep1172 ep1164 72640445170 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 156744011502537) (BSN.sinEvenQ 281474976710656) 0 2 ep1169 ep1170 ep1164 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 156744011502537) (BSN.sinOddQ 281474976710656) 0 2 ep1171 ep1172 ep1164 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1174 := @Enclosure.Real.IsNear.sin_image qz137 qz492 Bool.false 10057953842631 34359738368 5 1073741824 Bool.true 72640445170 137438953472 1 21043360000 (@Enclosure.Real.IsNear.recentre' qz137 Bool.false 164789515757669818207 562949953421312000 76345488221497 16440125000000000000000 10057953842631 34359738368 5 1073741824 (ep1159 rfl) rfl) (Enclosure.sfrac_false_div 10057953842631 34359738368) (BSN.sin_reduce2 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1160) (@Nat.cast Real Real.instNatCast ep1161)) 226375608064910080 72057594037927936 Bool.false 72640445170 137438953472 46 1000000000000000 42086720000 21043360000 (BSN.sin_reduce_arg_pos_rat_q2 10057953842631 34359738368 226375608064910080 72057594037927936 46 ep1160 ep1161 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 72640445170 137438953472 ep1160 ep1161 156744011502537 281474976710656 42127820313 42086720000 (ep1173 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz493 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 3841535 137438953472 1 137438953472 3841535 137438953472 1 137438953472 (ep1154 rfl rfl) rfl)

noncomputable def ep1175 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz134) (@HMul.hMul Real Real Real qz0 qz242 qz415) Bool.true 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 Bool.false 139525406268067975 9444732965739290427392 3087624732345216041 ep1151 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz134 3841535 137438953472 1 137438953472 14584255025 17179869184 415197429 88262249021440000 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 qz493 (@Enclosure.Real.IsNear.recentre' qz134 Bool.true 116674040200 137438953472 106290541824 22595135749488640000 14584255025 17179869184 415197429 88262249021440000 (ep1168 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz415 3841535 137438953472 1 137438953472 36320222585 68719476736 415197429 88262249021440000 139525406268067975 9444732965739290427392 3087624732345216041 ep1151 qz493 (@Enclosure.Real.IsNear.neg qz135 Bool.true 36320222585 68719476736 415197429 88262249021440000 (@Enclosure.Real.IsNear.recentre' qz135 Bool.true 72640445170 137438953472 106290541824 22595135749488640000 36320222585 68719476736 415197429 88262249021440000 (ep1174 rfl rfl) rfl)) rfl)

noncomputable def ep1176 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 116551742141293 90000000000 0 1 139525406268067975 9444732965739290427392 3087624732345216041 ep1151 ep1098

noncomputable def ep1177 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 7160706847 120000000 0 1 Bool.false 116551742141293 90000000000 0 1 ep1149

noncomputable def ep1178 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 Bool.false 139525406268067975 9444732965739290427392 3087624732345216041 ep1151

noncomputable def ep1179 := nat_lit 39964021279768442641756993

noncomputable def ep1180 := nat_lit 45334718235548594051481600000

noncomputable def ep1181 := nat_lit 22109575561870930872482932727

noncomputable def ep1182 := nat_lit 93163554329024791222576742400000000000

noncomputable def ep1183 := nat_lit 52239354361881932622215461151

noncomputable def ep1184 := nat_lit 1700051933833072276930560000000

noncomputable def ep1185 := nat_lit 142700686354478035323935526347597

noncomputable def ep1186 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1179 ep1180 ep1181 ep1182 ep1183 ep1184 ep1185

noncomputable def ep1187 := nat_lit 17468166436692148354233139200000000000000

noncomputable def ep1188 := nat_lit 2300315499142477445913203783830223617881379723385241600000

noncomputable def ep1189 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 7160706847 120000000 0 1 139525406268067975 9444732965739290427392 3087624732345216041 ep1151 ep1179

noncomputable def ep1190 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 116551742141293 90000000000 0 1 56025926127463375 2361183241434822606848 1224354812144165729 ep1102 ep1183

noncomputable abbrev qz494 := (@ep1153 ep1151 (BSN.cpow_neg_s_sub_mk qz16 97714 1000 20 3 1280000000 qz17 rfl EMRow29.d17) ep1175)

noncomputable def ep1191 := ep1093 (@ep1100 ep1086 ep1101 ep1083 ep1084 ep1085 ep1086 (@ep1103 ep1095 ep1096 ep1097 ep1150 (ep1152 qz494) rfl) (@ep1176 ep1084 ep1099 ep1086 ep1177 (ep1178 qz494) rfl) rfl rfl) (@ep1186 ep1187 ep1188 ep1088 ep1089 ep1090 ep1092 (@ep1189 ep1180 ep1181 ep1182 ep1150 (ep1178 qz494) rfl) (@ep1190 ep1184 ep1185 ep1187 ep1177 (ep1152 qz494) rfl) rfl rfl)

noncomputable def ep1192 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1088 ep1089 ep1090 ep1092 ep1088 ep1089 ep1090

noncomputable def ep1193 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.true ep1083 ep1084 ep1085 ep1086 Bool.true ep1088 ep1089 ep1090

noncomputable def ep1194 := @ep1055 72942174637795539 72057594037927936 146773963883 504403158265495552 (@ep1056 1 3670016 (ep1057 (@ep1058 1048576 1 1048576 (ep1059 (@ep1060 9560275796 2390068949 250000 0 1 (ep1064 rfl) (ep1067 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1068 1383 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1069 1383 137438953472 4980140771 137438953472 1383 137438953472 (@ep1074 2490069694 2490071077 68719476736 (@ep1078 ep1079 ep1080 ep1081 ep1082 ep1070 ep1071 ep1072 ep1073 (@ep1087 ep1086 ep1075 ep1071 ep1076 ep1073 (@ep1091 ep1092 ep1191) (@ep1091 ep1092 ep1191) rfl) (@ep1192 ep1092 ep1077 ep1079 ep1080 ep1081 (@ep1193 ep1092 ep1191) (@ep1193 ep1092 ep1191) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow29.d18 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 228275164124183161 216172782113783808 117180492078401 1513209474796486656 := ep1053 (ep1054 ep1194) rfl rfl

noncomputable abbrev qz535 := (@HAdd.hAdd Complex Complex Complex qz537 qz543 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz495 := qz535

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz495) (@HAdd.hAdd Real Real Real qz387 (Complex.re qz423) qz292))

noncomputable abbrev qz496 := (@HPow.hPow Complex Complex Complex qz511 qz526 (@HSub.hSub Complex Complex Complex qz518 qz528 qz513))

noncomputable abbrev qz244 := qz496

noncomputable def ep1195 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 19382703823 463856467968 36110327 463856467968 559939609727677985 504403158265495552 159669267655

noncomputable def ep1196 := nat_lit 269508306667706979136911179776

noncomputable def ep1197 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20)) 26561 1769472 1 1769472 729743 262144 333 65536 19382703823 463856467968

noncomputable def ep1198 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20)) (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))))) Bool.false 729743 262144 333 65536

noncomputable def ep1199 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))))) Bool.false 2918972 1048576 5328 1048576

noncomputable def ep1200 := nat_lit 2158296984766318956439669752517788391302953

noncomputable def ep1201 := nat_lit 278515619297388893158190432309477376000000

noncomputable def ep1202 := nat_lit 18167716232648059255689310603581518670253307557930972769003

noncomputable def ep1203 := nat_lit 642311835589881590617930767125752931635679826146230272000000

noncomputable def ep1204 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20)))) ep1200 ep1201 ep1202 ep1203 1456822 1462150

noncomputable def ep1205 := nat_lit 13487741058442272103336178709718812408529256512801

noncomputable def ep1206 := nat_lit 1740592070763941482716723755765814037315584000000

noncomputable def ep1207 := nat_lit 18031123263722971978024448810292650410758673391667339312539

noncomputable def ep1208 := nat_lit 4291046108462573330914436911731249039787321521

noncomputable def ep1209 := nat_lit 12377543614321361654874480041001344265355264000000

noncomputable def ep1210 := nat_lit 2845686852605984951351287360184755406138211797159030343

noncomputable def ep1211 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20))) ep1205 ep1206 ep1207 ep1203 ep1208 ep1209 ep1210

noncomputable def ep1212 := nat_lit 13381496574789199804540224315119852742409996378046464000000

noncomputable def ep1213 := nat_lit 166952572170373861070516634344523180908713012349213568062208036640108118385518304454380617728000000

noncomputable def ep1214 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz146 1 20)) (Complex.re (zetaApproximant qz146 1 20)) ep770 ep771 ep772 ep773 ep770 ep771 ep772 ep773 ep1205

noncomputable def ep1215 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz146 1 20)) (Complex.im (zetaApproximant qz146 1 20)) 65506076881939536059961 ep890 ep891 ep892 65506076881939536059961 ep890 ep891 ep892 ep1208

noncomputable def ep1216 := @ep1195 504403158265495552 ep1196 15687448127876674939 13618885273168379904 1064514893068541 13618885273168379904 (@ep1197 36110327 463856467968 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz477) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow29.d14 EMRow29.d15 rfl) (ep1033 rfl)) (ep1198 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz146 1 20)) (@ep1199 729743 262144 333 65536 (@ep1204 524288 (@ep1211 ep1212 ep1213 ep1200 ep1201 ep1202 ep1203 (@ep1214 ep1206 ep1207 ep1203 ep1015 ep1015 rfl) (@ep1215 ep1209 ep1210 ep1212 ep1021 ep1021 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz495)

noncomputable def ep1217 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz480) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 559939609727677985 504403158265495552 159669267655 504403158265495552 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz151 3)

noncomputable def ep1218 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz480) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 104916565 3670016 1 3670016 5336999069 137438953472 1471 137438953472

noncomputable def ep1219 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz480 104916565 1048576 1 1048576 2 7 0 1 104916565 3670016

noncomputable abbrev qz497 := (Complex.re qz535)

noncomputable abbrev qz498 := (Complex.im qz535)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz267 qz497 qz497) (@HMul.hMul Real Real Real qz267 qz498 qz498))

noncomputable abbrev qz247 := qz495

noncomputable def ep1220 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 104916565 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1221 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 104916565 1048576 1 1048576 104916565

noncomputable def ep1222 := @Enclosure.Real.IsNear.sqrt_image qz246 400450001 40000 0 1 52458282 52458283 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz497 qz497)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz498 qz498)

noncomputable def ep1223 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 399960001 40000 0 1

noncomputable abbrev qz250 := qz497

noncomputable def ep1224 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1225 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz483 qz151) Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 99995 1000 3 qz152)

noncomputable abbrev qz499 := (ep1225 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz151 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz153))

noncomputable def ep1226 := @ep1224 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz499)

noncomputable def ep1227 := ep1226 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz499)

noncomputable abbrev qz251 := qz498

noncomputable def ep1228 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 99995 1000 0 1 99995 1000 0 1 399960001 40000

noncomputable def ep1229 := @ep1228 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz499)

noncomputable def ep1230 := ep1229 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 99995 1000 0 1 qz499)

noncomputable def ep1231 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 5336999069 137438953472

noncomputable def ep1232 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 5336999069 137438953472

noncomputable def ep1233 := nat_lit 714033998944123922161037559556007070759135047072755884012313

noncomputable def ep1234 := nat_lit 473526530495212545497993885800075698368522143924224000000000000

noncomputable def ep1235 := nat_lit 66449186464579026085683875676418739016401256019350794919187470855917423

noncomputable def ep1236 := nat_lit 79989791433681290499660183169657582529575677456961146716160000000000000000000000

noncomputable def ep1237 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1233 ep1234 ep1235 ep1236

noncomputable def ep1238 := nat_lit 595921357790575845144710062834822369514571675313472856787849

noncomputable def ep1239 := nat_lit 53514549453827610418594695441570196273690245917558816461141329820238399

noncomputable def ep1240 := nat_lit 820226674677417201502274282786004869753912303883909911281

noncomputable def ep1241 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1238 ep1234 ep1239 ep1236 ep1240

noncomputable def ep1242 := nat_lit 3288378683994531565958290873611636794225848221696000000000000

noncomputable def ep1243 := nat_lit 89823868130218164354785973853114880157715347929110961514209312747771

noncomputable def ep1244 := nat_lit 555484662733897850692084605344844323122053315673341296640000000000000000000000

noncomputable def ep1245 := nat_lit 2348014181775230964862067380503646519880960112859412317821614740262186852415863352289667146578623328417742848000000000000

noncomputable def ep1246 := nat_lit 771959427554697232706390048957

noncomputable def ep1247 := nat_lit 21760664753063325144711168000000

noncomputable def ep1248 := nat_lit 84333906991176578379533427757343

noncomputable def ep1249 := nat_lit 8943701215586379957367367270400000000000

noncomputable def ep1250 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1246 ep1247 ep1248 ep1249 ep1246 ep1247 ep1248

noncomputable def ep1251 := nat_lit 28639599764616425266010122841

noncomputable def ep1252 := nat_lit 1813388729421943762059264000000

noncomputable def ep1253 := nat_lit 3815483843380249173571000261289

noncomputable def ep1254 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1246 ep1247 ep1248 ep1249 Bool.true ep1251 ep1252 ep1253

noncomputable def ep1255 := nat_lit 745308434632198329780613939200000000000

noncomputable def ep1256 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.true ep1246 ep1247 ep1248 ep1249 Bool.true ep1251 ep1252 ep1253 ep1255

noncomputable def ep1257 := nat_lit 2361802697005347358663401

noncomputable def ep1258 := nat_lit 3022314549036572936765440000

noncomputable def ep1259 := nat_lit 263115147530773855371246979

noncomputable def ep1260 := nat_lit 1242180724386997216301023232000000000

noncomputable def ep1261 := nat_lit 754954448136258731724013561757

noncomputable def ep1262 := nat_lit 82439477928955006620860449508543

noncomputable abbrev qz252 := (Complex.re qz496)

noncomputable abbrev qz253 := (Complex.im qz496)

noncomputable def ep1263 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1257 ep1258 ep1259 ep1260 ep1261 ep1247 ep1262

noncomputable def ep1264 := nat_lit 2333104209164505763028004492850178735247320426825646080000

noncomputable def ep1265 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 1199830003 19200000 0 1 29526716590267005 2361183241434822606848 657881067000056979 ep1102 ep1257

noncomputable def ep1266 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 1199830003 19200000 0 1 0 1 0 1 1199830003

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3599490009 80000 0 1 1199830003 19200000 0

noncomputable abbrev qz500 := (@HAdd.hAdd Complex Complex Complex qz510 qz527 qz514)

noncomputable abbrev qz254 := qz500

noncomputable def ep1268 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1

noncomputable abbrev qz255 := (Complex.re qz500)

noncomputable abbrev qz256 := (Complex.im qz500)

noncomputable def ep1269 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 399930001 16000 0 1 399960001 20000 0 1

noncomputable def ep1270 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 399930001 40000 0 1 5 2 0 1 399930001 16000

noncomputable abbrev qz501 := (@HAdd.hAdd Complex Complex Complex qz510 qz527 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz501

noncomputable def ep1271 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz66 (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1

noncomputable abbrev qz258 := (Complex.re qz501)

noncomputable abbrev qz259 := (Complex.im qz501)

noncomputable def ep1272 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 399960001 40000 0 1

noncomputable def ep1273 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1274 := @ep1273 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep1275 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz487 qz151) Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 99995 1000 1 qz152)

noncomputable abbrev qz502 := (ep1275 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz151 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz153))

noncomputable def ep1276 := ep1274 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz502)

noncomputable def ep1277 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 99995 1000 0 1 99995 1000 0 1 399960001 40000

noncomputable def ep1278 := @ep1277 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep1279 := ep1278 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz502)

noncomputable def ep1280 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 (@ep1272 1599720004 399930001 40000 0 1 (ep1276 rfl) (ep1279 rfl) rfl rfl)

noncomputable def ep1281 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 19999 400 0 1 59997 400 0 1

noncomputable def ep1282 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 99995 1000 0 1 19999 400

noncomputable def ep1283 := @ep1282 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep1284 := ep1283 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz502)

noncomputable def ep1285 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 99995 1000 0 1 3 2 0 1 59997 400

noncomputable def ep1286 := @ep1285 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 99995 1000 0 1 ep978)

noncomputable def ep1287 := ep1286 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 99995 1000 0 1 qz502)

noncomputable abbrev qz260 := (ep1271 (BSN.ascPochhammer_succ_eval_c 1 2 qz423 rfl) (ep1280 (@ep1281 31998400 19999 100 0 1 (ep1284 rfl) (ep1287 rfl) rfl rfl)))

noncomputable def ep1288 := @ep1270 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz260)

noncomputable def ep1289 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz489 qz151) Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 (BSN.s_add_nat_mk qz151 Bool.false 99995 1000 2 qz152)

noncomputable abbrev qz503 := (ep1289 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz151 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz153))

noncomputable def ep1290 := ep1288 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz503)

noncomputable def ep1291 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 19999 100 0 1 99995 1000 0 1 399960001 20000

noncomputable def ep1292 := @ep1291 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz260)

noncomputable def ep1293 := ep1292 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz503)

noncomputable def ep1294 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 (@ep1269 14397960036000 3599490009 80000 0 1 (ep1290 rfl) (ep1293 rfl) rfl rfl)

noncomputable def ep1295 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 7998200089999 8000000 0 1 19999 40 0 1

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 399930001 40000 0 1 99995 1000 0 1 7998200089999 8000000

noncomputable def ep1297 := @ep1296 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz260)

noncomputable def ep1298 := ep1297 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz503)

noncomputable def ep1299 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 19999 100 0 1 5 2 0 1 19999 40

noncomputable def ep1300 := @ep1299 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 399930001 40000 0 1 Bool.false 19999 100 0 1 qz260)

noncomputable def ep1301 := ep1300 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 99995 1000 0 1 qz503)

noncomputable abbrev qz261 := (ep1268 (BSN.ascPochhammer_succ_eval_c 2 3 qz423 rfl) (ep1294 (@ep1295 319768011599960 7994200289999 8000000 0 1 (ep1298 rfl) (ep1301 rfl) rfl rfl)))

noncomputable def ep1302 := @ep1267 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz261)

noncomputable def ep1303 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 7994200289999 8000000 0 1 0 1 0

noncomputable def ep1304 := @ep1303 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz261)

noncomputable def ep1305 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) 7994200289999 5760000000 0 1 0 1 0 1 7994200289999

noncomputable def ep1306 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 7994200289999 8000000 0 1 7994200289999 5760000000 0

noncomputable def ep1307 := @ep1306 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz261)

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3599490009 80000 0 1 0 1 0

noncomputable def ep1309 := @ep1308 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1106) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 3599490009 80000 0 1 Bool.true 7994200289999 8000000 0 1 qz261)

noncomputable def ep1310 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 (@ep1266 1199830003 19200000 0 1 (ep1302 rfl) (ep1304 rfl) rfl rfl) (@ep1305 7994200289999 5760000000 0 1 (ep1307 rfl) (ep1309 rfl) rfl rfl)

noncomputable def ep1311 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 ep1310

noncomputable def ep1312 := nat_lit 1552725905483746520376279040000

noncomputable def ep1313 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 29526716590267005 2361183241434822606848 657881067000056979 ep1102 Bool.false 472188849884541215 18889465931478580854784 10312410865173021457 ep1312

noncomputable def ep1314 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz472)) Bool.true 29526716590267005 2361183241434822606848 657881067000056979 ep1102 Bool.false 472188849884541215 18889465931478580854784 10312410865173021457

noncomputable def ep1315 := @Enclosure.Real.IsNear.mulLit_ff qz151 qz136 99995 1000 0 1 3372894687714551 1125899906842624 1562631521 32880250000000000000 67454520859603305449 225179981368524800 31251067788479 6576050000000000000000 qz153 (BSN.isNear_log_sfrac 20 1 3372894687714551 1125899906842624 1562631521 32880250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz418 Bool.false ep1155 ep1156 1000084173440000 ep1157 3372894687714551 1125899906842624 1562631521 32880250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 15334308083 68719476736 24973259072661432 36028797018963968 21043360000 1000000000000000 rfl rfl rfl rfl (ep1158 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1316 := nat_lit 21925336329814276097582301184

noncomputable def ep1317 := nat_lit 7418189462824577424079455067485192770740243876587053069847625670045522424516677777198806674930081706202677522041708303139704558467962547825806894149836959649606764751558377047686641

noncomputable def ep1318 := nat_lit 118471658034259428782235204372444635462331972429639033257780066369387519461588934825569028614577116538889267969336012369372246813616988720376390556367654990461123310430062324062617600

noncomputable def ep1319 := nat_lit 837138975607167629907319708304204371190224742074349061282457552322783289530584357139469916727183550844975155209955777735038972070912449269210672757134972047305994073816792561

noncomputable def ep1320 := nat_lit 44976888902011099055214124549665707565784715233783894689067097044229857752249391702194678466552902400833361316551824090577944926946153229994852268343083208483124174317466711846387185

noncomputable def ep1321 := nat_lit 10780920881117608019183403597892461827072209491097152026457986039614264271004593069126781603926517605038923385209577125612874460039145973554251540629456604131962221249135671489698201600

noncomputable def ep1322 := BSN.cos_dyadic_bound_f 311577769164931 281474976710656 4 3 137438953472 42127820313 ep1317 ep1318 ep1319 ep1320 ep1321 ep1319 61489413144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 311577769164931) (BSN.cosEvenQ 281474976710656) 0 3 ep1317 ep1318 ep1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 311577769164931) (BSN.cosOddQ 281474976710656) 0 3 ep1320 ep1321 ep1319 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz504 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41170972204347) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1323 := @Enclosure.Real.IsNear.cos_image qz218 qz504 Bool.false 41170972204347 137438953472 327 68719476736 Bool.true 61489413144 137438953472 1 21043360000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 67454520859603305449 225179981368524800 31251067788479 6576050000000000000000 41170972204347 137438953472 327 68719476736 (ep1315 rfl) rfl) (Enclosure.sfrac_false_div 41170972204347 137438953472) (BSN.cos_reduce2 qz504 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1316) (@Nat.cast Real Real.instNatCast ep1027)) 226375608064910080 72057594037927936 Bool.false 61489413144 137438953472 47 1000000000000000 42086720000 21043360000 (BSN.sin_reduce_arg_pos_rat_q2 41170972204347 137438953472 226375608064910080 72057594037927936 47 ep1316 ep1027 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 61489413144 137438953472 ep1316 ep1027 311577769164931 281474976710656 42127820313 42086720000 (ep1322 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1324 := nat_lit 19279637093172818166980686372514366059463178197517550446081541588397308914609207583824590925559103234804835052216644713750085893984244148737093401052922813985222743476380080815832561

noncomputable def ep1325 := nat_lit 1540131554445372574169057656841780261010315641585307432351140862802037753000656152732397371989502515005560483601368160801839208577020853364893077232779514875994603035590810212814028800

noncomputable def ep1326 := nat_lit 96368609184869943681078204921700898993797075860044146732651376282517149728373072161495822637228776210043706516810710648421335144880842969910338841832648772137909010840337726125211121

noncomputable def ep1327 := nat_lit 53904604405588040095917017989462309135361047455485760132289930198071321355022965345633908019632588025194616926047885628064372300195729867771257703147283020659811106245678357448491008000

noncomputable def ep1328 := BSN.sin_dyadic_bound_f 311577769164931 281474976710656 4 3 137438953472 42127820313 ep1324 ep1325 ep1319 ep1326 ep1327 ep1319 122916711649 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 311577769164931) (BSN.sinEvenQ 281474976710656) 0 3 ep1324 ep1325 ep1319 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 311577769164931) (BSN.sinOddQ 281474976710656) 0 3 ep1326 ep1327 ep1319 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1329 := @Enclosure.Real.IsNear.sin_image qz218 qz504 Bool.false 41170972204347 137438953472 327 68719476736 Bool.true 122916711649 137438953472 1 21043360000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 67454520859603305449 225179981368524800 31251067788479 6576050000000000000000 41170972204347 137438953472 327 68719476736 (ep1315 rfl) rfl) (Enclosure.sfrac_false_div 41170972204347 137438953472) (BSN.sin_reduce2 qz504 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1316) (@Nat.cast Real Real.instNatCast ep1027)) 226375608064910080 72057594037927936 Bool.false 122916711649 137438953472 47 1000000000000000 42086720000 21043360000 (BSN.sin_reduce_arg_pos_rat_q2 41170972204347 137438953472 226375608064910080 72057594037927936 47 ep1316 ep1027 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 122916711649 137438953472 ep1316 ep1027 311577769164931 281474976710656 42127820313 42086720000 (ep1328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1330 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz472) Bool.true 29526716590267005 2361183241434822606848 657881067000056979 ep1102 Bool.false 472188849884541215 18889465931478580854784 10312410865173021457 ep1312 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 3841535 137438953472 1 137438953472 7686176643 17179869184 27148039831 5648783937372160000 29526716590267005 2361183241434822606848 657881067000056979 ep1102 qz493 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 61489413144 137438953472 6949898196736 1446088687967272960000 7686176643 17179869184 27148039831 5648783937372160000 (ep1323 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz242 qz472 3841535 137438953472 1 137438953472 122916711649 137438953472 27148039831 5648783937372160000 472188849884541215 18889465931478580854784 10312410865173021457 ep1312 qz493 (@Enclosure.Real.IsNear.neg qz217 Bool.true 122916711649 137438953472 27148039831 5648783937372160000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.true 122916711649 137438953472 6949898196736 1446088687967272960000 122916711649 137438953472 27148039831 5648783937372160000 (ep1329 rfl rfl) rfl)) rfl)

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 7994200289999 5760000000 0 1 472188849884541215 18889465931478580854784 10312410865173021457 ep1312 ep1261

noncomputable def ep1332 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1199830003 19200000 0 1 Bool.false 7994200289999 5760000000 0 1 ep1310

noncomputable def ep1333 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 29526716590267005 2361183241434822606848 657881067000056979 ep1102 Bool.false 472188849884541215 18889465931478580854784 10312410865173021457 ep1312

noncomputable def ep1334 := nat_lit 113309269834707127129414729

noncomputable def ep1335 := nat_lit 72535549176877750482370560000

noncomputable def ep1336 := nat_lit 12373139959297778930271374371

noncomputable def ep1337 := nat_lit 29812337385287933191224557568000000000

noncomputable def ep1338 := nat_lit 5245388585080683907374248511

noncomputable def ep1339 := nat_lit 302231454903657293676544000000

noncomputable def ep1340 := nat_lit 1753077672198902350157107951007

noncomputable def ep1341 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1334 ep1335 ep1336 ep1337 ep1338 ep1339 ep1340

noncomputable def ep1342 := nat_lit 372654217316099164890306969600000000000

noncomputable def ep1343 := nat_lit 346231516188738527028049665093048325850523278413660160000

noncomputable def ep1344 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 1199830003 19200000 0 1 472188849884541215 18889465931478580854784 10312410865173021457 ep1312 ep1334

noncomputable def ep1345 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 7994200289999 5760000000 0 1 29526716590267005 2361183241434822606848 657881067000056979 ep1102 ep1338

noncomputable abbrev qz505 := (@ep1314 ep1312 (BSN.cpow_neg_s_sub_mk qz151 99995 1000 20 3 1280000000 qz152 rfl EMRow29.d17) ep1330)

noncomputable def ep1346 := ep1256 (@ep1263 ep1249 ep1264 ep1246 ep1247 ep1248 ep1249 (@ep1265 ep1258 ep1259 ep1260 ep1311 (ep1313 qz505) rfl) (@ep1331 ep1247 ep1262 ep1249 ep1332 (ep1333 qz505) rfl) rfl rfl) (@ep1341 ep1342 ep1343 ep1251 ep1252 ep1253 ep1255 (@ep1344 ep1335 ep1336 ep1337 ep1311 (ep1333 qz505) rfl) (@ep1345 ep1339 ep1340 ep1342 ep1332 (ep1313 qz505) rfl) rfl rfl)

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1251 ep1252 ep1253 ep1255 ep1251 ep1252 ep1253

noncomputable def ep1348 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.true ep1246 ep1247 ep1248 ep1249 Bool.true ep1251 ep1252 ep1253

noncomputable def ep1349 := @ep1218 559939609727677985 504403158265495552 159669267655 504403158265495552 (@ep1219 1 3670016 (ep1220 (@ep1221 1048576 1 1048576 (ep1222 (@ep1223 1601800004 400450001 40000 0 1 (ep1227 rfl) (ep1230 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1231 1471 137438953472 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1232 1471 137438953472 5336999069 137438953472 1471 137438953472 (@ep1237 2668498799 2668500270 68719476736 (@ep1241 ep1242 ep1243 ep1244 ep1245 ep1233 ep1234 ep1235 ep1236 (@ep1250 ep1249 ep1238 ep1234 ep1239 ep1236 (@ep1254 ep1255 ep1346) (@ep1254 ep1255 ep1346) rfl) (@ep1347 ep1255 ep1240 ep1242 ep1243 ep1244 (@ep1348 ep1255 ep1346) (@ep1348 ep1255 ep1346) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow29.d19 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 15687448127876674939 13618885273168379904 1064514893068541 13618885273168379904 := ep1216 (ep1217 ep1349) rfl rfl

noncomputable def EMRow29.d20 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz506 := (EMRow29.d3 qz515 qz529 (@Enclosure.dec_le_dec qz515 qz529 97714 1000 99995 1000 (@Eq.refl Real qz515) (@Eq.refl Real qz529) rfl rfl rfl) 20 20 1 1)

noncomputable abbrev qz262 := qz506

noncomputable def ep1350 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz16 97714 1000 qz17) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz506)

noncomputable def ep1351 := @Enclosure.Real.IsNear.neg_val qz263 ep267 ep268

noncomputable def ep1352 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 20 qz16) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz506)

noncomputable def ep1353 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1351 ep269 ep270 (@ep1352 ep267 ep268 ep269 ep270 (@Eq.refl Real (hardyZApproximantEM 1 20 qz16)) EMRow29.d10) rfl rfl rfl)

noncomputable def ep1354 := @Enclosure.Real.IsNear.pos_val qz264 ep755 ep756

noncomputable def ep1355 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 20 qz151) Bool.false

noncomputable def ep1356 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 20 qz16)

noncomputable def ep1357 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 20 qz16) Bool.true

noncomputable def ep1358 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz16) (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 228275164124183161 216172782113783808 117180492078401 1513209474796486656 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 20))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1359 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 20 qz151)

noncomputable def ep1360 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 20 qz151) Bool.false

noncomputable def ep1361 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 20 qz151) (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 15687448127876674939 13618885273168379904 1064514893068541 13618885273168379904 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz387 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz146 1 20))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz66 (@HMul.hMul Complex Complex Complex qz66 (@HDiv.hDiv Complex Complex Complex qz73 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz146 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1362 := @List.cons EMRow29.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1350 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 20 rfl) (ep1353 (@ep1354 ep757 ep758 (@ep1355 ep755 ep756 ep757 ep758 (@Eq.refl Real (hardyZApproximantEM 1 20 qz151)) EMRow29.d13) rfl rfl rfl)) (ep1356 (hardyZErrorBoundEM 1 20 qz16) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz16 rfl) (@ep1357 Bool.false ep267 ep268 ep269 ep270 228275164124183161 216172782113783808 117180492078401 1513209474796486656 (@ep1352 ep267 ep268 ep269 ep270 (@Eq.refl Real (hardyZApproximantEM 1 20 qz16)) EMRow29.d10) (ep1358 EMRow29.d18) rfl rfl rfl rfl rfl)) (ep1359 (hardyZErrorBoundEM 1 20 qz151) (BSN.hardyZErrorBoundEM_le_strong 1 20 qz151 rfl) (@ep1360 Bool.false ep755 ep756 ep757 ep758 15687448127876674939 13618885273168379904 1064514893068541 13618885273168379904 (@ep1355 ep755 ep756 ep757 ep758 (@Eq.refl Real (hardyZApproximantEM 1 20 qz151)) EMRow29.d13) (ep1361 EMRow29.d19) rfl rfl rfl rfl rfl)))) (@List.nil EMRow29.d0)

noncomputable abbrev qz507 := (@Enclosure.dec_le_dec qz515 qz529 97714 1000 99995 1000 (@Eq.refl Real qz515) (@Eq.refl Real qz529) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1362 (@List.IsChain.singleton EMRow29.d1 EMRow29.d20 (EMRow29.d2 qz280 qz430 qz507))))

noncomputable abbrev qz508 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1363 := And (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz508 qz265)) (@Option.some Real qz16))

noncomputable def ep1364 := ep1363 (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz508 qz265)) (@Option.some Real qz151))

noncomputable def ep1365 := @And.intro (@Eq Nat (@List.length qz508 qz265) 1) ep1364

noncomputable def ep1366 := @And.intro (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz508 qz265)) (@Option.some Real qz16))

noncomputable def ep1367 := @ep1366 (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz508 qz265)) (@Option.some Real qz151))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1362 (@List.IsChain.singleton EMRow29.d1 EMRow29.d20 (EMRow29.d2 qz280 qz430 qz507)))

theorem EMRow29.d21 : Zeta.Certificates.BatchSpec 1 97714 1000 99995 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz508 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz508 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz16)) (@Eq (Option Real) (@Option.map qz508 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz508 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz151)))) qz266 (ep1365 (@Eq.refl Nat 1) (ep1367 (@Eq.refl (Option Real) (@Option.some Real qz16)) (@Eq.refl (Option Real) (@Option.some Real qz151))))

theorem solution : Zeta.Certificates.BatchSpec 1 97714 1000 99995 1000 := EMRow29.d21
#print axioms solution
#check solution
