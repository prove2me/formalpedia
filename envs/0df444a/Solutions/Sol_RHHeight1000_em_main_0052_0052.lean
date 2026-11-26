-- Prove2me | solution 1 for RHHeight1000.em_main_0052_0052
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:36:02.263241+00:00
-- url     : https://prove2.me/submissions/f15b4f0a-21c1-457d-a513-f4b8360054ac

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMLast.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMLast.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMLast.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMLast.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMLast.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz269 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz269

noncomputable abbrev qz270 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz270 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 1562500001 500000000000000 4138529546116343 2251799813685248 1562500001 500000000000000 963576 524288

noncomputable abbrev qz271 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 3 524288 qz271 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 320000 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz272 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz272

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 1562500001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000640000 320000000000000000000 4138529546116343 2251799813685248 1562500001 500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 320000 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 1562500001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000640000 320000000000000000000 4138529546116343 2251799813685248 1562500001 500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi))

theorem EMLast.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 3 524288 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz270) Bool.false 120447 65536 3 524288 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz270) Bool.false 963576 524288 3 524288 120447 65536 3 524288 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 320000 1200336 1048576 1 320000 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 320000 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 320000 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 320000 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 320000 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 320000 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 320000 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMLast.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz744 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 146530 1000)))

noncomputable abbrev qz546 := qz744

noncomputable abbrev qz273 := qz546

noncomputable abbrev qz3 := (BSN.headSumC qz273 9)

noncomputable abbrev qz745 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz547 := qz745

noncomputable abbrev qz274 := qz547

noncomputable abbrev qz4 := qz274

noncomputable abbrev qz5 := qz273

noncomputable abbrev qz548 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz275 := qz548

noncomputable abbrev qz6 := qz275

noncomputable abbrev qz549 := (@Neg.neg Complex Complex.instNeg qz744)

noncomputable abbrev qz276 := qz549

noncomputable abbrev qz7 := qz276

noncomputable abbrev qz550 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz550) Bool.true 75625302037 274877906944 267701074169 85899345920000 Bool.true 29399003275 68719476736 1070699544801 343597383680000

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz550 Bool.false 10751288437 137438953472 479133724741 171798691840000 Bool.true 457201371007 1099511627776 1916958153339 687194767360000 Bool.true

noncomputable abbrev qz551 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz551) Bool.false 10751288437 137438953472 479133724741 171798691840000 Bool.true 457201371007 1099511627776 1916958153339 687194767360000

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz551 Bool.false 97453110899 274877906944 419035361917 171798691840000 Bool.true 86819181841 549755813888 838298309459 343597383680000 Bool.true

noncomputable abbrev qz552 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz552) Bool.false 97453110899 274877906944 419035361917 171798691840000 Bool.true 86819181841 549755813888 838298309459 343597383680000

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz552 Bool.false 145185274027 549755813888 708429872869 343597383680000 Bool.true 305678851381 549755813888 708410514119 343597383680000 Bool.false

noncomputable abbrev qz553 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz553) Bool.false 145185274027 549755813888 708429872869 343597383680000 Bool.true 305678851381 549755813888 708410514119 343597383680000

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz553 Bool.false 771158992855 1099511627776 226528458763 137438953472000 Bool.true 714443654535 1099511627776 226621395763 137438953472000 Bool.true

noncomputable abbrev qz554 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz554) Bool.false 771158992855 1099511627776 226528458763 137438953472000 Bool.true 714443654535 1099511627776 226621395763 137438953472000

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz554 Bool.false 517566913673 549755813888 407639823521 343597383680000 Bool.true 14513271015 68719476736 407742074771 343597383680000 Bool.true

noncomputable abbrev qz555 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz277 := qz555

noncomputable abbrev qz8 := qz277

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 517566913673 549755813888 407639823521 343597383680000 Bool.true 14513271015 68719476736 407742074771 343597383680000

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 747987515413 549755813888 224354103763 343597383680000 Bool.true 668788702725 1099511627776 448937760651 687194767360000 Bool.true

noncomputable abbrev qz556 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz278 := qz556

noncomputable abbrev qz9 := qz278

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 747987515413 549755813888 224354103763 343597383680000 Bool.true 668788702725 1099511627776 448937760651 687194767360000

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz557 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz557

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 146530 1000)

noncomputable abbrev qz558 := qz746

noncomputable abbrev qz279 := qz558

noncomputable abbrev qz280 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz269 qz279 (Real.log qz280))

noncomputable abbrev qz12 := qz279

noncomputable abbrev qz281 := (@Eq.refl Real qz558)

noncomputable abbrev qz13 := qz281

noncomputable abbrev qz282 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.false 198231701525 549755813888 224354103763 343597383680000 Bool.true 668788702725 1099511627776 448937760651 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz283 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz284 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image qz283 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz283 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz284 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 160000 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 874884406130210524817754712925423789523555284584765504755651482084709920013121

noncomputable def ep57 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep58 := nat_lit 598755083042738188635710355365239730286432742569724988171087259026505464641

noncomputable def ep59 := nat_lit 2623455708224546098075992718065540889110092988269157064290612271736076749110081

noncomputable def ep60 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz15 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.cosOddQ 2147483648)

noncomputable def ep61 := BSN.cos_dyadic_bound_f 2224109431 2147483648 3 2 1048576 320313 ep56 ep57 ep58 ep59 ep60 ep58 534710 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2224109431) qz15 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2224109431) qz16 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 146530 1000)

noncomputable abbrev qz285 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 160000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 160000 rfl rfl rfl (ep55 rfl)))

noncomputable abbrev qz286 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz559 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26625087) qz17)

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz11 qz559 Bool.false 26625087 262144 961 1048576 Bool.false 534710 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 332813589 3276800 14653 16000000 26625087 262144 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 146530 1000 0 1 363408 524288 1 160000 332813589 3276800 14653 16000000 qz18 qz285 rfl) rfl) (Enclosure.sfrac_false_div 26625087 262144) (BSN.cos_reduce0 qz559 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39126946904686758723584) qz286) 226375608064910080 72057594037927936 Bool.false 534710 1048576 16 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 26625087 262144 226375608064910080 72057594037927936 16 39126946904686758723584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 534710 1048576 39126946904686758723584 37778931862957161709568 2224109431 2147483648 320313 320000 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 1574312926967944754121049914981470629358170366058522128569635797945256651651905

noncomputable def ep64 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep65 := nat_lit 4122231110019690875154482436757069831612839591427206972463435805722962602621761

noncomputable def ep66 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz19 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz20 := (BSN.sinOddQ 2147483648)

noncomputable def ep67 := BSN.sin_dyadic_bound_f 2224109431 2147483648 3 2 1048576 320313 ep63 ep64 ep58 ep65 ep66 ep58 901995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2224109431) qz19 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2224109431) qz20 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz11 qz559 Bool.false 26625087 262144 961 1048576 Bool.false 901995 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 332813589 3276800 14653 16000000 26625087 262144 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz280) 146530 1000 0 1 363408 524288 1 160000 332813589 3276800 14653 16000000 qz18 qz285 rfl) rfl) (Enclosure.sfrac_false_div 26625087 262144) (BSN.sin_reduce0 qz559 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39126946904686758723584) qz286) 226375608064910080 72057594037927936 Bool.false 901995 1048576 16 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 26625087 262144 226375608064910080 72057594037927936 16 39126946904686758723584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 901995 1048576 39126946904686758723584 37778931862957161709568 2224109431 2147483648 320313 320000 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz287 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.false 198231701525 549755813888 224354103763 343597383680000 Bool.true 668788702725 1099511627776 448937760651 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz282 (Real.cos qz11) 741455 1048576 1 1048576 267355 524288 604721 655360000 198231701525 549755813888 224354103763 343597383680000 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.false 534710 1048576 154808576 167772160000 267355 524288 604721 655360000 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 901995 1048576 604721 655360000 668788702725 1099511627776 448937760651 687194767360000 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.false 901995 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.false 901995 1048576 154808576 167772160000 901995 1048576 604721 655360000 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz560 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz21 := qz560

noncomputable def ep70 := @ep51 198231701525 549755813888 224354103763 343597383680000 Bool.true 668788702725 1099511627776 448937760651 687194767360000 Bool.false 747987515413 747987515413 549755813888 224354103763 343597383680000 Bool.true 668788702725 668788702725 1099511627776 448937760651 687194767360000 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep53 ep69) rfl rfl

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz269 qz279 qz561)

noncomputable abbrev qz288 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.true 57605150435 137438953472 91642859879 171798691840000 Bool.false 436576366485 1099511627776 366546388891 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 3 qz13 rfl)

noncomputable abbrev qz289 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz290 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image qz289 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz289 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz290 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 160000 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 251390696682103333830244636414788499672287283925523145817296699617356880158976

noncomputable def ep75 := nat_lit 49484583831173271192642680372085207413323586476624897934802031643867095296

noncomputable def ep76 := nat_lit 754073120878647654948348623883621328602035204603616187656020494788782906286336

noncomputable def ep77 := BSN.cos_dyadic_bound_f 1628578662 2147483648 3 2 1048576 320313 ep74 ep57 ep75 ep76 ep60 ep75 761224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1628578662) qz15 0 2 ep74 ep57 ep75 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1628578662) qz16 0 2 ep76 ep60 ep75 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz562 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz291 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21099917) qz562)

noncomputable abbrev qz292 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 160000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 160000 rfl rfl rfl (ep73 rfl)))

noncomputable abbrev qz293 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz22 qz291 Bool.false 21099917 131072 961 1048576 Bool.true 761224 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 8439966817 52428800 14653 16000000 21099917 131072 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz561 146530 1000 0 1 575989 524288 1 160000 8439966817 52428800 14653 16000000 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 21099917 131072) (BSN.cos_reduce2 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14325129410991414575104) qz293) 226375608064910080 72057594037927936 Bool.false 761224 1048576 25 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 21099917 131072 226375608064910080 72057594037927936 25 14325129410991414575104 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 761224 1048576 14325129410991414575104 18889465931478580854784 1628578662 2147483648 320313 320000 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 7034527975008221629656864985094539536

noncomputable def ep80 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep81 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep82 := BSN.sin_dyadic_bound_f 1628578662 2147483648 2 1 1048576 320313 ep79 ep80 ep79 ep79 ep81 ep79 721143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1628578662) qz19 0 1 ep79 ep80 ep79 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1628578662) qz20 0 1 ep79 ep81 ep79 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz22 qz291 Bool.false 21099917 131072 961 1048576 Bool.true 721143 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 8439966817 52428800 14653 16000000 21099917 131072 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz561 146530 1000 0 1 575989 524288 1 160000 8439966817 52428800 14653 16000000 qz18 qz292 rfl) rfl) (Enclosure.sfrac_false_div 21099917 131072) (BSN.sin_reduce2 qz291 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14325129410991414575104) qz293) 226375608064910080 72057594037927936 Bool.false 721143 1048576 25 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 21099917 131072 226375608064910080 72057594037927936 25 14325129410991414575104 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 721143 1048576 14325129410991414575104 18889465931478580854784 1628578662 2147483648 320313 320000 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz294 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.true 57605150435 137438953472 91642859879 171798691840000 Bool.false 436576366485 1099511627776 366546388891 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz288 (Real.cos qz22) 605395 1048576 1 1048576 95153 131072 604721 655360000 57605150435 137438953472 91642859879 171798691840000 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.true 761224 1048576 154808576 167772160000 95153 131072 604721 655360000 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz288 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 721143 1048576 604721 655360000 436576366485 1099511627776 366546388891 687194767360000 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.true 721143 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.true 721143 1048576 154808576 167772160000 721143 1048576 604721 655360000 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep49 57605150435 137438953472 91642859879 171798691840000 Bool.false 436576366485 1099511627776 366546388891 687194767360000 Bool.false 71133854966950087622656 517566913673 549755813888 407639823521 343597383680000 Bool.true 255320163808910235402240 14513271015 68719476736 407742074771 343597383680000 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep84) rfl rfl

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz269 qz279 qz563)

noncomputable abbrev qz295 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz554 (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 263974834491 1099511627776 317362646773 687194767360000 Bool.true 482231318295 1099511627776 317622829273 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 4 qz13 rfl)

noncomputable abbrev qz296 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz297 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image qz296 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz296 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz297 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 160000 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 1338261770127830520098044265038918801

noncomputable def ep93 := BSN.sin_dyadic_bound_f 1075561549 2147483648 2 1 1048576 320313 ep92 ep80 ep92 ep92 ep81 ep92 503493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1075561549) qz19 0 1 ep92 ep80 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1075561549) qz20 0 1 ep92 ep81 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz24 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106500495) qz24)

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 160000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 160000 rfl rfl rfl (ep91 rfl)))

noncomputable def ep94 := @Enclosure.Real.IsNear.cos_image qz23 qz298 Bool.false 106500495 524288 961 1048576 Bool.true 503493 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 10650049501 52428800 14653 16000000 106500495 524288 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz563 146530 1000 0 1 726817 524288 1 160000 10650049501 52428800 14653 16000000 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 106500495 524288) (BSN.cos_reduce1 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37842957750258609684480) qz25) 226375608064910080 72057594037927936 Bool.false 503493 1048576 32 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 106500495 524288 226375608064910080 72057594037927936 32 37842957750258609684480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503493 1048576 37842957750258609684480 75557863725914323419136 1075561549 2147483648 320313 320000 (ep93 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep95 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep96 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep97 := BSN.cos_dyadic_bound_f 1075561549 2147483648 2 1 1048576 320313 ep92 ep95 ep92 ep92 ep96 ep92 919785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1075561549) qz15 0 1 ep92 ep95 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1075561549) qz16 0 1 ep92 ep96 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep98 := @Enclosure.Real.IsNear.sin_image qz23 qz298 Bool.false 106500495 524288 961 1048576 Bool.false 919785 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 10650049501 52428800 14653 16000000 106500495 524288 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz563 146530 1000 0 1 726817 524288 1 160000 10650049501 52428800 14653 16000000 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 106500495 524288) (BSN.sin_reduce1 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37842957750258609684480) qz25) 226375608064910080 72057594037927936 Bool.false 919785 1048576 32 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 106500495 524288 226375608064910080 72057594037927936 32 37842957750258609684480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 919785 1048576 37842957750258609684480 75557863725914323419136 1075561549 2147483648 320313 320000 (ep97 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep99 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 263974834491 1099511627776 317362646773 687194767360000 Bool.true 482231318295 1099511627776 317622829273 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz295 (Real.cos qz23) 524287 1048576 1 1048576 503493 1048576 604721 655360000 263974834491 1099511627776 317362646773 687194767360000 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 503493 1048576 154808576 167772160000 503493 1048576 604721 655360000 (ep94 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz295 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 524287 1048576 1 1048576 919785 1048576 604721 655360000 482231318295 1099511627776 317622829273 687194767360000 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 919785 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 919785 1048576 154808576 167772160000 919785 1048576 604721 655360000 (ep98 rfl rfl) rfl)) rfl)

noncomputable def ep100 := @ep47 263974834491 1099511627776 317362646773 687194767360000 Bool.true 482231318295 1099511627776 317622829273 687194767360000 Bool.false 423949139754050901770240 771158992855 1099511627776 226528458763 137438953472000 Bool.true 49096194097000753397760 714443654535 1099511627776 226621395763 137438953472000 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep99) rfl rfl

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz26 := (@HMul.hMul Real Real Real qz269 qz279 qz564)

noncomputable abbrev qz301 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep101 := @Enclosure.Complex.IsNear.of_eq qz553 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26)))) Bool.true 480788444801 1099511627776 284217451923 687194767360000 Bool.false 103085951773 1099511627776 283714049423 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 5 qz13 rfl)

noncomputable abbrev qz302 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep102 := @Enclosure.Real.IsNear.inv_image qz302 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz302 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz303 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep103 := nat_lit 11734546589655452485523914939250625

noncomputable def ep104 := nat_lit 2429970938528035899633153341031900

noncomputable def ep105 := nat_lit 824199001261152424427520000

noncomputable def ep106 := BSN.log_dyadic_bound 2 3 17 16 ep103 524288 160000 ep104 ep105 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base16 (BSN.artanhP 2) (BSN.artanhQ 3) 0 16 ep104 ep103 ep105 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep107 := nat_lit 42325297735158145843505318085001216

noncomputable def ep108 := BSN.cos_dyadic_bound_f 453575936 2147483648 2 1 1048576 320313 ep107 ep95 ep107 ep107 ep96 ep107 1025273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 453575936) qz15 0 1 ep107 ep95 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 453575936) qz16 0 1 ep107 ep96 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz304 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 160000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 160000 rfl rfl rfl (ep106 rfl)))

noncomputable abbrev qz565 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61821593) qz17)

noncomputable def ep109 := @Enclosure.Real.IsNear.cos_image qz26 qz565 Bool.false 61821593 262144 961 1048576 Bool.true 1025273 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 386384957 1638400 14653 16000000 61821593 262144 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz564 146530 1000 0 1 843808 524288 1 160000 386384957 1638400 14653 16000000 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 61821593 262144) (BSN.cos_reduce2 qz565 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7979392258846643716096) qz286) 226375608064910080 72057594037927936 Bool.false 1025273 1048576 37 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 61821593 262144 226375608064910080 72057594037927936 37 7979392258846643716096 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1025273 1048576 7979392258846643716096 37778931862957161709568 453575936 2147483648 320313 320000 (ep108 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep110 := BSN.sin_dyadic_bound_f 453575936 2147483648 2 1 1048576 320313 ep107 ep80 ep107 ep107 ep81 ep107 219829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 453575936) qz19 0 1 ep107 ep80 ep107 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 453575936) qz20 0 1 ep107 ep81 ep107 rfl rfl rfl rfl) rfl rfl

noncomputable def ep111 := @Enclosure.Real.IsNear.sin_image qz26 qz565 Bool.false 61821593 262144 961 1048576 Bool.true 219829 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz26 Bool.false 386384957 1638400 14653 16000000 61821593 262144 961 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz564 146530 1000 0 1 843808 524288 1 160000 386384957 1638400 14653 16000000 qz18 qz304 rfl) rfl) (Enclosure.sfrac_false_div 61821593 262144) (BSN.sin_reduce2 qz565 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7979392258846643716096) qz286) 226375608064910080 72057594037927936 Bool.false 219829 1048576 37 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 61821593 262144 226375608064910080 72057594037927936 37 7979392258846643716096 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 219829 1048576 7979392258846643716096 37778931862957161709568 453575936 2147483648 320313 320000 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep102 rfl rfl) rfl)

noncomputable def ep112 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz26)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26))) Bool.true 480788444801 1099511627776 284217451923 687194767360000 Bool.false 103085951773 1099511627776 283714049423 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz301 (Real.cos qz26) 468937 1048576 1 1048576 1025273 1048576 604721 655360000 480788444801 1099511627776 284217451923 687194767360000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz26) Bool.true 1025273 1048576 154808576 167772160000 1025273 1048576 604721 655360000 (ep109 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz301 (@Neg.neg Real Real.instNeg (Real.sin qz26)) 468937 1048576 1 1048576 219829 1048576 604721 655360000 103085951773 1099511627776 283714049423 687194767360000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz26) Bool.true 219829 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz26) Bool.true 219829 1048576 154808576 167772160000 219829 1048576 604721 655360000 (ep111 rfl rfl) rfl)) rfl)

noncomputable def ep113 := @ep45 480788444801 1099511627776 284217451923 687194767360000 Bool.false 103085951773 1099511627776 283714049423 687194767360000 Bool.false 319265793949062769147904 145185274027 549755813888 708429872869 343597383680000 Bool.true 672194902917242591117312 305678851381 549755813888 708410514119 343597383680000 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep100 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep101 ep112) rfl rfl

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz269 qz279 qz566)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep114 := @Enclosure.Complex.IsNear.of_eq qz552 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 49720947771 549755813888 25928170193 68719476736000 Bool.false 54714917385 137438953472 6494389767 17179869184000 (BSN.cpow_neg_s_mk qz12 146530 1000 6 qz13 rfl)

noncomputable abbrev qz307 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz567 := (@HDiv.hDiv Real Real Real qz1 qz308 qz14)

noncomputable def ep115 := @Enclosure.Real.IsNear.inv_image qz307 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz307 (Real.sqrt qz567) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz567) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep116 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 160000 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep117 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz566 146530 1000 0 1 4034681531866359 2251799813685248 3125000001 500000000000000 59120188486437758427 225179981368524800 45790625014653 50000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 3125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz567) Bool.false 33845361775666394038272 18889465931478580854784 1000000000320000 160000000000000000000 4034681531866359 2251799813685248 3125000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep118 := nat_lit 52963795057280872388077900543672576

noncomputable def ep119 := BSN.sin_dyadic_bound_f 479727676 2147483648 2 1 1048576 320313 ep118 ep80 ep118 ep118 ep81 ep118 232298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 479727676) qz19 0 1 ep118 ep80 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 479727676) qz20 0 1 ep118 ep81 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137649915) qz24)

noncomputable def ep120 := @Enclosure.Real.IsNear.cos_image qz27 qz309 Bool.false 137649915 524288 481 524288 Bool.false 232298 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 59120188486437758427 225179981368524800 45790625014653 50000000000000000 137649915 524288 481 524288 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 137649915 524288) (BSN.cos_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16878917060933137203200) qz25) 226375608064910080 72057594037927936 Bool.false 232298 1048576 41 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 137649915 524288 226375608064910080 72057594037927936 41 16878917060933137203200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 232298 1048576 16878917060933137203200 75557863725914323419136 479727676 2147483648 320313 320000 (ep119 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep121 := BSN.cos_dyadic_bound_f 479727676 2147483648 2 1 1048576 320313 ep118 ep95 ep118 ep118 ep96 ep118 1022520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 479727676) qz15 0 1 ep118 ep95 ep118 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 479727676) qz16 0 1 ep118 ep96 ep118 rfl rfl rfl rfl) rfl rfl

noncomputable def ep122 := @Enclosure.Real.IsNear.sin_image qz27 qz309 Bool.false 137649915 524288 481 524288 Bool.true 1022520 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 59120188486437758427 225179981368524800 45790625014653 50000000000000000 137649915 524288 481 524288 (ep117 rfl) rfl) (Enclosure.sfrac_false_div 137649915 524288) (BSN.sin_reduce3 qz309 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16878917060933137203200) qz25) 226375608064910080 72057594037927936 Bool.false 1022520 1048576 41 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 137649915 524288 226375608064910080 72057594037927936 41 16878917060933137203200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022520 1048576 16878917060933137203200 75557863725914323419136 479727676 2147483648 320313 320000 (ep121 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz310 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep115 rfl rfl) rfl)

noncomputable def ep123 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 49720947771 549755813888 25928170193 68719476736000 Bool.false 54714917385 137438953472 6494389767 17179869184000 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz27) 428079 1048576 1 1048576 116149 524288 302673 327680000 49720947771 549755813888 25928170193 68719476736000 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 232298 1048576 77484288 83886080000 116149 524288 302673 327680000 (ep120 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 428079 1048576 1 1048576 127815 131072 302673 327680000 54714917385 137438953472 6494389767 17179869184000 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 127815 131072 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 1022520 1048576 77484288 83886080000 127815 131072 302673 327680000 (ep122 rfl rfl) rfl)) rfl)

noncomputable def ep124 := @ep43 49720947771 549755813888 25928170193 68719476736000 Bool.false 54714917385 137438953472 6494389767 17179869184000 Bool.false 107150828596394536730624 97453110899 274877906944 419035361917 171798691840000 Bool.true 11932337493522306301952 86819181841 549755813888 838298309459 343597383680000 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep113 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep114 ep123) rfl rfl

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz269 qz279 qz568)

noncomputable abbrev qz311 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep125 := @Enclosure.Complex.IsNear.of_eq qz551 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 75950534025 274877906944 7512295353 21474836480000 Bool.true 283563007325 1099511627776 240361534421 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 7 qz13 rfl)

noncomputable abbrev qz312 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz313 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz569 := (@HDiv.hDiv Real Real Real qz1 qz313 qz14)

noncomputable def ep126 := @Enclosure.Real.IsNear.inv_image qz312 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz312 (Real.sqrt qz569) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz569) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep127 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 160000 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz568 146530 1000 0 1 4381796493761783 2251799813685248 3125000001 500000000000000 64206464023091406299 225179981368524800 45790625014653 50000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 3125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz569) Bool.false 36757173121942042968064 18889465931478580854784 1000000000320000 160000000000000000000 4381796493761783 2251799813685248 3125000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep127 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep129 := nat_lit 9608192222157311060012475452033725456

noncomputable def ep130 := BSN.sin_dyadic_bound_f 1760598878 2147483648 2 1 1048576 320313 ep129 ep80 ep129 ep129 ep81 ep129 766548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1760598878) qz19 0 1 ep129 ep80 ep129 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1760598878) qz20 0 1 ep129 ep81 ep129 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149492323) qz24)

noncomputable def ep131 := @Enclosure.Real.IsNear.cos_image qz28 qz314 Bool.false 149492323 524288 481 524288 Bool.true 766548 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 64206464023091406299 225179981368524800 45790625014653 50000000000000000 149492323 524288 481 524288 (ep128 rfl) rfl) (Enclosure.sfrac_false_div 149492323 524288) (BSN.cos_reduce1 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61945566036055258300416) qz25) 226375608064910080 72057594037927936 Bool.false 766548 1048576 45 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 149492323 524288 226375608064910080 72057594037927936 45 61945566036055258300416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 766548 1048576 61945566036055258300416 75557863725914323419136 1760598878 2147483648 320313 320000 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep132 := nat_lit 343389648432417251657588490489312104873029824524046285116122883892244474921216

noncomputable def ep133 := nat_lit 92317357777924247090517630491994998669212171115368132504616149630382407936

noncomputable def ep134 := nat_lit 1029984310581695906478584436206952324621751049229908119083359419377472659947776

noncomputable def ep135 := BSN.cos_dyadic_bound_f 1760598878 2147483648 3 2 1048576 320313 ep132 ep57 ep133 ep134 ep60 ep133 715481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1760598878) qz15 0 2 ep132 ep57 ep133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1760598878) qz16 0 2 ep134 ep60 ep133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep136 := @Enclosure.Real.IsNear.sin_image qz28 qz314 Bool.false 149492323 524288 481 524288 Bool.false 715481 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 64206464023091406299 225179981368524800 45790625014653 50000000000000000 149492323 524288 481 524288 (ep128 rfl) rfl) (Enclosure.sfrac_false_div 149492323 524288) (BSN.sin_reduce1 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61945566036055258300416) qz25) 226375608064910080 72057594037927936 Bool.false 715481 1048576 45 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 149492323 524288 226375608064910080 72057594037927936 45 61945566036055258300416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 715481 1048576 61945566036055258300416 75557863725914323419136 1760598878 2147483648 320313 320000 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep126 rfl rfl) rfl)

noncomputable def ep137 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 75950534025 274877906944 7512295353 21474836480000 Bool.true 283563007325 1099511627776 240361534421 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz311 (Real.cos qz28) 396325 1048576 1 1048576 191637 262144 302673 327680000 75950534025 274877906944 7512295353 21474836480000 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 766548 1048576 77484288 83886080000 191637 262144 302673 327680000 (ep131 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz311 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 396325 1048576 1 1048576 715481 1048576 302673 327680000 283563007325 1099511627776 240361534421 687194767360000 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 715481 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 715481 1048576 77484288 83886080000 715481 1048576 302673 327680000 (ep136 rfl rfl) rfl)) rfl)

noncomputable def ep138 := @ep41 75950534025 274877906944 7512295353 21474836480000 Bool.true 283563007325 1099511627776 240361534421 687194767360000 Bool.false 5910583325027578413056 10751288437 137438953472 479133724741 171798691840000 Bool.true 251349111828662731145216 457201371007 1099511627776 1916958153339 687194767360000 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep124 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep125 ep137) rfl rfl

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz269 qz279 qz570)

noncomputable abbrev qz316 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep139 := @Enclosure.Complex.IsNear.of_eq qz550 (Complex.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.true 97127878911 274877906944 56268423597 171798691840000 Bool.true 13182681393 1099511627776 224440936263 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 8 qz13 rfl)

noncomputable abbrev qz317 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz318 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz571 := (@HDiv.hDiv Real Real Real qz1 qz318 qz14)

noncomputable def ep140 := @Enclosure.Real.IsNear.inv_image qz317 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz317 (Real.sqrt qz571) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz571) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep141 := BSN.log_dyadic_bound 0 16 1 0 1 524288 160000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep142 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 146530 1000 0 1 9364972152248037 4503599627370496 6250000003 1000000000000000 137224936946890486161 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 39279540158062550581248 18889465931478580854784 1000000000480000 160000000000000000000 9364972152248037 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep143 := nat_lit 7645005387254326157806700920807886339516202144375636528997342946064000000000000

noncomputable def ep144 := nat_lit 14078361172062283849145778284489075747870968478862441878906250000000000000000

noncomputable def ep145 := nat_lit 19999839619958943858499885437274339052283976429160889812903383311120000000000000

noncomputable def ep146 := BSN.sin_dyadic_bound_f 3300418500 2147483648 3 2 1048576 320313 ep143 ep64 ep144 ep145 ep66 ep144 1047972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3300418500) qz19 0 2 ep143 ep64 ep144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3300418500) qz20 0 2 ep145 ep66 ep144 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz30 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz31 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 319501703) qz30)

noncomputable def ep147 := @Enclosure.Real.IsNear.cos_image qz29 qz319 Bool.false 319501703 1048576 481 524288 Bool.true 1047972 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 137224936946890486161 450359962737049600 91581250043959 100000000000000000 319501703 1048576 481 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 319501703 1048576) (BSN.cos_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232246305162911941656576) qz31) 226375608064910080 72057594037927936 Bool.false 1047972 1048576 48 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 319501703 1048576 226375608064910080 72057594037927936 48 232246305162911941656576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047972 1048576 232246305162911941656576 151115727451828646838272 3300418500 2147483648 320313 320000 (ep146 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep148 := nat_lit 4253482264551097769381120857464154222285832732865959156944704414480000000000000

noncomputable def ep149 := nat_lit 12732290071309168740445071015823484515361756261640152587076300743440000000000000

noncomputable def ep150 := BSN.cos_dyadic_bound_f 3300418500 2147483648 3 2 1048576 320313 ep148 ep57 ep144 ep149 ep60 ep144 35559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3300418500) qz15 0 2 ep148 ep57 ep144 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3300418500) qz16 0 2 ep149 ep60 ep144 rfl rfl rfl rfl) rfl rfl

noncomputable def ep151 := @Enclosure.Real.IsNear.sin_image qz29 qz319 Bool.false 319501703 1048576 481 524288 Bool.false 35559 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 137224936946890486161 450359962737049600 91581250043959 100000000000000000 319501703 1048576 481 524288 (ep142 rfl) rfl) (Enclosure.sfrac_false_div 319501703 1048576) (BSN.sin_reduce1 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232246305162911941656576) qz31) 226375608064910080 72057594037927936 Bool.false 35559 1048576 48 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 319501703 1048576 226375608064910080 72057594037927936 48 232246305162911941656576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 35559 1048576 232246305162911941656576 151115727451828646838272 3300418500 2147483648 320313 320000 (ep150 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep140 rfl rfl) rfl)

noncomputable def ep152 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.true 97127878911 274877906944 56268423597 171798691840000 Bool.true 13182681393 1099511627776 224440936263 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz316 (Real.cos qz29) 370727 1048576 1 1048576 261993 262144 302673 327680000 97127878911 274877906944 56268423597 171798691840000 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.true 1047972 1048576 77484288 83886080000 261993 262144 302673 327680000 (ep147 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz316 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 370727 1048576 1 1048576 35559 1048576 302673 327680000 13182681393 1099511627776 224440936263 687194767360000 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.false 35559 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.false 35559 1048576 77484288 83886080000 35559 1048576 302673 327680000 (ep151 rfl rfl) rfl)) rfl)

noncomputable def ep153 := @ep39 97127878911 274877906944 56268423597 171798691840000 Bool.true 13182681393 1099511627776 224440936263 687194767360000 Bool.true 10393862367969189822464 75625302037 274877906944 267701074169 85899345920000 Bool.true 517192735134195279462400 29399003275 68719476736 1070699544801 343597383680000 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep138 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep139 ep152) rfl rfl

theorem EMLast.d6 : Enclosure.Complex.IsNear qz3 Bool.true 75625302037 274877906944 267701074169 85899345920000 Bool.true 29399003275 68719476736 1070699544801 343597383680000 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep153 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz32 := (BSN.headSumC qz273 17)

noncomputable abbrev qz572 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep154 := @Enclosure.Complex.IsNear.of_eq qz32 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz572) Bool.false 55841465275 1099511627776 3598906277373 687194767360000 Bool.false 106378857499 1099511627776 3599294559873 687194767360000

noncomputable def ep155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz572 Bool.false 203901404533 1099511627776 3439865451799 687194767360000 Bool.true 3912945607 34359738368 860013643731 171798691840000 Bool.true

noncomputable abbrev qz573 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz573) Bool.false 203901404533 1099511627776 3439865451799 687194767360000 Bool.true 3912945607 34359738368 860013643731 171798691840000

noncomputable def ep157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz573 Bool.false 21667467425 549755813888 1637885707221 343597383680000 Bool.false 54453968681 549755813888 818947683923 171798691840000 Bool.false

noncomputable abbrev qz574 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz574) Bool.false 21667467425 549755813888 1637885707221 343597383680000 Bool.false 54453968681 549755813888 818947683923 171798691840000

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz574 Bool.false 162671172389 549755813888 1552748947509 343597383680000 Bool.false 13152876313 549755813888 776490482817 171798691840000 Bool.true

noncomputable abbrev qz575 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz575) Bool.false 162671172389 549755813888 1552748947509 343597383680000 Bool.false 13152876313 549755813888 776490482817 171798691840000

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz575 Bool.false 50148163909 274877906944 366170302333 85899345920000 Bool.true 31495011485 137438953472 1464748268707 343597383680000 Bool.false

noncomputable abbrev qz576 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz576) Bool.false 50148163909 274877906944 366170302333 85899345920000 Bool.true 31495011485 137438953472 1464748268707 343597383680000

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz576 Bool.true 12691455205 137438953472 343187697207 85899345920000 Bool.true 87310818829 274877906944 1373029323203 343597383680000 Bool.false

noncomputable abbrev qz577 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz577) Bool.true 12691455205 137438953472 343187697207 85899345920000 Bool.true 87310818829 274877906944 1373029323203 343597383680000

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz577 Bool.true 98316852583 274877906944 1276868736619 343597383680000 Bool.true 31668644607 68719476736 638639999247 171798691840000 Bool.false

noncomputable abbrev qz578 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz578) Bool.true 98316852583 274877906944 1276868736619 343597383680000 Bool.true 31668644607 68719476736 638639999247 171798691840000

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz578 Bool.true 282721937923 1099511627776 2353009673723 687194767360000 Bool.true 836353155075 1099511627776 2353419206223 687194767360000 Bool.true

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz579) Bool.true 282721937923 1099511627776 2353009673723 687194767360000 Bool.true 836353155075 1099511627776 2353419206223 687194767360000

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP qz3 qz579 Bool.true 75625302037 274877906944 267701074169 85899345920000 Bool.true 29399003275 68719476736 1070699544801 343597383680000 Bool.false

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz33 := (@HMul.hMul Real Real Real qz269 qz279 qz580)

noncomputable abbrev qz321 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz33)))) Bool.false 19779270225 1099511627776 211401080371 687194767360000 Bool.true 365969102675 1099511627776 212020116621 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 9 qz13 rfl)

noncomputable abbrev qz322 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz323 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz581 := (@HDiv.hDiv Real Real Real qz1 qz323 qz14)

noncomputable def ep171 := @Enclosure.Real.IsNear.inv_image qz322 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz322 (Real.sqrt qz581) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz581) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep172 := BSN.log_dyadic_bound 1 17 2 1 867 524288 160000 1 1 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 17) 0 1 1 867 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep173 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz580 146530 1000 0 1 9895417793173221 4503599627370496 6250000003 1000000000000000 144997556923367207313 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 41504390431577613533184 18889465931478580854784 1000000000480000 160000000000000000000 9895417793173221 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep172 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep174 := nat_lit 4034870497621045675084574991866787538845173485479811056098711836532238367415841

noncomputable def ep175 := nat_lit 12672705963404463164344896689018815567072834339965135426161126681231376342561

noncomputable def ep176 := nat_lit 12079266080936328098925035182222324985401374787759502897443813256234252349562401

noncomputable def ep177 := BSN.cos_dyadic_bound_f 3257306829 2147483648 3 2 1048576 320313 ep174 ep57 ep175 ep176 ep60 ep175 56589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3257306829) qz15 0 2 ep174 ep57 ep175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3257306829) qz16 0 2 ep176 ep60 ep175 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 337598745) qz30)

noncomputable def ep178 := @Enclosure.Real.IsNear.cos_image qz33 qz324 Bool.false 337598745 1048576 961 1048576 Bool.false 56589 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 144997556923367207313 450359962737049600 91581250043959 100000000000000000 337598745 1048576 961 1048576 (ep173 rfl) rfl) (Enclosure.sfrac_false_div 337598745 1048576) (BSN.cos_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 229212590984592170680320) qz31) 226375608064910080 72057594037927936 Bool.false 56589 1048576 51 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 337598745 1048576 226375608064910080 72057594037927936 51 229212590984592170680320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56589 1048576 229212590984592170680320 151115727451828646838272 3257306829 2147483648 320313 320000 (ep177 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep179 := nat_lit 7252628730947158644620759068009002517467654006391687792636752404413043960274465

noncomputable def ep180 := nat_lit 18974462295206570176502572488241357082449547332570667332882471615978835762830881

noncomputable def ep181 := BSN.sin_dyadic_bound_f 3257306829 2147483648 3 2 1048576 320313 ep179 ep64 ep175 ep180 ep66 ep175 1047047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3257306829) qz19 0 2 ep179 ep64 ep175 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3257306829) qz20 0 2 ep180 ep66 ep175 rfl rfl rfl rfl) rfl rfl

noncomputable def ep182 := @Enclosure.Real.IsNear.sin_image qz33 qz324 Bool.false 337598745 1048576 961 1048576 Bool.false 1047047 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 144997556923367207313 450359962737049600 91581250043959 100000000000000000 337598745 1048576 961 1048576 (ep173 rfl) rfl) (Enclosure.sfrac_false_div 337598745 1048576) (BSN.sin_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 229212590984592170680320) qz31) 226375608064910080 72057594037927936 Bool.false 1047047 1048576 51 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 337598745 1048576 226375608064910080 72057594037927936 51 229212590984592170680320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047047 1048576 229212590984592170680320 151115727451828646838272 3257306829 2147483648 320313 320000 (ep181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep171 rfl rfl) rfl)

noncomputable def ep183 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz33)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz33))) Bool.false 19779270225 1099511627776 211401080371 687194767360000 Bool.true 365969102675 1099511627776 212020116621 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz321 (Real.cos qz33) 349525 1048576 1 1048576 56589 1048576 604721 655360000 19779270225 1099511627776 211401080371 687194767360000 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz33) Bool.false 56589 1048576 154808576 167772160000 56589 1048576 604721 655360000 (ep178 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz33)) 349525 1048576 1 1048576 1047047 1048576 604721 655360000 365969102675 1099511627776 212020116621 687194767360000 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz33) Bool.false 1047047 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz33) Bool.false 1047047 1048576 154808576 167772160000 1047047 1048576 604721 655360000 (ep182 rfl rfl) rfl)) rfl)

noncomputable def ep184 := @ep169 19779270225 1099511627776 211401080371 687194767360000 Bool.true 365969102675 1099511627776 212020116621 687194767360000 Bool.true 77714014543425738637312 282721937923 1099511627776 2353009673723 687194767360000 Bool.true 57473751183256662835200 836353155075 1099511627776 2353419206223 687194767360000 EMLast.d6 (ep170 ep183) rfl rfl

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz582))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz269 qz279 qz583)

noncomputable def ep185 := @Enclosure.Complex.IsNear.of_eq qz578 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.true 110545472409 1099511627776 40145559903 137438953472000 Bool.false 329654841363 1099511627776 40228158153 137438953472000 (BSN.cpow_neg_s_mk qz12 146530 1000 10 qz13 rfl)

noncomputable abbrev qz584 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep186 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz582) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz582) (Real.sqrt qz584) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz584) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep187 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 160000 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep188 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 146530 1000 0 1 10369917190100709 4503599627370496 6250000003 1000000000000000 151950396586545688977 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 43494585150108164161536 18889465931478580854784 1000000000480000 160000000000000000000 10369917190100709 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep187 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep189 := nat_lit 1841527776837463670829766335374578779781392527154186953752205709125313139572736

noncomputable def ep190 := nat_lit 2648797808001230405179222167615774285587533072497277096227342018953038790656

noncomputable def ep191 := nat_lit 5519285734896388551678940561788504790773002515317566307064162443338033341136896

noncomputable def ep192 := BSN.cos_dyadic_bound_f 2678434936 2147483648 3 2 1048576 320313 ep189 ep57 ep190 ep191 ep60 ep190 333381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2678434936) qz15 0 2 ep189 ep57 ep190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2678434936) qz16 0 2 ep191 ep60 ep190 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176893543) qz24)

noncomputable def ep193 := @Enclosure.Real.IsNear.cos_image qz35 qz326 Bool.false 176893543 524288 961 1048576 Bool.true 333381 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 151950396586545688977 450359962737049600 91581250043959 100000000000000000 176893543 524288 961 1048576 (ep188 rfl) rfl) (Enclosure.sfrac_false_div 176893543 524288) (BSN.cos_reduce2 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94239051406484686503936) qz25) 226375608064910080 72057594037927936 Bool.false 333381 1048576 53 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 176893543 524288 226375608064910080 72057594037927936 53 94239051406484686503936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 333381 1048576 94239051406484686503936 75557863725914323419136 2678434936 2147483648 320313 320000 (ep192 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep194 := nat_lit 3312630960061033623169436025940149184178036522419538695076988402810401220198400

noncomputable def ep195 := nat_lit 8671649698946895592406804184429012800194382505171891467045839644091793513906176

noncomputable def ep196 := BSN.sin_dyadic_bound_f 2678434936 2147483648 3 2 1048576 320313 ep194 ep64 ep190 ep195 ep66 ep190 994167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2678434936) qz19 0 2 ep194 ep64 ep190 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2678434936) qz20 0 2 ep195 ep66 ep190 rfl rfl rfl rfl) rfl rfl

noncomputable def ep197 := @Enclosure.Real.IsNear.sin_image qz35 qz326 Bool.false 176893543 524288 961 1048576 Bool.true 994167 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 151950396586545688977 450359962737049600 91581250043959 100000000000000000 176893543 524288 961 1048576 (ep188 rfl) rfl) (Enclosure.sfrac_false_div 176893543 524288) (BSN.sin_reduce2 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94239051406484686503936) qz25) 226375608064910080 72057594037927936 Bool.false 994167 1048576 53 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 176893543 524288 226375608064910080 72057594037927936 53 94239051406484686503936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994167 1048576 94239051406484686503936 75557863725914323419136 2678434936 2147483648 320313 320000 (ep196 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep186 rfl rfl) rfl)

noncomputable def ep198 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.true 110545472409 1099511627776 40145559903 137438953472000 Bool.false 329654841363 1099511627776 40228158153 137438953472000 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz35) 331589 1048576 1 1048576 333381 1048576 604721 655360000 110545472409 1099511627776 40145559903 137438953472000 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.true 333381 1048576 154808576 167772160000 333381 1048576 604721 655360000 (ep193 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 331589 1048576 1 1048576 994167 1048576 604721 655360000 329654841363 1099511627776 40228158153 137438953472000 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.true 994167 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.true 994167 1048576 154808576 167772160000 994167 1048576 604721 655360000 (ep197 rfl rfl) rfl)) rfl)

noncomputable def ep199 := @ep167 110545472409 1099511627776 40145559903 137438953472000 Bool.false 329654841363 1099511627776 40228158153 137438953472000 Bool.true 432402090485389440581632 98316852583 274877906944 1276868736619 343597383680000 Bool.true 557120687700835420864512 31668644607 68719476736 638639999247 171798691840000 (ep168 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep184 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep185 ep198) rfl rfl

noncomputable abbrev qz585 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz585))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz269 qz279 qz586)

noncomputable def ep200 := @Enclosure.Complex.IsNear.of_eq qz577 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.false 72933942173 274877906944 95882052209 343597383680000 Bool.false 39363759599 274877906944 95749324709 343597383680000 (BSN.cpow_neg_s_mk qz12 146530 1000 11 qz13 rfl)

noncomputable abbrev qz587 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep201 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz585) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz585) (Real.sqrt qz587) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz587) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep202 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 160000 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep203 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 146530 1000 0 1 10799156221662949 4503599627370496 6250000003 1000000000000000 158240036116027191697 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 45294944137145793642496 18889465931478580854784 1000000000480000 160000000000000000000 10799156221662949 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep202 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep204 := nat_lit 1833458015842859904886938430043365984321679462941686629019750187549799412203520

noncomputable def ep205 := nat_lit 811997471670227185434100036760217897129854309670342693067166434707070058496

noncomputable def ep206 := nat_lit 4800599188443833668784612107196918177580474067393522521167713174117091775676416

noncomputable def ep207 := BSN.sin_dyadic_bound_f 2310438084 2147483648 3 2 1048576 320313 ep204 ep64 ep205 ep206 ep66 ep205 922756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2310438084) qz19 0 2 ep204 ep64 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2310438084) qz20 0 2 ep206 ep66 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184215647) qz24)

noncomputable def ep208 := @Enclosure.Real.IsNear.cos_image qz37 qz328 Bool.false 184215647 524288 961 1048576 Bool.false 922756 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 158240036116027191697 450359962737049600 91581250043959 100000000000000000 184215647 524288 961 1048576 (ep203 rfl) rfl) (Enclosure.sfrac_false_div 184215647 524288) (BSN.cos_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81291313267241086091264) qz25) 226375608064910080 72057594037927936 Bool.false 922756 1048576 55 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 184215647 524288 226375608064910080 72057594037927936 55 81291313267241086091264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 922756 1048576 81291313267241086091264 75557863725914323419136 2310438084 2147483648 320313 320000 (ep207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep209 := nat_lit 1018948674344553381464047616707096754799657414660790501763446622609758371250176

noncomputable def ep210 := nat_lit 3055222028090319690021274650047769828604712535363030819904205534959860973633536

noncomputable def ep211 := BSN.cos_dyadic_bound_f 2310438084 2147483648 3 2 1048576 320313 ep209 ep57 ep205 ep210 ep60 ep205 498028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2310438084) qz15 0 2 ep209 ep57 ep205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2310438084) qz16 0 2 ep210 ep60 ep205 rfl rfl rfl rfl) rfl rfl

noncomputable def ep212 := @Enclosure.Real.IsNear.sin_image qz37 qz328 Bool.false 184215647 524288 961 1048576 Bool.true 498028 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 158240036116027191697 450359962737049600 91581250043959 100000000000000000 184215647 524288 961 1048576 (ep203 rfl) rfl) (Enclosure.sfrac_false_div 184215647 524288) (BSN.sin_reduce3 qz328 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81291313267241086091264) qz25) 226375608064910080 72057594037927936 Bool.false 498028 1048576 55 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 184215647 524288 226375608064910080 72057594037927936 55 81291313267241086091264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498028 1048576 81291313267241086091264 75557863725914323419136 2310438084 2147483648 320313 320000 (ep211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz329 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep201 rfl rfl) rfl)

noncomputable def ep213 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.false 72933942173 274877906944 95882052209 343597383680000 Bool.false 39363759599 274877906944 95749324709 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz37) 316157 1048576 1 1048576 230689 262144 604721 655360000 72933942173 274877906944 95882052209 343597383680000 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.false 922756 1048576 154808576 167772160000 230689 262144 604721 655360000 (ep208 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 316157 1048576 1 1048576 124507 262144 604721 655360000 39363759599 274877906944 95749324709 343597383680000 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 124507 262144 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 498028 1048576 154808576 167772160000 124507 262144 604721 655360000 (ep212 rfl rfl) rfl)) rfl)

noncomputable def ep214 := @ep165 72933942173 274877906944 95882052209 343597383680000 Bool.false 39363759599 274877906944 95749324709 343597383680000 Bool.true 6977201285647868887040 12691455205 137438953472 343187697207 85899345920000 Bool.true 5999953783320576262144 87310818829 274877906944 1373029323203 343597383680000 (ep166 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep199 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep200 ep213) rfl rfl

noncomputable abbrev qz588 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz38 := (@Inv.inv Real Real.instInv (Real.sqrt qz588))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz39 := (@HMul.hMul Real Real Real qz269 qz279 qz589)

noncomputable def ep215 := @Enclosure.Complex.IsNear.of_eq qz576 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)))) Bool.false 75531074319 274877906944 11491302563 42949672960000 Bool.false 24320795859 274877906944 2866217047 10737418240000 (BSN.cpow_neg_s_mk qz12 146530 1000 12 qz13 rfl)

noncomputable abbrev qz590 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep216 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz588) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz588) (Real.sqrt qz590) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz590) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep217 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 160000 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep218 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 146530 1000 0 1 11191020447815397 4503599627370496 6250000003 1000000000000000 163982022621839012241 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 46938541828353910898688 18889465931478580854784 1000000000480000 160000000000000000000 11191020447815397 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep217 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep219 := nat_lit 3442498859726380149650973735597749530354458724665829692536032948387845373123105

noncomputable def ep220 := nat_lit 2860375834876052637060280121160780026738901211287787415380781905389405035041

noncomputable def ep221 := nat_lit 9011437357455482021006833615893178935646957486449373729398041217930869321456161

noncomputable def ep222 := BSN.sin_dyadic_bound_f 2704287667 2147483648 3 2 1048576 320313 ep219 ep64 ep220 ep221 ep66 ep220 998108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2704287667) qz19 0 2 ep219 ep64 ep220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2704287667) qz20 0 2 ep221 ep66 ep220 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190900199) qz24)

noncomputable def ep223 := @Enclosure.Real.IsNear.cos_image qz39 qz330 Bool.false 190900199 524288 481 524288 Bool.false 998108 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 163982022621839012241 450359962737049600 91581250043959 100000000000000000 190900199 524288 481 524288 (ep218 rfl) rfl) (Enclosure.sfrac_false_div 190900199 524288) (BSN.cos_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95148663540994998796288) qz25) 226375608064910080 72057594037927936 Bool.false 998108 1048576 57 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 190900199 524288 226375608064910080 72057594037927936 57 95148663540994998796288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 998108 1048576 95148663540994998796288 75557863725914323419136 2704287667 2147483648 320313 320000 (ep222 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep224 := nat_lit 1913770644663489439867012199830376752431027692019366623593520874395642720639521

noncomputable def ep225 := nat_lit 5735591182320716214326916039248808697239605273635524295949801059376149351848481

noncomputable def ep226 := BSN.cos_dyadic_bound_f 2704287667 2147483648 3 2 1048576 320313 ep224 ep57 ep220 ep225 ep60 ep220 321388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2704287667) qz15 0 2 ep224 ep57 ep220 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2704287667) qz16 0 2 ep225 ep60 ep220 rfl rfl rfl rfl) rfl rfl

noncomputable def ep227 := @Enclosure.Real.IsNear.sin_image qz39 qz330 Bool.false 190900199 524288 481 524288 Bool.true 321388 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 163982022621839012241 450359962737049600 91581250043959 100000000000000000 190900199 524288 481 524288 (ep218 rfl) rfl) (Enclosure.sfrac_false_div 190900199 524288) (BSN.sin_reduce3 qz330 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95148663540994998796288) qz25) 226375608064910080 72057594037927936 Bool.false 321388 1048576 57 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 190900199 524288 226375608064910080 72057594037927936 57 95148663540994998796288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 321388 1048576 95148663540994998796288 75557863725914323419136 2704287667 2147483648 320313 320000 (ep226 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz331 := (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep216 rfl rfl) rfl)

noncomputable def ep228 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz39)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39))) Bool.false 75531074319 274877906944 11491302563 42949672960000 Bool.false 24320795859 274877906944 2866217047 10737418240000 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz39) 302697 1048576 1 1048576 249527 262144 302673 327680000 75531074319 274877906944 11491302563 42949672960000 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz39) Bool.false 998108 1048576 77484288 83886080000 249527 262144 302673 327680000 (ep223 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz38 (@Neg.neg Real Real.instNeg (Real.sin qz39)) 302697 1048576 1 1048576 80347 262144 302673 327680000 24320795859 274877906944 2866217047 10737418240000 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz39) Bool.true 80347 262144 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz39) Bool.true 321388 1048576 77484288 83886080000 80347 262144 302673 327680000 (ep227 rfl rfl) rfl)) rfl)

noncomputable def ep229 := @ep163 75531074319 274877906944 11491302563 42949672960000 Bool.false 24320795859 274877906944 2866217047 10737418240000 Bool.false 6892311166195280642048 50148163909 274877906944 366170302333 85899345920000 Bool.true 17314565672348082503680 31495011485 137438953472 1464748268707 343597383680000 (ep164 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep215 ep228) rfl rfl

noncomputable abbrev qz591 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz40 := (@Inv.inv Real Real.instInv (Real.sqrt qz591))

noncomputable abbrev qz592 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz41 := (@HMul.hMul Real Real Real qz269 qz279 qz592)

noncomputable def ep230 := @Enclosure.Complex.IsNear.of_eq qz575 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)))) Bool.false 62374844571 549755813888 88067738177 343597383680000 Bool.false 139132922253 549755813888 88232696927 343597383680000 (BSN.cpow_neg_s_mk qz12 146530 1000 13 qz13 rfl)

noncomputable abbrev qz593 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep231 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz591) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz591) (Real.sqrt qz593) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz593) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep232 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 160000 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep233 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz592 146530 1000 0 1 11551497052968677 4503599627370496 6250000003 1000000000000000 169264086317150024081 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 48450490295254733815808 18889465931478580854784 1000000000480000 160000000000000000000 11551497052968677 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep232 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep234 := nat_lit 670964683449965926030805783486837776

noncomputable def ep235 := BSN.sin_dyadic_bound_f 905054882 2147483648 2 1 1048576 320313 ep234 ep80 ep234 ep234 ep81 ep234 428954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 905054882) qz19 0 1 ep234 ep80 ep234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 905054882) qz20 0 1 ep234 ep81 ep234 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 394098661) qz30)

noncomputable def ep236 := @Enclosure.Real.IsNear.cos_image qz41 qz332 Bool.false 394098661 1048576 961 1048576 Bool.false 428954 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 169264086317150024081 450359962737049600 91581250043959 100000000000000000 394098661 1048576 961 1048576 (ep233 rfl) rfl) (Enclosure.sfrac_false_div 394098661 1048576) (BSN.cos_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63687575515160245174272) qz31) 226375608064910080 72057594037927936 Bool.false 428954 1048576 59 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 394098661 1048576 226375608064910080 72057594037927936 59 63687575515160245174272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 428954 1048576 63687575515160245174272 151115727451828646838272 905054882 2147483648 320313 320000 (ep235 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep237 := BSN.cos_dyadic_bound_f 905054882 2147483648 2 1 1048576 320313 ep234 ep95 ep234 ep234 ep96 ep234 956822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 905054882) qz15 0 1 ep234 ep95 ep234 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 905054882) qz16 0 1 ep234 ep96 ep234 rfl rfl rfl rfl) rfl rfl

noncomputable def ep238 := @Enclosure.Real.IsNear.sin_image qz41 qz332 Bool.false 394098661 1048576 961 1048576 Bool.true 956822 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 169264086317150024081 450359962737049600 91581250043959 100000000000000000 394098661 1048576 961 1048576 (ep233 rfl) rfl) (Enclosure.sfrac_false_div 394098661 1048576) (BSN.sin_reduce3 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63687575515160245174272) qz31) 226375608064910080 72057594037927936 Bool.false 956822 1048576 59 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 394098661 1048576 226375608064910080 72057594037927936 59 63687575515160245174272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956822 1048576 63687575515160245174272 151115727451828646838272 905054882 2147483648 320313 320000 (ep237 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep231 rfl rfl) rfl)

noncomputable def ep239 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz41)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41))) Bool.false 62374844571 549755813888 88067738177 343597383680000 Bool.false 139132922253 549755813888 88232696927 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz41) 290823 1048576 1 1048576 214477 524288 604721 655360000 62374844571 549755813888 88067738177 343597383680000 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz41) Bool.false 428954 1048576 154808576 167772160000 214477 524288 604721 655360000 (ep236 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz40 (@Neg.neg Real Real.instNeg (Real.sin qz41)) 290823 1048576 1 1048576 478411 524288 604721 655360000 139132922253 549755813888 88232696927 343597383680000 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz41) Bool.true 478411 524288 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz41) Bool.true 956822 1048576 154808576 167772160000 478411 524288 604721 655360000 (ep238 rfl rfl) rfl)) rfl)

noncomputable def ep240 := @ep161 62374844571 549755813888 88067738177 343597383680000 Bool.false 139132922253 549755813888 88232696927 343597383680000 Bool.false 44714711386414924169216 162671172389 549755813888 1552748947509 343597383680000 Bool.false 1807717555605377908736 13152876313 549755813888 776490482817 171798691840000 (ep162 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep229 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep230 ep239) rfl rfl

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt qz594))

noncomputable abbrev qz595 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz269 qz279 qz595)

noncomputable def ep241 := @Enclosure.Complex.IsNear.of_eq qz574 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.true 35250926241 137438953472 2660523741 10737418240000 Bool.false 2581318273 34359738368 21228600553 85899345920000 (BSN.cpow_neg_s_mk qz12 146530 1000 14 qz13 rfl)

noncomputable abbrev qz596 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep242 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz594) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz594) (Real.sqrt qz596) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz596) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep243 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 160000 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep244 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz595 146530 1000 0 1 11885250371606245 4503599627370496 6250000003 1000000000000000 34830914739029261597 90071992547409920 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 49850353174629559828480 18889465931478580854784 1000000000480000 160000000000000000000 11885250371606245 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep245 := nat_lit 140191031581765804905518879267642001

noncomputable def ep246 := BSN.cos_dyadic_bound_f 611899443 2147483648 2 1 1048576 320313 ep245 ep95 ep245 ep245 ep96 ep245 1006296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 611899443) qz15 0 1 ep245 ep95 ep245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 611899443) qz16 0 1 ep245 ep96 ep245 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202742607) qz24)

noncomputable def ep247 := @Enclosure.Real.IsNear.cos_image qz43 qz334 Bool.false 202742607 524288 481 524288 Bool.true 1006296 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 34830914739029261597 90071992547409920 91581250043959 100000000000000000 202742607 524288 481 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 202742607 524288) (BSN.cos_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21529297714981543870464) qz25) 226375608064910080 72057594037927936 Bool.false 1006296 1048576 61 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 202742607 524288 226375608064910080 72057594037927936 61 21529297714981543870464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1006296 1048576 21529297714981543870464 75557863725914323419136 611899443 2147483648 320313 320000 (ep246 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep248 := BSN.sin_dyadic_bound_f 611899443 2147483648 2 1 1048576 320313 ep245 ep80 ep245 ep245 ep81 ep245 294752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 611899443) qz19 0 1 ep245 ep80 ep245 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 611899443) qz20 0 1 ep245 ep81 ep245 rfl rfl rfl rfl) rfl rfl

noncomputable def ep249 := @Enclosure.Real.IsNear.sin_image qz43 qz334 Bool.false 202742607 524288 481 524288 Bool.true 294752 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 34830914739029261597 90071992547409920 91581250043959 100000000000000000 202742607 524288 481 524288 (ep244 rfl) rfl) (Enclosure.sfrac_false_div 202742607 524288) (BSN.sin_reduce2 qz334 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21529297714981543870464) qz25) 226375608064910080 72057594037927936 Bool.false 294752 1048576 61 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 202742607 524288 226375608064910080 72057594037927936 61 21529297714981543870464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 294752 1048576 21529297714981543870464 75557863725914323419136 611899443 2147483648 320313 320000 (ep248 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz335 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep242 rfl rfl) rfl)

noncomputable def ep250 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.true 35250926241 137438953472 2660523741 10737418240000 Bool.false 2581318273 34359738368 21228600553 85899345920000 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz43) 280243 1048576 1 1048576 125787 131072 302673 327680000 35250926241 137438953472 2660523741 10737418240000 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.true 1006296 1048576 77484288 83886080000 125787 131072 302673 327680000 (ep247 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 280243 1048576 1 1048576 9211 32768 302673 327680000 2581318273 34359738368 21228600553 85899345920000 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 9211 32768 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 294752 1048576 77484288 83886080000 9211 32768 302673 327680000 (ep249 rfl rfl) rfl)) rfl)

noncomputable def ep251 := @ep159 35250926241 137438953472 2660523741 10737418240000 Bool.false 2581318273 34359738368 21228600553 85899345920000 Bool.false 2977954047280650649600 21667467425 549755813888 1637885707221 343597383680000 Bool.false 1871024116978426052608 54453968681 549755813888 818947683923 171798691840000 (ep160 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep240 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep241 ep250) rfl rfl

noncomputable abbrev qz597 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt qz597))

noncomputable abbrev qz598 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz269 qz279 qz598)

noncomputable def ep252 := @Enclosure.Complex.IsNear.of_eq qz573 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.false 160566469683 1099511627776 164094037357 687194767360000 Bool.true 117061098393 549755813888 320827811 1342177280000 (BSN.cpow_neg_s_mk qz12 146530 1000 15 qz13 rfl)

noncomputable abbrev qz599 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep253 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz597) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz597) (Real.sqrt qz599) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz599) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep254 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 160000 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep255 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz598 146530 1000 0 1 12195965485668069 4503599627370496 6250000003 1000000000000000 178707482261494215057 450359962737049600 91581250043959 100000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz599) Bool.false 51153586820399524478976 18889465931478580854784 1000000000480000 160000000000000000000 12195965485668069 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep254 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep256 := nat_lit 672099895075192754039459470398491798876051718656443194375333499892251323157441

noncomputable def ep257 := nat_lit 353470552639909571247581981169056203879372087919924782794415953293406260161

noncomputable def ep258 := nat_lit 2015592744120298442975883247233137284220396411793489733560411667770167156952001

noncomputable def ep259 := BSN.cos_dyadic_bound_f 2082304103 2147483648 3 2 1048576 320313 ep256 ep57 ep257 ep258 ep60 ep257 593063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2082304103) qz15 0 2 ep256 ep57 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2082304103) qz16 0 2 ep258 ep60 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz336 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 416085781) qz30)

noncomputable def ep260 := @Enclosure.Real.IsNear.cos_image qz45 qz336 Bool.false 416085781 1048576 961 1048576 Bool.false 593063 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 178707482261494215057 450359962737049600 91581250043959 100000000000000000 416085781 1048576 961 1048576 (ep255 rfl) rfl) (Enclosure.sfrac_false_div 416085781 1048576) (BSN.cos_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146529124732047428943872) qz31) 226375608064910080 72057594037927936 Bool.false 593063 1048576 63 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 416085781 1048576 226375608064910080 72057594037927936 63 146529124732047428943872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 593063 1048576 146529124732047428943872 151115727451828646838272 2082304103 2147483648 320313 320000 (ep259 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep261 := nat_lit 1209497034693235029614028981132349993013789595911261810049364767043417656675265

noncomputable def ep262 := nat_lit 3167158043301817604921389341662833414515549005910958195719050097379809300204481

noncomputable def ep263 := BSN.sin_dyadic_bound_f 2082304103 2147483648 3 2 1048576 320313 ep261 ep64 ep257 ep262 ep66 ep257 864746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2082304103) qz19 0 2 ep261 ep64 ep257 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2082304103) qz20 0 2 ep262 ep66 ep257 rfl rfl rfl rfl) rfl rfl

noncomputable def ep264 := @Enclosure.Real.IsNear.sin_image qz45 qz336 Bool.false 416085781 1048576 961 1048576 Bool.false 864746 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 178707482261494215057 450359962737049600 91581250043959 100000000000000000 416085781 1048576 961 1048576 (ep255 rfl) rfl) (Enclosure.sfrac_false_div 416085781 1048576) (BSN.sin_reduce0 qz336 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146529124732047428943872) qz31) 226375608064910080 72057594037927936 Bool.false 864746 1048576 63 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 416085781 1048576 226375608064910080 72057594037927936 63 146529124732047428943872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 864746 1048576 146529124732047428943872 151115727451828646838272 2082304103 2147483648 320313 320000 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep253 rfl rfl) rfl)

noncomputable def ep265 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.false 160566469683 1099511627776 164094037357 687194767360000 Bool.true 117061098393 549755813888 320827811 1342177280000 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz45) 270741 1048576 1 1048576 593063 1048576 604721 655360000 160566469683 1099511627776 164094037357 687194767360000 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.false 593063 1048576 154808576 167772160000 593063 1048576 604721 655360000 (ep260 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 432373 524288 604721 655360000 117061098393 549755813888 320827811 1342177280000 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.false 432373 524288 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.false 864746 1048576 154808576 167772160000 432373 524288 604721 655360000 (ep264 rfl rfl) rfl)) rfl)

noncomputable def ep266 := @ep157 160566469683 1099511627776 164094037357 687194767360000 Bool.true 117061098393 549755813888 320827811 1342177280000 Bool.false 112095982601945747554304 203901404533 1099511627776 3439865451799 687194767360000 Bool.true 34418633550012147040256 3912945607 34359738368 860013643731 171798691840000 (ep158 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep251 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep252 ep265) rfl rfl

noncomputable abbrev qz600 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz600))

noncomputable abbrev qz601 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz269 qz279 qz601)

noncomputable def ep267 := @Enclosure.Complex.IsNear.of_eq qz572 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 74029969629 549755813888 79520412787 343597383680000 Bool.false 231593116923 1099511627776 159239984949 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 16 qz13 rfl)

noncomputable abbrev qz602 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep268 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz600) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz600) (Real.sqrt qz602) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz602) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep269 := BSN.log_dyadic_bound 0 32 1 0 1 524288 160000 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep270 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz601 146530 1000 0 1 3121657384082679 1125899906842624 1562500001 250000000000000 45741645648963495387 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz602) Bool.false 52372720210750067441664 18889465931478580854784 1000000000640000 160000000000000000000 3121657384082679 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep271 := nat_lit 766357641745461591370594703481828188882530802505141977388430885179288551301376

noncomputable def ep272 := nat_lit 459498972611444303607290813483718848843658785951908005464818973691256381696

noncomputable def ep273 := nat_lit 2298153927291161885504569528818517128949905089943522116154363017590483141140736

noncomputable def ep274 := BSN.cos_dyadic_bound_f 2151719066 2147483648 3 2 1048576 320313 ep271 ep57 ep272 ep273 ep60 ep272 564806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151719066) qz15 0 2 ep271 ep57 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151719066) qz16 0 2 ep273 ep60 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 426002271) qz30)

noncomputable def ep275 := @Enclosure.Real.IsNear.cos_image qz47 qz338 Bool.false 426002271 1048576 481 524288 Bool.true 564806 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 45741645648963495387 112589990684262400 22895312514653 25000000000000000 426002271 1048576 481 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 426002271 1048576) (BSN.cos_reduce2 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151413768520764512796672) qz31) 226375608064910080 72057594037927936 Bool.false 564806 1048576 64 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 426002271 1048576 226375608064910080 72057594037927936 64 151413768520764512796672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 564806 1048576 151413768520764512796672 151115727451828646838272 2151719066 2147483648 320313 320000 (ep274 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep276 := nat_lit 1379076155963741709024184633616503764909480517480494032894803738143766387237120

noncomputable def ep277 := nat_lit 3611122172044619280476547950535679077579083050604990806525161988228649932431616

noncomputable def ep278 := BSN.sin_dyadic_bound_f 2151719066 2147483648 3 2 1048576 320313 ep276 ep64 ep272 ep277 ep66 ep272 883461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151719066) qz19 0 2 ep276 ep64 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151719066) qz20 0 2 ep277 ep66 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable def ep279 := @Enclosure.Real.IsNear.sin_image qz47 qz338 Bool.false 426002271 1048576 481 524288 Bool.true 883461 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 45741645648963495387 112589990684262400 22895312514653 25000000000000000 426002271 1048576 481 524288 (ep270 rfl) rfl) (Enclosure.sfrac_false_div 426002271 1048576) (BSN.sin_reduce2 qz338 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151413768520764512796672) qz31) 226375608064910080 72057594037927936 Bool.false 883461 1048576 64 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 426002271 1048576 226375608064910080 72057594037927936 64 151413768520764512796672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883461 1048576 151413768520764512796672 151115727451828646838272 2151719066 2147483648 320313 320000 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz339 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep268 rfl rfl) rfl)

noncomputable def ep280 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 74029969629 549755813888 79520412787 343597383680000 Bool.false 231593116923 1099511627776 159239984949 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 262143 1048576 1 1048576 282403 524288 302673 327680000 74029969629 549755813888 79520412787 343597383680000 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 564806 1048576 77484288 83886080000 282403 524288 302673 327680000 (ep275 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 883461 1048576 302673 327680000 231593116923 1099511627776 159239984949 687194767360000 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.true 883461 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.true 883461 1048576 77484288 83886080000 883461 1048576 302673 327680000 (ep279 rfl rfl) rfl)) rfl)

noncomputable def ep281 := @ep155 74029969629 549755813888 79520412787 343597383680000 Bool.false 231593116923 1099511627776 159239984949 687194767360000 Bool.false 30699170190956114739200 55841465275 1099511627776 3598906277373 687194767360000 Bool.false 3655149711552394821632 106378857499 1099511627776 3599294559873 687194767360000 (ep156 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep266 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep267 ep280) rfl rfl

theorem EMLast.d7 : Enclosure.Complex.IsNear qz32 Bool.false 55841465275 1099511627776 3598906277373 687194767360000 Bool.false 106378857499 1099511627776 3599294559873 687194767360000 := ep154 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep281 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz273 25)

noncomputable abbrev qz603 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz603) Bool.false 221973231291 274877906944 94598623219 13743895347200 Bool.true 91071763311 549755813888 23642790611 3435973836800

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz603 Bool.false 719810024815 1099511627776 919974419247 137438953472000 Bool.true 4177101895 137438953472 459855557811 68719476736000 Bool.false

noncomputable abbrev qz604 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz604) Bool.false 719810024815 1099511627776 919974419247 137438953472000 Bool.true 4177101895 137438953472 459855557811 68719476736000

noncomputable def ep285 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz604 Bool.false 277702350305 549755813888 1116761716509 171798691840000 Bool.false 126372518029 1099511627776 4465743542911 687194767360000 Bool.false

noncomputable abbrev qz605 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz605) Bool.false 277702350305 549755813888 1116761716509 171798691840000 Bool.false 126372518029 1099511627776 4465743542911 687194767360000

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz605 Bool.false 354461608945 1099511627776 4331294870593 687194767360000 Bool.false 247090615345 1099511627776 4330215833093 687194767360000 Bool.false

noncomputable abbrev qz606 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz606) Bool.false 354461608945 1099511627776 4331294870593 687194767360000 Bool.false 247090615345 1099511627776 4330215833093 687194767360000

noncomputable def ep289 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz606 Bool.false 114535410317 1099511627776 4191611928873 687194767360000 Bool.false 248902625087 1099511627776 4191833675123 687194767360000 Bool.false

noncomputable abbrev qz607 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep290 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz607) Bool.false 114535410317 1099511627776 4191611928873 687194767360000 Bool.false 248902625087 1099511627776 4191833675123 687194767360000

noncomputable def ep291 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz607 Bool.true 46158856709 1099511627776 4049394649753 687194767360000 Bool.false 15707065289 274877906944 2024774371439 343597383680000 Bool.false

noncomputable abbrev qz608 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz608) Bool.true 46158856709 1099511627776 4049394649753 687194767360000 Bool.false 15707065289 274877906944 2024774371439 343597383680000

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz608 Bool.false 4953370737 68719476736 1951723389559 343597383680000 Bool.true 156029670895 1099511627776 3903358090993 687194767360000 Bool.true

noncomputable abbrev qz609 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz609) Bool.false 4953370737 68719476736 1951723389559 343597383680000 Bool.true 156029670895 1099511627776 3903358090993 687194767360000

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz609 Bool.false 294756010487 1099511627776 3753443808901 687194767360000 Bool.true 6041127709 549755813888 1876768034763 343597383680000 Bool.true

noncomputable abbrev qz610 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz32 qz610) Bool.false 294756010487 1099511627776 3753443808901 687194767360000 Bool.true 6041127709 549755813888 1876768034763 343597383680000

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP qz32 qz610 Bool.false 55841465275 1099511627776 3598906277373 687194767360000 Bool.false 106378857499 1099511627776 3599294559873 687194767360000 Bool.false

noncomputable abbrev qz611 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt qz611))

noncomputable abbrev qz612 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz269 qz279 qz612)

noncomputable def ep298 := @Enclosure.Complex.IsNear.of_eq qz610 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.false 59728636303 274877906944 19317191441 85899345920000 Bool.true 118461112917 1099511627776 154241509653 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 17 qz13 rfl)

noncomputable abbrev qz613 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep299 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz611) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz611) (Real.sqrt qz613) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz613) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep300 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 160000 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep301 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz612 146530 1000 0 1 3189913004350711 1125899906842624 1562500001 250000000000000 46741795252750968283 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 53517859495200818200576 18889465931478580854784 1000000000640000 160000000000000000000 3189913004350711 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep302 := nat_lit 954796015032198317970748643314331281

noncomputable def ep303 := BSN.cos_dyadic_bound_f 988502221 2147483648 2 1 1048576 320313 ep302 ep95 ep302 ep302 ep96 ep302 939436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 988502221) qz15 0 1 ep302 ep95 ep302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 988502221) qz16 0 1 ep302 ep96 ep302 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217658445) qz24)

noncomputable def ep304 := @Enclosure.Real.IsNear.cos_image qz50 qz340 Bool.false 217658445 524288 481 524288 Bool.false 939436 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 46741795252750968283 112589990684262400 22895312514653 25000000000000000 217658445 524288 481 524288 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 217658445 524288) (BSN.cos_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34779829973539073556480) qz25) 226375608064910080 72057594037927936 Bool.false 939436 1048576 66 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 217658445 524288 226375608064910080 72057594037927936 66 34779829973539073556480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 939436 1048576 34779829973539073556480 75557863725914323419136 988502221 2147483648 320313 320000 (ep303 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep305 := BSN.sin_dyadic_bound_f 988502221 2147483648 2 1 1048576 320313 ep302 ep80 ep302 ep302 ep81 ep302 465801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 988502221) qz19 0 1 ep302 ep80 ep302 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 988502221) qz20 0 1 ep302 ep81 ep302 rfl rfl rfl rfl) rfl rfl

noncomputable def ep306 := @Enclosure.Real.IsNear.sin_image qz50 qz340 Bool.false 217658445 524288 481 524288 Bool.false 465801 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 46741795252750968283 112589990684262400 22895312514653 25000000000000000 217658445 524288 481 524288 (ep301 rfl) rfl) (Enclosure.sfrac_false_div 217658445 524288) (BSN.sin_reduce0 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34779829973539073556480) qz25) 226375608064910080 72057594037927936 Bool.false 465801 1048576 66 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 217658445 524288 226375608064910080 72057594037927936 66 34779829973539073556480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 465801 1048576 34779829973539073556480 75557863725914323419136 988502221 2147483648 320313 320000 (ep305 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep299 rfl rfl) rfl)

noncomputable def ep307 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.false 59728636303 274877906944 19317191441 85899345920000 Bool.true 118461112917 1099511627776 154241509653 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz49 (Real.cos qz50) 254317 1048576 1 1048576 234859 262144 302673 327680000 59728636303 274877906944 19317191441 85899345920000 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.false 939436 1048576 77484288 83886080000 234859 262144 302673 327680000 (ep304 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 465801 1048576 302673 327680000 118461112917 1099511627776 154241509653 687194767360000 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.false 465801 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.false 465801 1048576 77484288 83886080000 465801 1048576 302673 327680000 (ep306 rfl rfl) rfl)) rfl)

noncomputable def ep308 := @ep297 59728636303 274877906944 19317191441 85899345920000 Bool.true 118461112917 1099511627776 154241509653 687194767360000 Bool.false 81021915221830274121728 294756010487 1099511627776 3753443808901 687194767360000 Bool.true 13284580321850575290368 6041127709 549755813888 1876768034763 343597383680000 EMLast.d7 (ep298 ep307) rfl rfl

noncomputable abbrev qz614 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt qz614))

noncomputable abbrev qz615 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz269 qz279 qz615)

noncomputable def ep309 := @Enclosure.Complex.IsNear.of_eq qz609 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.true 215502078695 1099511627776 150002970217 687194767360000 Bool.true 143947415477 1099511627776 149822021467 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 18 qz13 rfl)

noncomputable abbrev qz616 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep310 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz614) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz614) (Real.sqrt qz616) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz616) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep311 := BSN.log_dyadic_bound 2 34 2 1 3468 524288 160000 4 4 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 34) 0 1 4 3468 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep312 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz615 146530 1000 0 1 3254268794313975 1125899906842624 1562500001 250000000000000 1907392025723307027 4503599627370496 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 54597570484265130393600 18889465931478580854784 1000000000640000 160000000000000000000 3254268794313975 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep311 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep313 := nat_lit 1271796496403823100526600265263060202746543564030902751731336998457116350644480

noncomputable def ep314 := nat_lit 390810119429734484257512468325566985778573787683807438616190519336640348416

noncomputable def ep315 := nat_lit 3330262845626174264595155198359297232073496405377066756776694497023045405409536

noncomputable def ep316 := BSN.sin_dyadic_bound_f 2108607394 2147483648 3 2 1048576 320313 ep313 ep64 ep314 ep315 ep66 ep314 871945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2108607394) qz19 0 2 ep313 ep64 ep314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2108607394) qz20 0 2 ep315 ep66 ep314 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 444099313) qz30)

noncomputable def ep317 := @Enclosure.Real.IsNear.cos_image qz52 qz342 Bool.false 444099313 1048576 961 1048576 Bool.true 871945 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 1907392025723307027 4503599627370496 22895312514653 25000000000000000 444099313 1048576 961 1048576 (ep312 rfl) rfl) (Enclosure.sfrac_false_div 444099313 1048576) (BSN.cos_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148380054342444741820416) qz31) 226375608064910080 72057594037927936 Bool.false 871945 1048576 67 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 444099313 1048576 226375608064910080 72057594037927936 67 148380054342444741820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 871945 1048576 148380054342444741820416 151115727451828646838272 2108607394 2147483648 320313 320000 (ep316 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep318 := nat_lit 706727302499648271174447930687622586852870235033916554267905528262547590512896

noncomputable def ep319 := nat_lit 2119400287260085344554828767126216626587053557526382047926484203748969490841856

noncomputable def ep320 := BSN.cos_dyadic_bound_f 2108607394 2147483648 3 2 1048576 320313 ep318 ep57 ep314 ep319 ep60 ep314 582427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2108607394) qz15 0 2 ep318 ep57 ep314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2108607394) qz16 0 2 ep319 ep60 ep314 rfl rfl rfl rfl) rfl rfl

noncomputable def ep321 := @Enclosure.Real.IsNear.sin_image qz52 qz342 Bool.false 444099313 1048576 961 1048576 Bool.false 582427 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 1907392025723307027 4503599627370496 22895312514653 25000000000000000 444099313 1048576 961 1048576 (ep312 rfl) rfl) (Enclosure.sfrac_false_div 444099313 1048576) (BSN.sin_reduce1 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148380054342444741820416) qz31) 226375608064910080 72057594037927936 Bool.false 582427 1048576 67 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 444099313 1048576 226375608064910080 72057594037927936 67 148380054342444741820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 582427 1048576 148380054342444741820416 151115727451828646838272 2108607394 2147483648 320313 320000 (ep320 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep310 rfl rfl) rfl)

noncomputable def ep322 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.true 215502078695 1099511627776 150002970217 687194767360000 Bool.true 143947415477 1099511627776 149822021467 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz51 (Real.cos qz52) 247151 1048576 1 1048576 871945 1048576 604721 655360000 215502078695 1099511627776 150002970217 687194767360000 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.true 871945 1048576 154808576 167772160000 871945 1048576 604721 655360000 (ep317 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 582427 1048576 604721 655360000 143947415477 1099511627776 149822021467 687194767360000 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.false 582427 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.false 582427 1048576 154808576 167772160000 582427 1048576 604721 655360000 (ep321 rfl rfl) rfl)) rfl)

noncomputable def ep323 := @ep295 215502078695 1099511627776 150002970217 687194767360000 Bool.true 143947415477 1099511627776 149822021467 687194767360000 Bool.false 87140619552269996654592 4953370737 68719476736 1951723389559 343597383680000 Bool.true 85778218713557510389760 156029670895 1099511627776 3903358090993 687194767360000 (ep296 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep308 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep309 ep322) rfl rfl

noncomputable abbrev qz617 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt qz617))

noncomputable abbrev qz618 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz269 qz279 qz618)

noncomputable def ep324 := @Enclosure.Complex.IsNear.of_eq qz608 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.true 125412788501 1099511627776 29189574127 137438953472000 Bool.false 218857932051 1099511627776 29238130377 137438953472000 (BSN.cpow_neg_s_mk qz12 146530 1000 19 qz13 rfl)

noncomputable abbrev qz619 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep325 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz617) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz617) (Real.sqrt qz619) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz619) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep326 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 160000 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep327 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz618 146530 1000 0 1 3315143513283831 1125899906842624 1562500001 250000000000000 48576797900147975643 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 55618878793361701994496 18889465931478580854784 1000000000640000 160000000000000000000 3315143513283831 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep328 := nat_lit 925870875671266386431529031871326077224125674131389300431620511825249766998016

noncomputable def ep329 := nat_lit 670523634778947832433542793759208855462929012386877770367037560818537332736

noncomputable def ep330 := nat_lit 2776271579744241263629720010026459813961451164369394145754127460354112226328576

noncomputable def ep331 := BSN.cos_dyadic_bound_f 2255806072 2147483648 3 2 1048576 320313 ep328 ep57 ep329 ep330 ep60 ep329 521339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2255806072) qz15 0 2 ep328 ep57 ep329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2255806072) qz16 0 2 ep330 ep60 ep329 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113101671) qz17)

noncomputable def ep332 := @Enclosure.Real.IsNear.cos_image qz54 qz344 Bool.false 113101671 262144 481 524288 Bool.true 521339 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 48576797900147975643 112589990684262400 22895312514653 25000000000000000 113101671 262144 481 524288 (ep327 rfl) rfl) (Enclosure.sfrac_false_div 113101671 262144) (BSN.cos_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39684560102999963205632) qz286) 226375608064910080 72057594037927936 Bool.false 521339 1048576 68 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 113101671 262144 226375608064910080 72057594037927936 68 39684560102999963205632 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521339 1048576 39684560102999963205632 37778931862957161709568 2255806072 2147483648 320313 320000 (ep331 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep333 := nat_lit 1666031157300456337310805423133379571919055870226591238560623291236794750730240

noncomputable def ep334 := nat_lit 4362329326092505444085312277016574445450587298859112584601990559093137191469056

noncomputable def ep335 := BSN.sin_dyadic_bound_f 2255806072 2147483648 3 2 1048576 320313 ep333 ep64 ep329 ep334 ep66 ep329 909789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2255806072) qz19 0 2 ep333 ep64 ep329 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2255806072) qz20 0 2 ep334 ep66 ep329 rfl rfl rfl rfl) rfl rfl

noncomputable def ep336 := @Enclosure.Real.IsNear.sin_image qz54 qz344 Bool.false 113101671 262144 481 524288 Bool.true 909789 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 48576797900147975643 112589990684262400 22895312514653 25000000000000000 113101671 262144 481 524288 (ep327 rfl) rfl) (Enclosure.sfrac_false_div 113101671 262144) (BSN.sin_reduce2 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39684560102999963205632) qz286) 226375608064910080 72057594037927936 Bool.false 909789 1048576 68 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 113101671 262144 226375608064910080 72057594037927936 68 39684560102999963205632 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 909789 1048576 39684560102999963205632 37778931862957161709568 2255806072 2147483648 320313 320000 (ep335 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep325 rfl rfl) rfl)

noncomputable def ep337 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.true 125412788501 1099511627776 29189574127 137438953472000 Bool.false 218857932051 1099511627776 29238130377 137438953472000 (@Enclosure.Real.IsNear.mulLit_ft qz53 (Real.cos qz54) 240559 1048576 1 1048576 521339 1048576 302673 327680000 125412788501 1099511627776 29189574127 137438953472000 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.true 521339 1048576 77484288 83886080000 521339 1048576 302673 327680000 (ep332 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 909789 1048576 302673 327680000 218857932051 1099511627776 29238130377 137438953472000 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.true 909789 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.true 909789 1048576 77484288 83886080000 909789 1048576 302673 327680000 (ep336 rfl rfl) rfl)) rfl)

noncomputable def ep338 := @ep293 125412788501 1099511627776 29189574127 137438953472000 Bool.false 218857932051 1099511627776 29238130377 137438953472000 Bool.true 3172012479774483021824 46158856709 1099511627776 4049394649753 687194767360000 Bool.false 69080403693969191469056 15707065289 274877906944 2024774371439 343597383680000 (ep294 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep323 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep324 ep337) rfl rfl

noncomputable abbrev qz620 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt qz620))

noncomputable abbrev qz621 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz269 qz279 qz621)

noncomputable def ep339 := @Enclosure.Complex.IsNear.of_eq qz607 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 80347133513 549755813888 1777715989 8589934592000 Bool.false 186074363931 1099511627776 28456986449 137438953472000 (BSN.cpow_neg_s_mk qz12 146530 1000 20 qz13 rfl)

noncomputable abbrev qz622 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep340 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz620) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz620) (Real.sqrt qz622) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz622) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep341 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 160000 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz621 146530 1000 0 1 3372893643545847 1125899906842624 1562500001 250000000000000 49423010558877296091 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 56587765202795681021952 18889465931478580854784 1000000000640000 160000000000000000000 3372893643545847 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep343 := nat_lit 5476024498359332071188296323880442001

noncomputable def ep344 := BSN.sin_dyadic_bound_f 1529735501 2147483648 2 1 1048576 320313 ep343 ep80 ep343 ep343 ep81 ep343 685354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1529735501) qz19 0 1 ep343 ep80 ep343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1529735501) qz20 0 1 ep343 ep81 ep343 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz346 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230143827) qz24)

noncomputable def ep345 := @Enclosure.Real.IsNear.cos_image qz56 qz346 Bool.false 230143827 524288 961 1048576 Bool.false 685354 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 49423010558877296091 112589990684262400 22895312514653 25000000000000000 230143827 524288 961 1048576 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 230143827 524288) (BSN.cos_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53822783085410972073984) qz25) 226375608064910080 72057594037927936 Bool.false 685354 1048576 69 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 230143827 524288 226375608064910080 72057594037927936 69 53822783085410972073984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 685354 1048576 53822783085410972073984 75557863725914323419136 1529735501 2147483648 320313 320000 (ep344 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep346 := nat_lit 195686417494276244965353377647607396231647573855875691385387590194566860046881

noncomputable def ep347 := nat_lit 29986844306631574453617500818289756498167028462816316454581302763124884001

noncomputable def ep348 := nat_lit 586999278794215471747152897941185609181946387510701441523253607978174330372641

noncomputable def ep349 := BSN.cos_dyadic_bound_f 1529735501 2147483648 3 2 1048576 320313 ep346 ep57 ep347 ep348 ep60 ep347 793599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1529735501) qz15 0 2 ep346 ep57 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1529735501) qz16 0 2 ep348 ep60 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable def ep350 := @Enclosure.Real.IsNear.sin_image qz56 qz346 Bool.false 230143827 524288 961 1048576 Bool.true 793599 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 49423010558877296091 112589990684262400 22895312514653 25000000000000000 230143827 524288 961 1048576 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 230143827 524288) (BSN.sin_reduce3 qz346 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53822783085410972073984) qz25) 226375608064910080 72057594037927936 Bool.false 793599 1048576 69 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 230143827 524288 226375608064910080 72057594037927936 69 53822783085410972073984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 793599 1048576 53822783085410972073984 75557863725914323419136 1529735501 2147483648 320313 320000 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz347 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep340 rfl rfl) rfl)

noncomputable def ep351 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 80347133513 549755813888 1777715989 8589934592000 Bool.false 186074363931 1099511627776 28456986449 137438953472000 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 342677 524288 604721 655360000 80347133513 549755813888 1777715989 8589934592000 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 685354 1048576 154808576 167772160000 342677 524288 604721 655360000 (ep345 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 793599 1048576 604721 655360000 186074363931 1099511627776 28456986449 137438953472000 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.true 793599 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.true 793599 1048576 154808576 167772160000 793599 1048576 604721 655360000 (ep350 rfl rfl) rfl)) rfl)

noncomputable def ep352 := @ep291 80347133513 549755813888 1777715989 8589934592000 Bool.false 186074363931 1099511627776 28456986449 137438953472000 Bool.false 62966507717818367082496 114535410317 1099511627776 4191611928873 687194767360000 Bool.false 68417832616781705904128 248902625087 1099511627776 4191833675123 687194767360000 (ep292 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep338 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep339 ep351) rfl rfl

noncomputable abbrev qz623 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt qz623))

noncomputable abbrev qz624 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz269 qz279 qz624)

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq qz606 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 59981549657 274877906944 3492073543 17179869184000 Bool.true 906004871 549755813888 13838215797 68719476736000 (BSN.cpow_neg_s_mk qz12 146530 1000 21 qz13 rfl)

noncomputable abbrev qz625 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep354 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz623) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz623) (Real.sqrt qz625) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz625) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep355 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 160000 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz624 146530 1000 0 1 3427826275261687 1125899906842624 1562500001 250000000000000 50227938411409499611 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz625) Bool.false 57509381830540779323392 18889465931478580854784 1000000000640000 160000000000000000000 3427826275261687 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep357 := BSN.cos_dyadic_bound_f 16219170 2147483648 1 0 1048576 320313 0 1 1 0 1 1 1048546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16219170) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16219170) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 467784129) qz30)

noncomputable def ep358 := @Enclosure.Real.IsNear.cos_image qz58 qz348 Bool.false 467784129 1048576 961 1048576 Bool.false 1048546 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 50227938411409499611 112589990684262400 22895312514653 25000000000000000 467784129 1048576 961 1048576 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 467784129 1048576) (BSN.cos_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1141322690417831968768) qz31) 226375608064910080 72057594037927936 Bool.false 1048546 1048576 71 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 467784129 1048576 226375608064910080 72057594037927936 71 1141322690417831968768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048546 1048576 1141322690417831968768 151115727451828646838272 16219170 2147483648 320313 320000 (ep357 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep359 := BSN.sin_dyadic_bound_f 16219170 2147483648 1 0 1048576 320313 0 1 1 0 1 1 7919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 16219170) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 16219170) qz20 0 0 rfl) rfl rfl

noncomputable def ep360 := @Enclosure.Real.IsNear.sin_image qz58 qz348 Bool.false 467784129 1048576 961 1048576 Bool.false 7919 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 50227938411409499611 112589990684262400 22895312514653 25000000000000000 467784129 1048576 961 1048576 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 467784129 1048576) (BSN.sin_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1141322690417831968768) qz31) 226375608064910080 72057594037927936 Bool.false 7919 1048576 71 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 467784129 1048576 226375608064910080 72057594037927936 71 1141322690417831968768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7919 1048576 1141322690417831968768 151115727451828646838272 16219170 2147483648 320313 320000 (ep359 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep354 rfl rfl) rfl)

noncomputable def ep361 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 59981549657 274877906944 3492073543 17179869184000 Bool.true 906004871 549755813888 13838215797 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 524273 524288 604721 655360000 59981549657 274877906944 3492073543 17179869184000 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 1048546 1048576 154808576 167772160000 524273 524288 604721 655360000 (ep358 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 7919 1048576 604721 655360000 906004871 549755813888 13838215797 68719476736000 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 7919 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 7919 1048576 154808576 167772160000 7919 1048576 604721 655360000 (ep360 rfl rfl) rfl)) rfl)

noncomputable def ep362 := @ep289 59981549657 274877906944 3492073543 17179869184000 Bool.true 906004871 549755813888 13838215797 68719476736000 Bool.false 97433665158804228014080 354461608945 1099511627776 4331294870593 687194767360000 Bool.false 135839502343077216911360 247090615345 1099511627776 4330215833093 687194767360000 (ep290 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep352 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep353 ep361) rfl rfl

noncomputable abbrev qz626 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt qz626))

noncomputable abbrev qz627 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz269 qz279 qz627)

noncomputable def ep363 := @Enclosure.Complex.IsNear.of_eq qz605 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 200943091665 1099511627776 135751995443 687194767360000 Bool.true 30179524329 274877906944 67763854909 343597383680000 (BSN.cpow_neg_s_mk qz12 146530 1000 22 qz13 rfl)

noncomputable abbrev qz628 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep364 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz626) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz626) (Real.sqrt qz628) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz628) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep365 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 160000 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep366 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz627 146530 1000 0 1 3480203401436407 1125899906842624 1562500001 250000000000000 50995420441247671771 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz628) Bool.false 58388124189833310502912 18889465931478580854784 1000000000640000 160000000000000000000 3480203401436407 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep367 := nat_lit 1821519197433820115311945111506250000

noncomputable def ep368 := BSN.cos_dyadic_bound_f 1161738650 2147483648 2 1 1048576 320313 ep367 ep95 ep367 ep367 ep96 ep367 898845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1161738650) qz15 0 1 ep367 ep95 ep367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1161738650) qz16 0 1 ep367 ep96 ep367 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237465931) qz24)

noncomputable def ep369 := @Enclosure.Real.IsNear.cos_image qz60 qz350 Bool.false 237465931 524288 961 1048576 Bool.false 898845 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 50995420441247671771 112589990684262400 22895312514653 25000000000000000 237465931 524288 961 1048576 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 237465931 524288) (BSN.cos_reduce0 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40875044946167371661312) qz25) 226375608064910080 72057594037927936 Bool.false 898845 1048576 72 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 237465931 524288 226375608064910080 72057594037927936 72 40875044946167371661312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 898845 1048576 40875044946167371661312 75557863725914323419136 1161738650 2147483648 320313 320000 (ep368 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep370 := BSN.sin_dyadic_bound_f 1161738650 2147483648 2 1 1048576 320313 ep367 ep80 ep367 ep367 ep81 ep367 539988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1161738650) qz19 0 1 ep367 ep80 ep367 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1161738650) qz20 0 1 ep367 ep81 ep367 rfl rfl rfl rfl) rfl rfl

noncomputable def ep371 := @Enclosure.Real.IsNear.sin_image qz60 qz350 Bool.false 237465931 524288 961 1048576 Bool.false 539988 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 50995420441247671771 112589990684262400 22895312514653 25000000000000000 237465931 524288 961 1048576 (ep366 rfl) rfl) (Enclosure.sfrac_false_div 237465931 524288) (BSN.sin_reduce0 qz350 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40875044946167371661312) qz25) 226375608064910080 72057594037927936 Bool.false 539988 1048576 72 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 237465931 524288 226375608064910080 72057594037927936 72 40875044946167371661312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 539988 1048576 40875044946167371661312 75557863725914323419136 1161738650 2147483648 320313 320000 (ep370 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz351 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep364 rfl rfl) rfl)

noncomputable def ep372 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 200943091665 1099511627776 135751995443 687194767360000 Bool.true 30179524329 274877906944 67763854909 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 898845 1048576 604721 655360000 200943091665 1099511627776 135751995443 687194767360000 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 898845 1048576 154808576 167772160000 898845 1048576 604721 655360000 (ep369 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 134997 262144 604721 655360000 30179524329 274877906944 67763854909 343597383680000 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 134997 262144 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 539988 1048576 154808576 167772160000 134997 262144 604721 655360000 (ep371 rfl rfl) rfl)) rfl)

noncomputable def ep373 := @ep287 200943091665 1099511627776 135751995443 687194767360000 Bool.true 30179524329 274877906944 67763854909 343597383680000 Bool.false 610673926442143040143360 277702350305 549755813888 1116761716509 171798691840000 Bool.false 34737013251054424293376 126372518029 1099511627776 4465743542911 687194767360000 (ep288 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep362 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep363 ep372) rfl rfl

noncomputable abbrev qz629 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz629))

noncomputable abbrev qz630 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz269 qz279 qz630)

noncomputable def ep374 := @Enclosure.Complex.IsNear.of_eq qz604 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 164405324205 1099511627776 132825230199 687194767360000 Bool.true 159789333189 1099511627776 132812035199 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 23 qz13 rfl)

noncomputable abbrev qz631 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep375 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz629) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz629) (Real.sqrt qz631) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz631) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep376 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 160000 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep377 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz630 146530 1000 0 1 3530250507853047 1125899906842624 1562500001 250000000000000 51728760691570697691 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz631) Bool.false 59227775304360265777152 18889465931478580854784 1000000000640000 160000000000000000000 3530250507853047 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep378 := nat_lit 268794129364421876427637805488997560182864080620597135738932550235031524693121

noncomputable def ep379 := nat_lit 56571701827746141712115746402974672065154435193546302182382824784602944641

noncomputable def ep380 := nat_lit 806269244689610136999489184974186731204461932991404314612432885055525368190081

noncomputable def ep381 := BSN.cos_dyadic_bound_f 1656055569 2147483648 3 2 1048576 320313 ep378 ep57 ep379 ep380 ep60 ep379 751935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1656055569) qz15 0 2 ep378 ep57 ep379 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1656055569) qz16 0 2 ep380 ep60 ep379 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz352 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 481761625) qz30)

noncomputable def ep382 := @Enclosure.Real.IsNear.cos_image qz62 qz352 Bool.false 481761625 1048576 481 524288 Bool.false 751935 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 51728760691570697691 112589990684262400 22895312514653 25000000000000000 481761625 1048576 481 524288 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 481761625 1048576) (BSN.cos_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116534550741771763056640) qz31) 226375608064910080 72057594037927936 Bool.false 751935 1048576 73 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 481761625 1048576 226375608064910080 72057594037927936 73 116534550741771763056640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 751935 1048576 116534550741771763056640 151115727451828646838272 1656055569 2147483648 320313 320000 (ep381 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep383 := nat_lit 7521416211575193882910683294989165121

noncomputable def ep384 := BSN.sin_dyadic_bound_f 1656055569 2147483648 2 1 1048576 320313 ep383 ep80 ep383 ep383 ep81 ep383 730823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1656055569) qz19 0 1 ep383 ep80 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1656055569) qz20 0 1 ep383 ep81 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable def ep385 := @Enclosure.Real.IsNear.sin_image qz62 qz352 Bool.false 481761625 1048576 481 524288 Bool.false 730823 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 51728760691570697691 112589990684262400 22895312514653 25000000000000000 481761625 1048576 481 524288 (ep377 rfl) rfl) (Enclosure.sfrac_false_div 481761625 1048576) (BSN.sin_reduce0 qz352 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116534550741771763056640) qz31) 226375608064910080 72057594037927936 Bool.false 730823 1048576 73 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 481761625 1048576 226375608064910080 72057594037927936 73 116534550741771763056640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730823 1048576 116534550741771763056640 151115727451828646838272 1656055569 2147483648 320313 320000 (ep384 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz353 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep375 rfl rfl) rfl)

noncomputable def ep386 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 164405324205 1099511627776 132825230199 687194767360000 Bool.true 159789333189 1099511627776 132812035199 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 751935 1048576 302673 327680000 164405324205 1099511627776 132825230199 687194767360000 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 751935 1048576 77484288 83886080000 751935 1048576 302673 327680000 (ep382 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 730823 1048576 302673 327680000 159789333189 1099511627776 132812035199 687194767360000 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 730823 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 730823 1048576 77484288 83886080000 730823 1048576 302673 327680000 (ep385 rfl rfl) rfl)) rfl)

noncomputable def ep387 := @ep285 164405324205 1099511627776 132825230199 687194767360000 Bool.true 159789333189 1099511627776 132812035199 687194767360000 Bool.false 395719746036911801630720 719810024815 1099511627776 919974419247 137438953472000 Bool.true 36742176831661313884160 4177101895 137438953472 459855557811 68719476736000 (ep286 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep373 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep374 ep386) rfl rfl

noncomputable abbrev qz632 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz632))

noncomputable abbrev qz633 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz269 qz279 qz633)

noncomputable def ep388 := @Enclosure.Complex.IsNear.of_eq qz603 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 168082900349 1099511627776 26011812943 137438953472000 Bool.true 74363355731 549755813888 13000254409 68719476736000 (BSN.cpow_neg_s_mk qz12 146530 1000 24 qz13 rfl)

noncomputable abbrev qz634 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep389 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz632) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz632) (Real.sqrt qz634) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz634) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep390 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 160000 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep391 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz633 146530 1000 0 1 3578169457974519 1125899906842624 1562500001 250000000000000 52430917067700626907 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz634) Bool.false 60031721881041427759104 18889465931478580854784 1000000000640000 160000000000000000000 3578169457974519 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep392 := nat_lit 209256285384941225791364853044920120416869931532940360512970130150082979289921

noncomputable def ep393 := nat_lit 34289187522508932239701954604400292495068691252619327962923947420284869441

noncomputable def ep394 := nat_lit 627700277779778659509615155225551560665619657216315842882984542555408368130881

noncomputable def ep395 := BSN.cos_dyadic_bound_f 1555588233 2147483648 3 2 1048576 320313 ep392 ep57 ep393 ep394 ep60 ep393 785291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1555588233) qz15 0 2 ep392 ep57 ep393 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1555588233) qz16 0 2 ep394 ep60 ep393 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 244150483) qz24)

noncomputable def ep396 := @Enclosure.Real.IsNear.cos_image qz64 qz354 Bool.false 244150483 524288 481 524288 Bool.false 785291 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 52430917067700626907 112589990684262400 22895312514653 25000000000000000 244150483 524288 481 524288 (ep391 rfl) rfl) (Enclosure.sfrac_false_div 244150483 524288) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54732395219921284366336) qz25) 226375608064910080 72057594037927936 Bool.false 785291 1048576 74 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 244150483 524288 226375608064910080 72057594037927936 74 54732395219921284366336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 785291 1048576 54732395219921284366336 75557863725914323419136 1555588233 2147483648 320313 320000 (ep395 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep397 := nat_lit 5855697014233995717085030230423919521

noncomputable def ep398 := BSN.sin_dyadic_bound_f 1555588233 2147483648 2 1 1048576 320313 ep397 ep80 ep397 ep397 ep81 ep397 694858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1555588233) qz19 0 1 ep397 ep80 ep397 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1555588233) qz20 0 1 ep397 ep81 ep397 rfl rfl rfl rfl) rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.sin_image qz64 qz354 Bool.false 244150483 524288 481 524288 Bool.false 694858 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 52430917067700626907 112589990684262400 22895312514653 25000000000000000 244150483 524288 481 524288 (ep391 rfl) rfl) (Enclosure.sfrac_false_div 244150483 524288) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54732395219921284366336) qz25) 226375608064910080 72057594037927936 Bool.false 694858 1048576 74 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 244150483 524288 226375608064910080 72057594037927936 74 54732395219921284366336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 694858 1048576 54732395219921284366336 75557863725914323419136 1555588233 2147483648 320313 320000 (ep398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep389 rfl rfl) rfl)

noncomputable def ep400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 168082900349 1099511627776 26011812943 137438953472000 Bool.true 74363355731 549755813888 13000254409 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 785291 1048576 302673 327680000 168082900349 1099511627776 26011812943 137438953472000 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 785291 1048576 77484288 83886080000 785291 1048576 302673 327680000 (ep396 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 347429 524288 302673 327680000 74363355731 549755813888 13000254409 68719476736000 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 347429 524288 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 694858 1048576 77484288 83886080000 347429 524288 302673 327680000 (ep399 rfl rfl) rfl)) rfl)

noncomputable def ep401 := @ep283 168082900349 1099511627776 26011812943 137438953472000 Bool.true 74363355731 549755813888 13000254409 68719476736000 Bool.false 976248595437863791755264 221973231291 274877906944 94598623219 13743895347200 Bool.true 12516807840313525665792 91071763311 549755813888 23642790611 3435973836800 (ep284 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep387 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep388 ep400) rfl rfl

theorem EMLast.d8 : Enclosure.Complex.IsNear qz48 Bool.false 221973231291 274877906944 94598623219 13743895347200 Bool.true 91071763311 549755813888 23642790611 3435973836800 := ep282 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz273 33)

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep402 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz635) Bool.false 1361036149053 1099511627776 5686828261913 687194767360000 Bool.false 21616452021 549755813888 710617683911 85899345920000

noncomputable def ep403 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz635 Bool.false 1273518491507 1099511627776 5574323817219 687194767360000 Bool.true 130315985153 1099511627776 5572146949719 687194767360000 Bool.false

noncomputable abbrev qz636 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep404 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz636) Bool.false 1273518491507 1099511627776 5574323817219 687194767360000 Bool.true 130315985153 1099511627776 5572146949719 687194767360000

noncomputable def ep405 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz636 Bool.false 1102858894945 1099511627776 5459752643789 687194767360000 Bool.true 30955488043 1099511627776 5457812393789 687194767360000 Bool.false

noncomputable abbrev qz637 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz637) Bool.false 1102858894945 1099511627776 5459752643789 687194767360000 Bool.true 30955488043 1099511627776 5457812393789 687194767360000

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz637 Bool.false 1187407015693 1099511627776 1068741282833 137438953472000 Bool.false 75556752731 549755813888 534144778979 68719476736000 Bool.true

noncomputable abbrev qz638 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep408 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz638) Bool.false 1187407015693 1099511627776 1068741282833 137438953472000 Bool.false 75556752731 549755813888 534144778979 68719476736000

noncomputable def ep409 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz638 Bool.false 1388296817773 1099511627776 5225191042429 687194767360000 Bool.false 57321692981 549755813888 2611730087777 343597383680000 Bool.true

noncomputable abbrev qz639 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep410 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz639) Bool.false 1388296817773 1099511627776 5225191042429 687194767360000 Bool.false 57321692981 549755813888 2611730087777 343597383680000

noncomputable def ep411 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz639 Bool.false 1439697922017 1099511627776 1021014228037 137438953472000 Bool.true 21671861939 274877906944 127571684989 17179869184000 Bool.true

noncomputable abbrev qz640 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep412 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz640) Bool.false 1439697922017 1099511627776 1021014228037 137438953472000 Bool.true 21671861939 274877906944 127571684989 17179869184000

noncomputable def ep413 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz640 Bool.false 1302685683771 1099511627776 996497594227 137438953472000 Bool.true 123970698137 549755813888 498020915051 68719476736000 Bool.false

noncomputable abbrev qz641 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz641) Bool.false 1302685683771 1099511627776 996497594227 137438953472000 Bool.true 123970698137 549755813888 498020915051 68719476736000

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz641 Bool.false 1088439814509 1099511627776 4857479579561 687194767360000 Bool.true 272353482447 1099511627776 4855777710811 687194767360000 Bool.false

noncomputable abbrev qz642 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep416 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz642) Bool.false 1088439814509 1099511627776 4857479579561 687194767360000 Bool.true 272353482447 1099511627776 4855777710811 687194767360000

noncomputable def ep417 := @Enclosure.Complex.IsNear.addLitP qz48 qz642 Bool.false 221973231291 274877906944 94598623219 13743895347200 Bool.true 91071763311 549755813888 23642790611 3435973836800 Bool.false

noncomputable abbrev qz643 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz269 qz279 qz643)

noncomputable abbrev qz356 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable def ep418 := @Enclosure.Complex.IsNear.of_eq qz642 (Complex.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 200546889345 1099511627776 127548418611 687194767360000 Bool.true 90209955825 1099511627776 127219588611 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 25 qz13 rfl)

noncomputable abbrev qz357 := (Real.sqrt (@Nat.cast Real Real.instNatCast 25))

noncomputable abbrev qz358 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz644 := (@HDiv.hDiv Real Real Real qz1 qz358 qz14)

noncomputable def ep419 := @Enclosure.Real.IsNear.inv_image qz357 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq qz357 (Real.sqrt qz644) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz644) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep420 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 160000 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep421 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz643 146530 1000 0 1 3624129903009015 1125899906842624 1562500001 250000000000000 10620875093758219359 22517998136852480 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz644) Bool.false 60802810194841294602240 18889465931478580854784 1000000000640000 160000000000000000000 3624129903009015 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep420 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep422 := nat_lit 678992247999495787538242706589351936

noncomputable def ep423 := BSN.cos_dyadic_bound_f 907749888 2147483648 2 1 1048576 320313 ep422 ep95 ep422 ep422 ep96 ep422 956283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 907749888) qz15 0 1 ep422 ep95 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 907749888) qz16 0 1 ep422 ep96 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 123643259) qz17)

noncomputable def ep424 := @Enclosure.Real.IsNear.cos_image qz66 qz359 Bool.false 123643259 262144 481 524288 Bool.false 956283 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 10620875093758219359 22517998136852480 22895312514653 25000000000000000 123643259 262144 481 524288 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 123643259 262144) (BSN.cos_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15969304926422824910848) qz286) 226375608064910080 72057594037927936 Bool.false 956283 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 123643259 262144 226375608064910080 72057594037927936 75 15969304926422824910848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956283 1048576 15969304926422824910848 37778931862957161709568 907749888 2147483648 320313 320000 (ep423 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep425 := BSN.sin_dyadic_bound_f 907749888 2147483648 2 1 1048576 320313 ep422 ep80 ep422 ep422 ep81 ep422 430155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 907749888) qz19 0 1 ep422 ep80 ep422 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 907749888) qz20 0 1 ep422 ep81 ep422 rfl rfl rfl rfl) rfl rfl

noncomputable def ep426 := @Enclosure.Real.IsNear.sin_image qz66 qz359 Bool.false 123643259 262144 481 524288 Bool.false 430155 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 10620875093758219359 22517998136852480 22895312514653 25000000000000000 123643259 262144 481 524288 (ep421 rfl) rfl) (Enclosure.sfrac_false_div 123643259 262144) (BSN.sin_reduce0 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15969304926422824910848) qz286) 226375608064910080 72057594037927936 Bool.false 430155 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 123643259 262144 226375608064910080 72057594037927936 75 15969304926422824910848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 430155 1048576 15969304926422824910848 37778931862957161709568 907749888 2147483648 320313 320000 (ep425 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25))) Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep419 rfl rfl) rfl)

noncomputable def ep427 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 200546889345 1099511627776 127548418611 687194767360000 Bool.true 90209955825 1099511627776 127219588611 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz356 (Real.cos qz66) 209715 1048576 1 1048576 956283 1048576 302673 327680000 200546889345 1099511627776 127548418611 687194767360000 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 956283 1048576 77484288 83886080000 956283 1048576 302673 327680000 (ep424 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz356 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 209715 1048576 1 1048576 430155 1048576 302673 327680000 90209955825 1099511627776 127219588611 687194767360000 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.false 430155 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.false 430155 1048576 77484288 83886080000 430155 1048576 302673 327680000 (ep426 rfl rfl) rfl)) rfl)

noncomputable def ep428 := @ep417 200546889345 1099511627776 127548418611 687194767360000 Bool.true 90209955825 1099511627776 127219588611 687194767360000 Bool.false 299188058046749523050496 1088439814509 1099511627776 4857479579561 687194767360000 Bool.true 149727910407881606823936 272353482447 1099511627776 4855777710811 687194767360000 EMLast.d8 (ep418 ep427) rfl rfl

noncomputable abbrev qz645 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz269 qz279 qz645)

noncomputable abbrev qz361 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable def ep429 := @Enclosure.Complex.IsNear.of_eq qz641 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 107122934631 549755813888 62504195787 343597383680000 Bool.false 24412086173 1099511627776 124431439699 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 26 qz13 rfl)

noncomputable abbrev qz362 := (Real.sqrt (@Nat.cast Real Real.instNatCast 26))

noncomputable abbrev qz363 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz646 := (@HDiv.hDiv Real Real Real qz1 qz363 qz14)

noncomputable def ep430 := @Enclosure.Real.IsNear.inv_image qz362 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq qz362 (Real.sqrt qz646) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz646) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep431 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 160000 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep432 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz645 146530 1000 0 1 3668288609262839 1125899906842624 1562500001 250000000000000 53751432991528379867 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz646) Bool.false 61543670347942250676224 18889465931478580854784 1000000000640000 160000000000000000000 3668288609262839 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep431 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep433 := nat_lit 6178914185852818943651503308078631906683349784343433279774110094526414480482560

noncomputable def ep434 := nat_lit 9202952433589829235558106452576853159419507514432590241249543724142706565376

noncomputable def ep435 := nat_lit 16167970468531570843182081253568435326674474994447529634255884319634854495396096

noncomputable def ep436 := BSN.sin_dyadic_bound_f 3129614874 2147483648 3 2 1048576 320313 ep433 ep64 ep434 ep435 ep66 ep434 1041834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3129614874) qz19 0 2 ep433 ep64 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3129614874) qz20 0 2 ep435 ep66 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz364 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 500599229) qz30)

noncomputable def ep437 := @Enclosure.Real.IsNear.cos_image qz67 qz364 Bool.false 500599229 1048576 961 1048576 Bool.false 1041834 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 53751432991528379867 112589990684262400 22895312514653 25000000000000000 500599229 1048576 961 1048576 (ep432 rfl) rfl) (Enclosure.sfrac_false_div 500599229 1048576) (BSN.cos_reduce3 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220227068475283968360448) qz31) 226375608064910080 72057594037927936 Bool.false 1041834 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 500599229 1048576 226375608064910080 72057594037927936 75 220227068475283968360448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1041834 1048576 220227068475283968360448 151115727451828646838272 3129614874 2147483648 320313 320000 (ep436 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep438 := nat_lit 3436820304333161559466638774022607438450491883530544084426172071947627025408256

noncomputable def ep439 := nat_lit 10292055008132305019928800109162668609032636635562767072796017128394595663094016

noncomputable def ep440 := BSN.cos_dyadic_bound_f 3129614874 2147483648 3 2 1048576 320313 ep438 ep57 ep434 ep439 ep60 ep434 118711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3129614874) qz15 0 2 ep438 ep57 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3129614874) qz16 0 2 ep439 ep60 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable def ep441 := @Enclosure.Real.IsNear.sin_image qz67 qz364 Bool.false 500599229 1048576 961 1048576 Bool.true 118711 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 53751432991528379867 112589990684262400 22895312514653 25000000000000000 500599229 1048576 961 1048576 (ep432 rfl) rfl) (Enclosure.sfrac_false_div 500599229 1048576) (BSN.sin_reduce3 qz364 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220227068475283968360448) qz31) 226375608064910080 72057594037927936 Bool.false 118711 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 500599229 1048576 226375608064910080 72057594037927936 75 220227068475283968360448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 118711 1048576 220227068475283968360448 151115727451828646838272 3129614874 2147483648 320313 320000 (ep440 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz365 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26))) Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep430 rfl rfl) rfl)

noncomputable def ep442 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 107122934631 549755813888 62504195787 343597383680000 Bool.false 24412086173 1099511627776 124431439699 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz361 (Real.cos qz67) 205643 1048576 1 1048576 520917 524288 604721 655360000 107122934631 549755813888 62504195787 343597383680000 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 1041834 1048576 154808576 167772160000 520917 524288 604721 655360000 (ep437 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 205643 1048576 1 1048576 118711 1048576 604721 655360000 24412086173 1099511627776 124431439699 687194767360000 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 118711 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 118711 1048576 154808576 167772160000 118711 1048576 604721 655360000 (ep441 rfl rfl) rfl)) rfl)

noncomputable def ep443 := @ep415 107122934631 549755813888 62504195787 343597383680000 Bool.false 24412086173 1099511627776 124431439699 687194767360000 Bool.false 716159028321771898011648 1302685683771 1099511627776 996497594227 137438953472000 Bool.true 272614448210280001306624 123970698137 549755813888 498020915051 68719476736000 (ep416 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep428 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep429 ep442) rfl rfl

noncomputable abbrev qz647 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz269 qz279 qz647)

noncomputable abbrev qz366 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable def ep444 := @Enclosure.Complex.IsNear.of_eq qz640 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.false 68506119123 549755813888 2451663381 13743895347200 Bool.false 80626974259 549755813888 2453164981 13743895347200 (BSN.cpow_neg_s_mk qz12 146530 1000 27 qz13 rfl)

noncomputable abbrev qz367 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27))

noncomputable abbrev qz368 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz648 := (@HDiv.hDiv Real Real Real qz1 qz368 qz14)

noncomputable def ep445 := @Enclosure.Real.IsNear.inv_image qz367 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq qz367 (Real.sqrt qz648) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz648) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep446 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 160000 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep447 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz647 146530 1000 0 1 3710780868205815 1125899906842624 1562500001 250000000000000 10874814412363961439 22517998136852480 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz648) Bool.false 62256572154556490711040 18889465931478580854784 1000000000640000 160000000000000000000 3710780868205815 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep446 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep448 := nat_lit 5233018378836350531447434356979434561

noncomputable def ep449 := BSN.sin_dyadic_bound_f 1512474513 2147483648 2 1 1048576 320313 ep448 ep80 ep448 ep448 ep81 ep448 678954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1512474513) qz19 0 1 ep448 ep80 ep448 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1512474513) qz20 0 1 ep448 ep81 ep448 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 506398007) qz30)

noncomputable def ep450 := @Enclosure.Real.IsNear.cos_image qz68 qz369 Bool.false 506398007 1048576 481 524288 Bool.false 678954 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 10874814412363961439 22517998136852480 22895312514653 25000000000000000 506398007 1048576 481 524288 (ep447 rfl) rfl) (Enclosure.sfrac_false_div 506398007 1048576) (BSN.cos_reduce3 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106430932146334721900544) qz31) 226375608064910080 72057594037927936 Bool.false 678954 1048576 76 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 506398007 1048576 226375608064910080 72057594037927936 76 106430932146334721900544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 678954 1048576 106430932146334721900544 151115727451828646838272 1512474513 2147483648 320313 320000 (ep449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep451 := nat_lit 187001291890929826052668780577832126239787348116168809076612733535093346998401

noncomputable def ep452 := nat_lit 27384481353239026287728464073496393136817708922149803863049647491281262721

noncomputable def ep453 := nat_lit 560949106710083000105430884805349385933088408930662127622112101310297478469761

noncomputable def ep454 := BSN.cos_dyadic_bound_f 1512474513 2147483648 3 2 1048576 320313 ep451 ep57 ep452 ep453 ep60 ep452 799082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1512474513) qz15 0 2 ep451 ep57 ep452 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1512474513) qz16 0 2 ep453 ep60 ep452 rfl rfl rfl rfl) rfl rfl

noncomputable def ep455 := @Enclosure.Real.IsNear.sin_image qz68 qz369 Bool.false 506398007 1048576 481 524288 Bool.true 799082 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 10874814412363961439 22517998136852480 22895312514653 25000000000000000 506398007 1048576 481 524288 (ep447 rfl) rfl) (Enclosure.sfrac_false_div 506398007 1048576) (BSN.sin_reduce3 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106430932146334721900544) qz31) 226375608064910080 72057594037927936 Bool.false 799082 1048576 76 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 506398007 1048576 226375608064910080 72057594037927936 76 106430932146334721900544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 799082 1048576 106430932146334721900544 151115727451828646838272 1512474513 2147483648 320313 320000 (ep454 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz370 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27))) Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep445 rfl rfl) rfl)

noncomputable def ep456 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.false 68506119123 549755813888 2451663381 13743895347200 Bool.false 80626974259 549755813888 2453164981 13743895347200 (@Enclosure.Real.IsNear.mulLit_ff qz366 (Real.cos qz68) 201799 1048576 1 1048576 339477 524288 302673 327680000 68506119123 549755813888 2451663381 13743895347200 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.false 678954 1048576 77484288 83886080000 339477 524288 302673 327680000 (ep450 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz366 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 201799 1048576 1 1048576 399541 524288 302673 327680000 80626974259 549755813888 2453164981 13743895347200 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.true 399541 524288 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.true 799082 1048576 77484288 83886080000 399541 524288 302673 327680000 (ep455 rfl rfl) rfl)) rfl)

noncomputable def ep457 := @ep413 68506119123 549755813888 2451663381 13743895347200 Bool.false 80626974259 549755813888 2453164981 13743895347200 Bool.false 791482302871318189572096 1439697922017 1099511627776 1021014228037 137438953472000 Bool.true 23828464197486629617664 21671861939 274877906944 127571684989 17179869184000 (ep414 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep443 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep444 ep456) rfl rfl

noncomputable abbrev qz649 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz269 qz279 qz649)

noncomputable abbrev qz371 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable def ep458 := @Enclosure.Complex.IsNear.of_eq qz639 (Complex.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.true 12850276061 274877906944 30029975561 171798691840000 Bool.false 100665416859 549755813888 60296387997 343597383680000 (BSN.cpow_neg_s_mk qz12 146530 1000 28 qz13 rfl)

noncomputable abbrev qz372 := (Real.sqrt (@Nat.cast Real Real.instNatCast 28))

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz650 := (@HDiv.hDiv Real Real Real qz1 qz373 qz14)

noncomputable def ep459 := @Enclosure.Real.IsNear.inv_image qz372 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq qz372 (Real.sqrt qz650) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz650) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep460 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 160000 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep461 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz649 146530 1000 0 1 3751726938922231 1125899906842624 1562500001 250000000000000 54974054836027450843 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz650) Bool.false 62943533227317076688896 18889465931478580854784 1000000000640000 160000000000000000000 3751726938922231 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep460 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep462 := nat_lit 2316973868087800559175285204095533687112182619197886886985828941846894575190625

noncomputable def ep463 := nat_lit 4189986424168304813906685506214838615911638591101563783892334786153250390625

noncomputable def ep464 := nat_lit 6942541631415065067898042241274171384104724580411457533389702155968377224790625

noncomputable def ep465 := BSN.cos_dyadic_bound_f 2836459435 2147483648 3 2 1048576 320313 ep462 ep57 ep463 ep464 ep60 ep463 259388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2836459435) qz15 0 2 ep462 ep57 ep463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2836459435) qz16 0 2 ep464 ep60 ep463 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 255992891) qz24)

noncomputable def ep466 := @Enclosure.Real.IsNear.cos_image qz69 qz374 Bool.false 255992891 524288 481 524288 Bool.true 259388 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 54974054836027450843 112589990684262400 22895312514653 25000000000000000 255992891 524288 481 524288 (ep461 rfl) rfl) (Enclosure.sfrac_false_div 255992891 524288) (BSN.cos_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99799044195043405463552) qz25) 226375608064910080 72057594037927936 Bool.false 259388 1048576 77 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 255992891 524288 226375608064910080 72057594037927936 77 99799044195043405463552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 259388 1048576 99799044195043405463552 75557863725914323419136 2836459435 2147483648 320313 320000 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep467 := nat_lit 4167200973418706362664388018966988765909199403683315145547378227495487635030625

noncomputable def ep468 := nat_lit 10907313999981291789660405415998717981526903404308803801735879196643933781590625

noncomputable def ep469 := BSN.sin_dyadic_bound_f 2836459435 2147483648 3 2 1048576 320313 ep467 ep64 ep463 ep468 ep66 ep463 1015986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2836459435) qz19 0 2 ep467 ep64 ep463 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2836459435) qz20 0 2 ep468 ep66 ep463 rfl rfl rfl rfl) rfl rfl

noncomputable def ep470 := @Enclosure.Real.IsNear.sin_image qz69 qz374 Bool.false 255992891 524288 481 524288 Bool.true 1015986 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 54974054836027450843 112589990684262400 22895312514653 25000000000000000 255992891 524288 481 524288 (ep461 rfl) rfl) (Enclosure.sfrac_false_div 255992891 524288) (BSN.sin_reduce2 qz374 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99799044195043405463552) qz25) 226375608064910080 72057594037927936 Bool.false 1015986 1048576 77 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 255992891 524288 226375608064910080 72057594037927936 77 99799044195043405463552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1015986 1048576 99799044195043405463552 75557863725914323419136 2836459435 2147483648 320313 320000 (ep469 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz375 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28))) Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep459 rfl rfl) rfl)

noncomputable def ep471 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.true 12850276061 274877906944 30029975561 171798691840000 Bool.false 100665416859 549755813888 60296387997 343597383680000 (@Enclosure.Real.IsNear.mulLit_ft qz371 (Real.cos qz69) 198163 1048576 1 1048576 64847 262144 302673 327680000 12850276061 274877906944 30029975561 171798691840000 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.true 259388 1048576 77484288 83886080000 64847 262144 302673 327680000 (ep466 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz371 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 198163 1048576 1 1048576 507993 524288 302673 327680000 100665416859 549755813888 60296387997 343597383680000 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 507993 524288 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 1015986 1048576 77484288 83886080000 507993 524288 302673 327680000 (ep470 rfl rfl) rfl)) rfl)

noncomputable def ep472 := @ep411 12850276061 274877906944 30029975561 171798691840000 Bool.false 100665416859 549755813888 60296387997 343597383680000 Bool.false 381612123486458019315712 1388296817773 1099511627776 5225191042429 687194767360000 Bool.false 15756466989103855960064 57321692981 549755813888 2611730087777 343597383680000 (ep412 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep457 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep458 ep471) rfl rfl

noncomputable abbrev qz651 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz269 qz279 qz651)

noncomputable abbrev qz376 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep473 := @Enclosure.Complex.IsNear.of_eq qz638 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.true 6277806315 34359738368 14814421467 85899345920000 Bool.false 9117529875 274877906944 29496903559 171798691840000 (BSN.cpow_neg_s_mk qz12 146530 1000 29 qz13 rfl)

noncomputable abbrev qz377 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz378 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz652 := (@HDiv.hDiv Real Real Real qz1 qz378 qz14)

noncomputable def ep474 := @Enclosure.Real.IsNear.inv_image qz377 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz377 (Real.sqrt qz652) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz652) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep475 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 160000 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz651 146530 1000 0 1 3791236343078135 1125899906842624 1562500001 250000000000000 11110597227024782431 22517998136852480 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 63606391034871975772160 18889465931478580854784 1000000000640000 160000000000000000000 3791236343078135 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep475 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep477 := nat_lit 22121739100106367237280624215900625

noncomputable def ep478 := BSN.cos_dyadic_bound_f 385660195 2147483648 2 1 1048576 320313 ep477 ep95 ep477 ep477 ep96 ep477 1031712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 385660195) qz15 0 1 ep477 ep95 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 385660195) qz16 0 1 ep477 ep96 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 129344375) qz17)

noncomputable def ep479 := @Enclosure.Real.IsNear.cos_image qz70 qz379 Bool.false 129344375 262144 481 524288 Bool.true 1031712 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 11110597227024782431 22517998136852480 22895312514653 25000000000000000 129344375 262144 481 524288 (ep476 rfl) rfl) (Enclosure.sfrac_false_div 129344375 262144) (BSN.cos_reduce2 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6784605900744918302720) qz286) 226375608064910080 72057594037927936 Bool.false 1031712 1048576 78 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 129344375 262144 226375608064910080 72057594037927936 78 6784605900744918302720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1031712 1048576 6784605900744918302720 37778931862957161709568 385660195 2147483648 320313 320000 (ep478 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep480 := BSN.sin_dyadic_bound_f 385660195 2147483648 2 1 1048576 320313 ep477 ep80 ep477 ep477 ep81 ep477 187300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 385660195) qz19 0 1 ep477 ep80 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 385660195) qz20 0 1 ep477 ep81 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable def ep481 := @Enclosure.Real.IsNear.sin_image qz70 qz379 Bool.false 129344375 262144 481 524288 Bool.true 187300 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 11110597227024782431 22517998136852480 22895312514653 25000000000000000 129344375 262144 481 524288 (ep476 rfl) rfl) (Enclosure.sfrac_false_div 129344375 262144) (BSN.sin_reduce2 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6784605900744918302720) qz286) 226375608064910080 72057594037927936 Bool.false 187300 1048576 78 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 129344375 262144 226375608064910080 72057594037927936 78 6784605900744918302720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 187300 1048576 6784605900744918302720 37778931862957161709568 385660195 2147483648 320313 320000 (ep480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz380 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep474 rfl rfl) rfl)

noncomputable def ep482 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.true 6277806315 34359738368 14814421467 85899345920000 Bool.false 9117529875 274877906944 29496903559 171798691840000 (@Enclosure.Real.IsNear.mulLit_ft qz376 (Real.cos qz70) 194715 1048576 1 1048576 32241 32768 302673 327680000 6277806315 34359738368 14814421467 85899345920000 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.true 1031712 1048576 77484288 83886080000 32241 32768 302673 327680000 (ep479 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz376 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 194715 1048576 1 1048576 46825 262144 302673 327680000 9117529875 274877906944 29496903559 171798691840000 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 46825 262144 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 187300 1048576 77484288 83886080000 46825 262144 302673 327680000 (ep481 rfl rfl) rfl)) rfl)

noncomputable def ep483 := @ep409 6277806315 34359738368 14814421467 85899345920000 Bool.false 9117529875 274877906944 29496903559 171798691840000 Bool.false 40798994395539150209024 1187407015693 1099511627776 1068741282833 137438953472000 Bool.false 20768882046182635864064 75556752731 549755813888 534144778979 68719476736000 (ep410 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep472 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep473 ep482) rfl rfl

noncomputable abbrev qz653 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz269 qz279 qz653)

noncomputable abbrev qz381 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq qz637 (Complex.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 21137030187 274877906944 14505778703 85899345920000 Bool.true 182068993505 1099511627776 116364603999 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 30 qz13 rfl)

noncomputable abbrev qz382 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz383 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz654 := (@HDiv.hDiv Real Real Real qz1 qz383 qz14)

noncomputable def ep485 := @Enclosure.Real.IsNear.inv_image qz382 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz382 (Real.sqrt qz654) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz654) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep486 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 160000 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz653 146530 1000 0 1 3829405717437687 1125899906842624 1562500001 250000000000000 56112281977614427611 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz654) Bool.false 64246766873087041339392 18889465931478580854784 1000000000640000 160000000000000000000 3829405717437687 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep488 := nat_lit 759717373309820352356406630002770176

noncomputable def ep489 := BSN.sin_dyadic_bound_f 933604668 2147483648 2 1 1048576 320313 ep488 ep80 ep488 ep488 ep81 ep488 441636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 933604668) qz19 0 1 ep488 ep80 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 933604668) qz20 0 1 ep488 ep81 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz384 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 522586349) qz30)

noncomputable def ep490 := @Enclosure.Real.IsNear.cos_image qz71 qz384 Bool.false 522586349 1048576 961 1048576 Bool.true 441636 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 56112281977614427611 112589990684262400 22895312514653 25000000000000000 522586349 1048576 961 1048576 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 522586349 1048576) (BSN.cos_reduce1 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65696588089900000083968) qz31) 226375608064910080 72057594037927936 Bool.false 441636 1048576 79 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 522586349 1048576 226375608064910080 72057594037927936 79 65696588089900000083968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441636 1048576 65696588089900000083968 151115727451828646838272 933604668 2147483648 320313 320000 (ep489 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep491 := BSN.cos_dyadic_bound_f 933604668 2147483648 2 1 1048576 320313 ep488 ep95 ep488 ep488 ep96 ep488 951035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 933604668) qz15 0 1 ep488 ep95 ep488 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 933604668) qz16 0 1 ep488 ep96 ep488 rfl rfl rfl rfl) rfl rfl

noncomputable def ep492 := @Enclosure.Real.IsNear.sin_image qz71 qz384 Bool.false 522586349 1048576 961 1048576 Bool.false 951035 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 56112281977614427611 112589990684262400 22895312514653 25000000000000000 522586349 1048576 961 1048576 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 522586349 1048576) (BSN.sin_reduce1 qz384 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65696588089900000083968) qz31) 226375608064910080 72057594037927936 Bool.false 951035 1048576 79 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 522586349 1048576 226375608064910080 72057594037927936 79 65696588089900000083968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 951035 1048576 65696588089900000083968 151115727451828646838272 933604668 2147483648 320313 320000 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz385 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep485 rfl rfl) rfl)

noncomputable def ep493 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 21137030187 274877906944 14505778703 85899345920000 Bool.true 182068993505 1099511627776 116364603999 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz381 (Real.cos qz71) 191443 1048576 1 1048576 110409 262144 604721 655360000 21137030187 274877906944 14505778703 85899345920000 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 441636 1048576 154808576 167772160000 110409 262144 604721 655360000 (ep490 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz381 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 191443 1048576 1 1048576 951035 1048576 604721 655360000 182068993505 1099511627776 116364603999 687194767360000 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 951035 1048576 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 951035 1048576 154808576 167772160000 951035 1048576 604721 655360000 (ep492 rfl rfl) rfl)) rfl)

noncomputable def ep494 := @ep407 21137030187 274877906944 14505778703 85899345920000 Bool.true 182068993505 1099511627776 116364603999 687194767360000 Bool.false 303151544697054381998080 1102858894945 1099511627776 5459752643789 687194767360000 Bool.true 17017959523379717341184 30955488043 1099511627776 5457812393789 687194767360000 (ep408 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep483 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep484 ep493) rfl rfl

noncomputable abbrev qz655 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz72 := (@HMul.hMul Real Real Real qz269 qz279 qz655)

noncomputable abbrev qz386 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep495 := @Enclosure.Complex.IsNear.of_eq qz636 (Complex.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72)))) Bool.false 85329798281 549755813888 11457117343 68719476736000 Bool.true 49680248555 549755813888 11433455593 68719476736000 (BSN.cpow_neg_s_mk qz12 146530 1000 31 qz13 rfl)

noncomputable abbrev qz387 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz388 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz656 := (@HDiv.hDiv Real Real Real qz1 qz388 qz14)

noncomputable def ep496 := @Enclosure.Real.IsNear.inv_image qz387 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz387 (Real.sqrt qz656) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz656) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep497 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 160000 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep498 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz655 146530 1000 0 1 3866325256314103 1125899906842624 1562500001 250000000000000 56653263980770551259 112589990684262400 22895312514653 25000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz656) Bool.false 64866173951437069877248 18889465931478580854784 1000000000640000 160000000000000000000 3866325256314103 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep499 := nat_lit 1643429811648113181499110220161125136

noncomputable def ep500 := BSN.cos_dyadic_bound_f 1132238166 2147483648 2 1 1048576 320313 ep499 ep95 ep499 ep499 ep96 ep499 906178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1132238166) qz15 0 1 ep499 ep95 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1132238166) qz16 0 1 ep499 ep96 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz389 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131906159) qz17)

noncomputable def ep501 := @Enclosure.Real.IsNear.cos_image qz72 qz389 Bool.false 131906159 262144 481 524288 Bool.false 906178 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 56653263980770551259 112589990684262400 22895312514653 25000000000000000 131906159 262144 481 524288 (ep498 rfl) rfl) (Enclosure.sfrac_false_div 131906159 262144) (BSN.cos_reduce0 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19918544467056549429248) qz286) 226375608064910080 72057594037927936 Bool.false 906178 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 131906159 262144 226375608064910080 72057594037927936 80 19918544467056549429248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 906178 1048576 19918544467056549429248 37778931862957161709568 1132238166 2147483648 320313 320000 (ep500 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep502 := BSN.sin_dyadic_bound_f 1132238166 2147483648 2 1 1048576 320313 ep499 ep80 ep499 ep499 ep81 ep499 527590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1132238166) qz19 0 1 ep499 ep80 ep499 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1132238166) qz20 0 1 ep499 ep81 ep499 rfl rfl rfl rfl) rfl rfl

noncomputable def ep503 := @Enclosure.Real.IsNear.sin_image qz72 qz389 Bool.false 131906159 262144 481 524288 Bool.false 527590 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 56653263980770551259 112589990684262400 22895312514653 25000000000000000 131906159 262144 481 524288 (ep498 rfl) rfl) (Enclosure.sfrac_false_div 131906159 262144) (BSN.sin_reduce0 qz389 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19918544467056549429248) qz286) 226375608064910080 72057594037927936 Bool.false 527590 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 131906159 262144 226375608064910080 72057594037927936 80 19918544467056549429248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 527590 1048576 19918544467056549429248 37778931862957161709568 1132238166 2147483648 320313 320000 (ep502 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz390 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep496 rfl rfl) rfl)

noncomputable def ep504 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz72)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72))) Bool.false 85329798281 549755813888 11457117343 68719476736000 Bool.true 49680248555 549755813888 11433455593 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz386 (Real.cos qz72) 188329 1048576 1 1048576 453089 524288 302673 327680000 85329798281 549755813888 11457117343 68719476736000 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz72) Bool.false 906178 1048576 77484288 83886080000 453089 524288 302673 327680000 (ep501 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz386 (@Neg.neg Real Real.instNeg (Real.sin qz72)) 188329 1048576 1 1048576 263795 524288 302673 327680000 49680248555 549755813888 11433455593 68719476736000 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz72) Bool.false 263795 524288 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz72) Bool.false 527590 1048576 77484288 83886080000 263795 524288 302673 327680000 (ep503 rfl rfl) rfl)) rfl)

noncomputable def ep505 := @ep405 85329798281 549755813888 11457117343 68719476736000 Bool.true 49680248555 549755813888 11433455593 68719476736000 Bool.false 700124194799848800649216 1273518491507 1099511627776 5574323817219 687194767360000 Bool.true 71641970480404039204864 130315985153 1099511627776 5572146949719 687194767360000 (ep406 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep494 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep495 ep504) rfl rfl

noncomputable abbrev qz657 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz269 qz279 qz657)

noncomputable abbrev qz391 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep506 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.false 43758828773 549755813888 56252222347 343597383680000 Bool.false 173548889195 1099511627776 112794521569 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 32 qz13 rfl)

noncomputable abbrev qz392 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz393 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz658 := (@HDiv.hDiv Real Real Real qz1 qz393 qz14)

noncomputable def ep507 := @Enclosure.Real.IsNear.inv_image qz392 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz392 (Real.sqrt qz658) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz658) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep508 := BSN.log_dyadic_bound 0 64 1 0 1 524288 160000 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz657 146530 1000 0 1 15608286920413395 4503599627370496 1250000001 200000000000000 45741645648963495387 90071992547409920 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz658) Bool.false 65465900263437584302080 18889465931478580854784 1000000000800000 160000000000000000000 15608286920413395 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep508 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep510 := nat_lit 1012133343245449818318708148559097921

noncomputable def ep511 := BSN.sin_dyadic_bound_f 1003019631 2147483648 2 1 1048576 320313 ep510 ep80 ep510 ep510 ep81 ep510 472142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1003019631) qz19 0 1 ep510 ep80 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1003019631) qz20 0 1 ep510 ep81 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 532502839) qz30)

noncomputable def ep512 := @Enclosure.Real.IsNear.cos_image qz73 qz394 Bool.false 532502839 1048576 481 524288 Bool.false 472142 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 45741645648963495387 90071992547409920 18316250014653 20000000000000000 532502839 1048576 481 524288 (ep509 rfl) rfl) (Enclosure.sfrac_false_div 532502839 1048576) (BSN.cos_reduce3 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70581231878617083936768) qz31) 226375608064910080 72057594037927936 Bool.false 472142 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 532502839 1048576 226375608064910080 72057594037927936 80 70581231878617083936768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 472142 1048576 70581231878617083936768 151115727451828646838272 1003019631 2147483648 320313 320000 (ep511 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep513 := BSN.cos_dyadic_bound_f 1003019631 2147483648 2 1 1048576 320313 ep510 ep95 ep510 ep510 ep96 ep510 936265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1003019631) qz15 0 1 ep510 ep95 ep510 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1003019631) qz16 0 1 ep510 ep96 ep510 rfl rfl rfl rfl) rfl rfl

noncomputable def ep514 := @Enclosure.Real.IsNear.sin_image qz73 qz394 Bool.false 532502839 1048576 481 524288 Bool.true 936265 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 45741645648963495387 90071992547409920 18316250014653 20000000000000000 532502839 1048576 481 524288 (ep509 rfl) rfl) (Enclosure.sfrac_false_div 532502839 1048576) (BSN.sin_reduce3 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70581231878617083936768) qz31) 226375608064910080 72057594037927936 Bool.false 936265 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 532502839 1048576 226375608064910080 72057594037927936 80 70581231878617083936768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 936265 1048576 70581231878617083936768 151115727451828646838272 1003019631 2147483648 320313 320000 (ep513 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz395 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep507 rfl rfl) rfl)

noncomputable def ep515 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.false 43758828773 549755813888 56252222347 343597383680000 Bool.false 173548889195 1099511627776 112794521569 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz391 (Real.cos qz73) 185363 1048576 1 1048576 236071 524288 302673 327680000 43758828773 549755813888 56252222347 343597383680000 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.false 472142 1048576 77484288 83886080000 236071 524288 302673 327680000 (ep512 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz391 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 185363 1048576 1 1048576 936265 1048576 302673 327680000 173548889195 1099511627776 112794521569 687194767360000 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.true 936265 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.true 936265 1048576 77484288 83886080000 936265 1048576 302673 327680000 (ep514 rfl rfl) rfl)) rfl)

noncomputable def ep516 := @ep403 43758828773 549755813888 56252222347 343597383680000 Bool.false 173548889195 1099511627776 112794521569 687194767360000 Bool.false 748237535853621295448064 1361036149053 1099511627776 5686828261913 687194767360000 Bool.false 47535080696703029870592 21616452021 549755813888 710617683911 85899345920000 (ep404 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep505 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep506 ep515) rfl rfl

theorem EMLast.d9 : Enclosure.Complex.IsNear qz65 Bool.false 1361036149053 1099511627776 5686828261913 687194767360000 Bool.false 21616452021 549755813888 710617683911 85899345920000 := ep402 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep516 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMLast.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMLast.d11 : @Eq Nat (Nat.pow 37 1) 37 := @Eq.refl Nat 37

noncomputable def ep517 := nat_lit 813379634825211858382809089863

noncomputable def ep518 := nat_lit 732739505104267325983047024640

noncomputable def ep519 := nat_lit 40636123188114876326372759262397379

noncomputable def ep520 := nat_lit 4293395537720316363181916160000000000

noncomputable abbrev qz747 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz659 := qz747

noncomputable abbrev qz396 := qz659

noncomputable abbrev qz74 := qz396

noncomputable abbrev qz660 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz397 := qz660

noncomputable abbrev qz75 := qz397

noncomputable abbrev qz748 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz749 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz661 := (@HAdd.hAdd Complex Complex Complex qz745 (@HAdd.hAdd Complex Complex Complex qz745 qz748 (@HMul.hMul Complex Complex Complex qz747 Complex.I (@HDiv.hDiv Complex Complex Complex qz749 (↑qz746) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz398 := qz661

noncomputable abbrev qz76 := (Complex.Stirling.logGammaStirling 1 qz398)

noncomputable abbrev qz662 := (@HAdd.hAdd Complex Complex Complex qz745 qz748 (@HMul.hMul Complex Complex Complex qz747 Complex.I (@HDiv.hDiv Complex Complex Complex qz749 (↑qz746) (2 : Complex))))

noncomputable abbrev qz399 := qz662

noncomputable abbrev qz77 := qz399

noncomputable abbrev qz78 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz400 := (@instHSub Real Real.instSub)

noncomputable def ep521 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78))) (zetaApproximant qz5 1 37))

noncomputable def ep522 := @Enclosure.Real.IsNear.of_eq ep521 (@HSub.hSub Real Real Real qz400 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 37))))

noncomputable def ep523 := nat_lit 162675822980111298971211923055

noncomputable def ep524 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 37))) ep523

noncomputable def ep525 := nat_lit 146547901020853465196609404928

noncomputable def ep526 := nat_lit 13535403755548045408698742485420709

noncomputable def ep527 := nat_lit 1431131845906772121060638720000000000

noncomputable def ep528 := nat_lit 183184876276066831495761756160

noncomputable def ep529 := nat_lit 7477980367685025069132951533813

noncomputable def ep530 := nat_lit 1073348884430079090795479040000000000

noncomputable def ep531 := nat_lit 29799769554185770908192087298263185572078257219498426761216

noncomputable def ep532 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.re (zetaApproximant qz5 1 37)) 1048575 1048576 270971

noncomputable def ep533 := nat_lit 59019835019777540096000000

noncomputable def ep534 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.false 1048575 1048576 69368576

noncomputable abbrev qz663 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82355059) qz24)

noncomputable def ep535 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz663 Bool.false 82355059 524288 427

noncomputable def ep536 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) Bool.false 8489094876703497571 54043195528445952 127616060112945146777 314572800000000000000000

noncomputable def ep537 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78 325540571151023136427 1351079888211148800 39698060112945146777 314572800000000000000000 1099282713 13107200

noncomputable def ep538 := nat_lit 2781706609198202084065280000

noncomputable def ep539 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25949511650172715531 225179981368524800 12460939891918605391 52428800000000000000000 Bool.false 325540571151023136427 1351079888211148800

noncomputable def ep540 := @Enclosure.Complex.IsNear.subLitP qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 24015594719242084131 225179981368524800 12297099891289459791 52428800000000000000000 Bool.false 329757455071847419627 1351079888211148800 37731980112630573977

noncomputable def ep541 := nat_lit 29216552749541046604832774337593344

noncomputable def ep542 := nat_lit 91631524683107889833136048792666112

noncomputable abbrev qz750 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz664 := qz750

noncomputable abbrev qz401 := (@HSub.hSub Complex Complex Complex qz660 qz661 qz664)

noncomputable abbrev qz402 := (Complex.log qz661)

noncomputable abbrev qz79 := (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 qz401 qz402) qz398)

noncomputable abbrev qz403 := qz664

noncomputable abbrev qz80 := (@HMul.hMul Complex Complex Complex qz396 qz403 ↑(Real.log (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)))

noncomputable abbrev qz665 := qz749

noncomputable abbrev qz404 := qz665

noncomputable abbrev qz81 := qz404

noncomputable abbrev qz82 := (@instHMul Nat instMulNat)

noncomputable abbrev qz666 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz405 := qz666

noncomputable abbrev qz83 := qz405

noncomputable abbrev qz84 := qz398

noncomputable abbrev qz85 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz86 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz406 := (@instHSub Int Int.instSub)

noncomputable abbrev qz407 := (@instHMul Int Int.instMul)

noncomputable def ep543 := @Enclosure.Complex.IsNear.of_eq qz76 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 24015594719242084131

noncomputable def ep544 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz79 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 24015602577536048931 225179981368524800

noncomputable def ep545 := nat_lit 1650339102610160851992409276416

noncomputable def ep546 := nat_lit 1133037988116619198079962814873600

noncomputable def ep547 := @ep544 187638818397081 800000000000000000 Bool.false 109919663457644545273 450359962737049600 23989062588093 200000000000000000 Bool.false 2398161 68719476736 3 68719476736 Bool.true 11713417711 10307921510400 14653 10307921510400 Bool.true ep545 24015594719242084131 225179981368524800 12297099891289459791 52428800000000000000000 Bool.false ep546

noncomputable def ep548 := @Enclosure.Complex.IsNear.addLitP qz79 qz80 Bool.true 24222528947896573731 225179981368524800 92675000018853 400000000000000000

noncomputable def ep549 := nat_lit 3147773061042805005484032

noncomputable def ep550 := @ep548 Bool.false 109919663457644545273 450359962737049600 23989062588093 200000000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true ep549 24015602577536048931 225179981368524800 187638818397081 800000000000000000 Bool.false 109919663457644545273 109919663457644545273 450359962737049600

noncomputable abbrev qz87 := (@HMul.hMul Complex Complex Complex qz396 qz401 qz402)

noncomputable def ep551 := @Enclosure.Complex.IsNear.subLitP qz87 qz84 Bool.true 23715873989817392931 225179981368524800 92675000018853 400000000000000000 Bool.false 142915286127574484217

noncomputable def ep552 := @ep551 450359962737049600 23989062588093 200000000000000000 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 Bool.true 96890115791586294924000 24222528947896573731 225179981368524800 92675000018853 400000000000000000 Bool.false 439678653830578181092000 109919663457644545273 450359962737049600 23989062588093 200000000000000000

noncomputable abbrev qz88 := qz401

noncomputable abbrev qz89 := qz402

noncomputable def ep553 := @Enclosure.Complex.IsNear.mul qz88 qz89 Bool.true 23715873989817392931 225179981368524800 92675000018853 400000000000000000 Bool.false 142915286127574484217 450359962737049600 23989062588093

noncomputable abbrev qz90 := (Complex.re qz401)

noncomputable abbrev qz91 := (Complex.re qz402)

noncomputable abbrev qz92 := (Complex.im qz401)

noncomputable abbrev qz93 := (Complex.im qz402)

noncomputable def ep554 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz90 qz91) (@HMul.hMul Real Real Real qz0 qz92 qz93) 67693334780665923 9007199254740992 5468750021 2000000000000000 12704103679667020503 112589990684262400

noncomputable def ep555 := nat_lit 106806801263307249051895421548363776

noncomputable def ep556 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 7000 4000 0 1 9670476397237989 2251799813685248 781250003 500000000000000

noncomputable def ep557 := @Enclosure.Complex.IsNear.re_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable abbrev qz667 := (Enclosure.sfrac Bool.false 293060 4000)

noncomputable abbrev qz408 := qz667

noncomputable def ep558 := @Enclosure.Complex.IsNear.of_eq qz88 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz408) Bool.false 7000 4000 0 1 Bool.false 293060 4000 0

noncomputable abbrev qz668 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz409 := (Complex.log (Complex.mk qz668 qz667))

noncomputable def ep559 := @Enclosure.Complex.IsNear.of_eq qz89 qz409 Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000

noncomputable def ep560 := nat_lit 1269653194440197434919221656422111334666844934826288353280000000000000

noncomputable def ep561 := nat_lit 7780480299006913012299851812511533026174033932029587456000000000000

noncomputable def ep562 := nat_lit 1090422431871862388851262689736955396133030750679040000000000000

noncomputable def ep563 := BSN.log_dyadic_bound 20429163600 151501163600 4 3 ep560 1048576 320000 ep561 ep562 284523 171930327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20429163600) (BSN.artanhQ 151501163600) 0 3 ep561 ep560 ep562 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz94 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz410 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz669 := (Real.log (Enclosure.sfrac Bool.false 85965163600 16000000))

noncomputable abbrev qz670 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep564 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz669 1 2 0 1 9670476397237989 1125899906842624 781250003 250000000000000 9670476397237989 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 85965163600 16000000 9670476397237989 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85965163600) qz670)) Bool.false 324487342678727089717248 37778931862957161709568 1000000003840000 320000000000000000000 9670476397237989 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 85965163600 16000000 12 171930327200 131072000000 284523 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep563 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep565 := BSN.arctan_dyadic_bound_f 9000 293060 1 0 1048576 320000 0 1 1 0 1 1 32192 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz95 := (@HMul.hMul Real Real Real qz269 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz96 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz410 BSN.pi_near_15 rfl)

noncomputable abbrev qz411 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 293060)))

noncomputable def ep566 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz411 884279719003555 562949953421312 1 2000000000000000 32192 1048576 1 320000 909112005733332811776 866996770604451 562949953421312 6250000001 2000000000000000 qz96 (ep565 rfl) rfl rfl

noncomputable abbrev qz412 := (Complex.mk qz668 qz667)

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293060) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep567 := @Enclosure.Complex.IsNear.re_isNear qz89 Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (ep559 (@congrArg Complex Complex qz84 qz412 Complex.log (BSN.w_shift_mk qz12 Bool.false 146530 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz409 Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz409) (@HMul.hMul Real Real Real qz0 qz94 qz669) Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 9000 293060 4000 85965163600 16000000 rfl rfl rfl) (ep564 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz409) qz413 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 9000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz413 (@HSub.hSub Real Real Real qz400 qz95 qz411) Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 293060 9000 rfl rfl) ep566))))

noncomputable def ep568 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz93 293060 4000 0 1 866996770604451 562949953421312 6250000001 2000000000000000

noncomputable def ep569 := @Enclosure.Complex.IsNear.im_isNear qz88 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable def ep570 := @Enclosure.Complex.IsNear.im_isNear qz89 Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (ep559 (@congrArg Complex Complex qz84 qz412 Complex.log (BSN.w_shift_mk qz12 Bool.false 146530 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz409 Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz409) (@HMul.hMul Real Real Real qz0 qz94 qz669) Bool.false 9670476397237989 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 9000 293060 4000 85965163600 16000000 rfl rfl rfl) (ep564 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz409) qz413 Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 9000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz413 (@HSub.hSub Real Real Real qz400 qz95 qz411) Bool.false 866996770604451 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 293060 9000 rfl rfl) ep566))))

noncomputable abbrev qz97 := (@ep558 1 (BSN.w_sub_half_mk qz279 Bool.false 146530 1000 2 qz281 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz408 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 293060 4000)))

noncomputable def ep571 := @ep554 91581250014653 400000000000000000 ep555 23715873989817392931 225179981368524800 92675000018853 400000000000000000 (@ep556 67693334780665923 9007199254740992 5468750021 2000000000000000 (ep557 qz97) ep567 rfl) (@ep568 12704103679667020503 112589990684262400 91581250014653 400000000000000000 (ep569 qz97) ep570 rfl) rfl

noncomputable def ep572 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz90 qz93) (@HMul.hMul Real Real Real qz0 qz92 qz91) 6068977394231157 2251799813685248 43750000007 8000000000000000 141701490648728252817 450359962737049600

noncomputable def ep573 := nat_lit 321816614674846131691760211581730816

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz93 7000 4000 0 1 866996770604451 562949953421312 6250000001 2000000000000000

noncomputable def ep575 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz91 293060 4000 0 1 9670476397237989 2251799813685248 781250003 500000000000000

noncomputable def ep576 := @ep572 11447656293959 100000000000000000 ep573 142915286127574484217 450359962737049600 23989062588093 200000000000000000 (@ep574 6068977394231157 2251799813685248 43750000007 8000000000000000 (ep557 qz97) ep570 rfl) (@ep575 141701490648728252817 450359962737049600 11447656293959 100000000000000000 (ep569 qz97) ep567 rfl) rfl

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz84 qz412 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 146530 1000 2 qz13 rfl)

noncomputable abbrev qz414 := (ep577 (@Enclosure.Complex.IsNear.mk qz668 qz667 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 293060 4000)))

noncomputable abbrev qz98 := qz414

noncomputable def ep578 := ep552 (@ep553 200000000000000000 (ep571 rfl) (ep576 rfl)) qz98 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz99 := qz403

noncomputable def ep579 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.im ↑qz2)) 120447 131072 3 1048576 0 1 0 1 120447 120447

noncomputable def ep580 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.re ↑qz2) 1 2 0 1 120447 65536 3 524288 120447 131072 3 1048576

noncomputable abbrev qz100 := (@Enclosure.Complex.IsNear.of_eq qz403 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz557) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz557 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz410 qz560))

noncomputable def ep581 := ep580 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMLast.d4)

noncomputable def ep582 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep583 := ep582 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep584 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz99) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz99) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep585 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz99) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep586 := ep585 (@Enclosure.Complex.IsNear.re_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz21)

noncomputable def ep587 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz99) (Complex.re ↑qz2) 0 1 0 1 120447 65536 3 524288 0 1 0 1

noncomputable def ep588 := ep587 (@Enclosure.Complex.IsNear.im_isNear qz99 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz100) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 3 524288 (Complex.ofReal_re qz2) EMLast.d4)

noncomputable def ep589 := @ep550 23989062588093 200000000000000000 (ep578 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep579 131072 3 1048576 (ep581 rfl) (ep583 rfl) rfl rfl) (@ep584 1 0 1 (ep586 rfl) (ep588 rfl) rfl rfl))

noncomputable abbrev qz101 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz415 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz102 := (@HMul.hMul Complex Complex Complex qz396 (@HMul.hMul Complex Complex Complex qz396 (2 : Complex) qz415) (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 (2 : Complex) qz415) (1 : Complex)))

noncomputable abbrev qz416 := (@HPow.hPow Complex Int Complex qz666 qz661 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz103 := qz416

noncomputable def ep590 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103)) Bool.false 2398161 68719476736 3 68719476736

noncomputable def ep591 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103) Bool.false 0 1 0 1 Bool.false

noncomputable def ep592 := @ep591 0 1 0 1 Bool.false 2398161 68719476736 3 68719476736 Bool.true 11713417711 10307921510400 14653 10307921510400 Bool.false 2398161 2398161 68719476736 3 68719476736 Bool.true 11713417711 11713417711 10307921510400 14653

noncomputable def ep593 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz84 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep594 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz103 Bool.false 2398161 68719476736 3 68719476736 Bool.true 11713417711 10307921510400 14653 10307921510400

noncomputable abbrev qz104 := (Complex.re qz416)

noncomputable abbrev qz105 := (Complex.im qz416)

noncomputable def ep595 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) 2398161 68719476736 3 68719476736 0 1 0

noncomputable def ep596 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 1 12 0 1 7194483 17179869184 9 17179869184 2398161

noncomputable def ep597 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz417 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz21)

noncomputable def ep598 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep597 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz417)

noncomputable def ep599 := @Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 7194483 17179869184 9 17179869184 Bool.true 11713417711 858993459200 14653 858993459200

noncomputable abbrev qz671 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz418 := (@HPow.hPow Complex Nat Complex qz671 qz661 1)

noncomputable abbrev qz106 := (@Inv.inv Complex Complex.instInv qz418)

noncomputable def ep600 := @Enclosure.Complex.IsNear.of_eq qz103 qz106 Bool.false 7194483 17179869184 9 17179869184 Bool.true 11713417711 858993459200 14653

noncomputable def ep601 := @Enclosure.Complex.IsNear.of_parts qz106 Bool.false 7194483 17179869184 9 17179869184 Bool.true 11713417711 858993459200 14653

noncomputable abbrev qz107 := (Complex.re qz418)

noncomputable abbrev qz108 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz109 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz110 := qz418

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 9000 4000 0 1 799387 4294967296 1 4294967296

noncomputable def ep603 := @Enclosure.Complex.IsNear.re_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable def ep604 := @Enclosure.Complex.IsNear.of_eq qz110 qz84 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0

noncomputable def ep605 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) Bool.false 799387 4294967296 1 4294967296 799387 4294967296 1

noncomputable abbrev qz111 := (Complex.im qz418)

noncomputable abbrev qz419 := (@instHAdd Real Real.instAdd)

noncomputable def ep606 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111)) Bool.false 214912909 40000 0 1

noncomputable def ep607 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz107 qz107) (@HMul.hMul Real Real Real qz0 qz111 qz111) 81 16 0 1 214710409 40000

noncomputable def ep608 := @Enclosure.Real.IsNear.mulLit_ff qz107 qz107 9000 4000 0 1 9000 4000 0 1

noncomputable def ep609 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 293060 4000 0 1 293060 4000 0 1

noncomputable def ep610 := @Enclosure.Complex.IsNear.im_isNear qz110 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable abbrev qz112 := (ep603 (@ep604 1 (BSN.pow_one_c qz398) qz414))

noncomputable abbrev qz113 := (ep610 (@ep604 1 (BSN.pow_one_c qz398) qz414))

noncomputable def ep611 := @ep607 0 1 3438606544 214912909 40000 0 1 (@ep608 81 16 0 1 qz112 qz112 rfl) (@ep609 214710409 40000 0 1 qz113 qz113 rfl)

noncomputable def ep612 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110) 214912909 40000 0 1 399693 399694 2147483648 (ep606 (Enclosure.Complex.normSq_eq_mul_add_mul qz110) (ep611 rfl rfl)) rfl

noncomputable def ep613 := @Enclosure.Real.IsNear.of_eq (Complex.re qz106) (@HMul.hMul Real Real Real qz0 qz107 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.false 7194483 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz110) (@ep602 7194483 17179869184 9 17179869184 qz112 (@ep605 4294967296 (ep612 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep614 := @Enclosure.Real.IsNear.of_eq (Complex.im qz106) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110))) Bool.true 11713417711 858993459200 14653 858993459200 (Enclosure.Complex.inv_im_eq_mul qz110)

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz111) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz110)) 293060 4000 0 1 799387 4294967296 1

noncomputable def ep616 := @ep615 4294967296 11713417711 858993459200 14653 858993459200 (@Enclosure.Real.IsNear.neg qz111 Bool.false 293060 4000 0 1 qz113) (@ep605 4294967296 (ep612 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 0 1 0 1 11713417711 858993459200 14653 858993459200 0

noncomputable def ep618 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep597 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz417)

noncomputable def ep619 := @Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 7194483 17179869184 9 17179869184 Bool.true 11713417711 858993459200 14653 858993459200

noncomputable abbrev qz114 := (@ep600 858993459200 (BSN.zpow_one_sub_two_mul qz398 1 1 rfl rfl) (@ep601 858993459200 ep613 (ep614 ep616)))

noncomputable def ep620 := @ep595 1 2398161 2398161 68719476736 3 68719476736 (@ep596 68719476736 3 68719476736 ep598 (ep599 qz114) rfl) (@ep617 1 0 1 ep618 (ep619 qz114) rfl) rfl

noncomputable def ep621 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104) 11713417711 10307921510400 14653 10307921510400 0 1 0

noncomputable def ep622 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz105 1 12 0 1 11713417711 858993459200 14653 858993459200 11713417711

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz104 0 1 0 1 7194483 17179869184 9 17179869184 0

noncomputable def ep624 := @ep621 1 11713417711 11713417711 10307921510400 14653 10307921510400 (@ep622 10307921510400 14653 10307921510400 ep598 (ep619 qz114) rfl) (@ep623 1 0 1 ep618 (ep599 qz114) rfl) rfl

noncomputable abbrev qz115 := (@Enclosure.Complex.IsNear.mk qz557 qz557 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz560 qz560)

noncomputable def ep625 := @ep592 10307921510400 (@ep593 0 1 0 1 (BSN.stirling_sum_base qz84) qz115) (ep594 (ep620 rfl) (ep624 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep626 := @ep547 329757455071847419627 1351079888211148800 37731980112630573977 314572800000000000000000 (ep589 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep590 Bool.true 11713417711 10307921510400 14653 10307921510400 (BSN.stirling_sum_succ qz84 0 1 rfl) (ep625 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9669584654653157 1125899906842624 781250003 250000000000000 Bool.false 878517483505059 281474976710656

noncomputable abbrev qz116 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz399 qz415))

noncomputable def ep628 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz116) Bool.false 9669584654653157 1125899906842624 781250003 250000000000000 Bool.false 878517483505059 281474976710656 6250000001 1000000000000000

noncomputable def ep629 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz116 Bool.false 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 562949953421312 6250000001 2000000000000000 Bool.false

noncomputable def ep630 := nat_lit 43547937847523424115782815055872

noncomputable def ep631 := nat_lit 989122752837962394645420834816

noncomputable abbrev qz117 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz399 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep632 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz117) Bool.false 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 562949953421312 6250000001 2000000000000000

noncomputable def ep633 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz117 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz420 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz667))

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq qz117 qz420 Bool.false 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 562949953421312 6250000001 2000000000000000

noncomputable def ep635 := nat_lit 1265635868377839008238392995333859302133032558561584353280000000000000

noncomputable def ep636 := nat_lit 7702793682663886153601240019714668133129091596848787456000000000000

noncomputable def ep637 := nat_lit 1065051575828602550327721796097828810855050078679040000000000000

noncomputable def ep638 := BSN.log_dyadic_bound 20349163600 151421163600 4 3 ep635 1048576 320000 ep636 ep637 283546 171770327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20349163600) (BSN.artanhQ 151421163600) 0 3 ep636 ep635 ep637 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 85885163600 16000000)) 1 2 0 1 9669427351475941 1125899906842624 781250003 250000000000000 9669427351475941 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 85885163600 16000000 9669427351475941 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85885163600) qz670)) Bool.false 324452142544039561920512 37778931862957161709568 1000000003840000 320000000000000000000 9669427351475941 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 85885163600 16000000 12 171770327200 131072000000 283546 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep638 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep640 := BSN.arctan_dyadic_bound_f 1000 293060 1 0 1048576 320000 0 1 1 0 1 1 3578 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz421 := (@Nat.cast Real Real.instNatCast 293060)

noncomputable abbrev qz672 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep641 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz672 qz421)) 884279719003555 562949953421312 1 2000000000000000 3578 1048576 1 320000 925220255700530233344 882358794880419 562949953421312 6250000001 2000000000000000 qz96 (ep640 rfl) rfl rfl

noncomputable abbrev qz118 := (@HAdd.hAdd Complex Complex Complex qz274 qz399 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz422 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz667)

noncomputable def ep642 := @ep633 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 562949953421312 6250000001 2000000000000000 Bool.false 9669427351475941 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 882358794880419 562949953421312 6250000001 2000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz115) (ep634 (@congrArg Complex Complex qz118 qz422 Complex.log (BSN.w_shift_mk qz12 Bool.false 146530 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz420 Bool.false 9669427351475941 2251799813685248 781250003 500000000000000 Bool.false 882358794880419 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz420) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 85885163600 16000000))) Bool.false 9669427351475941 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 1000 293060 4000 85885163600 16000000 rfl rfl rfl) (ep639 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz420) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz672)) Bool.false 882358794880419 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 1000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz672)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz672 qz421))) Bool.false 882358794880419 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 293060 1000 rfl rfl) ep641)))) rfl rfl

noncomputable abbrev qz423 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz667))

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq qz116 qz423 Bool.false 9669741957830373 2251799813685248 781250003 500000000000000 Bool.false 874676172129699 562949953421312 6250000001 2000000000000000

noncomputable def ep644 := nat_lit 1266839952353897299621096060191582395123900244560995553280000000000000

noncomputable def ep645 := nat_lit 7726043614444295238413749925489936036614876121403027456000000000000

noncomputable def ep646 := nat_lit 1072610625883402030057319786115501905634604280279040000000000000

noncomputable def ep647 := BSN.log_dyadic_bound 20373163600 151445163600 4 3 ep644 1048576 320000 ep645 ep646 283839 171818327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20373163600) (BSN.artanhQ 151445163600) 0 3 ep645 ep644 ep646 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep648 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 85909163600 16000000)) 1 2 0 1 9669741957830373 1125899906842624 781250003 250000000000000 9669741957830373 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 85909163600 16000000 9669741957830373 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85909163600) qz670)) Bool.false 324462698981566118363136 37778931862957161709568 1000000003840000 320000000000000000000 9669741957830373 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 85909163600 16000000 12 171818327200 131072000000 283839 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep647 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep649 := BSN.arctan_dyadic_bound_f 5000 293060 1 0 1048576 320000 0 1 1 0 1 1 17888 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz673 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep650 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz673 qz421)) 884279719003555 562949953421312 1 2000000000000000 17888 1048576 1 320000 917164441867071258624 874676172129699 562949953421312 6250000001 2000000000000000 qz96 (ep649 rfl) rfl rfl

noncomputable abbrev qz119 := (@HAdd.hAdd Complex Complex Complex qz274 qz399 qz415)

noncomputable abbrev qz424 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz667)

noncomputable def ep651 := @ep629 9669741957830373 2251799813685248 781250003 500000000000000 Bool.false 874676172129699 562949953421312 6250000001 2000000000000000 Bool.false ep630 9669584654653157 1125899906842624 781250003 250000000000000 Bool.false ep631 878517483505059 281474976710656 6250000001 1000000000000000 (ep632 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep642 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep643 (@congrArg Complex Complex qz119 qz424 Complex.log (BSN.w_shift_mk qz12 Bool.false 146530 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz423 Bool.false 9669741957830373 2251799813685248 781250003 500000000000000 Bool.false 874676172129699 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz423) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 85909163600 16000000))) Bool.false 9669741957830373 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 5000 293060 4000 85909163600 16000000 rfl rfl rfl) (ep648 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz423) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz673)) Bool.false 874676172129699 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 5000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz673)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz673 qz421))) Bool.false 874676172129699 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 293060 5000 rfl rfl) ep650)))) rfl rfl

noncomputable def ep652 := @ep540 314572800000000000000000 Bool.false 9669584654653157 1125899906842624 781250003 250000000000000 Bool.false 878517483505059 281474976710656 6250000001 1000000000000000 Bool.true ep541 25949511650172715531 225179981368524800 12460939891918605391 52428800000000000000000 Bool.false ep542 325540571151023136427 1351079888211148800 39698060112945146777 314572800000000000000000 (@ep543 225179981368524800 12297099891289459791 52428800000000000000000 Bool.false 329757455071847419627 1351079888211148800 37731980112630573977 314572800000000000000000 (BSN.logGammaStirling_unfold 1 qz84) (ep626 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep627 6250000001 1000000000000000 (BSN.log_sum_c_eq qz12 2) (ep628 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep651 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz120 := (@HDiv.hDiv Real Real Real qz272 qz279 (2 : Real))

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff qz120 (Real.log Real.pi) 146530 2000 0 1 75021 65536 1 262144 1099282713 13107200 14653 52428800 (@Enclosure.Real.IsNear.of_eq qz120 (Enclosure.sfrac Bool.false 146530 2000) Bool.false 146530 2000 0 1 (BSN.t_half_eq qz12 Bool.false 146530 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 146530 2000)) EMLast.d5 rfl

noncomputable def ep654 := @ep537 14653 52428800 ep538 8489094876703497571 54043195528445952 127616060112945146777 314572800000000000000000 (@ep539 39698060112945146777 314572800000000000000000 (ep652 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep653 rfl rfl

noncomputable def ep655 := nat_lit 8347746859401489388635245041151530999698311943033988968077464462264726034453025

noncomputable def ep656 := nat_lit 16779859881707055492460990912702361029294554640973351204331353807573646709281

noncomputable def ep657 := nat_lit 21835979144338279832771181122490586890876721048051252347776822828338210852704801

noncomputable def ep658 := BSN.sin_dyadic_bound_f 3373638477 2147483648 3 2 1048576 320313 ep655 ep64 ep656 ep657 ep66 ep656 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3373638477) qz19 0 2 ep655 ep64 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3373638477) qz20 0 2 ep657 ep66 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable def ep659 := @ep535 1048576 Bool.false 1048575 1048576 1 160000 (@ep536 82355059 524288 427 1048576 ep654 rfl) (Enclosure.sfrac_false_div 82355059 524288) (BSN.cos_reduce3 qz663 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118699351470784787775488) qz25) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 24 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 82355059 524288 226375608064910080 72057594037927936 24 118699351470784787775488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118699351470784787775488 75557863725914323419136 3373638477 2147483648 320313 320000 (ep658 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep660 := nat_lit 9818203736220372256615477

noncomputable def ep661 := nat_lit 1091866947865884491776000000

noncomputable abbrev qz425 := (@HPow.hPow Complex Complex Complex qz548 (@Nat.cast Complex Complex.instNatCast 37) qz549)

noncomputable abbrev qz121 := qz425

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 37)

noncomputable abbrev qz122 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz404 qz426 (@HSub.hSub Complex Complex Complex qz397 qz273 (1 : Complex))) qz403)

noncomputable abbrev qz123 := (@instHSub Nat instSubNat)

noncomputable abbrev qz427 := qz671

noncomputable abbrev qz124 := qz427

noncomputable abbrev qz125 := qz426

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 37) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz74 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false 775699511146609918085077 698794846634166074736640 530892165749899801990617

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz74 qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 1184516556929 1099511627776 6120994906433 687194767360000

noncomputable def ep664 := nat_lit 852890632165856527217829033124298752

noncomputable def ep665 := nat_lit 4610187130158283107539696811507712

noncomputable def ep666 := @ep663 Bool.false 79729143955 1099511627776 6118717440183 687194767360000 Bool.false 22879763883816416560517 698794846634166074736640 5189516816134904551817 ep533 Bool.true 80200752121181398614337 1048192269951249112104960 96323341333004131247677 ep661 Bool.false ep664 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 Bool.true ep665 4192940769060699592537 1048192269951249112104960

noncomputable def ep667 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 37) Bool.false 1184516556929 1099511627776 6120994906433 687194767360000 Bool.false 79729143955 1099511627776 6118717440183

noncomputable abbrev qz674 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 36) qz7)

noncomputable def ep668 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 37) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 36) qz674) Bool.false 1184516556929 1099511627776 6120994906433 687194767360000 Bool.false 79729143955 1099511627776 6118717440183 687194767360000

noncomputable def ep669 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 36) qz674 Bool.false 1349764410631 1099511627776 6014720474339 687194767360000 Bool.false 517464679 1099511627776 6012750696839 687194767360000 Bool.true

noncomputable abbrev qz675 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz7)

noncomputable def ep670 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 35) qz675) Bool.false 1349764410631 1099511627776 6014720474339 687194767360000 Bool.false 517464679 1099511627776 6012750696839 687194767360000

noncomputable def ep671 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 35) qz675 Bool.false 1190300682931 1099511627776 5906865426107 687194767360000 Bool.true 23734495001 274877906944 46133760619 5368709120000 Bool.false

noncomputable abbrev qz676 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz7)

noncomputable def ep672 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 34) qz676) Bool.false 1190300682931 1099511627776 5906865426107 687194767360000 Bool.true 23734495001 274877906944 46133760619 5368709120000

noncomputable def ep673 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 34) qz676 Bool.false 1176247406239 1099511627776 5797957212427 687194767360000 Bool.false 93101832307 1099511627776 5795608451177 687194767360000 Bool.false

noncomputable abbrev qz677 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep674 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz677) Bool.false 1176247406239 1099511627776 5797957212427 687194767360000 Bool.false 93101832307 1099511627776 5795608451177 687194767360000

noncomputable def ep675 := @Enclosure.Complex.IsNear.addLitP qz65 qz677 Bool.false 1361036149053 1099511627776 5686828261913 687194767360000 Bool.false 21616452021 549755813888 710617683911 85899345920000 Bool.true

noncomputable abbrev qz678 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz269 qz279 qz678)

noncomputable abbrev qz428 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep676 := @Enclosure.Complex.IsNear.of_eq qz677 (Complex.mk (@HMul.hMul Real Real Real qz0 qz428 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz428 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.true 92394371407 549755813888 55564475257 343597383680000 Bool.false 49868928265 1099511627776 110666979889 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 33 qz13 rfl)

noncomputable abbrev qz429 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz430 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz679 := (@HDiv.hDiv Real Real Real qz1 qz430 qz14)

noncomputable def ep677 := @Enclosure.Real.IsNear.inv_image qz429 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz429 (Real.sqrt qz679) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz679) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep678 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 160000 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep679 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz678 146530 1000 0 1 15746868335186131 4503599627370496 1250000001 200000000000000 230738861715482377543 450359962737049600 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz679) Bool.false 66047152845744529997824 18889465931478580854784 1000000000800000 160000000000000000000 15746868335186131 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep678 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep680 := nat_lit 102668827469450806797980097596850081

noncomputable def ep681 := BSN.cos_dyadic_bound_f 566056329 2147483648 2 1 1048576 320313 ep680 ep95 ep680 ep680 ep96 ep680 1012358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 566056329) qz15 0 1 ep680 ep95 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 566056329) qz16 0 1 ep680 ep96 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz431 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153847) qz562)

noncomputable def ep682 := @Enclosure.Real.IsNear.cos_image qz126 qz431 Bool.false 67153847 131072 481 524288 Bool.true 1012358 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 230738861715482377543 450359962737049600 18316250014653 20000000000000000 67153847 131072 481 524288 (ep679 rfl) rfl) (Enclosure.sfrac_false_div 67153847 131072) (BSN.cos_reduce2 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4979084129700176461824) qz293) 226375608064910080 72057594037927936 Bool.false 1012358 1048576 81 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 67153847 131072 226375608064910080 72057594037927936 81 4979084129700176461824 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012358 1048576 4979084129700176461824 18889465931478580854784 566056329 2147483648 320313 320000 (ep681 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep683 := BSN.sin_dyadic_bound_f 566056329 2147483648 2 1 1048576 320313 ep680 ep80 ep680 ep680 ep81 ep680 273205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 566056329) qz19 0 1 ep680 ep80 ep680 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 566056329) qz20 0 1 ep680 ep81 ep680 rfl rfl rfl rfl) rfl rfl

noncomputable def ep684 := @Enclosure.Real.IsNear.sin_image qz126 qz431 Bool.false 67153847 131072 481 524288 Bool.true 273205 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 230738861715482377543 450359962737049600 18316250014653 20000000000000000 67153847 131072 481 524288 (ep679 rfl) rfl) (Enclosure.sfrac_false_div 67153847 131072) (BSN.sin_reduce2 qz431 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4979084129700176461824) qz293) 226375608064910080 72057594037927936 Bool.false 273205 1048576 81 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 67153847 131072 226375608064910080 72057594037927936 81 4979084129700176461824 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 273205 1048576 4979084129700176461824 18889465931478580854784 566056329 2147483648 320313 320000 (ep683 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz432 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep677 rfl rfl) rfl)

noncomputable def ep685 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz428 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz428 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.true 92394371407 549755813888 55564475257 343597383680000 Bool.false 49868928265 1099511627776 110666979889 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz428 (Real.cos qz126) 182533 1048576 1 1048576 506179 524288 302673 327680000 92394371407 549755813888 55564475257 343597383680000 qz432 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.true 1012358 1048576 77484288 83886080000 506179 524288 302673 327680000 (ep682 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz428 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 182533 1048576 1 1048576 273205 1048576 302673 327680000 49868928265 1099511627776 110666979889 687194767360000 qz432 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.true 273205 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.true 273205 1048576 77484288 83886080000 273205 1048576 302673 327680000 (ep684 rfl rfl) rfl)) rfl)

noncomputable def ep686 := @ep675 92394371407 549755813888 55564475257 343597383680000 Bool.false 49868928265 1099511627776 110666979889 687194767360000 Bool.false 646648850150570414047232 1176247406239 1099511627776 5797957212427 687194767360000 Bool.false 51183273594398877679616 93101832307 1099511627776 5795608451177 687194767360000 EMLast.d9 (ep676 ep685) rfl rfl

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz269 qz279 qz680)

noncomputable abbrev qz433 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable def ep687 := @Enclosure.Complex.IsNear.of_eq qz676 (Complex.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.false 3513319173 274877906944 1361352671 8589934592000 Bool.true 188039812311 1099511627776 21902581611 137438953472000 (BSN.cpow_neg_s_mk qz12 146530 1000 34 qz13 rfl)

noncomputable abbrev qz434 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz681 := (@HDiv.hDiv Real Real Real qz1 qz435 qz14)

noncomputable def ep688 := @Enclosure.Real.IsNear.inv_image qz434 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz434 (Real.sqrt qz681) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz681) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep689 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 160000 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep690 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz680 146530 1000 0 1 15881309401485523 4503599627370496 1250000001 200000000000000 232708826659967368519 450359962737049600 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz681) Bool.false 66611039547888335060992 18889465931478580854784 1000000000800000 160000000000000000000 15881309401485523 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep689 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep691 := nat_lit 3819432493877595375209815111127615912525480076560904622574441281583940685893601

noncomputable def ep692 := nat_lit 11359339440893584672741436006824468726397856071833554010402556645450313469921

noncomputable def ep693 := nat_lit 11435578802750998956283962461369198800123644517539046759702518731460921430740961

noncomputable def ep694 := BSN.cos_dyadic_bound_f 3213062213 2147483648 3 2 1048576 320313 ep691 ep57 ep692 ep693 ep60 ep692 78148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3213062213) qz15 0 2 ep691 ep57 ep692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3213062213) qz16 0 2 ep693 ep60 ep692 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 270908729) qz24)

noncomputable def ep695 := @Enclosure.Real.IsNear.cos_image qz127 qz436 Bool.false 270908729 524288 481 524288 Bool.false 78148 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 232708826659967368519 450359962737049600 18316250014653 20000000000000000 270908729 524288 481 524288 (ep690 rfl) rfl) (Enclosure.sfrac_false_div 270908729 524288) (BSN.cos_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113049576453600935149568) qz25) 226375608064910080 72057594037927936 Bool.false 78148 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 270908729 524288 226375608064910080 72057594037927936 82 113049576453600935149568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 78148 1048576 113049576453600935149568 75557863725914323419136 3213062213 2147483648 320313 320000 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := nat_lit 6865891017426956807639474051224249067564745852952161477425672261534732983832545

noncomputable def ep697 := nat_lit 17963704210356773454347517333004841275207785466948882877240870831355476354895841

noncomputable def ep698 := BSN.sin_dyadic_bound_f 3213062213 2147483648 3 2 1048576 320313 ep696 ep64 ep692 ep697 ep66 ep692 1045659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3213062213) qz19 0 2 ep696 ep64 ep692 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3213062213) qz20 0 2 ep697 ep66 ep692 rfl rfl rfl rfl) rfl rfl

noncomputable def ep699 := @Enclosure.Real.IsNear.sin_image qz127 qz436 Bool.false 270908729 524288 481 524288 Bool.false 1045659 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 232708826659967368519 450359962737049600 18316250014653 20000000000000000 270908729 524288 481 524288 (ep690 rfl) rfl) (Enclosure.sfrac_false_div 270908729 524288) (BSN.sin_reduce0 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113049576453600935149568) qz25) 226375608064910080 72057594037927936 Bool.false 1045659 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 270908729 524288 226375608064910080 72057594037927936 82 113049576453600935149568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045659 1048576 113049576453600935149568 75557863725914323419136 3213062213 2147483648 320313 320000 (ep698 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz437 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep688 rfl rfl) rfl)

noncomputable def ep700 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.false 3513319173 274877906944 1361352671 8589934592000 Bool.true 188039812311 1099511627776 21902581611 137438953472000 (@Enclosure.Real.IsNear.mulLit_ff qz433 (Real.cos qz127) 179829 1048576 1 1048576 19537 262144 302673 327680000 3513319173 274877906944 1361352671 8589934592000 qz437 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.false 78148 1048576 77484288 83886080000 19537 262144 302673 327680000 (ep695 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz433 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 179829 1048576 1 1048576 1045659 1048576 302673 327680000 188039812311 1099511627776 21902581611 137438953472000 qz437 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.false 1045659 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.false 1045659 1048576 77484288 83886080000 1045659 1048576 302673 327680000 (ep699 rfl rfl) rfl)) rfl)

noncomputable def ep701 := @ep673 3513319173 274877906944 1361352671 8589934592000 Bool.true 188039812311 1099511627776 21902581611 137438953472000 Bool.false 327187360358087067172864 1190300682931 1099511627776 5906865426107 687194767360000 Bool.true 104385412931963378991104 23734495001 274877906944 46133760619 5368709120000 (ep674 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep686 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep687 ep700) rfl rfl

noncomputable abbrev qz682 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz128 := (@HMul.hMul Real Real Real qz269 qz279 qz682)

noncomputable abbrev qz438 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35)))

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq qz675 (Complex.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz128)))) Bool.false 39865931925 274877906944 13481881029 85899345920000 Bool.false 95455444683 1099511627776 107629337607 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 35 qz13 rfl)

noncomputable abbrev qz439 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35))

noncomputable abbrev qz440 := (@Nat.cast Real Real.instNatCast 35)

noncomputable abbrev qz683 := (@HDiv.hDiv Real Real Real qz1 qz440 qz14)

noncomputable def ep703 := @Enclosure.Real.IsNear.inv_image qz439 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz439 (Real.sqrt qz683) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz683) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep704 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 160000 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep705 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz682 146530 1000 0 1 16011859227414739 4503599627370496 1250000001 200000000000000 234621773259308170567 450359962737049600 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz683) Bool.false 67158605204982549446656 18889465931478580854784 1000000000800000 160000000000000000000 16011859227414739 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep704 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep706 := nat_lit 1548457745648058565123607025101371942473903701962409462228724377005856130760960

noncomputable def ep707 := nat_lit 579256920681083796922948929352609132854176691853687103568185978520881234176

noncomputable def ep708 := nat_lit 4054546727397145915843000291284641339311793409543309288621834400573922725232896

noncomputable def ep709 := BSN.sin_dyadic_bound_f 2214924382 2147483648 3 2 1048576 320313 ep706 ep64 ep707 ep708 ep66 ep707 899700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2214924382) qz19 0 2 ep706 ep64 ep707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2214924382) qz20 0 2 ep708 ep66 ep707 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68283923) qz562)

noncomputable def ep710 := @Enclosure.Real.IsNear.cos_image qz128 qz441 Bool.false 68283923 131072 481 524288 Bool.false 899700 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 234621773259308170567 450359962737049600 18316250014653 20000000000000000 68283923 131072 481 524288 (ep705 rfl) rfl) (Enclosure.sfrac_false_div 68283923 131072) (BSN.cos_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19482680908291606839296) qz293) 226375608064910080 72057594037927936 Bool.false 899700 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 68283923 131072 226375608064910080 72057594037927936 82 19482680908291606839296 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 899700 1048576 19482680908291606839296 18889465931478580854784 2214924382 2147483648 320313 320000 (ep709 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep711 := nat_lit 860511750658113017867302991247141127655659468508829117728654958771484908749056

noncomputable def ep712 := nat_lit 2580376738132976886008063075882718164701270052142779978978828504357412963778816

noncomputable def ep713 := BSN.cos_dyadic_bound_f 2214924382 2147483648 3 2 1048576 320313 ep711 ep57 ep707 ep712 ep60 ep707 538563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2214924382) qz15 0 2 ep711 ep57 ep707 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2214924382) qz16 0 2 ep712 ep60 ep707 rfl rfl rfl rfl) rfl rfl

noncomputable def ep714 := @Enclosure.Real.IsNear.sin_image qz128 qz441 Bool.false 68283923 131072 481 524288 Bool.true 538563 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz128 Bool.false 234621773259308170567 450359962737049600 18316250014653 20000000000000000 68283923 131072 481 524288 (ep705 rfl) rfl) (Enclosure.sfrac_false_div 68283923 131072) (BSN.sin_reduce3 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19482680908291606839296) qz293) 226375608064910080 72057594037927936 Bool.false 538563 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 68283923 131072 226375608064910080 72057594037927936 82 19482680908291606839296 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 538563 1048576 19482680908291606839296 18889465931478580854784 2214924382 2147483648 320313 320000 (ep713 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz442 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35))) Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep703 rfl rfl) rfl)

noncomputable def ep715 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz128)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz128))) Bool.false 39865931925 274877906944 13481881029 85899345920000 Bool.false 95455444683 1099511627776 107629337607 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz438 (Real.cos qz128) 177241 1048576 1 1048576 224925 262144 302673 327680000 39865931925 274877906944 13481881029 85899345920000 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz128) Bool.false 899700 1048576 77484288 83886080000 224925 262144 302673 327680000 (ep710 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz438 (@Neg.neg Real Real.instNeg (Real.sin qz128)) 177241 1048576 1 1048576 538563 1048576 302673 327680000 95455444683 1099511627776 107629337607 687194767360000 qz442 (@Enclosure.Real.IsNear.neg (Real.sin qz128) Bool.true 538563 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz128) Bool.true 538563 1048576 77484288 83886080000 538563 1048576 302673 327680000 (ep714 rfl rfl) rfl)) rfl)

noncomputable def ep716 := @ep671 39865931925 274877906944 13481881029 85899345920000 Bool.false 95455444683 1099511627776 107629337607 687194767360000 Bool.false 371020416061751022321664 1349764410631 1099511627776 6014720474339 687194767360000 Bool.false 142239607880968830976 517464679 1099511627776 6012750696839 687194767360000 (ep672 (BSN.head_sum_c_succ qz5 34 35 rfl rfl) (ep701 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep702 ep715) rfl rfl

noncomputable abbrev qz684 := (Real.log (Enclosure.sfrac Bool.false 36 1))

noncomputable abbrev qz129 := (@HMul.hMul Real Real Real qz269 qz279 qz684)

noncomputable abbrev qz443 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36)))

noncomputable def ep717 := @Enclosure.Complex.IsNear.of_eq qz674 (Complex.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz129)))) Bool.true 82623926851 549755813888 53137216047 343597383680000 Bool.false 19802919819 274877906944 6622921459 42949672960000 (BSN.cpow_neg_s_mk qz12 146530 1000 36 qz13 rfl)

noncomputable abbrev qz444 := (Real.sqrt (@Nat.cast Real Real.instNatCast 36))

noncomputable abbrev qz445 := (@Nat.cast Real Real.instNatCast 36)

noncomputable abbrev qz685 := (@HDiv.hDiv Real Real Real qz1 qz445 qz14)

noncomputable def ep718 := @Enclosure.Real.IsNear.inv_image qz444 6291457 1048576 1 1048576 87381 87382 524288 (@Enclosure.Real.IsNear.of_eq qz444 (Real.sqrt qz685) Bool.false 6291457 1048576 1 1048576 (BSN.sqrt_natCast_div_one 36) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz685) Bool.false 6291457 1048576 1 1048576 6291457 1048576 1 1048576 (BSN.sqrt_enclosure 36 1 3145728 3145729 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep719 := BSN.log_dyadic_bound 4 68 2 1 13872 524288 160000 16 16 61752 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4) (BSN.artanhQ 68) 0 1 16 13872 16 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep720 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz684 146530 1000 0 1 16138732561338579 4503599627370496 1250000001 200000000000000 236480848221294198087 450359962737049600 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz685) Bool.false 67690750536952647254016 18889465931478580854784 1000000000800000 160000000000000000000 16138732561338579 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep719 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep721 := nat_lit 849020882434487111296777597954560000

noncomputable def ep722 := BSN.cos_dyadic_bound_f 959907960 2147483648 2 1 1048576 320313 ep721 ep95 ep721 ep721 ep96 ep721 945554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 959907960) qz15 0 1 ep721 ep95 ep721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 959907960) qz16 0 1 ep721 ep96 ep721 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 550599881) qz30)

noncomputable def ep723 := @Enclosure.Real.IsNear.cos_image qz129 qz446 Bool.false 550599881 1048576 961 1048576 Bool.true 945554 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 236480848221294198087 450359962737049600 18316250014653 20000000000000000 550599881 1048576 961 1048576 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 550599881 1048576) (BSN.cos_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67547517700297312960512) qz31) 226375608064910080 72057594037927936 Bool.false 945554 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 550599881 1048576 226375608064910080 72057594037927936 83 67547517700297312960512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945554 1048576 67547517700297312960512 151115727451828646838272 959907960 2147483648 320313 320000 (ep722 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep724 := BSN.sin_dyadic_bound_f 959907960 2147483648 2 1 1048576 320313 ep721 ep80 ep721 ep721 ep81 ep721 453252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 959907960) qz19 0 1 ep721 ep80 ep721 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 959907960) qz20 0 1 ep721 ep81 ep721 rfl rfl rfl rfl) rfl rfl

noncomputable def ep725 := @Enclosure.Real.IsNear.sin_image qz129 qz446 Bool.false 550599881 1048576 961 1048576 Bool.true 453252 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz129 Bool.false 236480848221294198087 450359962737049600 18316250014653 20000000000000000 550599881 1048576 961 1048576 (ep720 rfl) rfl) (Enclosure.sfrac_false_div 550599881 1048576) (BSN.sin_reduce2 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67547517700297312960512) qz31) 226375608064910080 72057594037927936 Bool.false 453252 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 550599881 1048576 226375608064910080 72057594037927936 83 67547517700297312960512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 453252 1048576 67547517700297312960512 151115727451828646838272 959907960 2147483648 320313 320000 (ep724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz447 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36))) Bool.false 174763 1048576 1 1048576 174763 1048576 1 1048576 (ep718 rfl rfl) rfl)

noncomputable def ep726 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz129)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz129))) Bool.true 82623926851 549755813888 53137216047 343597383680000 Bool.false 19802919819 274877906944 6622921459 42949672960000 (@Enclosure.Real.IsNear.mulLit_ft qz443 (Real.cos qz129) 174763 1048576 1 1048576 472777 524288 604721 655360000 82623926851 549755813888 53137216047 343597383680000 qz447 (@Enclosure.Real.IsNear.recentre' (Real.cos qz129) Bool.true 945554 1048576 154808576 167772160000 472777 524288 604721 655360000 (ep723 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 (@Neg.neg Real Real.instNeg (Real.sin qz129)) 174763 1048576 1 1048576 113313 262144 604721 655360000 19802919819 274877906944 6622921459 42949672960000 qz447 (@Enclosure.Real.IsNear.neg (Real.sin qz129) Bool.true 113313 262144 604721 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz129) Bool.true 453252 1048576 154808576 167772160000 113313 262144 604721 655360000 (ep725 rfl rfl) rfl)) rfl)

noncomputable def ep727 := @ep669 82623926851 549755813888 53137216047 343597383680000 Bool.false 19802919819 274877906944 6622921459 42949672960000 Bool.false 651194863818313880829952 1184516556929 1099511627776 6120994906433 687194767360000 Bool.false 21915780212787270123520 79729143955 1099511627776 6118717440183 687194767360000 (ep670 (BSN.head_sum_c_succ qz5 35 36 rfl rfl) (ep716 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep717 ep726) rfl rfl

noncomputable def ep728 := @Enclosure.Complex.IsNear.mul qz121 (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 22879763883816416560517 698794846634166074736640 5189516816134904551817 ep533 Bool.true

noncomputable abbrev qz130 := (Complex.re qz425)

noncomputable abbrev qz131 := (Complex.im qz425)

noncomputable def ep729 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 1068949370368335763675 52409613497562455605248 124612719935069600341

noncomputable def ep730 := nat_lit 1637800421798826737664000

noncomputable def ep731 := nat_lit 2096384539902498224209920

noncomputable def ep732 := nat_lit 6551201687195306950656000000

noncomputable def ep733 := nat_lit 3597358746198920570050348122679839238964379648

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 11206921235 274877906944 6532231441 42949672960000 95382964505

noncomputable abbrev qz686 := (Real.log (Enclosure.sfrac Bool.false 37 1))

noncomputable abbrev qz132 := (@HMul.hMul Real Real Real qz269 qz279 qz686)

noncomputable abbrev qz133 := (Real.sin (@HMul.hMul Real Real Real qz269 qz279 qz686))

noncomputable abbrev qz448 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 37)))

noncomputable abbrev qz687 := (@Neg.neg Real Real.instNeg qz133)

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq qz121 (Complex.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz448 qz687)) Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (BSN.cpow_neg_s_mk qz12 146530 1000 37 qz13 rfl)

noncomputable abbrev qz449 := (Real.sqrt (@Nat.cast Real Real.instNatCast 37))

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37) qz14)

noncomputable def ep736 := @Enclosure.Real.IsNear.inv_image qz449 6378239 1048576 1 1048576 86192 86193 524288 (@Enclosure.Real.IsNear.of_eq qz449 (Real.sqrt qz450) Bool.false 6378239 1048576 1 1048576 (BSN.sqrt_natCast_div_one 37) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz450) Bool.false 6378239 1048576 1 1048576 6378239 1048576 1 1048576 (BSN.sqrt_enclosure 37 1 3189119 3189120 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep737 := BSN.log_dyadic_bound 5 69 3 2 340006815 524288 160000 597000 1875 76117 74 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 69) 0 2 597000 340006815 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz134 := qz686

noncomputable def ep738 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz134 146530 1000 0 1 16262126971752659 4503599627370496 1250000001 200000000000000 238288946517091712327 450359962737049600 18316250014653 20000000000000000 qz18 (BSN.isNear_log_sfrac 37 1 16262126971752659 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz450) Bool.false 68208304206130064654336 18889465931478580854784 1000000000800000 160000000000000000000 16262126971752659 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 76117 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep737 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep739 := nat_lit 2312435021858794592989764207235821926263673462935629744837469714015646048649216

noncomputable def ep740 := nat_lit 4173616035444351139562000643661964372338013347714037636913412429317826215936

noncomputable def ep741 := nat_lit 6928957833505495076690168620420141850046344362111461159238582317188302493515776

noncomputable def ep742 := BSN.cos_dyadic_bound_f 2835071796 2147483648 3 2 1048576 320313 ep739 ep57 ep740 ep741 ep60 ep740 260044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2835071796) qz15 0 2 ep739 ep57 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2835071796) qz16 0 2 ep741 ep60 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 554809687) qz30)

noncomputable def ep743 := @Enclosure.Real.IsNear.cos_image qz132 qz451 Bool.false 554809687 1048576 481 524288 Bool.false 260044 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 238288946517091712327 450359962737049600 18316250014653 20000000000000000 554809687 1048576 481 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 554809687 1048576) (BSN.cos_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199500441948621513949184) qz31) 226375608064910080 72057594037927936 Bool.false 260044 1048576 84 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 554809687 1048576 226375608064910080 72057594037927936 84 199500441948621513949184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 260044 1048576 199500441948621513949184 151115727451828646838272 2835071796 2147483648 320313 320000 (ep742 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep744 := nat_lit 4159044146517474786469925972509549895776741822605962310597914755284708626595840

noncomputable def ep745 := nat_lit 10885977386345524062719086688863844641860062275690745228725250262764865160544256

noncomputable def ep746 := BSN.sin_dyadic_bound_f 2835071796 2147483648 3 2 1048576 320313 ep744 ep64 ep740 ep745 ep66 ep740 1015819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2835071796) qz19 0 2 ep744 ep64 ep740 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2835071796) qz20 0 2 ep745 ep66 ep740 rfl rfl rfl rfl) rfl rfl

noncomputable def ep747 := @Enclosure.Real.IsNear.sin_image qz132 qz451 Bool.false 554809687 1048576 481 524288 Bool.false 1015819 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 238288946517091712327 450359962737049600 18316250014653 20000000000000000 554809687 1048576 481 524288 (ep738 rfl) rfl) (Enclosure.sfrac_false_div 554809687 1048576) (BSN.sin_reduce0 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199500441948621513949184) qz31) 226375608064910080 72057594037927936 Bool.false 1015819 1048576 84 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 554809687 1048576 226375608064910080 72057594037927936 84 199500441948621513949184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1015819 1048576 199500441948621513949184 151115727451828646838272 2835071796 2147483648 320313 320000 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz452 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 37))) Bool.false 172385 1048576 1 1048576 172385 1048576 1 1048576 (ep736 rfl rfl) rfl)

noncomputable def ep748 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz448 qz687) Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz448 (Real.cos qz132) 172385 1048576 1 1048576 65011 262144 302673 327680000 11206921235 274877906944 6532231441 42949672960000 qz452 (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 260044 1048576 77484288 83886080000 65011 262144 302673 327680000 (ep743 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz448 qz687 172385 1048576 1 1048576 1015819 1048576 302673 327680000 175111958315 1099511627776 104988062431 687194767360000 qz452 (@Enclosure.Real.IsNear.neg qz133 Bool.false 1015819 1048576 302673 327680000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 1015819 1048576 77484288 83886080000 1015819 1048576 302673 327680000 (ep747 rfl rfl) rfl)) rfl)

noncomputable def ep749 := @ep734 190665063192 0 1 1068949370368335763675 52409613497562455605248 124612719935069600341 ep730 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (ep735 ep748))

noncomputable def ep750 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 95382964505 190665063192 0 1 Bool.false

noncomputable def ep751 := @Enclosure.Complex.IsNear.addLitP qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 214342909 429425818 0 1 Bool.true 54216100

noncomputable def ep752 := @ep751 214712909 0 1 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1 Bool.false 190765929010 95382964505 190665063192 0 1 Bool.false 738993415577 738993415577 9533253159600 0 1

noncomputable abbrev qz135 := (@HDiv.hDiv Complex Complex Complex qz404 qz426 (@HSub.hSub Complex Complex Complex qz397 qz273 (1 : Complex)))

noncomputable def ep753 := @Enclosure.Complex.IsNear.addLitP qz135 qz99 Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1

noncomputable def ep754 := @Enclosure.Complex.IsNear.of_eq qz135 (Complex.mk (Enclosure.sfrac Bool.true 74000000 85885163600) (Enclosure.sfrac Bool.true 21686440000 85885163600)) Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1

noncomputable def ep755 := @ep753 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 85737163600 214342909 429425818 0 1 Bool.true 21686440000 54216100 214712909 0 1 (ep754 (BSN.N_div_s_sub_one_mk qz12 146530 1000 37 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 74000000 85885163600) (Enclosure.sfrac Bool.true 21686440000 85885163600) Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1 (Enclosure.Real.IsNear.const Bool.true 74000000 85885163600) (Enclosure.Real.IsNear.const Bool.true 21686440000 85885163600))) qz100 rfl

noncomputable abbrev qz136 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz137 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz426 1))

noncomputable def ep756 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137)) Bool.false 1 888 0 1

noncomputable def ep757 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137) Bool.false 0 1 0 1 Bool.false

noncomputable def ep758 := @ep757 0 1 0 1 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1 Bool.false 1 1 888 0 1 Bool.false 14653 14653 44400 0

noncomputable def ep759 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep760 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz137 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1

noncomputable def ep761 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137)) 1 888 0 1 0 1 0

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137) 1 24 0 1 1 37 0 1 1

noncomputable def ep763 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMLast.d10 rfl) qz417

noncomputable def ep766 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep767 := ep766 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz94 qz12) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 146530 1000 qz13) (@Enclosure.Complex.IsNear.mk qz94 qz12 Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 qz410 qz18))

noncomputable def ep768 := @ep764 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 146530 1000 0 1 0 1 0

noncomputable def ep770 := @ep769 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep771 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 14653 1200 0 1 0 1 0 1 14653

noncomputable def ep772 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 146530 1000 0 1 14653 1200 0

noncomputable def ep773 := @ep772 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep775 := @ep774 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep776 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 (@ep763 1 24 0 1 (ep768 rfl) (ep770 rfl) rfl rfl) (@ep771 14653 1200 0 1 (ep773 rfl) (ep775 rfl) rfl rfl)

noncomputable def ep777 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 ep776

noncomputable abbrev qz138 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz426 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 37) qz557) Bool.false 1 37 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 37 1 37 EMLast.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 37) qz557 Bool.false 1 37 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 37) qz560))

noncomputable def ep778 := @ep762 888 0 1 ep777 (@Enclosure.Complex.IsNear.re_isNear qz137 Bool.false 1 37 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep779 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137) 14653 1200 0 1 0 1 0 1 0

noncomputable def ep780 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 ep776

noncomputable def ep781 := @ep779 1 0 1 ep780 (@Enclosure.Complex.IsNear.im_isNear qz137 Bool.false 1 37 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep782 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137)) 0 1 0 1 14653 44400 0

noncomputable def ep783 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz137) 1 24 0 1 0 1 0 1 0

noncomputable def ep784 := @ep783 1 0 1 ep777 (@Enclosure.Complex.IsNear.im_isNear qz137 Bool.false 1 37 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep785 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz137) 14653 1200 0 1 1 37 0 1 14653

noncomputable def ep786 := @ep785 44400 0 1 ep780 (@Enclosure.Complex.IsNear.re_isNear qz137 Bool.false 1 37 0 1 Bool.false 0 1 0 1 qz138)

noncomputable def ep787 := @ep758 1 (@ep759 0 1 0 1 (BSN.bern_sum_base qz5 37) qz115) (ep760 (@ep761 1 1 1 888 0 1 (ep778 rfl) (ep781 rfl) rfl rfl) (@ep782 1 14653 14653 44400 0 1 (ep784 rfl) (ep786 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep788 := ep752 (ep755 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep756 Bool.false 14653 44400 0 1 (BSN.bern_sum_succ qz5 37 0 1 1 rfl rfl) (ep787 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep789 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 175111958315 1099511627776 104988062431 687194767360000 738993415577

noncomputable def ep790 := @ep789 9533253159600 0 1 25881316836715819134551 ep731 77585486850696003887687 ep732 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (ep735 ep748))

noncomputable def ep791 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 95382964505 190665063192 0 1 Bool.false

noncomputable def ep792 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 1656368200311012215519 524096134975624556052480 4827276023924058556457

noncomputable def ep793 := nat_lit 409450105449706684416000000

noncomputable def ep794 := nat_lit 26204806748781227802624000

noncomputable def ep795 := nat_lit 8406580841769858741957914872609830131730481152

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ff qz130 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 11206921235 274877906944 6532231441 42949672960000 738993415577

noncomputable def ep797 := @ep796 9533253159600 0 1 1656368200311012215519 524096134975624556052480 4827276023924058556457 ep793 (@Enclosure.Complex.IsNear.re_isNear qz121 Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (ep735 ep748))

noncomputable def ep798 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz122 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz125 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 175111958315 1099511627776 104988062431 687194767360000 95382964505

noncomputable def ep799 := @ep798 190665063192 0 1 16702697704360684609075 209638453990249822420992 2002814526460959402331 ep794 (@Enclosure.Complex.IsNear.im_isNear qz121 Bool.false 11206921235 274877906944 6532231441 42949672960000 Bool.true 175111958315 1099511627776 104988062431 687194767360000 (ep735 ep748))

noncomputable abbrev qz688 := (ep788 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep800 := @ep728 80200752121181398614337 1048192269951249112104960 96323341333004131247677 ep661 (@ep729 ep730 25881316836715819134551 ep731 77585486850696003887687 ep732 ep733 22879763883816416560517 698794846634166074736640 5189516816134904551817 ep533 (ep749 (@ep750 738993415577 9533253159600 0 1 qz688) rfl) (ep790 (@ep791 738993415577 9533253159600 0 1 qz688) rfl) rfl rfl) (@ep792 ep793 16702697704360684609075 209638453990249822420992 2002814526460959402331 ep794 ep795 80200752121181398614337 1048192269951249112104960 96323341333004131247677 ep661 (ep797 (@ep791 738993415577 9533253159600 0 1 qz688) rfl) (ep799 (@ep750 738993415577 9533253159600 0 1 qz688) rfl) rfl rfl)

noncomputable def ep801 := @ep666 ep660 ep661 (@ep667 687194767360000 (BSN.head_sum_c_eq qz5 37) (ep668 (BSN.head_sum_c_succ qz5 36 37 rfl rfl) (ep727 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep800 rfl rfl rfl

noncomputable def ep802 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 37) Bool.false 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 Bool.true 4192940769060699592537 1048192269951249112104960 ep660 ep661 (@ep662 ep533 Bool.true 4192940769060699592537 1048192269951249112104960 ep660 ep661 (BSN.zetaApproximant_eq_folded' qz5 1 37 rfl) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep803 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) (Complex.im (zetaApproximant qz5 1 37)) 93 524288 270971

noncomputable def ep804 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78)) Bool.false 186 1048576 69368576

noncomputable def ep805 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) qz663 Bool.false 82355059 524288 427

noncomputable def ep806 := nat_lit 4645094859614919462794007685489829382512081992637093138356071969617102751011361

noncomputable def ep807 := nat_lit 13901724859081344277397101074644083425477656868629332712659553201236160959615521

noncomputable def ep808 := BSN.cos_dyadic_bound_t 3373638477 2147483648 3 2 1048576 320313 ep806 ep57 ep656 ep807 ep60 ep656 186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3373638477) qz15 0 2 ep806 ep57 ep656 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3373638477) qz16 0 2 ep807 ep60 ep656 rfl rfl rfl rfl) rfl rfl

noncomputable def ep809 := @ep805 1048576 Bool.false 186 1048576 1 160000 (@ep536 82355059 524288 427 1048576 ep654 rfl) (Enclosure.sfrac_false_div 82355059 524288) (BSN.sin_reduce3 qz663 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118699351470784787775488) qz25) 226375608064910080 72057594037927936 Bool.true 186 1048576 24 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 82355059 524288 226375608064910080 72057594037927936 24 118699351470784787775488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.true 186 1048576 118699351470784787775488 75557863725914323419136 3373638477 2147483648 320313 320000 (ep808 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep810 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 37) Bool.false 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 Bool.true 4192940769060699592537 1048192269951249112104960 ep660 ep661 (@ep662 ep533 Bool.true 4192940769060699592537 1048192269951249112104960 ep660 ep661 (BSN.zetaApproximant_eq_folded' qz5 1 37 rfl) (ep801 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMLast.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 37 qz12) Bool.false ep517 ep518 ep519 ep520 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 37 qz12) ep521 Bool.false ep517 ep518 ep519 ep520 (@Eq.refl Real ep521) (@ep522 Bool.false ep517 ep518 ep519 ep520 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz76 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz77 (@Nat.cast Complex Complex.instNatCast j))))) qz78) (zetaApproximant qz5 1 37)) (@ep524 ep525 ep526 ep527 129981163840881687368647 ep528 ep529 ep530 ep531 ep517 ep518 ep519 ep520 (@ep532 655360000 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 ep523 ep525 ep526 ep527 (@ep534 167772160000 1048575 1048576 270971 655360000 (ep659 rfl rfl) rfl) ep802 rfl) (@ep803 655360000 4192940769060699592537 1048192269951249112104960 ep660 ep661 129981163840881687368647 ep528 ep529 ep530 (@ep804 167772160000 93 524288 270971 655360000 (ep809 rfl rfl) rfl) ep810 rfl) rfl rfl))

noncomputable abbrev qz751 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 149500 1000)))

noncomputable abbrev qz689 := qz751

noncomputable abbrev qz453 := qz689

noncomputable abbrev qz139 := (BSN.headSumC qz453 9)

noncomputable abbrev qz140 := qz453

noncomputable abbrev qz690 := (@Neg.neg Complex Complex.instNeg qz751)

noncomputable abbrev qz454 := qz690

noncomputable abbrev qz141 := qz454

noncomputable abbrev qz691 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz141)

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq qz139 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 8) qz691) Bool.false 161700167471 549755813888 1091698491529 343597383680000 Bool.true 266133988727 274877906944 1091312847779 343597383680000

noncomputable def ep812 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 8) qz691 Bool.false 708268716357 1099511627776 390785407109 137438953472000 Bool.true 252460835513 274877906944 195371238367 68719476736000 Bool.true

noncomputable abbrev qz692 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz141)

noncomputable def ep813 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 7) qz692) Bool.false 708268716357 1099511627776 390785407109 137438953472000 Bool.true 252460835513 274877906944 195371238367 68719476736000

noncomputable def ep814 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 7) qz692 Bool.false 837418351457 1099511627776 1709102637999 687194767360000 Bool.true 614844049177 1099511627776 1708468744249 687194767360000 Bool.true

noncomputable abbrev qz693 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz141)

noncomputable def ep815 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 6) qz693) Bool.false 837418351457 1099511627776 1709102637999 687194767360000 Bool.true 614844049177 1099511627776 1708468744249 687194767360000

noncomputable def ep816 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 6) qz693 Bool.false 1139514557915 1099511627776 1444441608569 687194767360000 Bool.true 946844998417 1099511627776 1443764053569 687194767360000 Bool.true

noncomputable abbrev qz694 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz141)

noncomputable def ep817 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 5) qz694) Bool.false 1139514557915 1099511627776 1444441608569 687194767360000 Bool.true 946844998417 1099511627776 1443764053569 687194767360000

noncomputable def ep818 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 5) qz694 Bool.false 1274859154855 1099511627776 231037065769 137438953472000 Bool.true 474122738953 1099511627776 230811623269 137438953472000 Bool.true

noncomputable abbrev qz695 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz141)

noncomputable def ep819 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 4) qz695) Bool.false 1274859154855 1099511627776 231037065769 137438953472000 Bool.true 474122738953 1099511627776 230811623269 137438953472000

noncomputable def ep820 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 4) qz695 Bool.false 727544421241 1099511627776 831336588571 687194767360000 Bool.true 32866244025 68719476736 51925009481 42949672960000 Bool.false

noncomputable def ep821 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz141)) Bool.false 727544421241 1099511627776 831336588571 687194767360000 Bool.true 32866244025 68719476736 51925009481 42949672960000

noncomputable def ep822 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz141) Bool.false 80727173739 274877906944 114430923947 171798691840000 Bool.true 4591830815 137438953472 57137504161 85899345920000 Bool.false

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz141)) Bool.false 80727173739 274877906944 114430923947 171798691840000 Bool.true 4591830815 137438953472 57137504161 85899345920000

noncomputable def ep824 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz141) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz140)

noncomputable abbrev qz752 := (Enclosure.sfrac Bool.false 149500 1000)

noncomputable abbrev qz696 := qz752

noncomputable abbrev qz455 := qz696

noncomputable abbrev qz142 := (@HMul.hMul Real Real Real qz269 qz455 (Real.log qz280))

noncomputable abbrev qz143 := qz455

noncomputable abbrev qz456 := (@Eq.refl Real qz696)

noncomputable abbrev qz144 := qz456

noncomputable def ep826 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz141) (Complex.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz142)))) Bool.true 194150733205 274877906944 114430923947 171798691840000 Bool.true 4591830815 137438953472 57137504161 85899345920000 (BSN.cpow_neg_s_mk qz143 149500 1000 2 qz144 rfl)

noncomputable def ep827 := nat_lit 7382378562129060345966519965154023649868562923541207603341845345451005536491105

noncomputable def ep828 := nat_lit 13129372990533678800014348836091447441342954016983637231533375474520371091041

noncomputable def ep829 := nat_lit 19313543915972389235664671915383056739512633350389951167520445677793886280472161

noncomputable def ep830 := BSN.sin_dyadic_bound_f 3271752917 2147483648 3 2 1048576 320313 ep827 ep64 ep828 ep829 ep66 ep828 1047404 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3271752917) qz19 0 2 ep827 ep64 ep828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3271752917) qz20 0 2 ep829 ep66 ep828 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz145 := (Enclosure.Real.IsNear.const Bool.false 149500 1000)

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6791187) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz458 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep831 := @Enclosure.Real.IsNear.cos_image qz142 qz457 Bool.false 6791187 65536 299 320000 Bool.true 1047404 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 (Real.log qz280) 149500 1000 0 1 363408 524288 1 160000 6791187 65536 299 320000 qz145 qz285 rfl) (Enclosure.sfrac_false_div 6791187 65536) (BSN.cos_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14389321504080856612864) qz458) 226375608064910080 72057594037927936 Bool.false 1047404 1048576 16 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 6791187 65536 226375608064910080 72057594037927936 16 14389321504080856612864 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047404 1048576 14389321504080856612864 9444732965739290427392 3271752917 2147483648 320313 320000 (ep830 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep832 := nat_lit 4107156700289715160559184135679387115456465159308219173959484469905901018535521

noncomputable def ep833 := nat_lit 12295211354888078124077523709365978451486709569890690247415386658768662313424481

noncomputable def ep834 := BSN.cos_dyadic_bound_f 3271752917 2147483648 3 2 1048576 320313 ep832 ep57 ep828 ep833 ep60 ep828 49544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3271752917) qz15 0 2 ep832 ep57 ep828 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3271752917) qz16 0 2 ep833 ep60 ep828 rfl rfl rfl rfl) rfl rfl

noncomputable def ep835 := @Enclosure.Real.IsNear.sin_image qz142 qz457 Bool.false 6791187 65536 299 320000 Bool.false 49544 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 (Real.log qz280) 149500 1000 0 1 363408 524288 1 160000 6791187 65536 299 320000 qz145 qz285 rfl) (Enclosure.sfrac_false_div 6791187 65536) (BSN.sin_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14389321504080856612864) qz458) 226375608064910080 72057594037927936 Bool.false 49544 1048576 16 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 6791187 65536 226375608064910080 72057594037927936 16 14389321504080856612864 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 49544 1048576 14389321504080856612864 9444732965739290427392 3271752917 2147483648 320313 320000 (ep834 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep836 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz282 (Real.cos qz142)) (@HMul.hMul Real Real Real qz0 qz282 (@Neg.neg Real Real.instNeg (Real.sin qz142))) Bool.true 194150733205 274877906944 114430923947 171798691840000 Bool.true 4591830815 137438953472 57137504161 85899345920000 (@Enclosure.Real.IsNear.mulLit_ft qz282 (Real.cos qz142) 741455 1048576 1 1048576 261851 262144 301 320000 194150733205 274877906944 114430923947 171798691840000 qz287 (@Enclosure.Real.IsNear.recentre' (Real.cos qz142) Bool.true 1047404 1048576 48160000 51200000000 261851 262144 301 320000 (ep831 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz282 (@Neg.neg Real Real.instNeg (Real.sin qz142)) 741455 1048576 1 1048576 6193 131072 301 320000 4591830815 137438953472 57137504161 85899345920000 qz287 (@Enclosure.Real.IsNear.neg (Real.sin qz142) Bool.false 6193 131072 301 320000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz142) Bool.false 49544 1048576 48160000 51200000000 6193 131072 301 320000 (ep835 rfl rfl) rfl)) rfl)

noncomputable def ep837 := @ep824 194150733205 274877906944 114430923947 171798691840000 Bool.true 4591830815 137438953472 57137504161 85899345920000 Bool.false 80727173739 80727173739 274877906944 114430923947 171798691840000 Bool.true 4591830815 4591830815 137438953472 57137504161 85899345920000 (ep825 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz21)) (ep826 ep836) rfl rfl

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz269 qz455 qz561)

noncomputable def ep838 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz141) (Complex.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 404635726285 1099511627776 373612892783 687194767360000 Bool.true 61140657235 137438953472 46712514801 85899345920000 (BSN.cpow_neg_s_mk qz143 149500 1000 3 qz144 rfl)

noncomputable def ep839 := nat_lit 455139219353328599126462258072320315241721386827859224317798951846482864800000

noncomputable def ep840 := nat_lit 162151707598567070812849826353976104458689122468942114895137395984100000000

noncomputable def ep841 := nat_lit 1365093354644788663237761074564252993516246782238639788723606580747480394400000

noncomputable def ep842 := BSN.cos_dyadic_bound_f 1889035810 2147483648 3 2 1048576 320313 ep839 ep57 ep840 ep841 ep60 ep840 668383 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1889035810) qz15 0 2 ep839 ep57 ep840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1889035810) qz16 0 2 ep841 ep60 ep840 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172220711) qz30)

noncomputable def ep843 := @Enclosure.Real.IsNear.cos_image qz146 qz459 Bool.false 172220711 1048576 299 320000 Bool.false 668383 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz561 149500 1000 0 1 575989 524288 1 160000 172220711 1048576 299 320000 qz145 qz292 rfl) (Enclosure.sfrac_false_div 172220711 1048576) (BSN.cos_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132929077686420396572672) qz31) 226375608064910080 72057594037927936 Bool.false 668383 1048576 26 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 172220711 1048576 226375608064910080 72057594037927936 26 132929077686420396572672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 668383 1048576 132929077686420396572672 151115727451828646838272 1889035810 2147483648 320313 320000 (ep842 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep844 := nat_lit 819120873469912624770981784669093386551531544992171450080122003406881876640000

noncomputable def ep845 := nat_lit 2145054042037468718190302917271623860608697121162165986785727405519763991200000

noncomputable def ep846 := BSN.sin_dyadic_bound_f 1889035810 2147483648 3 2 1048576 320313 ep844 ep64 ep840 ep845 ep66 ep840 807944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1889035810) qz19 0 2 ep844 ep64 ep840 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1889035810) qz20 0 2 ep845 ep66 ep840 rfl rfl rfl rfl) rfl rfl

noncomputable def ep847 := @Enclosure.Real.IsNear.sin_image qz146 qz459 Bool.false 172220711 1048576 299 320000 Bool.false 807944 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz561 149500 1000 0 1 575989 524288 1 160000 172220711 1048576 299 320000 qz145 qz292 rfl) (Enclosure.sfrac_false_div 172220711 1048576) (BSN.sin_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 132929077686420396572672) qz31) 226375608064910080 72057594037927936 Bool.false 807944 1048576 26 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 172220711 1048576 226375608064910080 72057594037927936 26 132929077686420396572672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 807944 1048576 132929077686420396572672 151115727451828646838272 1889035810 2147483648 320313 320000 (ep846 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep848 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz288 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz288 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 404635726285 1099511627776 373612892783 687194767360000 Bool.true 61140657235 137438953472 46712514801 85899345920000 (@Enclosure.Real.IsNear.mulLit_ff qz288 (Real.cos qz146) 605395 1048576 1 1048576 668383 1048576 301 320000 404635726285 1099511627776 373612892783 687194767360000 qz294 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 668383 1048576 48160000 51200000000 668383 1048576 301 320000 (ep843 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz288 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 605395 1048576 1 1048576 100993 131072 301 320000 61140657235 137438953472 46712514801 85899345920000 qz294 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.false 100993 131072 301 320000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.false 807944 1048576 48160000 51200000000 100993 131072 301 320000 (ep847 rfl rfl) rfl)) rfl)

noncomputable def ep849 := @ep822 404635726285 1099511627776 373612892783 687194767360000 Bool.true 61140657235 137438953472 46712514801 85899345920000 Bool.false 199985887719509934997504 727544421241 1099511627776 831336588571 687194767360000 Bool.true 9034204366702746009600 32866244025 68719476736 51925009481 42949672960000 (ep823 (BSN.head_sum_c_succ qz140 2 3 rfl rfl) (ep837 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep838 ep848) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz269 qz455 qz563)

noncomputable def ep850 := @Enclosure.Complex.IsNear.of_eq qz695 (Complex.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.false 273657366807 549755813888 161924370137 343597383680000 Bool.false 51737165447 1099511627776 323257964649 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 4 qz144 rfl)

noncomputable def ep851 := nat_lit 6511648391873586861403982258812478125694940303101739757607910687029424291840000

noncomputable def ep852 := nat_lit 10219159577756219126393259331340072427495836910040843439786855242137600000000

noncomputable def ep853 := nat_lit 17037771910828741234615316829400987354794612295983537999594396890875507507200000

noncomputable def ep854 := BSN.sin_dyadic_bound_f 3170858760 2147483648 3 2 1048576 320313 ep851 ep64 ep852 ep853 ep66 ep852 1043922 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3170858760) qz19 0 2 ep851 ep64 ep852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3170858760) qz20 0 2 ep853 ep66 ep852 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217318283) qz30)

noncomputable def ep855 := @Enclosure.Real.IsNear.cos_image qz147 qz460 Bool.false 217318283 1048576 299 320000 Bool.false 1043922 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz563 149500 1000 0 1 726817 524288 1 160000 217318283 1048576 299 320000 qz145 qz299 rfl) (Enclosure.sfrac_false_div 217318283 1048576) (BSN.cos_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223129348969550940471296) qz31) 226375608064910080 72057594037927936 Bool.false 1043922 1048576 32 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 217318283 1048576 226375608064910080 72057594037927936 32 223129348969550940471296 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1043922 1048576 223129348969550940471296 151115727451828646838272 3170858760 2147483648 320313 320000 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := nat_lit 3622124288630995464836164925709750102020520540349873573533188984012852428800000

noncomputable def ep857 := nat_lit 10845934546737473956255708258466570161206569947229539033719993241554282086400000

noncomputable def ep858 := BSN.cos_dyadic_bound_f 3170858760 2147483648 3 2 1048576 320313 ep856 ep57 ep852 ep857 ep60 ep852 98681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3170858760) qz15 0 2 ep856 ep57 ep852 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3170858760) qz16 0 2 ep857 ep60 ep852 rfl rfl rfl rfl) rfl rfl

noncomputable def ep859 := @Enclosure.Real.IsNear.sin_image qz147 qz460 Bool.false 217318283 1048576 299 320000 Bool.true 98681 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz563 149500 1000 0 1 726817 524288 1 160000 217318283 1048576 299 320000 qz145 qz299 rfl) (Enclosure.sfrac_false_div 217318283 1048576) (BSN.sin_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223129348969550940471296) qz31) 226375608064910080 72057594037927936 Bool.false 98681 1048576 32 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 217318283 1048576 226375608064910080 72057594037927936 32 223129348969550940471296 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 98681 1048576 223129348969550940471296 151115727451828646838272 3170858760 2147483648 320313 320000 (ep858 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep860 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz295 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz295 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.false 273657366807 549755813888 161924370137 343597383680000 Bool.false 51737165447 1099511627776 323257964649 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz295 (Real.cos qz147) 524287 1048576 1 1048576 521961 524288 301 320000 273657366807 549755813888 161924370137 343597383680000 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.false 1043922 1048576 48160000 51200000000 521961 524288 301 320000 (ep855 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz295 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 524287 1048576 1 1048576 98681 1048576 301 320000 51737165447 1099511627776 323257964649 687194767360000 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.true 98681 1048576 301 320000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.true 98681 1048576 48160000 51200000000 98681 1048576 301 320000 (ep859 rfl rfl) rfl)) rfl)

noncomputable def ep861 := @ep820 273657366807 549755813888 161924370137 343597383680000 Bool.false 51737165447 1099511627776 323257964649 687194767360000 Bool.false 700861232269878351626240 1274859154855 1099511627776 231037065769 137438953472000 Bool.true 32581466529489284497408 474122738953 1099511627776 230811623269 137438953472000 (ep821 (BSN.head_sum_c_succ qz140 3 4 rfl rfl) (ep849 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep850 ep860) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz269 qz455 qz564)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq qz694 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 33836149235 274877906944 72314069931 171798691840000 Bool.true 59090282433 137438953472 36213242153 85899345920000 (BSN.cpow_neg_s_mk qz143 149500 1000 5 qz144 rfl)

noncomputable def ep863 := nat_lit 128587106573522951006961661071202576

noncomputable def ep864 := BSN.sin_dyadic_bound_f 598824218 2147483648 2 1 1048576 320313 ep863 ep80 ep863 ep863 ep81 ep863 288620 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 598824218) qz19 0 1 ep863 ep80 ep863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 598824218) qz20 0 1 ep863 ep81 ep863 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7884331) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz462 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep865 := @Enclosure.Real.IsNear.cos_image qz148 qz461 Bool.false 7884331 32768 299 320000 Bool.true 288620 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz564 149500 1000 0 1 843808 524288 1 160000 7884331 32768 299 320000 qz145 qz304 rfl) (Enclosure.sfrac_false_div 7884331 32768) (BSN.cos_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1316828381441857421312) qz462) 226375608064910080 72057594037927936 Bool.false 288620 1048576 38 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 7884331 32768 226375608064910080 72057594037927936 38 1316828381441857421312 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 288620 1048576 1316828381441857421312 4722366482869645213696 598824218 2147483648 320313 320000 (ep864 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep866 := BSN.cos_dyadic_bound_f 598824218 2147483648 2 1 1048576 320313 ep863 ep95 ep863 ep863 ep96 ep863 1008072 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 598824218) qz15 0 1 ep863 ep95 ep863 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 598824218) qz16 0 1 ep863 ep96 ep863 rfl rfl rfl rfl) rfl rfl

noncomputable def ep867 := @Enclosure.Real.IsNear.sin_image qz148 qz461 Bool.false 7884331 32768 299 320000 Bool.false 1008072 1048576 1 160000 (@Enclosure.Real.IsNear.mulLit_ff qz143 qz564 149500 1000 0 1 843808 524288 1 160000 7884331 32768 299 320000 qz145 qz304 rfl) (Enclosure.sfrac_false_div 7884331 32768) (BSN.sin_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1316828381441857421312) qz462) 226375608064910080 72057594037927936 Bool.false 1008072 1048576 38 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 7884331 32768 226375608064910080 72057594037927936 38 1316828381441857421312 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1008072 1048576 1316828381441857421312 4722366482869645213696 598824218 2147483648 320313 320000 (ep866 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep868 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 33836149235 274877906944 72314069931 171798691840000 Bool.true 59090282433 137438953472 36213242153 85899345920000 (@Enclosure.Real.IsNear.mulLit_ft qz301 (Real.cos qz148) 468937 1048576 1 1048576 72155 262144 301 320000 33836149235 274877906944 72314069931 171798691840000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 288620 1048576 48160000 51200000000 72155 262144 301 320000 (ep865 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz301 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 468937 1048576 1 1048576 126009 131072 301 320000 59090282433 137438953472 36213242153 85899345920000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 126009 131072 301 320000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 1008072 1048576 48160000 51200000000 126009 131072 301 320000 (ep867 rfl rfl) rfl)) rfl)

noncomputable def ep869 := @ep818 33836149235 274877906944 72314069931 171798691840000 Bool.true 59090282433 137438953472 36213242153 85899345920000 Bool.false 313227376611892668661760 1139514557915 1099511627776 1444441608569 687194767360000 Bool.true 130133385682629976653824 946844998417 1099511627776 1443764053569 687194767360000 (ep819 (BSN.head_sum_c_succ qz140 4 5 rfl rfl) (ep861 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep862 ep868) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz269 qz455 qz566)

noncomputable def ep870 := @Enclosure.Complex.IsNear.of_eq qz693 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 151048103229 549755813888 26466102943 68719476736000 Bool.false 41500118655 137438953472 6617617267 17179869184000 (BSN.cpow_neg_s_mk qz143 149500 1000 6 qz144 rfl)

noncomputable def ep871 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz566 149500 1000 0 1 4034681531866359 2251799813685248 3125000001 500000000000000 1206369778028041341 4503599627370496 934375000299 1000000000000000 qz145 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 3125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz567) Bool.false 33845361775666394038272 18889465931478580854784 1000000000320000 160000000000000000000 4034681531866359 2251799813685248 3125000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep116 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep872 := nat_lit 365140602990999221768451558572557630786325991660700538240258741118539503190625

noncomputable def ep873 := nat_lit 104379313899742607016618897147739998865653932915570888385972945865250390625

noncomputable def ep874 := nat_lit 1095213050345198180091321437923377412361246667116270472944004277463888008790625

noncomputable def ep875 := BSN.cos_dyadic_bound_f 1787832405 2147483648 3 2 1048576 320313 ep872 ep57 ep873 ep874 ep60 ep873 705702 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1787832405) qz15 0 2 ep872 ep57 ep873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1787832405) qz16 0 2 ep874 ep60 ep873 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 280879851) qz30)

noncomputable def ep876 := @Enclosure.Real.IsNear.cos_image qz149 qz463 Bool.false 280879851 1048576 981 1048576 Bool.true 705702 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1206369778028041341 4503599627370496 934375000299 1000000000000000 280879851 1048576 981 1048576 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 280879851 1048576) (BSN.cos_reduce2 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125807521197278177001472) qz31) 226375608064910080 72057594037927936 Bool.false 705702 1048576 42 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 280879851 1048576 226375608064910080 72057594037927936 42 125807521197278177001472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 705702 1048576 125807521197278177001472 151115727451828646838272 1787832405 2147483648 320313 320000 (ep875 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep877 := nat_lit 10216619494712652114951665249460200625

noncomputable def ep878 := BSN.sin_dyadic_bound_f 1787832405 2147483648 2 1 1048576 320313 ep877 ep80 ep877 ep877 ep81 ep877 775560 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1787832405) qz19 0 1 ep877 ep80 ep877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1787832405) qz20 0 1 ep877 ep81 ep877 rfl rfl rfl rfl) rfl rfl

noncomputable def ep879 := @Enclosure.Real.IsNear.sin_image qz149 qz463 Bool.false 280879851 1048576 981 1048576 Bool.true 775560 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 1206369778028041341 4503599627370496 934375000299 1000000000000000 280879851 1048576 981 1048576 (ep871 rfl) rfl) (Enclosure.sfrac_false_div 280879851 1048576) (BSN.sin_reduce2 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 125807521197278177001472) qz31) 226375608064910080 72057594037927936 Bool.false 775560 1048576 42 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 280879851 1048576 226375608064910080 72057594037927936 42 125807521197278177001472 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 775560 1048576 125807521197278177001472 151115727451828646838272 1787832405 2147483648 320313 320000 (ep878 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep880 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 151048103229 549755813888 26466102943 68719476736000 Bool.false 41500118655 137438953472 6617617267 17179869184000 (@Enclosure.Real.IsNear.mulLit_ft qz306 (Real.cos qz149) 428079 1048576 1 1048576 352851 524288 617221 655360000 151048103229 549755813888 26466102943 68719476736000 qz310 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 705702 1048576 158008576 167772160000 352851 524288 617221 655360000 (ep876 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 428079 1048576 1 1048576 96945 131072 617221 655360000 41500118655 137438953472 6617617267 17179869184000 qz310 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 96945 131072 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 775560 1048576 158008576 167772160000 96945 131072 617221 655360000 (ep879 rfl rfl) rfl)) rfl)

noncomputable def ep881 := @ep816 151048103229 549755813888 26466102943 68719476736000 Bool.false 41500118655 137438953472 6617617267 17179869184000 Bool.false 460375607369990265634816 837418351457 1099511627776 1709102637999 687194767360000 Bool.true 84503522667373782892544 614844049177 1099511627776 1708468744249 687194767360000 (ep817 (BSN.head_sum_c_succ qz140 5 6 rfl rfl) (ep869 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep870 ep880) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz269 qz455 qz568)

noncomputable def ep882 := @Enclosure.Complex.IsNear.of_eq qz692 (Complex.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 32287408775 274877906944 122412198773 343597383680000 Bool.true 394999292875 1099511627776 245243639421 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 7 qz144 rfl)

noncomputable def ep883 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz568 149500 1000 0 1 4381796493761783 2251799813685248 3125000001 500000000000000 1310157151634773117 4503599627370496 934375000299 1000000000000000 qz145 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 3125000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz569) Bool.false 36757173121942042968064 18889465931478580854784 1000000000320000 160000000000000000000 4381796493761783 2251799813685248 3125000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep127 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep884 := nat_lit 212079997820144923575822984838209201

noncomputable def ep885 := BSN.sin_dyadic_bound_f 678617301 2147483648 2 1 1048576 320313 ep884 ep80 ep884 ep884 ep81 ep884 325868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 678617301) qz19 0 1 ep884 ep80 ep884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 678617301) qz20 0 1 ep884 ep81 ep884 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz697 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 76261183) qz17)

noncomputable def ep886 := @Enclosure.Real.IsNear.cos_image qz150 qz697 Bool.false 76261183 262144 981 1048576 Bool.true 325868 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1310157151634773117 4503599627370496 934375000299 1000000000000000 76261183 262144 981 1048576 (ep883 rfl) rfl) (Enclosure.sfrac_false_div 76261183 262144) (BSN.cos_reduce1 qz697 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11938361827221754085376) qz286) 226375608064910080 72057594037927936 Bool.false 325868 1048576 46 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 76261183 262144 226375608064910080 72057594037927936 46 11938361827221754085376 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 325868 1048576 11938361827221754085376 37778931862957161709568 678617301 2147483648 320313 320000 (ep885 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep887 := BSN.cos_dyadic_bound_f 678617301 2147483648 2 1 1048576 320313 ep884 ep95 ep884 ep884 ep96 ep884 996655 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 678617301) qz15 0 1 ep884 ep95 ep884 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 678617301) qz16 0 1 ep884 ep96 ep884 rfl rfl rfl rfl) rfl rfl

noncomputable def ep888 := @Enclosure.Real.IsNear.sin_image qz150 qz697 Bool.false 76261183 262144 981 1048576 Bool.false 996655 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 1310157151634773117 4503599627370496 934375000299 1000000000000000 76261183 262144 981 1048576 (ep883 rfl) rfl) (Enclosure.sfrac_false_div 76261183 262144) (BSN.sin_reduce1 qz697 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11938361827221754085376) qz286) 226375608064910080 72057594037927936 Bool.false 996655 1048576 46 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 76261183 262144 226375608064910080 72057594037927936 46 11938361827221754085376 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 996655 1048576 11938361827221754085376 37778931862957161709568 678617301 2147483648 320313 320000 (ep887 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep889 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz311 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz311 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 32287408775 274877906944 122412198773 343597383680000 Bool.true 394999292875 1099511627776 245243639421 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz311 (Real.cos qz150) 396325 1048576 1 1048576 81467 262144 617221 655360000 32287408775 274877906944 122412198773 343597383680000 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 325868 1048576 158008576 167772160000 81467 262144 617221 655360000 (ep886 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz311 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 396325 1048576 1 1048576 996655 1048576 617221 655360000 394999292875 1099511627776 245243639421 687194767360000 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 996655 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 996655 1048576 158008576 167772160000 996655 1048576 617221 655360000 (ep888 rfl rfl) rfl)) rfl)

noncomputable def ep890 := @ep814 32287408775 274877906944 122412198773 343597383680000 Bool.true 394999292875 1099511627776 245243639421 687194767360000 Bool.false 194687422306125776683008 708268716357 1099511627776 390785407109 137438953472000 Bool.true 1110334496818350472036352 252460835513 274877906944 195371238367 68719476736000 (ep815 (BSN.head_sum_c_succ qz140 6 7 rfl rfl) (ep881 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep882 ep889) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz269 qz455 qz570)

noncomputable def ep891 := @Enclosure.Complex.IsNear.of_eq qz691 (Complex.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 384868381415 1099511627776 229469947513 687194767360000 Bool.true 6836576607 137438953472 14307081993 42949672960000 (BSN.cpow_neg_s_mk qz143 149500 1000 8 qz144 rfl)

noncomputable def ep892 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz570 149500 1000 0 1 9364972152248037 4503599627370496 6250000003 1000000000000000 2800126673522163063 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 39279540158062550581248 18889465931478580854784 1000000000480000 160000000000000000000 9364972152248037 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep141 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep893 := nat_lit 5721617687576195839678558365351800010365279489115940435542490924521254912327680

noncomputable def ep894 := nat_lit 7892891609298161662878501826730294405998431578155786037734381499634187042816

noncomputable def ep895 := nat_lit 14972410214379744461227754334868579550489829772748544153788287232270545610407936

noncomputable def ep896 := BSN.sin_dyadic_bound_f 3070114108 2147483648 3 2 1048576 320313 ep893 ep64 ep894 ep895 ep66 ep894 1038145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3070114108) qz19 0 2 ep893 ep64 ep894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3070114108) qz20 0 2 ep895 ep66 ep894 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 325977647) qz30)

noncomputable def ep897 := @Enclosure.Real.IsNear.cos_image qz151 qz464 Bool.false 325977647 1048576 981 1048576 Bool.true 1038145 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 2800126673522163063 9007199254740992 1868750000897 2000000000000000 325977647 1048576 981 1048576 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 325977647 1048576) (BSN.cos_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216040074282537712615424) qz31) 226375608064910080 72057594037927936 Bool.false 1038145 1048576 49 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 325977647 1048576 226375608064910080 72057594037927936 49 216040074282537712615424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1038145 1048576 216040074282537712615424 151115727451828646838272 3070114108 2147483648 320313 320000 (ep896 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep898 := nat_lit 3182184444924241316116033981562880136605599019099147257984821349844979034423296

noncomputable def ep899 := nat_lit 9530767551554127625022344941035179821004800194141130201878995286535668729184256

noncomputable def ep900 := BSN.cos_dyadic_bound_f 3070114108 2147483648 3 2 1048576 320313 ep898 ep57 ep894 ep899 ep60 ep894 147528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3070114108) qz15 0 2 ep898 ep57 ep894 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3070114108) qz16 0 2 ep899 ep60 ep894 rfl rfl rfl rfl) rfl rfl

noncomputable def ep901 := @Enclosure.Real.IsNear.sin_image qz151 qz464 Bool.false 325977647 1048576 981 1048576 Bool.false 147528 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 2800126673522163063 9007199254740992 1868750000897 2000000000000000 325977647 1048576 981 1048576 (ep892 rfl) rfl) (Enclosure.sfrac_false_div 325977647 1048576) (BSN.sin_reduce1 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216040074282537712615424) qz31) 226375608064910080 72057594037927936 Bool.false 147528 1048576 49 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 325977647 1048576 226375608064910080 72057594037927936 49 216040074282537712615424 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 147528 1048576 216040074282537712615424 151115727451828646838272 3070114108 2147483648 320313 320000 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz316 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz316 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 384868381415 1099511627776 229469947513 687194767360000 Bool.true 6836576607 137438953472 14307081993 42949672960000 (@Enclosure.Real.IsNear.mulLit_ft qz316 (Real.cos qz151) 370727 1048576 1 1048576 1038145 1048576 617221 655360000 384868381415 1099511627776 229469947513 687194767360000 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 1038145 1048576 158008576 167772160000 1038145 1048576 617221 655360000 (ep897 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz316 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 370727 1048576 1 1048576 18441 131072 617221 655360000 6836576607 137438953472 14307081993 42949672960000 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 18441 131072 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 147528 1048576 158008576 167772160000 18441 131072 617221 655360000 (ep901 rfl rfl) rfl)) rfl)

noncomputable def ep903 := @ep812 384868381415 1099511627776 229469947513 687194767360000 Bool.true 6836576607 137438953472 14307081993 42949672960000 Bool.false 355582428695382030548992 161700167471 549755813888 1091698491529 343597383680000 Bool.true 36577176893967925510144 266133988727 274877906944 1091312847779 343597383680000 (ep813 (BSN.head_sum_c_succ qz140 7 8 rfl rfl) (ep890 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep891 ep902) rfl rfl

theorem EMLast.d13 : Enclosure.Complex.IsNear qz139 Bool.false 161700167471 549755813888 1091698491529 343597383680000 Bool.true 266133988727 274877906944 1091312847779 343597383680000 := ep811 (BSN.head_sum_c_succ qz140 8 9 rfl rfl) (ep903 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz152 := (BSN.headSumC qz453 17)

noncomputable abbrev qz698 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz141)

noncomputable def ep904 := @Enclosure.Complex.IsNear.of_eq qz152 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 16) qz698) Bool.false 1258890581519 1099511627776 3670567028329 687194767360000 Bool.true 628762025231 549755813888 1834741440727 343597383680000

noncomputable def ep905 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 16) qz698 Bool.false 123608543671 137438953472 43851530761 8589934592000 Bool.true 654477729245 549755813888 350755947713 68719476736000 Bool.false

noncomputable abbrev qz699 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz141)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 15) qz699) Bool.false 123608543671 137438953472 43851530761 8589934592000 Bool.true 654477729245 549755813888 350755947713 68719476736000

noncomputable def ep907 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 15) qz699 Bool.false 1248979245485 1099511627776 3340414352273 687194767360000 Bool.true 597606957749 549755813888 835047314787 171798691840000 Bool.true

noncomputable abbrev qz700 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz141)

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 14) qz700) Bool.false 1248979245485 1099511627776 3340414352273 687194767360000 Bool.true 597606957749 549755813888 835047314787 171798691840000

noncomputable def ep909 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 14) qz700 Bool.false 1170895698881 1099511627776 3167267727849 687194767360000 Bool.true 1478505679095 1099511627776 3166584977849 687194767360000 Bool.false

noncomputable def ep910 := nat_lit 1314151597769732493672448

noncomputable abbrev qz701 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz141)

noncomputable def ep911 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 13) qz701) Bool.false 1170895698881 1099511627776 3167267727849 687194767360000 Bool.true 1478505679095 1099511627776 3166584977849 687194767360000

noncomputable def ep912 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 13) qz701 Bool.false 435584867191 549755813888 149356045731 34359738368000 Bool.true 1422302971053 1099511627776 597392302799 137438953472000 Bool.false

noncomputable abbrev qz702 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz141)

noncomputable def ep913 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 12) qz702) Bool.false 435584867191 549755813888 149356045731 34359738368000 Bool.true 1422302971053 1099511627776 597392302799 137438953472000

noncomputable def ep914 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 12) qz702 Bool.false 646749875885 1099511627776 2799825976737 687194767360000 Bool.true 1197850723977 1099511627776 2799666509237 687194767360000 Bool.false

noncomputable abbrev qz703 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz141)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 11) qz703) Bool.false 646749875885 1099511627776 2799825976737 687194767360000 Bool.true 1197850723977 1099511627776 2799666509237 687194767360000

noncomputable def ep916 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 11) qz703 Bool.false 334618186809 1099511627776 2604069577319 687194767360000 Bool.true 1086156249761 1099511627776 2604306347319 687194767360000 Bool.false

noncomputable abbrev qz704 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz141)

noncomputable def ep917 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 10) qz704) Bool.false 334618186809 1099511627776 2604069577319 687194767360000 Bool.true 1086156249761 1099511627776 2604306347319 687194767360000

noncomputable def ep918 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 10) qz704 Bool.false 254695953317 1099511627776 2399254623429 687194767360000 Bool.true 1424542161083 1099511627776 2399004224679 687194767360000 Bool.false

noncomputable abbrev qz705 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz141)

noncomputable def ep919 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 10) (@HAdd.hAdd Complex Complex Complex qz4 qz139 qz705) Bool.false 254695953317 1099511627776 2399254623429 687194767360000 Bool.true 1424542161083 1099511627776 2399004224679 687194767360000

noncomputable def ep920 := @Enclosure.Complex.IsNear.addLitP qz139 qz705 Bool.false 161700167471 549755813888 1091698491529 343597383680000 Bool.true 266133988727 274877906944 1091312847779 343597383680000 Bool.true

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz269 qz455 qz580)

noncomputable def ep921 := @Enclosure.Complex.IsNear.of_eq qz705 (Complex.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 68704381625 1099511627776 215857640371 687194767360000 Bool.true 360006206175 1099511627776 216378529121 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 9 qz144 rfl)

noncomputable def ep922 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz580 149500 1000 0 1 9895417793173221 4503599627370496 6250000003 1000000000000000 2958729920158793079 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 41504390431577613533184 18889465931478580854784 1000000000480000 160000000000000000000 9895417793173221 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep172 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep923 := nat_lit 26894024442108542452960397442585616

noncomputable def ep924 := BSN.sin_dyadic_bound_f 404961698 2147483648 2 1 1048576 320313 ep923 ep80 ep923 ep923 ep81 ep923 196565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 404961698) qz19 0 1 ep923 ep80 ep923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 404961698) qz20 0 1 ep923 ep81 ep923 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 344441495) qz30)

noncomputable def ep925 := @Enclosure.Real.IsNear.cos_image qz153 qz465 Bool.false 344441495 1048576 981 1048576 Bool.true 196565 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 2958729920158793079 9007199254740992 1868750000897 2000000000000000 344441495 1048576 981 1048576 (ep922 rfl) rfl) (Enclosure.sfrac_false_div 344441495 1048576) (BSN.cos_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28496646179299178577920) qz31) 226375608064910080 72057594037927936 Bool.false 196565 1048576 52 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 344441495 1048576 226375608064910080 72057594037927936 52 28496646179299178577920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 196565 1048576 28496646179299178577920 151115727451828646838272 404961698 2147483648 320313 320000 (ep924 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep926 := BSN.cos_dyadic_bound_f 404961698 2147483648 2 1 1048576 320313 ep923 ep95 ep923 ep923 ep96 ep923 1029987 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 404961698) qz15 0 1 ep923 ep95 ep923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 404961698) qz16 0 1 ep923 ep96 ep923 rfl rfl rfl rfl) rfl rfl

noncomputable def ep927 := @Enclosure.Real.IsNear.sin_image qz153 qz465 Bool.false 344441495 1048576 981 1048576 Bool.false 1029987 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 2958729920158793079 9007199254740992 1868750000897 2000000000000000 344441495 1048576 981 1048576 (ep922 rfl) rfl) (Enclosure.sfrac_false_div 344441495 1048576) (BSN.sin_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28496646179299178577920) qz31) 226375608064910080 72057594037927936 Bool.false 1029987 1048576 52 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 344441495 1048576 226375608064910080 72057594037927936 52 28496646179299178577920 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1029987 1048576 28496646179299178577920 151115727451828646838272 404961698 2147483648 320313 320000 (ep926 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep928 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz321 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz321 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 68704381625 1099511627776 215857640371 687194767360000 Bool.true 360006206175 1099511627776 216378529121 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz321 (Real.cos qz153) 349525 1048576 1 1048576 196565 1048576 617221 655360000 68704381625 1099511627776 215857640371 687194767360000 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 196565 1048576 158008576 167772160000 196565 1048576 617221 655360000 (ep925 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz321 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 349525 1048576 1 1048576 1029987 1048576 617221 655360000 360006206175 1099511627776 216378529121 687194767360000 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 1029987 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 1029987 1048576 158008576 167772160000 1029987 1048576 617221 655360000 (ep927 rfl rfl) rfl)) rfl)

noncomputable def ep929 := @ep920 68704381625 1099511627776 215857640371 687194767360000 Bool.true 360006206175 1099511627776 216378529121 687194767360000 Bool.false 140020581109767388266496 254695953317 1099511627776 2399254623429 687194767360000 Bool.true 391575167591977532260352 1424542161083 1099511627776 2399004224679 687194767360000 EMLast.d13 (ep921 ep928) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz269 qz455 qz583)

noncomputable def ep930 := @Enclosure.Complex.IsNear.of_eq qz704 (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 19980558373 274877906944 20481495389 68719476736000 Bool.false 169192955661 549755813888 2566276533 8589934592000 (BSN.cpow_neg_s_mk qz143 149500 1000 10 qz144 rfl)

noncomputable def ep931 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz583 149500 1000 0 1 10369917190100709 4503599627370496 6250000003 1000000000000000 3100605239840111991 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 43494585150108164161536 18889465931478580854784 1000000000480000 160000000000000000000 10369917190100709 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep187 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep932 := nat_lit 61545300454086018134480688686100625

noncomputable def ep933 := BSN.sin_dyadic_bound_f 498079565 2147483648 2 1 1048576 320313 ep932 ep80 ep932 ep932 ep81 ep932 241028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 498079565) qz19 0 1 ep932 ep80 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 498079565) qz20 0 1 ep932 ep81 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz706 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90239489) qz17)

noncomputable def ep934 := @Enclosure.Real.IsNear.cos_image qz154 qz706 Bool.false 90239489 262144 981 1048576 Bool.false 241028 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3100605239840111991 9007199254740992 1868750000897 2000000000000000 90239489 262144 981 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 90239489 262144) (BSN.cos_reduce3 qz706 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8762308379781552406528) qz286) 226375608064910080 72057594037927936 Bool.false 241028 1048576 54 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 90239489 262144 226375608064910080 72057594037927936 54 8762308379781552406528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 241028 1048576 8762308379781552406528 37778931862957161709568 498079565 2147483648 320313 320000 (ep933 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep935 := BSN.cos_dyadic_bound_f 498079565 2147483648 2 1 1048576 320313 ep932 ep95 ep932 ep932 ep96 ep932 1020498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 498079565) qz15 0 1 ep932 ep95 ep932 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 498079565) qz16 0 1 ep932 ep96 ep932 rfl rfl rfl rfl) rfl rfl

noncomputable def ep936 := @Enclosure.Real.IsNear.sin_image qz154 qz706 Bool.false 90239489 262144 981 1048576 Bool.true 1020498 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 3100605239840111991 9007199254740992 1868750000897 2000000000000000 90239489 262144 981 1048576 (ep931 rfl) rfl) (Enclosure.sfrac_false_div 90239489 262144) (BSN.sin_reduce3 qz706 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8762308379781552406528) qz286) 226375608064910080 72057594037927936 Bool.false 1020498 1048576 54 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 90239489 262144 226375608064910080 72057594037927936 54 8762308379781552406528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1020498 1048576 8762308379781552406528 37778931862957161709568 498079565 2147483648 320313 320000 (ep935 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep937 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 19980558373 274877906944 20481495389 68719476736000 Bool.false 169192955661 549755813888 2566276533 8589934592000 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz154) 331589 1048576 1 1048576 60257 262144 617221 655360000 19980558373 274877906944 20481495389 68719476736000 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 241028 1048576 158008576 167772160000 60257 262144 617221 655360000 (ep934 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 331589 1048576 1 1048576 510249 524288 617221 655360000 169192955661 549755813888 2566276533 8589934592000 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 510249 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 1020498 1048576 158008576 167772160000 510249 524288 617221 655360000 (ep936 rfl rfl) rfl)) rfl)

noncomputable def ep938 := @ep918 19980558373 274877906944 20481495389 68719476736000 Bool.false 169192955661 549755813888 2566276533 8589934592000 Bool.false 91979146815454310301696 334618186809 1099511627776 2604069577319 687194767360000 Bool.true 597120713096896360480768 1086156249761 1099511627776 2604306347319 687194767360000 (ep919 (BSN.head_sum_c_succ qz140 9 10 rfl rfl) (ep929 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep930 ep937) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz269 qz455 qz586)

noncomputable def ep939 := @Enclosure.Complex.IsNear.of_eq qz703 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.false 78032922269 274877906944 97878199709 343597383680000 Bool.true 13961809277 137438953472 97680080959 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 11 qz144 rfl)

noncomputable def ep940 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz586 149500 1000 0 1 10799156221662949 4503599627370496 6250000003 1000000000000000 3228947710277221751 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 45294944137145793642496 18889465931478580854784 1000000000480000 160000000000000000000 10799156221662949 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep202 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep941 := nat_lit 296595559724088674694365804283210000

noncomputable def ep942 := BSN.cos_dyadic_bound_f 737974170 2147483648 2 1 1048576 320313 ep941 ep95 ep941 ep941 ep96 ep941 987268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 737974170) qz15 0 1 ep941 ep95 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 737974170) qz16 0 1 ep941 ep96 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 187949493) qz24)

noncomputable def ep943 := @Enclosure.Real.IsNear.cos_image qz155 qz466 Bool.false 187949493 524288 981 1048576 Bool.false 987268 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 3228947710277221751 9007199254740992 1868750000897 2000000000000000 187949493 524288 981 1048576 (ep940 rfl) rfl) (Enclosure.sfrac_false_div 187949493 524288) (BSN.cos_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25965157797845350219776) qz25) 226375608064910080 72057594037927936 Bool.false 987268 1048576 57 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 187949493 524288 226375608064910080 72057594037927936 57 25965157797845350219776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 987268 1048576 25965157797845350219776 75557863725914323419136 737974170 2147483648 320313 320000 (ep942 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep944 := BSN.sin_dyadic_bound_f 737974170 2147483648 2 1 1048576 320313 ep941 ep80 ep941 ep941 ep81 ep941 353288 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 737974170) qz19 0 1 ep941 ep80 ep941 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 737974170) qz20 0 1 ep941 ep81 ep941 rfl rfl rfl rfl) rfl rfl

noncomputable def ep945 := @Enclosure.Real.IsNear.sin_image qz155 qz466 Bool.false 187949493 524288 981 1048576 Bool.false 353288 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 3228947710277221751 9007199254740992 1868750000897 2000000000000000 187949493 524288 981 1048576 (ep940 rfl) rfl) (Enclosure.sfrac_false_div 187949493 524288) (BSN.sin_reduce0 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25965157797845350219776) qz25) 226375608064910080 72057594037927936 Bool.false 353288 1048576 57 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 187949493 524288 226375608064910080 72057594037927936 57 25965157797845350219776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 353288 1048576 25965157797845350219776 75557863725914323419136 737974170 2147483648 320313 320000 (ep944 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep946 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.false 78032922269 274877906944 97878199709 343597383680000 Bool.true 13961809277 137438953472 97680080959 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz36 (Real.cos qz155) 316157 1048576 1 1048576 246817 262144 617221 655360000 78032922269 274877906944 97878199709 343597383680000 qz329 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.false 987268 1048576 158008576 167772160000 246817 262144 617221 655360000 (ep943 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 316157 1048576 1 1048576 44161 131072 617221 655360000 13961809277 137438953472 97680080959 343597383680000 qz329 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 44161 131072 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 353288 1048576 158008576 167772160000 44161 131072 617221 655360000 (ep945 rfl rfl) rfl)) rfl)

noncomputable def ep947 := @ep916 78032922269 274877906944 97878199709 343597383680000 Bool.true 13961809277 137438953472 97680080959 343597383680000 Bool.false 177777252199560579645440 646749875885 1099511627776 2799825976737 687194767360000 Bool.true 164631349919076417798144 1197850723977 1099511627776 2799666509237 687194767360000 (ep917 (BSN.head_sum_c_succ qz140 10 11 rfl rfl) (ep938 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep939 ep946) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz269 qz455 qz589)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz702 (Complex.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 224419858497 1099511627776 187294937883 687194767360000 Bool.true 56113061769 274877906944 93647502379 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 12 qz144 rfl)

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz589 149500 1000 0 1 11191020447815397 4503599627370496 6250000003 1000000000000000 3346115113896803703 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 46938541828353910898688 18889465931478580854784 1000000000480000 160000000000000000000 11191020447815397 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep217 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep950 := nat_lit 289311497016971928600937643558192300994054076393714837978296641295079521487681

noncomputable def ep951 := nat_lit 65535575819745834447102071237711409161182507463488606850604594234861652801

noncomputable def ep952 := nat_lit 867803419899276294133918726532101480163839864166217536721188714696768841157441

noncomputable def ep953 := BSN.cos_dyadic_bound_f 1686784649 2147483648 3 2 1048576 320313 ep950 ep57 ep951 ep952 ep60 ep951 741401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1686784649) qz15 0 2 ep950 ep57 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1686784649) qz16 0 2 ep952 ep60 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 389539067) qz30)

noncomputable def ep954 := @Enclosure.Real.IsNear.cos_image qz156 qz467 Bool.false 389539067 1048576 981 1048576 Bool.false 741401 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 3346115113896803703 9007199254740992 1868750000897 2000000000000000 389539067 1048576 981 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 389539067 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118696917462429722476544) qz31) 226375608064910080 72057594037927936 Bool.false 741401 1048576 59 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 389539067 1048576 226375608064910080 72057594037927936 59 118696917462429722476544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741401 1048576 118696917462429722476544 151115727451828646838272 1686784649 2147483648 320313 320000 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := nat_lit 8095404611243704503705792559834346401

noncomputable def ep956 := BSN.sin_dyadic_bound_f 1686784649 2147483648 2 1 1048576 320313 ep955 ep80 ep955 ep955 ep81 ep955 741508 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1686784649) qz19 0 1 ep955 ep80 ep955 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1686784649) qz20 0 1 ep955 ep81 ep955 rfl rfl rfl rfl) rfl rfl

noncomputable def ep957 := @Enclosure.Real.IsNear.sin_image qz156 qz467 Bool.false 389539067 1048576 981 1048576 Bool.false 741508 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 3346115113896803703 9007199254740992 1868750000897 2000000000000000 389539067 1048576 981 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 389539067 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118696917462429722476544) qz31) 226375608064910080 72057594037927936 Bool.false 741508 1048576 59 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 389539067 1048576 226375608064910080 72057594037927936 59 118696917462429722476544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741508 1048576 118696917462429722476544 151115727451828646838272 1686784649 2147483648 320313 320000 (ep956 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep958 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz38 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz38 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 224419858497 1099511627776 187294937883 687194767360000 Bool.true 56113061769 274877906944 93647502379 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz38 (Real.cos qz156) 302697 1048576 1 1048576 741401 1048576 617221 655360000 224419858497 1099511627776 187294937883 687194767360000 qz331 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 741401 1048576 158008576 167772160000 741401 1048576 617221 655360000 (ep954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz38 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 302697 1048576 1 1048576 185377 262144 617221 655360000 56113061769 274877906944 93647502379 343597383680000 qz331 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.false 185377 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.false 741508 1048576 158008576 167772160000 185377 262144 617221 655360000 (ep957 rfl rfl) rfl)) rfl)

noncomputable def ep959 := @ep914 224419858497 1099511627776 187294937883 687194767360000 Bool.true 56113061769 274877906944 93647502379 343597383680000 Bool.false 957861252719538373394432 435584867191 549755813888 149356045731 34359738368000 Bool.true 390959663723281259692032 1422302971053 1099511627776 597392302799 137438953472000 (ep915 (BSN.head_sum_c_succ qz140 11 12 rfl rfl) (ep947 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep948 ep958) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz269 qz455 qz592)

noncomputable def ep960 := @Enclosure.Complex.IsNear.of_eq qz701 (Complex.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 299725964499 1099511627776 180146813229 687194767360000 Bool.true 28101354021 549755813888 89811731927 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 13 qz144 rfl)

noncomputable def ep961 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz592 149500 1000 0 1 11551497052968677 4503599627370496 6250000003 1000000000000000 3453897618837634423 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 48450490295254733815808 18889465931478580854784 1000000000480000 160000000000000000000 11551497052968677 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep232 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep962 := nat_lit 25107193498532156143005137512960000

noncomputable def ep963 := BSN.cos_dyadic_bound_f 398060920 2147483648 2 1 1048576 320313 ep962 ep95 ep962 ep962 ep96 ep962 1030613 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 398060920) qz15 0 1 ep962 ep95 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 398060920) qz16 0 1 ep962 ep96 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201043301) qz24)

noncomputable def ep964 := @Enclosure.Real.IsNear.cos_image qz157 qz468 Bool.false 201043301 524288 981 1048576 Bool.false 1030613 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 3453897618837634423 9007199254740992 1868750000897 2000000000000000 201043301 524288 981 1048576 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 201043301 524288) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14005523528822357491712) qz25) 226375608064910080 72057594037927936 Bool.false 1030613 1048576 61 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 201043301 524288 226375608064910080 72057594037927936 61 14005523528822357491712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030613 1048576 14005523528822357491712 75557863725914323419136 398060920 2147483648 320313 320000 (ep963 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep965 := BSN.sin_dyadic_bound_f 398060920 2147483648 2 1 1048576 320313 ep962 ep80 ep962 ep962 ep81 ep962 193254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 398060920) qz19 0 1 ep962 ep80 ep962 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 398060920) qz20 0 1 ep962 ep81 ep962 rfl rfl rfl rfl) rfl rfl

noncomputable def ep966 := @Enclosure.Real.IsNear.sin_image qz157 qz468 Bool.false 201043301 524288 981 1048576 Bool.false 193254 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 3453897618837634423 9007199254740992 1868750000897 2000000000000000 201043301 524288 981 1048576 (ep961 rfl) rfl) (Enclosure.sfrac_false_div 201043301 524288) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14005523528822357491712) qz25) 226375608064910080 72057594037927936 Bool.false 193254 1048576 61 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 201043301 524288 226375608064910080 72057594037927936 61 14005523528822357491712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 193254 1048576 14005523528822357491712 75557863725914323419136 398060920 2147483648 320313 320000 (ep965 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep967 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz40 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 299725964499 1099511627776 180146813229 687194767360000 Bool.true 28101354021 549755813888 89811731927 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz40 (Real.cos qz157) 290823 1048576 1 1048576 1030613 1048576 617221 655360000 299725964499 1099511627776 180146813229 687194767360000 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 1030613 1048576 158008576 167772160000 1030613 1048576 617221 655360000 (ep964 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz40 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 290823 1048576 1 1048576 96627 524288 617221 655360000 28101354021 549755813888 89811731927 343597383680000 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 96627 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 193254 1048576 158008576 167772160000 96627 524288 617221 655360000 (ep966 rfl rfl) rfl)) rfl)

noncomputable def ep968 := @ep912 299725964499 1099511627776 180146813229 687194767360000 Bool.true 28101354021 549755813888 89811731927 343597383680000 Bool.false 643706717916282725859328 1170895698881 1099511627776 3167267727849 687194767360000 Bool.true 812817092948901872271360 1478505679095 1099511627776 3166584977849 687194767360000 (ep913 (BSN.head_sum_c_succ qz140 12 13 rfl rfl) (ep959 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep960 ep967) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz269 qz455 qz595)

noncomputable def ep969 := @Enclosure.Complex.IsNear.of_eq qz700 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 19520886651 274877906944 21643328053 85899345920000 Bool.false 283291763597 1099511627776 173604281299 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 14 qz144 rfl)

noncomputable def ep970 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz595 149500 1000 0 1 11885250371606245 4503599627370496 6250000003 1000000000000000 3553689861110267255 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz596) Bool.false 49850353174629559828480 18889465931478580854784 1000000000480000 160000000000000000000 11885250371606245 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep243 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep971 := nat_lit 111280005896752366705471576624350625

noncomputable def ep972 := BSN.sin_dyadic_bound_f 577569545 2147483648 2 1 1048576 320313 ep971 ep80 ep971 ep971 ep81 ep971 278628 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 577569545) qz19 0 1 ep971 ep80 ep971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 577569545) qz20 0 1 ep971 ep81 ep971 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103425987) qz17)

noncomputable def ep973 := @Enclosure.Real.IsNear.cos_image qz158 qz469 Bool.false 103425987 262144 981 1048576 Bool.false 278628 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 3553689861110267255 9007199254740992 1868750000897 2000000000000000 103425987 262144 981 1048576 (ep970 rfl) rfl) (Enclosure.sfrac_false_div 103425987 262144) (BSN.cos_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10160710893509640454144) qz286) 226375608064910080 72057594037927936 Bool.false 278628 1048576 62 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 103425987 262144 226375608064910080 72057594037927936 62 10160710893509640454144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 278628 1048576 10160710893509640454144 37778931862957161709568 577569545 2147483648 320313 320000 (ep972 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep974 := BSN.cos_dyadic_bound_f 577569545 2147483648 2 1 1048576 320313 ep971 ep95 ep971 ep971 ep96 ep971 1010879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 577569545) qz15 0 1 ep971 ep95 ep971 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 577569545) qz16 0 1 ep971 ep96 ep971 rfl rfl rfl rfl) rfl rfl

noncomputable def ep975 := @Enclosure.Real.IsNear.sin_image qz158 qz469 Bool.false 103425987 262144 981 1048576 Bool.true 1010879 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 3553689861110267255 9007199254740992 1868750000897 2000000000000000 103425987 262144 981 1048576 (ep970 rfl) rfl) (Enclosure.sfrac_false_div 103425987 262144) (BSN.sin_reduce3 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10160710893509640454144) qz286) 226375608064910080 72057594037927936 Bool.false 1010879 1048576 62 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 103425987 262144 226375608064910080 72057594037927936 62 10160710893509640454144 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1010879 1048576 10160710893509640454144 37778931862957161709568 577569545 2147483648 320313 320000 (ep974 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep976 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 19520886651 274877906944 21643328053 85899345920000 Bool.false 283291763597 1099511627776 173604281299 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz42 (Real.cos qz158) 280243 1048576 1 1048576 69657 262144 617221 655360000 19520886651 274877906944 21643328053 85899345920000 qz335 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 278628 1048576 158008576 167772160000 69657 262144 617221 655360000 (ep973 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 280243 1048576 1 1048576 1010879 1048576 617221 655360000 283291763597 1099511627776 173604281299 687194767360000 qz335 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 1010879 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 1010879 1048576 158008576 167772160000 1010879 1048576 617221 655360000 (ep975 rfl rfl) rfl)) rfl)

noncomputable def ep977 := @ep909 19520886651 274877906944 21643328053 85899345920000 Bool.false 283291763597 1099511627776 173604281299 687194767360000 Bool.false 343316800815413162147840 1248979245485 1099511627776 3340414352273 687194767360000 Bool.true ep910 597606957749 549755813888 835047314787 171798691840000 (ep911 (BSN.head_sum_c_succ qz140 13 14 rfl rfl) (ep968 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep969 ep976) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz269 qz455 qz598)

noncomputable def ep978 := @Enclosure.Complex.IsNear.of_eq qz699 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 260110896117 1099511627776 167708108607 687194767360000 Bool.true 7108846437 68719476736 83685108991 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 15 qz144 rfl)

noncomputable def ep979 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz598 149500 1000 0 1 12195965485668069 4503599627370496 6250000003 1000000000000000 3646593680214752631 9007199254740992 1868750000897 2000000000000000 qz145 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 6250000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz599) Bool.false 51153586820399524478976 18889465931478580854784 1000000000480000 160000000000000000000 12195965485668069 4503599627370496 6250000003 1000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep254 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep980 := nat_lit 2465858139662730086879573624551982127406821145592042845076318826395303594229760

noncomputable def ep981 := nat_lit 1468305139801287935920048077992125748414766637443790630319805729705547595776

noncomputable def ep982 := nat_lit 6455822633652233856597869891224156415806145759137584171322222002711033764970496

noncomputable def ep983 := BSN.sin_dyadic_bound_f 2488009532 2147483648 3 2 1048576 320313 ep980 ep64 ep981 ep982 ep66 ep981 960737 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2488009532) qz19 0 2 ep980 ep64 ep981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2488009532) qz20 0 2 ep982 ep66 ep981 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26532461) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep984 := @Enclosure.Real.IsNear.cos_image qz159 qz470 Bool.false 26532461 65536 981 1048576 Bool.true 960737 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 3646593680214752631 9007199254740992 1868750000897 2000000000000000 26532461 65536 981 1048576 (ep979 rfl) rfl) (Enclosure.sfrac_false_div 26532461 65536) (BSN.cos_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10942381643830585720832) qz458) 226375608064910080 72057594037927936 Bool.false 960737 1048576 64 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 26532461 65536 226375608064910080 72057594037927936 64 10942381643830585720832 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 960737 1048576 10942381643830585720832 9444732965739290427392 2488009532 2147483648 320313 320000 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := nat_lit 1370573768763650620682394257230208793336418310501109931989208150543926684614656

noncomputable def ep986 := nat_lit 4108784696011349286175342675534642128512425398228442214706984840172368958652416

noncomputable def ep987 := BSN.cos_dyadic_bound_f 2488009532 2147483648 3 2 1048576 320313 ep985 ep57 ep981 ep986 ep60 ep981 420112 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2488009532) qz15 0 2 ep985 ep57 ep981 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2488009532) qz16 0 2 ep986 ep60 ep981 rfl rfl rfl rfl) rfl rfl

noncomputable def ep988 := @Enclosure.Real.IsNear.sin_image qz159 qz470 Bool.false 26532461 65536 981 1048576 Bool.false 420112 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 3646593680214752631 9007199254740992 1868750000897 2000000000000000 26532461 65536 981 1048576 (ep979 rfl) rfl) (Enclosure.sfrac_false_div 26532461 65536) (BSN.sin_reduce1 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10942381643830585720832) qz458) 226375608064910080 72057594037927936 Bool.false 420112 1048576 64 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 26532461 65536 226375608064910080 72057594037927936 64 10942381643830585720832 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 420112 1048576 10942381643830585720832 9444732965739290427392 2488009532 2147483648 320313 320000 (ep987 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep989 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 260110896117 1099511627776 167708108607 687194767360000 Bool.true 7108846437 68719476736 83685108991 343597383680000 (@Enclosure.Real.IsNear.mulLit_ft qz44 (Real.cos qz159) 270741 1048576 1 1048576 960737 1048576 617221 655360000 260110896117 1099511627776 167708108607 687194767360000 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 960737 1048576 158008576 167772160000 960737 1048576 617221 655360000 (ep984 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 270741 1048576 1 1048576 26257 65536 617221 655360000 7108846437 68719476736 83685108991 343597383680000 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 26257 65536 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 420112 1048576 158008576 167772160000 26257 65536 617221 655360000 (ep988 rfl rfl) rfl)) rfl)

noncomputable def ep990 := @ep907 260110896117 1099511627776 167708108607 687194767360000 Bool.true 7108846437 68719476736 83685108991 343597383680000 Bool.false 1087272248469775940845568 123608543671 137438953472 43851530761 8589934592000 Bool.true 44975367089081884344320 654477729245 549755813888 350755947713 68719476736000 (ep908 (BSN.head_sum_c_succ qz140 14 15 rfl rfl) (ep977 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep978 ep989) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz269 qz455 qz601)

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq qz698 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 270022232151 1099511627776 162444567449 687194767360000 Bool.false 12857852007 274877906944 40480851081 171798691840000 (BSN.cpow_neg_s_mk qz143 149500 1000 16 qz144 rfl)

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz601 149500 1000 0 1 3121657384082679 1125899906842624 1562500001 250000000000000 933375557840721021 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz602) Bool.false 52372720210750067441664 18889465931478580854784 1000000000640000 160000000000000000000 3121657384082679 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep269 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep993 := nat_lit 5003861805352890923563546960074565157611480773238411547968298786389702346899585

noncomputable def ep994 := nat_lit 6038919279498080538269519342703979319177432884227439018180588002905836060801

noncomputable def ep995 := nat_lit 13095575049471717431318758054592816589132352848097566771982775869492134793019521

noncomputable def ep996 := BSN.sin_dyadic_bound_f 2969066351 2147483648 3 2 1048576 320313 ep993 ep64 ep994 ep995 ep66 ep994 1030057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2969066351) qz19 0 2 ep993 ep64 ep994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2969066351) qz20 0 2 ep995 ep66 ep994 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 434636863) qz30)

noncomputable def ep997 := @Enclosure.Real.IsNear.cos_image qz160 qz471 Bool.false 434636863 1048576 981 1048576 Bool.false 1030057 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 933375557840721021 2251799813685248 467187500299 500000000000000 434636863 1048576 981 1048576 (ep992 rfl) rfl) (Enclosure.sfrac_false_div 434636863 1048576) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 208929470547689258090496) qz31) 226375608064910080 72057594037927936 Bool.false 1030057 1048576 65 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 434636863 1048576 226375608064910080 72057594037927936 65 208929470547689258090496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1030057 1048576 208929470547689258090496 151115727451828646838272 2969066351 2147483648 320313 320000 (ep996 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep998 := nat_lit 2782607189320271882218979208638182411703790399747663055101579587106681675415681

noncomputable def ep999 := nat_lit 8335743729401819485580398587229139276473016333474534287268377585314233354125441

noncomputable def ep1000 := BSN.cos_dyadic_bound_f 2969066351 2147483648 3 2 1048576 320313 ep998 ep57 ep994 ep999 ep60 ep994 196196 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2969066351) qz15 0 2 ep998 ep57 ep994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2969066351) qz16 0 2 ep999 ep60 ep994 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1001 := @Enclosure.Real.IsNear.sin_image qz160 qz471 Bool.false 434636863 1048576 981 1048576 Bool.true 196196 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 933375557840721021 2251799813685248 467187500299 500000000000000 434636863 1048576 981 1048576 (ep992 rfl) rfl) (Enclosure.sfrac_false_div 434636863 1048576) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 208929470547689258090496) qz31) 226375608064910080 72057594037927936 Bool.false 196196 1048576 65 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 434636863 1048576 226375608064910080 72057594037927936 65 208929470547689258090496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 196196 1048576 208929470547689258090496 151115727451828646838272 2969066351 2147483648 320313 320000 (ep1000 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1002 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 270022232151 1099511627776 162444567449 687194767360000 Bool.false 12857852007 274877906944 40480851081 171798691840000 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz160) 262143 1048576 1 1048576 1030057 1048576 617221 655360000 270022232151 1099511627776 162444567449 687194767360000 qz339 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 1030057 1048576 158008576 167772160000 1030057 1048576 617221 655360000 (ep997 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 262143 1048576 1 1048576 49049 262144 617221 655360000 12857852007 274877906944 40480851081 171798691840000 qz339 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 49049 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 196196 1048576 158008576 167772160000 49049 262144 617221 655360000 (ep1001 rfl rfl) rfl)) rfl)

noncomputable def ep1003 := @ep905 270022232151 1099511627776 162444567449 687194767360000 Bool.false 12857852007 274877906944 40480851081 171798691840000 Bool.false 173020604059728864083968 1258890581519 1099511627776 3670567028329 687194767360000 Bool.true 172832789461367798104064 628762025231 549755813888 1834741440727 343597383680000 (ep906 (BSN.head_sum_c_succ qz140 15 16 rfl rfl) (ep990 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep991 ep1002) rfl rfl

theorem EMLast.d14 : Enclosure.Complex.IsNear qz152 Bool.false 1258890581519 1099511627776 3670567028329 687194767360000 Bool.true 628762025231 549755813888 1834741440727 343597383680000 := ep904 (BSN.head_sum_c_succ qz140 16 17 rfl rfl) (ep1003 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz161 := (BSN.headSumC qz453 25)

noncomputable abbrev qz707 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz141)

noncomputable def ep1004 := @Enclosure.Complex.IsNear.of_eq qz161 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 24) qz707) Bool.false 231645636425 549755813888 2411896989703 343597383680000 Bool.true 1201291872657 1099511627776 4821864812531 687194767360000

noncomputable def ep1005 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 24) qz707 Bool.false 629269741751 1099511627776 4691199334691 687194767360000 Bool.true 1352363595403 1099511627776 4689313695941 687194767360000 Bool.true

noncomputable abbrev qz708 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz141)

noncomputable def ep1006 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 23) qz708) Bool.false 629269741751 1099511627776 4691199334691 687194767360000 Bool.true 1352363595403 1099511627776 4689313695941 687194767360000

noncomputable def ep1007 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 23) qz708 Bool.false 810555398771 1099511627776 4555729453867 687194767360000 Bool.true 746355377873 549755813888 1138490209873 171798691840000 Bool.true

noncomputable abbrev qz709 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz141)

noncomputable def ep1008 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 22) qz709) Bool.false 810555398771 1099511627776 4555729453867 687194767360000 Bool.true 746355377873 549755813888 1138490209873 171798691840000

noncomputable def ep1009 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 22) qz709 Bool.false 8083881199 8589934592 1104279503981 171798691840000 Bool.true 1561221810409 1099511627776 4415784610299 687194767360000 Bool.true

noncomputable def ep1010 := nat_lit 1641252832849027605200896

noncomputable abbrev qz710 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz141)

noncomputable def ep1011 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 21) qz710) Bool.false 8083881199 8589934592 1104279503981 171798691840000 Bool.true 1561221810409 1099511627776 4415784610299 687194767360000

noncomputable def ep1012 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 21) qz710 Bool.false 157249543327 137438953472 534333233963 85899345920000 Bool.true 1473341511693 1099511627776 4274072023579 687194767360000 Bool.true

noncomputable abbrev qz711 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz141)

noncomputable def ep1013 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 20) qz711) Bool.false 157249543327 137438953472 534333233963 85899345920000 Bool.true 1473341511693 1099511627776 4274072023579 687194767360000

noncomputable def ep1014 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 20) qz711 Bool.false 81449536941 68719476736 2064912794417 343597383680000 Bool.true 1231672906579 1099511627776 4128708024459 687194767360000 Bool.true

noncomputable abbrev qz712 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz141)

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 19) qz712) Bool.false 81449536941 68719476736 2064912794417 343597383680000 Bool.true 1231672906579 1099511627776 4128708024459 687194767360000

noncomputable def ep1016 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 19) qz712 Bool.false 534038720613 549755813888 497592006103 85899345920000 Bool.true 142538183889 137438953472 1989995978787 343597383680000 Bool.false

noncomputable abbrev qz713 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz141)

noncomputable def ep1017 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 18) qz713) Bool.false 534038720613 549755813888 497592006103 85899345920000 Bool.true 142538183889 137438953472 1989995978787 343597383680000

noncomputable def ep1018 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 18) qz713 Bool.false 515761904163 549755813888 957024051683 171798691840000 Bool.true 349217736751 274877906944 1913397872741 343597383680000 Bool.false

noncomputable abbrev qz714 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz141)

noncomputable def ep1019 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 18) (@HAdd.hAdd Complex Complex Complex qz4 qz152 qz714) Bool.false 515761904163 549755813888 957024051683 171798691840000 Bool.true 349217736751 274877906944 1913397872741 343597383680000

noncomputable def ep1020 := @Enclosure.Complex.IsNear.addLitP qz152 qz714 Bool.false 1258890581519 1099511627776 3670567028329 687194767360000 Bool.true 628762025231 549755813888 1834741440727 343597383680000 Bool.true

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz269 qz455 qz612)

noncomputable def ep1021 := @Enclosure.Complex.IsNear.of_eq qz714 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 227366773193 1099511627776 157529178403 687194767360000 Bool.true 69673448271 549755813888 39328216007 171798691840000 (BSN.cpow_neg_s_mk qz143 149500 1000 17 qz144 rfl)

noncomputable def ep1022 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz612 149500 1000 0 1 3189913004350711 1125899906842624 1562500001 250000000000000 953783988300862589 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz613) Bool.false 53517859495200818200576 18889465931478580854784 1000000000640000 160000000000000000000 3189913004350711 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep300 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1023 := nat_lit 1486689377245307205633050769681151273799153448781461583556485333920404248101120

noncomputable def ep1024 := nat_lit 533981175511307792507570496392740894331138693066927452082164045714201149696

noncomputable def ep1025 := nat_lit 3892845732786881516422501663599331755645056236543624360106471418479426228879616

noncomputable def ep1026 := BSN.sin_dyadic_bound_f 2192505762 2147483648 3 2 1048576 320313 ep1023 ep64 ep1024 ep1025 ep66 ep1024 894029 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2192505762) qz19 0 2 ep1023 ep64 ep1024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2192505762) qz20 0 2 ep1025 ep66 ep1024 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 444140279) qz30)

noncomputable def ep1027 := @Enclosure.Real.IsNear.cos_image qz162 qz472 Bool.false 444140279 1048576 981 1048576 Bool.true 894029 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 953783988300862589 2251799813685248 467187500299 500000000000000 444140279 1048576 981 1048576 (ep1022 rfl) rfl) (Enclosure.sfrac_false_div 444140279 1048576) (BSN.cos_reduce1 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154283877137160253472768) qz31) 226375608064910080 72057594037927936 Bool.false 894029 1048576 67 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 444140279 1048576 226375608064910080 72057594037927936 67 154283877137160253472768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 894029 1048576 154283877137160253472768 151115727451828646838272 2192505762 2147483648 320313 320000 (ep1026 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1028 := nat_lit 826175867880953473259476014487925259174787977631063958621195036198319782789376

noncomputable def ep1029 := nat_lit 2477459641291837804193412902470990295735701655507058020959420780503530946068736

noncomputable def ep1030 := BSN.cos_dyadic_bound_f 2192505762 2147483648 3 2 1048576 320313 ep1028 ep57 ep1024 ep1029 ep60 ep1024 547926 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2192505762) qz15 0 2 ep1028 ep57 ep1024 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2192505762) qz16 0 2 ep1029 ep60 ep1024 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1031 := @Enclosure.Real.IsNear.sin_image qz162 qz472 Bool.false 444140279 1048576 981 1048576 Bool.false 547926 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 953783988300862589 2251799813685248 467187500299 500000000000000 444140279 1048576 981 1048576 (ep1022 rfl) rfl) (Enclosure.sfrac_false_div 444140279 1048576) (BSN.sin_reduce1 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154283877137160253472768) qz31) 226375608064910080 72057594037927936 Bool.false 547926 1048576 67 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 444140279 1048576 226375608064910080 72057594037927936 67 154283877137160253472768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 547926 1048576 154283877137160253472768 151115727451828646838272 2192505762 2147483648 320313 320000 (ep1030 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 227366773193 1099511627776 157529178403 687194767360000 Bool.true 69673448271 549755813888 39328216007 171798691840000 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz162) 254317 1048576 1 1048576 894029 1048576 617221 655360000 227366773193 1099511627776 157529178403 687194767360000 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 894029 1048576 158008576 167772160000 894029 1048576 617221 655360000 (ep1027 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz49 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 254317 1048576 1 1048576 273963 524288 617221 655360000 69673448271 549755813888 39328216007 171798691840000 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 273963 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 547926 1048576 158008576 167772160000 273963 524288 617221 655360000 (ep1031 rfl rfl) rfl)) rfl)

noncomputable def ep1033 := @ep1020 227366773193 1099511627776 157529178403 687194767360000 Bool.true 69673448271 549755813888 39328216007 171798691840000 Bool.false 1134172421582218881662976 515761904163 549755813888 957024051683 171798691840000 Bool.true 383968962183342667595776 349217736751 274877906944 1913397872741 343597383680000 EMLast.d14 (ep1021 ep1032) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz269 qz455 qz615)

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq qz713 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 9138408225 274877906944 38159960523 171798691840000 Bool.false 64141368973 274877906944 38299053023 171798691840000 (BSN.cpow_neg_s_mk qz143 149500 1000 18 qz144 rfl)

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz615 149500 1000 0 1 3254268794313975 1125899906842624 1562500001 250000000000000 973026369499878525 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 54597570484265130393600 18889465931478580854784 1000000000640000 160000000000000000000 3254268794313975 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep311 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1036 := BSN.sin_dyadic_bound_f 303913942 2147483648 1 0 1048576 320313 0 1 1 0 1 1 147900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 303913942) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 303913942) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 453100711) qz30)

noncomputable def ep1037 := @Enclosure.Real.IsNear.cos_image qz163 qz473 Bool.false 453100711 1048576 981 1048576 Bool.false 147900 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 973026369499878525 2251799813685248 467187500299 500000000000000 453100711 1048576 981 1048576 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 453100711 1048576) (BSN.cos_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21386042444450724052992) qz31) 226375608064910080 72057594037927936 Bool.false 147900 1048576 68 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 453100711 1048576 226375608064910080 72057594037927936 68 21386042444450724052992 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 147900 1048576 21386042444450724052992 151115727451828646838272 303913942 2147483648 320313 320000 (ep1036 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1038 := nat_lit 8531050148279330242192091801844496

noncomputable def ep1039 := BSN.cos_dyadic_bound_f 303913942 2147483648 2 1 1048576 320313 ep1038 ep95 ep1038 ep1038 ep96 ep1038 1038092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 303913942) qz15 0 1 ep1038 ep95 ep1038 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 303913942) qz16 0 1 ep1038 ep96 ep1038 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1040 := @Enclosure.Real.IsNear.sin_image qz163 qz473 Bool.false 453100711 1048576 981 1048576 Bool.true 1038092 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 973026369499878525 2251799813685248 467187500299 500000000000000 453100711 1048576 981 1048576 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 453100711 1048576) (BSN.sin_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21386042444450724052992) qz31) 226375608064910080 72057594037927936 Bool.false 1038092 1048576 68 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 453100711 1048576 226375608064910080 72057594037927936 68 21386042444450724052992 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1038092 1048576 21386042444450724052992 151115727451828646838272 303913942 2147483648 320313 320000 (ep1039 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 9138408225 274877906944 38159960523 171798691840000 Bool.false 64141368973 274877906944 38299053023 171798691840000 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz163) 247151 1048576 1 1048576 36975 262144 617221 655360000 9138408225 274877906944 38159960523 171798691840000 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 147900 1048576 158008576 167772160000 36975 262144 617221 655360000 (ep1037 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 247151 1048576 1 1048576 259523 262144 617221 655360000 64141368973 274877906944 38299053023 171798691840000 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 259523 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 1038092 1048576 158008576 167772160000 259523 262144 617221 655360000 (ep1040 rfl rfl) rfl)) rfl)

noncomputable def ep1042 := @ep1018 9138408225 274877906944 38159960523 171798691840000 Bool.false 64141368973 274877906944 38299053023 171798691840000 Bool.false 146795445749153028636672 534038720613 549755813888 497592006103 85899345920000 Bool.true 78361195294014604050432 142538183889 137438953472 1989995978787 343597383680000 (ep1019 (BSN.head_sum_c_succ qz140 17 18 rfl rfl) (ep1033 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1034 ep1041) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz269 qz455 qz618)

noncomputable def ep1043 := @Enclosure.Complex.IsNear.of_eq qz712 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 117557574915 549755813888 14908954001 68719476736000 Bool.true 91367435467 1099511627776 29743213377 137438953472000 (BSN.cpow_neg_s_mk qz143 149500 1000 19 qz144 rfl)

noncomputable def ep1044 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz618 149500 1000 0 1 3315143513283831 1125899906842624 1562500001 250000000000000 991227910471865469 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz619) Bool.false 55618878793361701994496 18889465931478580854784 1000000000640000 160000000000000000000 3315143513283831 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1045 := nat_lit 401386436308862287694202277098600625

noncomputable def ep1046 := BSN.cos_dyadic_bound_f 795958955 2147483648 2 1 1048576 320313 ep1045 ep95 ep1045 ep1045 ep96 ep1045 977370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 795958955) qz15 0 1 ep1045 ep95 ep1045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 795958955) qz16 0 1 ep1045 ep96 ep1045 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28848529) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep1047 := @Enclosure.Real.IsNear.cos_image qz164 qz474 Bool.false 28848529 65536 981 1048576 Bool.false 977370 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 991227910471865469 2251799813685248 467187500299 500000000000000 28848529 65536 981 1048576 (ep1044 rfl) rfl) (Enclosure.sfrac_false_div 28848529 65536) (BSN.cos_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3500664507037162405888) qz458) 226375608064910080 72057594037927936 Bool.false 977370 1048576 70 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 28848529 65536 226375608064910080 72057594037927936 70 3500664507037162405888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 977370 1048576 3500664507037162405888 9444732965739290427392 795958955 2147483648 320313 320000 (ep1046 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1048 := BSN.sin_dyadic_bound_f 795958955 2147483648 2 1 1048576 320313 ep1045 ep80 ep1045 ep1045 ep81 ep1045 379813 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 795958955) qz19 0 1 ep1045 ep80 ep1045 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 795958955) qz20 0 1 ep1045 ep81 ep1045 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1049 := @Enclosure.Real.IsNear.sin_image qz164 qz474 Bool.false 28848529 65536 981 1048576 Bool.false 379813 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 991227910471865469 2251799813685248 467187500299 500000000000000 28848529 65536 981 1048576 (ep1044 rfl) rfl) (Enclosure.sfrac_false_div 28848529 65536) (BSN.sin_reduce0 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3500664507037162405888) qz458) 226375608064910080 72057594037927936 Bool.false 379813 1048576 70 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 28848529 65536 226375608064910080 72057594037927936 70 3500664507037162405888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 379813 1048576 3500664507037162405888 9444732965739290427392 795958955 2147483648 320313 320000 (ep1048 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 117557574915 549755813888 14908954001 68719476736000 Bool.true 91367435467 1099511627776 29743213377 137438953472000 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz164) 240559 1048576 1 1048576 488685 524288 617221 655360000 117557574915 549755813888 14908954001 68719476736000 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 977370 1048576 158008576 167772160000 488685 524288 617221 655360000 (ep1047 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 240559 1048576 1 1048576 379813 1048576 617221 655360000 91367435467 1099511627776 29743213377 137438953472000 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 379813 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 379813 1048576 158008576 167772160000 379813 1048576 617221 655360000 (ep1049 rfl rfl) rfl)) rfl)

noncomputable def ep1051 := @ep1016 117557574915 549755813888 14908954001 68719476736000 Bool.true 91367435467 1099511627776 29743213377 137438953472000 Bool.false 358218851774401414692864 81449536941 68719476736 2064912794417 343597383680000 Bool.true 169279835300034183692288 1231672906579 1099511627776 4128708024459 687194767360000 (ep1017 (BSN.head_sum_c_succ qz140 18 19 rfl rfl) (ep1042 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1043 ep1050) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz269 qz455 qz621)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq qz711 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 5649530555 137438953472 14484028287 68719476736000 Bool.true 120834302557 549755813888 1817049989 8589934592000 (BSN.cpow_neg_s_mk qz143 149500 1000 20 qz144 rfl)

noncomputable def ep1053 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz621 149500 1000 0 1 3372893643545847 1125899906842624 1562500001 250000000000000 1008495199420208253 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz622) Bool.false 56587765202795681021952 18889465931478580854784 1000000000640000 160000000000000000000 3372893643545847 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1054 := nat_lit 24848558842405801812783149661290496

noncomputable def ep1055 := BSN.sin_dyadic_bound_f 397031808 2147483648 2 1 1048576 320313 ep1054 ep80 ep1054 ep1054 ep81 ep1054 192760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 397031808) qz19 0 1 ep1054 ep80 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 397031808) qz20 0 1 ep1054 ep81 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117404293) qz17)

noncomputable def ep1056 := @Enclosure.Real.IsNear.cos_image qz165 qz475 Bool.false 117404293 262144 981 1048576 Bool.true 192760 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 1008495199420208253 2251799813685248 467187500299 500000000000000 117404293 262144 981 1048576 (ep1053 rfl) rfl) (Enclosure.sfrac_false_div 117404293 262144) (BSN.cos_reduce1 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6984657446069438775296) qz286) 226375608064910080 72057594037927936 Bool.false 192760 1048576 71 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 117404293 262144 226375608064910080 72057594037927936 71 6984657446069438775296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 192760 1048576 6984657446069438775296 37778931862957161709568 397031808 2147483648 320313 320000 (ep1055 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1057 := BSN.cos_dyadic_bound_f 397031808 2147483648 2 1 1048576 320313 ep1054 ep95 ep1054 ep1054 ep96 ep1054 1030706 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 397031808) qz15 0 1 ep1054 ep95 ep1054 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 397031808) qz16 0 1 ep1054 ep96 ep1054 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1058 := @Enclosure.Real.IsNear.sin_image qz165 qz475 Bool.false 117404293 262144 981 1048576 Bool.false 1030706 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 1008495199420208253 2251799813685248 467187500299 500000000000000 117404293 262144 981 1048576 (ep1053 rfl) rfl) (Enclosure.sfrac_false_div 117404293 262144) (BSN.sin_reduce1 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6984657446069438775296) qz286) 226375608064910080 72057594037927936 Bool.false 1030706 1048576 71 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 117404293 262144 226375608064910080 72057594037927936 71 6984657446069438775296 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1030706 1048576 6984657446069438775296 37778931862957161709568 397031808 2147483648 320313 320000 (ep1057 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1059 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 5649530555 137438953472 14484028287 68719476736000 Bool.true 120834302557 549755813888 1817049989 8589934592000 (@Enclosure.Real.IsNear.mulLit_ft qz55 (Real.cos qz165) 234469 1048576 1 1048576 24095 131072 617221 655360000 5649530555 137438953472 14484028287 68719476736000 qz347 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 192760 1048576 158008576 167772160000 24095 131072 617221 655360000 (ep1056 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 234469 1048576 1 1048576 515353 524288 617221 655360000 120834302557 549755813888 1817049989 8589934592000 qz347 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.false 515353 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.false 1030706 1048576 158008576 167772160000 515353 524288 617221 655360000 (ep1058 rfl rfl) rfl)) rfl)

noncomputable def ep1060 := @ep1014 5649530555 137438953472 14484028287 68719476736000 Bool.true 120834302557 549755813888 1817049989 8589934592000 Bool.false 10806106334406400540672 157249543327 137438953472 534333233963 85899345920000 Bool.true 809978061895761483792384 1473341511693 1099511627776 4274072023579 687194767360000 (ep1015 (BSN.head_sum_c_succ qz140 19 20 rfl rfl) (ep1051 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1052 ep1059) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz269 qz455 qz624)

noncomputable def ep1061 := @Enclosure.Complex.IsNear.of_eq qz710 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 27907444143 137438953472 7122607211 34359738368000 Bool.true 21970074679 274877906944 885703667 4294967296000 (BSN.cpow_neg_s_mk qz143 149500 1000 21 qz144 rfl)

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz624 149500 1000 0 1 3427826275261687 1125899906842624 1562500001 250000000000000 1024920056303244413 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz625) Bool.false 57509381830540779323392 18889465931478580854784 1000000000640000 160000000000000000000 3427826275261687 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1063 := nat_lit 2798637488978081036169632474450103404495741290191070409647986785971873618329600

noncomputable def ep1064 := nat_lit 1891052945365950690852251743603176109303994213438946609204597668286673453056

noncomputable def ep1065 := nat_lit 7326703147316762603135276644546341869502354055107235635520300805130062005272576

noncomputable def ep1066 := BSN.sin_dyadic_bound_f 2567958264 2147483648 3 2 1048576 320313 ep1063 ep64 ep1064 ep1065 ep66 ep1064 975708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2567958264) qz19 0 2 ep1063 ep64 ep1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2567958264) qz20 0 2 ep1065 ep66 ep1064 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59658199) qz562)

noncomputable def ep1067 := @Enclosure.Real.IsNear.cos_image qz166 qz476 Bool.false 59658199 131072 981 1048576 Bool.true 975708 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 1024920056303244413 2251799813685248 467187500299 500000000000000 59658199 131072 981 1048576 (ep1062 rfl) rfl) (Enclosure.sfrac_false_div 59658199 131072) (BSN.cos_reduce1 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22587999769791339429888) qz293) 226375608064910080 72057594037927936 Bool.false 975708 1048576 72 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 59658199 131072 226375608064910080 72057594037927936 72 22587999769791339429888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 975708 1048576 22587999769791339429888 18889465931478580854784 2567958264 2147483648 320313 320000 (ep1066 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1068 := nat_lit 1555639072963540998179063486580547747435102491978789759408528035614723865051136

noncomputable def ep1069 := nat_lit 4663135112999891093155485956254436890086699487509491385007174911507598248247296

noncomputable def ep1070 := BSN.cos_dyadic_bound_f 2567958264 2147483648 3 2 1048576 320313 ep1068 ep57 ep1064 ep1069 ep60 ep1064 384062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2567958264) qz15 0 2 ep1068 ep57 ep1064 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2567958264) qz16 0 2 ep1069 ep60 ep1064 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1071 := @Enclosure.Real.IsNear.sin_image qz166 qz476 Bool.false 59658199 131072 981 1048576 Bool.false 384062 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 1024920056303244413 2251799813685248 467187500299 500000000000000 59658199 131072 981 1048576 (ep1062 rfl) rfl) (Enclosure.sfrac_false_div 59658199 131072) (BSN.sin_reduce1 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22587999769791339429888) qz293) 226375608064910080 72057594037927936 Bool.false 384062 1048576 72 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 59658199 131072 226375608064910080 72057594037927936 72 22587999769791339429888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 384062 1048576 22587999769791339429888 18889465931478580854784 2567958264 2147483648 320313 320000 (ep1070 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1072 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 27907444143 137438953472 7122607211 34359738368000 Bool.true 21970074679 274877906944 885703667 4294967296000 (@Enclosure.Real.IsNear.mulLit_ft qz57 (Real.cos qz166) 114409 524288 1 524288 243927 262144 617221 655360000 27907444143 137438953472 7122607211 34359738368000 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 975708 1048576 158008576 167772160000 243927 262144 617221 655360000 (ep1067 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 114409 524288 1 524288 192031 524288 617221 655360000 21970074679 274877906944 885703667 4294967296000 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.false 192031 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.false 384062 1048576 158008576 167772160000 192031 524288 617221 655360000 (ep1071 rfl rfl) rfl)) rfl)

noncomputable def ep1073 := @ep1012 27907444143 137438953472 7122607211 34359738368000 Bool.true 21970074679 274877906944 885703667 4294967296000 Bool.false 17776642751720585166848 8083881199 8589934592 1104279503981 171798691840000 Bool.true 429145383520548312580096 1561221810409 1099511627776 4415784610299 687194767360000 (ep1013 (BSN.head_sum_c_succ qz140 20 21 rfl rfl) (ep1060 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1061 ep1072) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz269 qz455 qz627)

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq qz709 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 224181394701 1099511627776 138611437943 687194767360000 Bool.false 68511054663 1099511627776 138176229193 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 22 qz144 rfl)

noncomputable def ep1075 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz627 149500 1000 0 1 3480203401436407 1125899906842624 1562500001 250000000000000 1040580817029485693 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz628) Bool.false 58388124189833310502912 18889465931478580854784 1000000000640000 160000000000000000000 3480203401436407 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep365 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1076 := nat_lit 164572412987502053384882932794671761

noncomputable def ep1077 := BSN.cos_dyadic_bound_f 636926413 2147483648 2 1 1048576 320313 ep1076 ep95 ep1076 ep1076 ep96 ep1076 1002793 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 636926413) qz15 0 1 ep1076 ep95 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 636926413) qz16 0 1 ep1076 ep96 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 242279101) qz24)

noncomputable def ep1078 := @Enclosure.Real.IsNear.cos_image qz167 qz477 Bool.false 242279101 524288 981 1048576 Bool.true 1002793 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 1040580817029485693 2251799813685248 467187500299 500000000000000 242279101 524288 981 1048576 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 242279101 524288) (BSN.cos_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22409855930421122957312) qz25) 226375608064910080 72057594037927936 Bool.false 1002793 1048576 73 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 242279101 524288 226375608064910080 72057594037927936 73 22409855930421122957312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002793 1048576 22409855930421122957312 75557863725914323419136 636926413 2147483648 320313 320000 (ep1077 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1079 := BSN.sin_dyadic_bound_f 636926413 2147483648 2 1 1048576 320313 ep1076 ep80 ep1076 ep1076 ep81 ep1076 306459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 636926413) qz19 0 1 ep1076 ep80 ep1076 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 636926413) qz20 0 1 ep1076 ep81 ep1076 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1080 := @Enclosure.Real.IsNear.sin_image qz167 qz477 Bool.false 242279101 524288 981 1048576 Bool.true 306459 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 1040580817029485693 2251799813685248 467187500299 500000000000000 242279101 524288 981 1048576 (ep1075 rfl) rfl) (Enclosure.sfrac_false_div 242279101 524288) (BSN.sin_reduce2 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22409855930421122957312) qz25) 226375608064910080 72057594037927936 Bool.false 306459 1048576 73 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 242279101 524288 226375608064910080 72057594037927936 73 22409855930421122957312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 306459 1048576 22409855930421122957312 75557863725914323419136 636926413 2147483648 320313 320000 (ep1079 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1081 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 224181394701 1099511627776 138611437943 687194767360000 Bool.false 68511054663 1099511627776 138176229193 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz59 (Real.cos qz167) 223557 1048576 1 1048576 1002793 1048576 617221 655360000 224181394701 1099511627776 138611437943 687194767360000 qz351 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 1002793 1048576 158008576 167772160000 1002793 1048576 617221 655360000 (ep1078 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz59 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 223557 1048576 1 1048576 306459 1048576 617221 655360000 68511054663 1099511627776 138176229193 687194767360000 qz351 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 306459 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 306459 1048576 158008576 167772160000 306459 1048576 617221 655360000 (ep1080 rfl rfl) rfl)) rfl)

noncomputable def ep1082 := @ep1009 224181394701 1099511627776 138611437943 687194767360000 Bool.false 68511054663 1099511627776 138176229193 687194767360000 Bool.false 6962617858635367186432 810555398771 1099511627776 4555729453867 687194767360000 Bool.true ep1010 746355377873 549755813888 1138490209873 171798691840000 (ep1011 (BSN.head_sum_c_succ qz140 21 22 rfl rfl) (ep1073 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1074 ep1081) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz269 qz455 qz630)

noncomputable def ep1083 := @Enclosure.Complex.IsNear.of_eq qz708 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 45321414255 274877906944 16933735103 85899345920000 Bool.false 140347160343 1099511627776 135352856449 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 23 qz144 rfl)

noncomputable def ep1084 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz630 149500 1000 0 1 3530250507853047 1125899906842624 1562500001 250000000000000 1055544901848061053 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz631) Bool.false 59227775304360265777152 18889465931478580854784 1000000000640000 160000000000000000000 3530250507853047 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep376 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1085 := nat_lit 143152450411862463956281582341147015914690068279324357303007575593088444721121

noncomputable def ep1086 := nat_lit 16048805063128230564605104853431566680990950206815614960680247231789852641

noncomputable def ep1087 := nat_lit 429425253625461135407715536813734184610708222937559440679101366284801754458081

noncomputable def ep1088 := BSN.cos_dyadic_bound_f 1414752069 2147483648 3 2 1048576 320313 ep1085 ep57 ep1086 ep1087 ep60 ep1086 829140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1414752069) qz15 0 2 ep1085 ep57 ep1086 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1414752069) qz16 0 2 ep1087 ep60 ep1086 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 491526397) qz30)

noncomputable def ep1089 := @Enclosure.Real.IsNear.cos_image qz168 qz478 Bool.false 491526397 1048576 981 1048576 Bool.true 829140 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 1055544901848061053 2251799813685248 467187500299 500000000000000 491526397 1048576 981 1048576 (ep1084 rfl) rfl) (Enclosure.sfrac_false_div 491526397 1048576) (BSN.cos_reduce2 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99554326425996145721344) qz31) 226375608064910080 72057594037927936 Bool.false 829140 1048576 74 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 491526397 1048576 226375608064910080 72057594037927936 74 99554326425996145721344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 829140 1048576 99554326425996145721344 151115727451828646838272 1414752069 2147483648 320313 320000 (ep1088 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1090 := nat_lit 4006095987757686088242874726345739121

noncomputable def ep1091 := BSN.sin_dyadic_bound_f 1414752069 2147483648 2 1 1048576 320313 ep1090 ep80 ep1090 ep1090 ep81 ep1090 641901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1414752069) qz19 0 1 ep1090 ep80 ep1090 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1414752069) qz20 0 1 ep1090 ep81 ep1090 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1092 := @Enclosure.Real.IsNear.sin_image qz168 qz478 Bool.false 491526397 1048576 981 1048576 Bool.true 641901 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 1055544901848061053 2251799813685248 467187500299 500000000000000 491526397 1048576 981 1048576 (ep1084 rfl) rfl) (Enclosure.sfrac_false_div 491526397 1048576) (BSN.sin_reduce2 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99554326425996145721344) qz31) 226375608064910080 72057594037927936 Bool.false 641901 1048576 74 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 491526397 1048576 226375608064910080 72057594037927936 74 99554326425996145721344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 641901 1048576 99554326425996145721344 151115727451828646838272 1414752069 2147483648 320313 320000 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 45321414255 274877906944 16933735103 85899345920000 Bool.false 140347160343 1099511627776 135352856449 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz61 (Real.cos qz168) 218643 1048576 1 1048576 207285 262144 617221 655360000 45321414255 274877906944 16933735103 85899345920000 qz353 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 829140 1048576 158008576 167772160000 207285 262144 617221 655360000 (ep1089 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz61 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 218643 1048576 1 1048576 641901 1048576 617221 655360000 140347160343 1099511627776 135352856449 687194767360000 qz353 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 641901 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 641901 1048576 158008576 167772160000 641901 1048576 617221 655360000 (ep1092 rfl rfl) rfl)) rfl)

noncomputable def ep1094 := @ep1007 45321414255 274877906944 16933735103 85899345920000 Bool.false 140347160343 1099511627776 135352856449 687194767360000 Bool.false 172972349515706289618944 629269741751 1099511627776 4691199334691 687194767360000 Bool.true 743469749063278200356864 1352363595403 1099511627776 4689313695941 687194767360000 (ep1008 (BSN.head_sum_c_succ qz140 22 23 rfl rfl) (ep1082 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1083 ep1093) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz269 qz455 qz633)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq qz707 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.true 165978468901 1099511627776 26518928943 137438953472000 Bool.false 75535861373 549755813888 13255111659 68719476736000 (BSN.cpow_neg_s_mk qz143 149500 1000 24 qz144 rfl)

noncomputable def ep1096 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz633 149500 1000 0 1 3578169457974519 1125899906842624 1562500001 250000000000000 1069872667934381181 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz634) Bool.false 60031721881041427759104 18889465931478580854784 1000000000640000 160000000000000000000 3578169457974519 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep390 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1097 := nat_lit 225959244589894360166913571682332433983922591507259673093012331142509766967296

noncomputable def ep1098 := nat_lit 39980575474195729309727239158333480782957004765823041263106718601345826816

noncomputable def ep1099 := nat_lit 677797772618734689042121260568680634990201860512247373196510779990326609248256

noncomputable def ep1100 := BSN.cos_dyadic_bound_f 1585736892 2147483648 3 2 1048576 320313 ep1097 ep57 ep1098 ep1099 ep60 ep1098 775459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1585736892) qz15 0 2 ep1097 ep57 ep1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1585736892) qz16 0 2 ep1099 ep60 ep1098 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 498198283) qz30)

noncomputable def ep1101 := @Enclosure.Real.IsNear.cos_image qz169 qz479 Bool.false 498198283 1048576 981 1048576 Bool.true 775459 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 1069872667934381181 2251799813685248 467187500299 500000000000000 498198283 1048576 981 1048576 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 498198283 1048576) (BSN.cos_reduce2 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111586313727581267951616) qz31) 226375608064910080 72057594037927936 Bool.false 775459 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 498198283 1048576 226375608064910080 72057594037927936 75 111586313727581267951616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 775459 1048576 111586313727581267951616 151115727451828646838272 1585736892 2147483648 320313 320000 (ep1100 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1102 := nat_lit 6323019490259043105500544315721072896

noncomputable def ep1103 := BSN.sin_dyadic_bound_f 1585736892 2147483648 2 1 1048576 320313 ep1102 ep80 ep1102 ep1102 ep81 ep1102 705814 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1585736892) qz19 0 1 ep1102 ep80 ep1102 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1585736892) qz20 0 1 ep1102 ep81 ep1102 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1104 := @Enclosure.Real.IsNear.sin_image qz169 qz479 Bool.false 498198283 1048576 981 1048576 Bool.true 705814 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 1069872667934381181 2251799813685248 467187500299 500000000000000 498198283 1048576 981 1048576 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 498198283 1048576) (BSN.sin_reduce2 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111586313727581267951616) qz31) 226375608064910080 72057594037927936 Bool.false 705814 1048576 75 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 498198283 1048576 226375608064910080 72057594037927936 75 111586313727581267951616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 705814 1048576 111586313727581267951616 151115727451828646838272 1585736892 2147483648 320313 320000 (ep1103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.true 165978468901 1099511627776 26518928943 137438953472000 Bool.false 75535861373 549755813888 13255111659 68719476736000 (@Enclosure.Real.IsNear.mulLit_ft qz63 (Real.cos qz169) 214039 1048576 1 1048576 775459 1048576 617221 655360000 165978468901 1099511627776 26518928943 137438953472000 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.true 775459 1048576 158008576 167772160000 775459 1048576 617221 655360000 (ep1101 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 214039 1048576 1 1048576 352907 524288 617221 655360000 75535861373 549755813888 13255111659 68719476736000 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 352907 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 705814 1048576 158008576 167772160000 352907 524288 617221 655360000 (ep1104 rfl rfl) rfl)) rfl)

noncomputable def ep1106 := @ep1005 165978468901 1099511627776 26518928943 137438953472000 Bool.false 75535861373 549755813888 13255111659 68719476736000 Bool.false 509394141545718454681600 231645636425 549755813888 2411896989703 343597383680000 Bool.true 660417191169588688060416 1201291872657 1099511627776 4821864812531 687194767360000 (ep1006 (BSN.head_sum_c_succ qz140 23 24 rfl rfl) (ep1094 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1095 ep1105) rfl rfl

theorem EMLast.d15 : Enclosure.Complex.IsNear qz161 Bool.false 231645636425 549755813888 2411896989703 343597383680000 Bool.true 1201291872657 1099511627776 4821864812531 687194767360000 := ep1004 (BSN.head_sum_c_succ qz140 24 25 rfl rfl) (ep1106 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz170 := (BSN.headSumC qz453 33)

noncomputable abbrev qz715 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz141)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq qz170 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 32) qz715) Bool.true 81020772433 1099511627776 5799826661619 687194767360000 Bool.true 1265743786915 1099511627776 5797014551619 687194767360000

noncomputable def ep1108 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 32) qz715 Bool.false 107991654311 1099511627776 227391152127 27487790694400 Bool.true 305108923547 274877906944 113649024601 13743895347200 Bool.true

noncomputable abbrev qz716 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz141)

noncomputable def ep1109 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 31) qz716) Bool.false 107991654311 1099511627776 227391152127 27487790694400 Bool.true 305108923547 274877906944 113649024601 13743895347200

noncomputable def ep1110 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 31) qz716 Bool.false 160549758315 1099511627776 1113672629949 137438953472000 Bool.true 88174397557 68719476736 278278913831 34359738368000 Bool.true

noncomputable abbrev qz717 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz141)

noncomputable def ep1111 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 30) qz717) Bool.false 160549758315 1099511627776 1113672629949 137438953472000 Bool.true 88174397557 68719476736 278278913831 34359738368000

noncomputable def ep1112 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 30) qz717 Bool.true 151484423 8589934592 1362403111749 171798691840000 Bool.true 1499780150703 1099511627776 5447124496371 687194767360000 Bool.false

noncomputable def ep1113 := nat_lit 1551180406177043643891712

noncomputable abbrev qz718 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz141)

noncomputable def ep1114 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 29) qz718) Bool.true 151484423 8589934592 1362403111749 171798691840000 Bool.true 1499780150703 1099511627776 5447124496371 687194767360000

noncomputable def ep1115 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 29) qz718 Bool.true 41997371101 274877906944 266447633263 34359738368000 Bool.true 1359762541353 1099511627776 1065298452177 137438953472000 Bool.false

noncomputable abbrev qz719 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz141)

noncomputable def ep1116 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 28) qz719) Bool.true 41997371101 274877906944 266447633263 34359738368000 Bool.true 1359762541353 1099511627776 1065298452177 137438953472000

noncomputable def ep1117 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 28) qz719 Bool.true 122259210731 1099511627776 5206497451141 687194767360000 Bool.true 1157068346195 1099511627776 5203541987391 687194767360000 Bool.true

noncomputable abbrev qz720 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz141)

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 27) qz720) Bool.true 122259210731 1099511627776 5206497451141 687194767360000 Bool.true 1157068346195 1099511627776 5203541987391 687194767360000

noncomputable def ep1119 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 27) qz720 Bool.false 63169854389 1099511627776 5081367953341 687194767360000 Bool.true 527565496969 549755813888 317416942201 42949672960000 Bool.true

noncomputable abbrev qz721 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz141)

noncomputable def ep1120 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 26) qz721) Bool.false 63169854389 1099511627776 5081367953341 687194767360000 Bool.true 527565496969 549755813888 317416942201 42949672960000

noncomputable def ep1121 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 26) qz721 Bool.false 276742859755 1099511627776 4953791056767 687194767360000 Bool.true 1084859362947 1099511627776 4951652928017 687194767360000 Bool.true

noncomputable abbrev qz722 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz141)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 26) (@HAdd.hAdd Complex Complex Complex qz4 qz161 qz722) Bool.false 276742859755 1099511627776 4953791056767 687194767360000 Bool.true 1084859362947 1099511627776 4951652928017 687194767360000

noncomputable def ep1123 := @Enclosure.Complex.IsNear.addLitP qz161 qz722 Bool.false 231645636425 549755813888 2411896989703 343597383680000 Bool.true 1201291872657 1099511627776 4821864812531 687194767360000 Bool.true

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz269 qz455 qz643)

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq qz722 (Complex.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.true 186548413095 1099511627776 129997077361 687194767360000 Bool.false 58216254855 549755813888 64894057743 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 25 qz144 rfl)

noncomputable def ep1125 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz643 149500 1000 0 1 3624129903009015 1125899906842624 1562500001 250000000000000 1083614840999695485 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz644) Bool.false 60802810194841294602240 18889465931478580854784 1000000000640000 160000000000000000000 3624129903009015 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep420 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1126 := nat_lit 2061576487703070322573767286092042496

noncomputable def ep1127 := BSN.cos_dyadic_bound_f 1198256692 2147483648 2 1 1048576 320313 ep1126 ep95 ep1126 ep1126 ep96 ep1126 889533 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1198256692) qz15 0 1 ep1126 ep95 ep1126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1198256692) qz16 0 1 ep1126 ep96 ep1126 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz480 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 504597481) qz30)

noncomputable def ep1128 := @Enclosure.Real.IsNear.cos_image qz171 qz480 Bool.false 504597481 1048576 981 1048576 Bool.true 889533 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1083614840999695485 2251799813685248 467187500299 500000000000000 504597481 1048576 981 1048576 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 504597481 1048576) (BSN.cos_reduce2 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84319818623137404157952) qz31) 226375608064910080 72057594037927936 Bool.false 889533 1048576 76 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 504597481 1048576 226375608064910080 72057594037927936 76 84319818623137404157952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 889533 1048576 84319818623137404157952 151115727451828646838272 1198256692 2147483648 320313 320000 (ep1127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1129 := BSN.sin_dyadic_bound_f 1198256692 2147483648 2 1 1048576 320313 ep1126 ep80 ep1126 ep1126 ep81 ep1126 555194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1198256692) qz19 0 1 ep1126 ep80 ep1126 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1198256692) qz20 0 1 ep1126 ep81 ep1126 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1130 := @Enclosure.Real.IsNear.sin_image qz171 qz480 Bool.false 504597481 1048576 981 1048576 Bool.true 555194 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 1083614840999695485 2251799813685248 467187500299 500000000000000 504597481 1048576 981 1048576 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 504597481 1048576) (BSN.sin_reduce2 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84319818623137404157952) qz31) 226375608064910080 72057594037927936 Bool.false 555194 1048576 76 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 504597481 1048576 226375608064910080 72057594037927936 76 84319818623137404157952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 555194 1048576 84319818623137404157952 151115727451828646838272 1198256692 2147483648 320313 320000 (ep1129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz356 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz356 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.true 186548413095 1099511627776 129997077361 687194767360000 Bool.false 58216254855 549755813888 64894057743 343597383680000 (@Enclosure.Real.IsNear.mulLit_ft qz356 (Real.cos qz171) 209715 1048576 1 1048576 889533 1048576 617221 655360000 186548413095 1099511627776 129997077361 687194767360000 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.true 889533 1048576 158008576 167772160000 889533 1048576 617221 655360000 (ep1128 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz356 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 209715 1048576 1 1048576 277597 524288 617221 655360000 58216254855 549755813888 64894057743 343597383680000 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 277597 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 555194 1048576 158008576 167772160000 277597 524288 617221 655360000 (ep1130 rfl rfl) rfl)) rfl)

noncomputable def ep1132 := @ep1123 186548413095 1099511627776 129997077361 687194767360000 Bool.false 58216254855 549755813888 64894057743 343597383680000 Bool.false 152140996102302665277440 276742859755 1099511627776 4953791056767 687194767360000 Bool.true 596407742030945175207936 1084859362947 1099511627776 4951652928017 687194767360000 EMLast.d15 (ep1124 ep1131) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz269 qz455 qz645)

noncomputable def ep1133 := @Enclosure.Complex.IsNear.of_eq qz721 (Complex.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.true 106786502683 549755813888 63788448287 343597383680000 Bool.false 29728369009 1099511627776 127018147199 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 26 qz144 rfl)

noncomputable def ep1134 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz645 149500 1000 0 1 3668288609262839 1125899906842624 1562500001 250000000000000 1096818294169588861 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz646) Bool.false 61543670347942250676224 18889465931478580854784 1000000000640000 160000000000000000000 3668288609262839 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep431 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1135 := nat_lit 7782207153643271681194446306755761

noncomputable def ep1136 := BSN.cos_dyadic_bound_f 297013163 2147483648 2 1 1048576 320313 ep1135 ep95 ep1135 ep1135 ep96 ep1135 1038562 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 297013163) qz15 0 1 ep1135 ep95 ep1135 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 297013163) qz16 0 1 ep1135 ep96 ep1135 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 255372909) qz24)

noncomputable def ep1137 := @Enclosure.Real.IsNear.cos_image qz172 qz481 Bool.false 255372909 524288 981 1048576 Bool.true 1038562 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1096818294169588861 2251799813685248 467187500299 500000000000000 255372909 524288 981 1048576 (ep1134 rfl) rfl) (Enclosure.sfrac_false_div 255372909 524288) (BSN.cos_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10450221661398130229248) qz25) 226375608064910080 72057594037927936 Bool.false 1038562 1048576 77 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 255372909 524288 226375608064910080 72057594037927936 77 10450221661398130229248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1038562 1048576 10450221661398130229248 75557863725914323419136 297013163 2147483648 320313 320000 (ep1136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1138 := BSN.sin_dyadic_bound_f 297013163 2147483648 1 0 1048576 320313 0 1 1 0 1 1 144563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 297013163) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 297013163) qz20 0 0 rfl) rfl rfl

noncomputable def ep1139 := @Enclosure.Real.IsNear.sin_image qz172 qz481 Bool.false 255372909 524288 981 1048576 Bool.true 144563 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 1096818294169588861 2251799813685248 467187500299 500000000000000 255372909 524288 981 1048576 (ep1134 rfl) rfl) (Enclosure.sfrac_false_div 255372909 524288) (BSN.sin_reduce2 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10450221661398130229248) qz25) 226375608064910080 72057594037927936 Bool.false 144563 1048576 77 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 255372909 524288 226375608064910080 72057594037927936 77 10450221661398130229248 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 144563 1048576 10450221661398130229248 75557863725914323419136 297013163 2147483648 320313 320000 (ep1138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz361 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz361 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.true 106786502683 549755813888 63788448287 343597383680000 Bool.false 29728369009 1099511627776 127018147199 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz361 (Real.cos qz172) 205643 1048576 1 1048576 519281 524288 617221 655360000 106786502683 549755813888 63788448287 343597383680000 qz365 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.true 1038562 1048576 158008576 167772160000 519281 524288 617221 655360000 (ep1137 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz361 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 205643 1048576 1 1048576 144563 1048576 617221 655360000 29728369009 1099511627776 127018147199 687194767360000 qz365 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.true 144563 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.true 144563 1048576 158008576 167772160000 144563 1048576 617221 655360000 (ep1139 rfl rfl) rfl)) rfl)

noncomputable def ep1141 := @ep1121 106786502683 549755813888 63788448287 343597383680000 Bool.false 29728369009 1099511627776 127018147199 687194767360000 Bool.false 34727994712811143954432 63169854389 1099511627776 5081367953341 687194767360000 Bool.true 1160128796661679168421888 527565496969 549755813888 317416942201 42949672960000 (ep1122 (BSN.head_sum_c_succ qz140 25 26 rfl rfl) (ep1132 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1133 ep1140) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz269 qz455 qz647)

noncomputable def ep1142 := @Enclosure.Complex.IsNear.of_eq qz720 (Complex.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.true 5794658285 34359738368 625647489 3435973836800 Bool.true 101937352257 1099511627776 4994836487 27487790694400 (BSN.cpow_neg_s_mk qz143 149500 1000 27 qz144 rfl)

noncomputable def ep1143 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz647 149500 1000 0 1 3710780868205815 1125899906842624 1562500001 250000000000000 1109523479593538685 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz648) Bool.false 62256572154556490711040 18889465931478580854784 1000000000640000 160000000000000000000 3710780868205815 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep446 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1144 := nat_lit 1781326840275823171436945170169383128341434560408482628277178429379947858533345

noncomputable def ep1145 := nat_lit 766497767630840419213743337843760594667211437993583490155995258711484439521

noncomputable def ep1146 := nat_lit 4664138823384325040703748432658542104693343601598798224599024275100044845161441

noncomputable def ep1147 := BSN.sin_dyadic_bound_f 2293843909 2147483648 3 2 1048576 320313 ep1144 ep64 ep1145 ep1146 ep66 ep1145 918880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2293843909) qz19 0 2 ep1144 ep64 ep1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2293843909) qz20 0 2 ep1146 ep66 ep1145 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 516662131) qz30)

noncomputable def ep1148 := @Enclosure.Real.IsNear.cos_image qz173 qz482 Bool.false 516662131 1048576 981 1048576 Bool.true 918880 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1109523479593538685 2251799813685248 467187500299 500000000000000 516662131 1048576 981 1048576 (ep1143 rfl) rfl) (Enclosure.sfrac_false_div 516662131 1048576) (BSN.cos_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161414915226613885960192) qz31) 226375608064910080 72057594037927936 Bool.false 918880 1048576 78 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 516662131 1048576 226375608064910080 72057594037927936 78 161414915226613885960192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 918880 1048576 161414915226613885960192 151115727451828646838272 2293843909 2147483648 320313 320000 (ep1147 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1149 := nat_lit 989966688049959913206842313799810076009537960866043052816279569770509470047201

noncomputable def ep1150 := nat_lit 2968367068614618058782099454723742706839279459722141991468526718794105441262561

noncomputable def ep1151 := BSN.cos_dyadic_bound_f 2293843909 2147483648 3 2 1048576 320313 ep1149 ep57 ep1145 ep1150 ep60 ep1145 505143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2293843909) qz15 0 2 ep1149 ep57 ep1145 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2293843909) qz16 0 2 ep1150 ep60 ep1145 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1152 := @Enclosure.Real.IsNear.sin_image qz173 qz482 Bool.false 516662131 1048576 981 1048576 Bool.false 505143 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 1109523479593538685 2251799813685248 467187500299 500000000000000 516662131 1048576 981 1048576 (ep1143 rfl) rfl) (Enclosure.sfrac_false_div 516662131 1048576) (BSN.sin_reduce1 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161414915226613885960192) qz31) 226375608064910080 72057594037927936 Bool.false 505143 1048576 78 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 516662131 1048576 226375608064910080 72057594037927936 78 161414915226613885960192 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 505143 1048576 161414915226613885960192 151115727451828646838272 2293843909 2147483648 320313 320000 (ep1151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1153 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz366 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz366 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.true 5794658285 34359738368 625647489 3435973836800 Bool.true 101937352257 1099511627776 4994836487 27487790694400 (@Enclosure.Real.IsNear.mulLit_ft qz366 (Real.cos qz173) 201799 1048576 1 1048576 28715 32768 617221 655360000 5794658285 34359738368 625647489 3435973836800 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.true 918880 1048576 158008576 167772160000 28715 32768 617221 655360000 (ep1148 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz366 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 201799 1048576 1 1048576 505143 1048576 617221 655360000 101937352257 1099511627776 4994836487 27487790694400 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.false 505143 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.false 505143 1048576 158008576 167772160000 505143 1048576 617221 655360000 (ep1152 rfl rfl) rfl)) rfl)

noncomputable def ep1154 := @ep1119 5794658285 34359738368 625647489 3435973836800 Bool.true 101937352257 1099511627776 4994836487 27487790694400 Bool.true 4200794493795338027008 122259210731 1099511627776 5206497451141 687194767360000 Bool.true 636105050386474372956160 1157068346195 1099511627776 5203541987391 687194767360000 (ep1120 (BSN.head_sum_c_succ qz140 26 27 rfl rfl) (ep1141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1142 ep1153) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz269 qz455 qz649)

noncomputable def ep1155 := @Enclosure.Complex.IsNear.of_eq qz719 (Complex.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.true 45730273673 1099511627776 122455214119 687194767360000 Bool.true 101347097579 549755813888 61475136747 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 28 qz144 rfl)

noncomputable def ep1156 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz649 149500 1000 0 1 3751726938922231 1125899906842624 1562500001 250000000000000 1121766354737747069 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz650) Bool.false 62943533227317076688896 18889465931478580854784 1000000000640000 160000000000000000000 3751726938922231 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep460 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1157 := nat_lit 51562153886285753726370988952699136

noncomputable def ep1158 := BSN.sin_dyadic_bound_f 476521788 2147483648 2 1 1048576 320313 ep1157 ep80 ep1157 ep1157 ep81 ep1157 230771 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 476521788) qz19 0 1 ep1157 ep80 ep1157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 476521788) qz20 0 1 ep1157 ep81 ep1157 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130590791) qz17)

noncomputable def ep1159 := @Enclosure.Real.IsNear.cos_image qz174 qz483 Bool.false 130590791 262144 981 1048576 Bool.true 230771 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 1121766354737747069 2251799813685248 467187500299 500000000000000 130590791 262144 981 1048576 (ep1156 rfl) rfl) (Enclosure.sfrac_false_div 130590791 262144) (BSN.cos_reduce1 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383059959797526822912) qz286) 226375608064910080 72057594037927936 Bool.false 230771 1048576 79 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 130590791 262144 226375608064910080 72057594037927936 79 8383059959797526822912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 230771 1048576 8383059959797526822912 37778931862957161709568 476521788 2147483648 320313 320000 (ep1158 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1160 := BSN.cos_dyadic_bound_f 476521788 2147483648 2 1 1048576 320313 ep1157 ep95 ep1157 ep1157 ep96 ep1157 1022866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 476521788) qz15 0 1 ep1157 ep95 ep1157 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 476521788) qz16 0 1 ep1157 ep96 ep1157 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1161 := @Enclosure.Real.IsNear.sin_image qz174 qz483 Bool.false 130590791 262144 981 1048576 Bool.false 1022866 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 1121766354737747069 2251799813685248 467187500299 500000000000000 130590791 262144 981 1048576 (ep1156 rfl) rfl) (Enclosure.sfrac_false_div 130590791 262144) (BSN.sin_reduce1 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8383059959797526822912) qz286) 226375608064910080 72057594037927936 Bool.false 1022866 1048576 79 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 130590791 262144 226375608064910080 72057594037927936 79 8383059959797526822912 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022866 1048576 8383059959797526822912 37778931862957161709568 476521788 2147483648 320313 320000 (ep1160 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1162 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz371 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz371 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.true 45730273673 1099511627776 122455214119 687194767360000 Bool.true 101347097579 549755813888 61475136747 343597383680000 (@Enclosure.Real.IsNear.mulLit_ft qz371 (Real.cos qz174) 198163 1048576 1 1048576 230771 1048576 617221 655360000 45730273673 1099511627776 122455214119 687194767360000 qz375 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.true 230771 1048576 158008576 167772160000 230771 1048576 617221 655360000 (ep1159 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz371 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 198163 1048576 1 1048576 511433 524288 617221 655360000 101347097579 549755813888 61475136747 343597383680000 qz375 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.false 511433 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.false 1022866 1048576 158008576 167772160000 511433 524288 617221 655360000 (ep1161 rfl rfl) rfl)) rfl)

noncomputable def ep1163 := @ep1117 45730273673 1099511627776 122455214119 687194767360000 Bool.true 101347097579 549755813888 61475136747 343597383680000 Bool.true 184706391446293005205504 41997371101 274877906944 266447633263 34359738368000 Bool.true 747537362615933771710464 1359762541353 1099511627776 1065298452177 137438953472000 (ep1118 (BSN.head_sum_c_succ qz140 27 28 rfl rfl) (ep1154 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1155 ep1162) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz269 qz455 qz651)

noncomputable def ep1164 := @Enclosure.Complex.IsNear.of_eq qz718 (Complex.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 37149869565 274877906944 15082472717 85899345920000 Bool.true 70008804675 549755813888 60316117743 343597383680000 (BSN.cpow_neg_s_mk qz143 149500 1000 29 qz144 rfl)

noncomputable def ep1165 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz651 149500 1000 0 1 3791236343078135 1125899906842624 1562500001 250000000000000 1133579666580362365 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 63606391034871975772160 18889465931478580854784 1000000000640000 160000000000000000000 3791236343078135 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep475 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1166 := nat_lit 247838244985438175395483741773838891475549235261072065512275562955126765936896

noncomputable def ep1167 := nat_lit 48096180065761001690073299512540169265998101196871899435362085659134812416

noncomputable def ep1168 := nat_lit 743418542596183004183071078722491594088115709580822452737955964694062028185856

noncomputable def ep1169 := BSN.cos_dyadic_bound_f 1622795606 2147483648 3 2 1048576 320313 ep1166 ep57 ep1167 ep1168 ep60 ep1167 763164 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1622795606) qz15 0 2 ep1166 ep57 ep1167 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1622795606) qz16 0 2 ep1168 ep60 ep1167 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 263932083) qz24)

noncomputable def ep1170 := @Enclosure.Real.IsNear.cos_image qz175 qz484 Bool.false 263932083 524288 981 1048576 Bool.false 763164 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 1133579666580362365 2251799813685248 467187500299 500000000000000 263932083 524288 981 1048576 (ep1165 rfl) rfl) (Enclosure.sfrac_false_div 263932083 524288) (BSN.cos_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57097044434017977368576) qz25) 226375608064910080 72057594037927936 Bool.false 763164 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 263932083 524288 226375608064910080 72057594037927936 80 57097044434017977368576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 763164 1048576 57097044434017977368576 75557863725914323419136 1622795606 2147483648 320313 320000 (ep1169 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1171 := nat_lit 6935140955003077779193695569221159696

noncomputable def ep1172 := BSN.sin_dyadic_bound_f 1622795606 2147483648 2 1 1048576 320313 ep1171 ep80 ep1171 ep1171 ep81 ep1171 719090 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1622795606) qz19 0 1 ep1171 ep80 ep1171 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1622795606) qz20 0 1 ep1171 ep81 ep1171 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1173 := @Enclosure.Real.IsNear.sin_image qz175 qz484 Bool.false 263932083 524288 981 1048576 Bool.false 719090 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 1133579666580362365 2251799813685248 467187500299 500000000000000 263932083 524288 981 1048576 (ep1165 rfl) rfl) (Enclosure.sfrac_false_div 263932083 524288) (BSN.sin_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57097044434017977368576) qz25) 226375608064910080 72057594037927936 Bool.false 719090 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 263932083 524288 226375608064910080 72057594037927936 80 57097044434017977368576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 719090 1048576 57097044434017977368576 75557863725914323419136 1622795606 2147483648 320313 320000 (ep1172 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1174 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz376 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz376 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 37149869565 274877906944 15082472717 85899345920000 Bool.true 70008804675 549755813888 60316117743 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz376 (Real.cos qz175) 194715 1048576 1 1048576 190791 262144 617221 655360000 37149869565 274877906944 15082472717 85899345920000 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 763164 1048576 158008576 167772160000 190791 262144 617221 655360000 (ep1170 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz376 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 194715 1048576 1 1048576 359545 524288 617221 655360000 70008804675 549755813888 60316117743 343597383680000 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 359545 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 719090 1048576 158008576 167772160000 359545 524288 617221 655360000 (ep1173 rfl rfl) rfl)) rfl)

noncomputable def ep1175 := @ep1115 37149869565 274877906944 15082472717 85899345920000 Bool.true 70008804675 549755813888 60316117743 343597383680000 Bool.true 1332471076123505065984 151484423 8589934592 1362403111749 171798691840000 Bool.true 824512857402795060363264 1499780150703 1099511627776 5447124496371 687194767360000 (ep1116 (BSN.head_sum_c_succ qz140 28 29 rfl rfl) (ep1163 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1164 ep1174) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz269 qz455 qz653)

noncomputable def ep1176 := @Enclosure.Complex.IsNear.of_eq qz717 (Complex.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.false 179939764459 1099511627776 118750702749 687194767360000 Bool.false 88989789791 1099511627776 118453780249 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 30 qz144 rfl)

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz653 149500 1000 0 1 3829405717437687 1125899906842624 1562500001 250000000000000 1144992309513868413 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz654) Bool.false 64246766873087041339392 18889465931478580854784 1000000000640000 160000000000000000000 3829405717437687 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1178 := nat_lit 2088825992818996345942175307844512328997147193728637688336430898123527862890625

noncomputable def ep1179 := nat_lit 1053813393307208187370059110187864823230482038499203518157739404449462890625

noncomputable def ep1180 := nat_lit 5469028569032016854688050472461990032897774250750766663756492202716321462890625

noncomputable def ep1181 := BSN.sin_dyadic_bound_f 2386961775 2147483648 3 2 1048576 320313 ep1178 ep64 ep1179 ep1180 ep66 ep1179 939913 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2386961775) qz19 0 2 ep1178 ep64 ep1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2386961775) qz20 0 2 ep1180 ep66 ep1179 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16661831) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1182 := @Enclosure.Real.IsNear.cos_image qz176 qz485 Bool.false 16661831 32768 981 1048576 Bool.false 939913 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 1144992309513868413 2251799813685248 467187500299 500000000000000 16661831 32768 981 1048576 (ep1177 rfl) rfl) (Enclosure.sfrac_false_div 16661831 32768) (BSN.cos_reduce3 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5248984455201278656512) qz462) 226375608064910080 72057594037927936 Bool.false 939913 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 16661831 32768 226375608064910080 72057594037927936 80 5248984455201278656512 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 939913 1048576 5248984455201278656512 4722366482869645213696 2386961775 2147483648 320313 320000 (ep1181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1183 := nat_lit 1160927246407578951384484086184812567142073099644131695083865049803937462890625

noncomputable def ep1184 := nat_lit 3480674112436122437778712140334061971779758334855396678215279670602913462890625

noncomputable def ep1185 := BSN.cos_dyadic_bound_f 2386961775 2147483648 3 2 1048576 320313 ep1183 ep57 ep1179 ep1184 ep60 ep1179 464837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2386961775) qz15 0 2 ep1183 ep57 ep1179 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2386961775) qz16 0 2 ep1184 ep60 ep1179 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1186 := @Enclosure.Real.IsNear.sin_image qz176 qz485 Bool.false 16661831 32768 981 1048576 Bool.true 464837 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 1144992309513868413 2251799813685248 467187500299 500000000000000 16661831 32768 981 1048576 (ep1177 rfl) rfl) (Enclosure.sfrac_false_div 16661831 32768) (BSN.sin_reduce3 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5248984455201278656512) qz462) 226375608064910080 72057594037927936 Bool.false 464837 1048576 80 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 16661831 32768 226375608064910080 72057594037927936 80 5248984455201278656512 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 464837 1048576 5248984455201278656512 4722366482869645213696 2386961775 2147483648 320313 320000 (ep1185 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1187 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz381 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz381 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.false 179939764459 1099511627776 118750702749 687194767360000 Bool.false 88989789791 1099511627776 118453780249 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz381 (Real.cos qz176) 191443 1048576 1 1048576 939913 1048576 617221 655360000 179939764459 1099511627776 118750702749 687194767360000 qz385 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 939913 1048576 158008576 167772160000 939913 1048576 617221 655360000 (ep1182 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz381 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 191443 1048576 1 1048576 464837 1048576 617221 655360000 88989789791 1099511627776 118453780249 687194767360000 qz385 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 464837 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 464837 1048576 158008576 167772160000 464837 1048576 617221 655360000 (ep1186 rfl rfl) rfl)) rfl)

noncomputable def ep1188 := @ep1112 179939764459 1099511627776 118750702749 687194767360000 Bool.false 88989789791 1099511627776 118453780249 687194767360000 Bool.false 1379111922687258132480 160549758315 1099511627776 1113672629949 137438953472000 Bool.true ep1113 88174397557 68719476736 278278913831 34359738368000 (ep1114 (BSN.head_sum_c_succ qz140 29 30 rfl rfl) (ep1175 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1176 ep1187) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz269 qz455 qz655)

noncomputable def ep1189 := @Enclosure.Complex.IsNear.of_eq qz716 (Complex.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 13139526001 274877906944 11641565343 68719476736000 Bool.false 47588666681 274877906944 11687295343 68719476736000 (BSN.cpow_neg_s_mk qz143 149500 1000 31 qz144 rfl)

noncomputable def ep1190 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz655 149500 1000 0 1 3866325256314103 1125899906842624 1562500001 250000000000000 1156031251637916797 2251799813685248 467187500299 500000000000000 qz145 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 1562500001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz656) Bool.false 64866173951437069877248 18889465931478580854784 1000000000640000 160000000000000000000 3866325256314103 1125899906842624 1562500001 250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep497 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1191 := nat_lit 2183407009075138538879893231676879297005210414166881539808722401458320435520321

noncomputable def ep1192 := nat_lit 3721603867539335921325339597695675455600870964821659764625461770467818283841

noncomputable def ep1193 := nat_lit 6542777819490336944797029015835246540104429500571001299896916280834025669993281

noncomputable def ep1194 := BSN.cos_dyadic_bound_f 2794739081 2147483648 3 2 1048576 320313 ep1191 ep57 ep1192 ep1193 ep60 ep1192 279076 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2794739081) qz15 0 2 ep1191 ep57 ep1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2794739081) qz16 0 2 ep1193 ep60 ep1192 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67289875) qz562)

noncomputable def ep1195 := @Enclosure.Real.IsNear.cos_image qz177 qz486 Bool.false 67289875 131072 981 1048576 Bool.true 279076 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 1156031251637916797 2251799813685248 467187500299 500000000000000 67289875 131072 981 1048576 (ep1190 rfl) rfl) (Enclosure.sfrac_false_div 67289875 131072) (BSN.cos_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24582784933282699018240) qz293) 226375608064910080 72057594037927936 Bool.false 279076 1048576 81 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 67289875 131072 226375608064910080 72057594037927936 81 24582784933282699018240 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 279076 1048576 24582784933282699018240 18889465931478580854784 2794739081 2147483648 320313 320000 (ep1194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1196 := nat_lit 3927155333241217901246747545340226194244898048728529443843999953208602529309505

noncomputable def ep1197 := nat_lit 10279381371274792721297431116542418462760903003203103951401082463156058728112961

noncomputable def ep1198 := BSN.sin_dyadic_bound_f 2794739081 2147483648 3 2 1048576 320313 ep1196 ep64 ep1192 ep1197 ep66 ep1192 1010756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2794739081) qz19 0 2 ep1196 ep64 ep1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2794739081) qz20 0 2 ep1197 ep66 ep1192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1199 := @Enclosure.Real.IsNear.sin_image qz177 qz486 Bool.false 67289875 131072 981 1048576 Bool.true 1010756 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 1156031251637916797 2251799813685248 467187500299 500000000000000 67289875 131072 981 1048576 (ep1190 rfl) rfl) (Enclosure.sfrac_false_div 67289875 131072) (BSN.sin_reduce2 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24582784933282699018240) qz293) 226375608064910080 72057594037927936 Bool.false 1010756 1048576 81 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 67289875 131072 226375608064910080 72057594037927936 81 24582784933282699018240 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1010756 1048576 24582784933282699018240 18889465931478580854784 2794739081 2147483648 320313 320000 (ep1198 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1200 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz386 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz386 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 13139526001 274877906944 11641565343 68719476736000 Bool.false 47588666681 274877906944 11687295343 68719476736000 (@Enclosure.Real.IsNear.mulLit_ft qz386 (Real.cos qz177) 188329 1048576 1 1048576 69769 262144 617221 655360000 13139526001 274877906944 11641565343 68719476736000 qz390 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 279076 1048576 158008576 167772160000 69769 262144 617221 655360000 (ep1195 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz386 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 188329 1048576 1 1048576 252689 262144 617221 655360000 47588666681 274877906944 11687295343 68719476736000 qz390 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.true 252689 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.true 1010756 1048576 158008576 167772160000 252689 262144 617221 655360000 (ep1199 rfl rfl) rfl)) rfl)

noncomputable def ep1201 := @ep1110 13139526001 274877906944 11641565343 68719476736000 Bool.false 47588666681 274877906944 11687295343 68719476736000 Bool.false 29684519904427674435584 107991654311 1099511627776 227391152127 27487790694400 Bool.true 20966925573634069102592 305108923547 274877906944 113649024601 13743895347200 (ep1111 (BSN.head_sum_c_succ qz140 30 31 rfl rfl) (ep1188 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1189 ep1200) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz269 qz455 qz657)

noncomputable def ep1202 := @Enclosure.Complex.IsNear.of_eq qz715 (Complex.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.true 23626553343 137438953472 28761964611 171798691840000 Bool.true 45308092727 1099511627776 114563321569 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 32 qz144 rfl)

noncomputable def ep1203 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz657 149500 1000 0 1 15608286920413395 4503599627370496 1250000001 200000000000000 4666877789203605105 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz658) Bool.false 65465900263437584302080 18889465931478580854784 1000000000800000 160000000000000000000 15608286920413395 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep508 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1204 := nat_lit 4355978719016921314643323520076250214940884876564008124731727297752656458430625

noncomputable def ep1205 := nat_lit 4577788272929633765660126717918395025281196049446677457585359909045875390625

noncomputable def ep1206 := nat_lit 11401104035459574512254778537894501732899481311682821896508909482832787878590625

noncomputable def ep1207 := BSN.sin_dyadic_bound_f 2868018595 2147483648 3 2 1048576 320313 ep1204 ep64 ep1205 ep1206 ep66 ep1205 1019688 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2868018595) qz19 0 2 ep1204 ep64 ep1205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2868018595) qz20 0 2 ep1206 ep66 ep1205 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz487 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 543296079) qz30)

noncomputable def ep1208 := @Enclosure.Real.IsNear.cos_image qz178 qz487 Bool.false 543296079 1048576 981 1048576 Bool.true 1019688 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 4666877789203605105 9007199254740992 373750000299 400000000000000 543296079 1048576 981 1048576 (ep1203 rfl) rfl) (Enclosure.sfrac_false_div 543296079 1048576) (BSN.cos_reduce1 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201818866812840803565568) qz31) 226375608064910080 72057594037927936 Bool.false 1019688 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 543296079 1048576 226375608064910080 72057594037927936 82 201818866812840803565568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1019688 1048576 201818866812840803565568 151115727451828646838272 2868018595 2147483648 320313 320000 (ep1207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1209 := nat_lit 2422022749797369456475473123028102739422838796335314148165441992044385088190625

noncomputable def ep1210 := nat_lit 7256912672846249101895099115648471428217953996907049089581155256315063513790625

noncomputable def ep1211 := BSN.cos_dyadic_bound_f 2868018595 2147483648 3 2 1048576 320313 ep1209 ep57 ep1205 ep1210 ep60 ep1205 244429 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2868018595) qz15 0 2 ep1209 ep57 ep1205 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2868018595) qz16 0 2 ep1210 ep60 ep1205 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1212 := @Enclosure.Real.IsNear.sin_image qz178 qz487 Bool.false 543296079 1048576 981 1048576 Bool.false 244429 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 4666877789203605105 9007199254740992 373750000299 400000000000000 543296079 1048576 981 1048576 (ep1203 rfl) rfl) (Enclosure.sfrac_false_div 543296079 1048576) (BSN.sin_reduce1 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201818866812840803565568) qz31) 226375608064910080 72057594037927936 Bool.false 244429 1048576 82 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 543296079 1048576 226375608064910080 72057594037927936 82 201818866812840803565568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 244429 1048576 201818866812840803565568 151115727451828646838272 2868018595 2147483648 320313 320000 (ep1211 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1213 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz391 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz391 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.true 23626553343 137438953472 28761964611 171798691840000 Bool.true 45308092727 1099511627776 114563321569 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz391 (Real.cos qz178) 185363 1048576 1 1048576 127461 131072 617221 655360000 23626553343 137438953472 28761964611 171798691840000 qz395 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.true 1019688 1048576 158008576 167772160000 127461 131072 617221 655360000 (ep1208 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz391 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 185363 1048576 1 1048576 244429 1048576 617221 655360000 45308092727 1099511627776 114563321569 687194767360000 qz395 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 244429 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 244429 1048576 158008576 167772160000 244429 1048576 617221 655360000 (ep1212 rfl rfl) rfl)) rfl)

noncomputable def ep1214 := @ep1108 23626553343 137438953472 28761964611 171798691840000 Bool.true 45308092727 1099511627776 114563321569 687194767360000 Bool.true 11135410172684587237376 81020772433 1099511627776 5799826661619 687194767360000 Bool.true 347925002874567534837760 1265743786915 1099511627776 5797014551619 687194767360000 (ep1109 (BSN.head_sum_c_succ qz140 31 32 rfl rfl) (ep1201 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1202 ep1213) rfl rfl

theorem EMLast.d16 : Enclosure.Complex.IsNear qz170 Bool.true 81020772433 1099511627776 5799826661619 687194767360000 Bool.true 1265743786915 1099511627776 5797014551619 687194767360000 := ep1107 (BSN.head_sum_c_succ qz140 32 33 rfl rfl) (ep1214 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMLast.d17 : @Eq Nat (Nat.pow 38 1) 38 := @Eq.refl Nat 38

noncomputable def ep1215 := nat_lit 2337640219177392325301805

noncomputable def ep1216 := nat_lit 1958396278742365333618688

noncomputable def ep1217 := nat_lit 92139096296662081945406694257

noncomputable def ep1218 := nat_lit 9179982556604837501337600000000

noncomputable abbrev qz723 := (@HAdd.hAdd Complex Complex Complex qz745 (@HAdd.hAdd Complex Complex Complex qz745 qz748 (@HMul.hMul Complex Complex Complex qz747 Complex.I (@HDiv.hDiv Complex Complex Complex qz749 (↑qz752) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz488 := qz723

noncomputable abbrev qz179 := (Complex.Stirling.logGammaStirling 1 qz488)

noncomputable abbrev qz724 := (@HAdd.hAdd Complex Complex Complex qz745 qz748 (@HMul.hMul Complex Complex Complex qz747 Complex.I (@HDiv.hDiv Complex Complex Complex qz749 (↑qz752) (2 : Complex))))

noncomputable abbrev qz489 := qz724

noncomputable abbrev qz180 := qz489

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz269 (@HDiv.hDiv Real Real Real qz272 qz455 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1219 := Complex.re (@HMul.hMul Complex Complex Complex qz74 (Complex.exp (@HMul.hMul Complex Complex Complex qz74 Complex.I ↑(@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181))) (zetaApproximant qz140 1 38))

noncomputable def ep1220 := @Enclosure.Real.IsNear.of_eq ep1219 (@HSub.hSub Real Real Real qz400 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz140 1 38))))

noncomputable def ep1221 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz140 1 38))) 83993048662020821895

noncomputable def ep1222 := nat_lit 159887855455043867512232443

noncomputable def ep1223 := nat_lit 764998546383736458444800000000

noncomputable def ep1224 := nat_lit 2336296330398799992151485

noncomputable def ep1225 := nat_lit 90220442031201555535259904941

noncomputable def ep1226 := nat_lit 286126619142218275800431745640533206080149258240

noncomputable def ep1227 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.re (zetaApproximant qz140 1 38)) 5367 262144 275971

noncomputable def ep1228 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.true 21468 1048576 70648576

noncomputable abbrev qz490 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2650465) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep1229 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz490 Bool.false 2650465 16384 435

noncomputable def ep1230 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) Bool.false 4371325638798947521 27021597764222976 2602559527589373871 6291456000000000000000

noncomputable def ep1231 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181 6683524271897785537 27021597764222976 808559527589373871 6291456000000000000000 22431279 262144

noncomputable def ep1232 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 1059036690896759913 9007199254740992 508169691678301351 2097152000000000000000 Bool.false 6683524271897785537 27021597764222976

noncomputable def ep1233 := @Enclosure.Complex.IsNear.subLitP qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 981318583571641665 9007199254740992 501616091653135527 2097152000000000000000 Bool.false 6767872954020483553 27021597764222976 153847585516616483

noncomputable def ep1234 := nat_lit 1192369311623582774381459602931712

noncomputable def ep1235 := nat_lit 1881244838777533283450014790582272

noncomputable abbrev qz491 := (@HSub.hSub Complex Complex Complex qz660 qz723 qz664)

noncomputable abbrev qz492 := (Complex.log qz723)

noncomputable abbrev qz182 := (@HSub.hSub Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz396 qz491 qz492) qz488)

noncomputable abbrev qz183 := qz488

noncomputable def ep1236 := @Enclosure.Complex.IsNear.of_eq qz179 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k)))))) Bool.true 981318583571641665

noncomputable def ep1237 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz182 qz80) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) Bool.true 981318885549339969 9007199254740992

noncomputable def ep1238 := nat_lit 67435699574355901187295805440

noncomputable def ep1239 := nat_lit 465084688016014217187854123008

noncomputable def ep1240 := @ep1237 7654052735907 32000000000000000 Bool.false 2255967683710360395 9007199254740992 195625000719 1600000000000000 Bool.false 2303907 68719476736 3 68719476736 Bool.true 229622731 206158430208 299 206158430208 Bool.true ep1238 981318583571641665 9007199254740992 501616091653135527 2097152000000000000000 Bool.false ep1239

noncomputable def ep1241 := @Enclosure.Complex.IsNear.addLitP qz182 qz80 Bool.true 989595940363760961 9007199254740992 1890625000383 8000000000000000

noncomputable def ep1242 := @ep1241 Bool.false 2255967683710360395 9007199254740992 195625000719 1600000000000000 Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 Bool.true 128623428966723088416768 981318885549339969 9007199254740992 7654052735907 32000000000000000 Bool.false 2255967683710360395 2255967683710360395 9007199254740992

noncomputable abbrev qz184 := (@HMul.hMul Complex Complex Complex qz396 qz491 qz492)

noncomputable def ep1243 := @Enclosure.Complex.IsNear.subLitP qz184 qz183 Bool.true 969329742040593729 9007199254740992 1890625000383 8000000000000000 Bool.false 2929255828002249547

noncomputable def ep1244 := @ep1243 9007199254740992 195625000719 1600000000000000 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0 1 Bool.true 3958383761455043844000 989595940363760961 9007199254740992 1890625000383 8000000000000000 Bool.false 9023870734841441580000 2255967683710360395 9007199254740992 195625000719 1600000000000000

noncomputable abbrev qz185 := qz491

noncomputable abbrev qz186 := qz492

noncomputable def ep1245 := @Enclosure.Complex.IsNear.mul qz185 qz186 Bool.true 969329742040593729 9007199254740992 1890625000383 8000000000000000 Bool.false 2929255828002249547 9007199254740992 195625000719

noncomputable abbrev qz187 := (Complex.re qz491)

noncomputable abbrev qz188 := (Complex.re qz492)

noncomputable abbrev qz189 := (Complex.im qz491)

noncomputable abbrev qz190 := (Complex.im qz492)

noncomputable def ep1246 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz187 qz188) (@HMul.hMul Real Real Real qz0 qz189 qz190) 68009338073210947 9007199254740992 5468750021 2000000000000000 259334770028451169 2251799813685248

noncomputable def ep1247 := nat_lit 2182736532526578464445005448609792

noncomputable def ep1248 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz188 7000 4000 0 1 9715619724744421 2251799813685248 781250003 500000000000000

noncomputable def ep1249 := @Enclosure.Complex.IsNear.re_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 299000 4000 0 1

noncomputable abbrev qz725 := (Enclosure.sfrac Bool.false 299000 4000)

noncomputable abbrev qz493 := qz725

noncomputable def ep1250 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz493) Bool.false 7000 4000 0 1 Bool.false 299000 4000 0

noncomputable abbrev qz494 := (Complex.log (Complex.mk qz668 qz725))

noncomputable def ep1251 := @Enclosure.Complex.IsNear.of_eq qz186 qz494 Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000

noncomputable def ep1252 := nat_lit 1457075566770277451810749886483520000000000000000000000000000000000000

noncomputable def ep1253 := nat_lit 11758196242442978399023408857024000000000000000000000000000000000000

noncomputable def ep1254 := nat_lit 2828063313659903833071829440000000000000000000000000000000000000

noncomputable def ep1255 := BSN.log_dyadic_bound 23946000000 155018000000 4 3 ep1252 1048576 320000 ep1253 ep1254 326566 178964000000 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 23946000000) (BSN.artanhQ 155018000000) 0 3 ep1253 ep1252 ep1254 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz726 := (Real.log (Enclosure.sfrac Bool.false 89482000000 16000000))

noncomputable def ep1256 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz726 1 2 0 1 9715619724744421 1125899906842624 781250003 250000000000000 9715619724744421 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 89482000000 16000000 9715619724744421 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89482000000) qz670)) Bool.false 326002101391795391823872 37778931862957161709568 1000000003840000 320000000000000000000 9715619724744421 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 89482000000 16000000 12 178964000000 131072000000 326566 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep1255 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1257 := BSN.arctan_dyadic_bound_f 9000 299000 1 0 1048576 320000 0 1 1 0 1 1 31552 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 299000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 299000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz495 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 299000)))

noncomputable def ep1258 := @Enclosure.Real.IsNear.subLit_ff_p qz95 qz495 884279719003555 562949953421312 1 2000000000000000 31552 1048576 1 320000 909472293703522451456 867340367988131 562949953421312 6250000001 2000000000000000 qz96 (ep1257 rfl) rfl rfl

noncomputable abbrev qz496 := (Complex.mk qz668 qz725)

noncomputable abbrev qz497 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 299000) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1259 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (ep1251 (@congrArg Complex Complex qz183 qz496 Complex.log (BSN.w_shift_mk qz143 Bool.false 149500 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz494 Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz494) (@HMul.hMul Real Real Real qz0 qz94 qz726) Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 9000 299000 4000 89482000000 16000000 rfl rfl rfl) (ep1256 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz494) qz497 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 9000 299000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz497 (@HSub.hSub Real Real Real qz400 qz95 qz495) Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 299000 9000 rfl rfl) ep1258))))

noncomputable def ep1260 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 299000 4000 0 1 867340367988131 562949953421312 6250000001 2000000000000000

noncomputable def ep1261 := @Enclosure.Complex.IsNear.im_isNear qz185 Bool.false 7000 4000 0 1 Bool.false 299000 4000 0 1

noncomputable def ep1262 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (ep1251 (@congrArg Complex Complex qz183 qz496 Complex.log (BSN.w_shift_mk qz143 Bool.false 149500 1000 2 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz494 Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz494) (@HMul.hMul Real Real Real qz0 qz94 qz726) Bool.false 9715619724744421 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 9000 299000 4000 89482000000 16000000 rfl rfl rfl) (ep1256 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz494) qz497 Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 9000 299000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz497 (@HSub.hSub Real Real Real qz400 qz95 qz495) Bool.false 867340367988131 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 299000 9000 rfl rfl) ep1258))))

noncomputable abbrev qz191 := (@ep1250 1 (BSN.w_sub_half_mk qz455 Bool.false 149500 1000 2 qz456 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz493 Bool.false 7000 4000 0 1 Bool.false 299000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 299000 4000)))

noncomputable def ep1263 := @ep1246 1868750000299 8000000000000000 ep1247 969329742040593729 9007199254740992 1890625000383 8000000000000000 (@ep1248 68009338073210947 9007199254740992 5468750021 2000000000000000 (ep1249 qz191) ep1259 rfl) (@ep1260 259334770028451169 2251799813685248 1868750000299 8000000000000000 (ep1261 qz191) ep1262 rfl) rfl

noncomputable def ep1264 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz187 qz190) (@HMul.hMul Real Real Real qz0 qz189 qz188) 6071382575916917 2251799813685248 43750000007 8000000000000000 2904970297698581879 9007199254740992

noncomputable def ep1265 := nat_lit 6596097727731892391140820208582656

noncomputable def ep1266 := @Enclosure.Real.IsNear.mulLit_ff qz187 qz190 7000 4000 0 1 867340367988131 562949953421312 6250000001 2000000000000000

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz188 299000 4000 0 1 9715619724744421 2251799813685248 781250003 500000000000000

noncomputable def ep1268 := @ep1264 233593750897 2000000000000000 ep1265 2929255828002249547 9007199254740992 195625000719 1600000000000000 (@ep1266 6071382575916917 2251799813685248 43750000007 8000000000000000 (ep1249 qz191) ep1262 rfl) (@ep1267 2904970297698581879 9007199254740992 233593750897 2000000000000000 (ep1261 qz191) ep1259 rfl) rfl

noncomputable def ep1269 := @Enclosure.Complex.IsNear.of_eq qz183 qz496 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0 1 (BSN.w_shift_mk qz143 Bool.false 149500 1000 2 qz144 rfl)

noncomputable abbrev qz498 := (ep1269 (@Enclosure.Complex.IsNear.mk qz668 qz725 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 299000 4000)))

noncomputable abbrev qz192 := qz498

noncomputable def ep1270 := ep1244 (@ep1245 1600000000000000 (ep1263 rfl) (ep1268 rfl)) qz192 rfl rfl rfl rfl rfl rfl

noncomputable def ep1271 := @ep1242 195625000719 1600000000000000 (ep1270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz99 (↑qz2) Bool.false 120447 131072 3 1048576 Bool.false 0 1 0 1 (@ep579 131072 3 1048576 (ep581 rfl) (ep583 rfl) rfl rfl) (@ep584 1 0 1 (ep586 rfl) (ep588 rfl) rfl rfl))

noncomputable abbrev qz499 := (@HPow.hPow Complex Int Complex qz666 qz723 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz193 := qz499

noncomputable def ep1272 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193)) Bool.false 2303907 68719476736 3 68719476736

noncomputable def ep1273 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1274 := @ep1273 0 1 0 1 Bool.false 2303907 68719476736 3 68719476736 Bool.true 229622731 206158430208 299 206158430208 Bool.false 2303907 2303907 68719476736 3 68719476736 Bool.true 229622731 229622731 206158430208 299

noncomputable def ep1275 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz75 (@HMul.hMul Complex Complex Complex qz74 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz83 qz183 (@HSub.hSub Int Int Int qz406 qz85 (@HMul.hMul Int Int Int qz407 qz86 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1276 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102) qz193 Bool.false 2303907 68719476736 3 68719476736 Bool.true 229622731 206158430208 299 206158430208

noncomputable abbrev qz194 := (Complex.re qz499)

noncomputable abbrev qz195 := (Complex.im qz499)

noncomputable def ep1277 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195) 2303907 68719476736 3 68719476736 0 1 0

noncomputable def ep1278 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194 1 12 0 1 6911721 17179869184 9 17179869184 2303907

noncomputable def ep1279 := @Enclosure.Complex.IsNear.re_isNear qz193 Bool.false 6911721 17179869184 9 17179869184 Bool.true 229622731 17179869184 299 17179869184

noncomputable abbrev qz500 := (@HPow.hPow Complex Nat Complex qz671 qz723 1)

noncomputable abbrev qz196 := (@Inv.inv Complex Complex.instInv qz500)

noncomputable def ep1280 := @Enclosure.Complex.IsNear.of_eq qz193 qz196 Bool.false 6911721 17179869184 9 17179869184 Bool.true 229622731 17179869184 299

noncomputable def ep1281 := @Enclosure.Complex.IsNear.of_parts qz196 Bool.false 6911721 17179869184 9 17179869184 Bool.true 229622731 17179869184 299

noncomputable abbrev qz197 := (Complex.re qz500)

noncomputable abbrev qz198 := qz500

noncomputable def ep1282 := @Enclosure.Real.IsNear.mulLit_ff qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) 9000 4000 0 1 767969 4294967296 1 4294967296

noncomputable def ep1283 := @Enclosure.Complex.IsNear.re_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0 1

noncomputable def ep1284 := @Enclosure.Complex.IsNear.of_eq qz198 qz183 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0

noncomputable def ep1285 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) Bool.false 767969 4294967296 1 4294967296 767969 4294967296 1

noncomputable abbrev qz199 := (Complex.im qz500)

noncomputable def ep1286 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199)) Bool.false 44741 8 0 1

noncomputable def ep1287 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz197 qz197) (@HMul.hMul Real Real Real qz0 qz199 qz199) 81 16 0 1 89401 16

noncomputable def ep1288 := @Enclosure.Real.IsNear.mulLit_ff qz197 qz197 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1289 := @Enclosure.Real.IsNear.mulLit_ff qz199 qz199 299000 4000 0 1 299000 4000 0 1

noncomputable def ep1290 := @Enclosure.Complex.IsNear.im_isNear qz198 Bool.false 9000 4000 0 1 Bool.false 299000 4000 0 1

noncomputable abbrev qz200 := (ep1283 (@ep1284 1 (BSN.pow_one_c qz488) qz498))

noncomputable abbrev qz201 := (ep1290 (@ep1284 1 (BSN.pow_one_c qz488) qz498))

noncomputable def ep1291 := @ep1287 0 1 1431712 44741 8 0 1 (@ep1288 81 16 0 1 qz200 qz200 rfl) (@ep1289 89401 16 0 1 qz201 qz201 rfl)

noncomputable def ep1292 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198) 44741 8 0 1 383984 383985 2147483648 (ep1286 (Enclosure.Complex.normSq_eq_mul_add_mul qz198) (ep1291 rfl rfl)) rfl

noncomputable def ep1293 := @Enclosure.Real.IsNear.of_eq (Complex.re qz196) (@HMul.hMul Real Real Real qz0 qz197 (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198))) Bool.false 6911721 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz198) (@ep1282 6911721 17179869184 9 17179869184 qz200 (@ep1285 4294967296 (ep1292 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1294 := @Enclosure.Real.IsNear.of_eq (Complex.im qz196) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198))) Bool.true 229622731 17179869184 299 17179869184 (Enclosure.Complex.inv_im_eq_mul qz198)

noncomputable def ep1295 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz199) (@Inv.inv Real Real.instInv (@DFunLike.coe qz108 Complex (fun (x : Complex) => Real) qz109 Complex.normSq qz198)) 299000 4000 0 1 767969 4294967296 1

noncomputable def ep1296 := @ep1295 4294967296 229622731 17179869184 299 17179869184 (@Enclosure.Real.IsNear.neg qz199 Bool.false 299000 4000 0 1 qz201) (@ep1285 4294967296 (ep1292 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1297 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195 0 1 0 1 229622731 17179869184 299 17179869184 0

noncomputable def ep1298 := @Enclosure.Complex.IsNear.im_isNear qz193 Bool.false 6911721 17179869184 9 17179869184 Bool.true 229622731 17179869184 299 17179869184

noncomputable abbrev qz202 := (@ep1280 17179869184 (BSN.zpow_one_sub_two_mul qz488 1 1 rfl rfl) (@ep1281 17179869184 ep1293 (ep1294 ep1296)))

noncomputable def ep1299 := @ep1277 1 2303907 2303907 68719476736 3 68719476736 (@ep1278 68719476736 3 68719476736 ep598 (ep1279 qz202) rfl) (@ep1297 1 0 1 ep618 (ep1298 qz202) rfl) rfl

noncomputable def ep1300 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194) 229622731 206158430208 299 206158430208 0 1 0

noncomputable def ep1301 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz195 1 12 0 1 229622731 17179869184 299 17179869184 229622731

noncomputable def ep1302 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 (@Rat.cast Complex Complex.instRatCast (bernoulli qz101)) qz102)) qz194 0 1 0 1 6911721 17179869184 9 17179869184 0

noncomputable def ep1303 := @ep1300 1 229622731 229622731 206158430208 299 206158430208 (@ep1301 206158430208 299 206158430208 ep598 (ep1298 qz202) rfl) (@ep1302 1 0 1 ep618 (ep1279 qz202) rfl) rfl

noncomputable def ep1304 := @ep1274 206158430208 (@ep1275 0 1 0 1 (BSN.stirling_sum_base qz183) qz115) (ep1276 (ep1299 rfl) (ep1303 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1305 := @ep1240 6767872954020483553 27021597764222976 153847585516616483 1258291200000000000000 (ep1271 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1272 Bool.true 229622731 206158430208 299 206158430208 (BSN.stirling_sum_succ qz183 0 1 rfl) (ep1304 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1306 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz143 2) Bool.false 9714763415639781 1125899906842624 781250003 250000000000000 Bool.false 878632105444771 281474976710656

noncomputable abbrev qz203 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz489 qz415))

noncomputable def ep1307 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz143 1) qz203) Bool.false 9714763415639781 1125899906842624 781250003 250000000000000 Bool.false 878632105444771 281474976710656 6250000001 1000000000000000

noncomputable def ep1308 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 1) qz203 Bool.false 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 562949953421312 6250000001 2000000000000000 Bool.false

noncomputable def ep1309 := nat_lit 43751404898667844664402563301376

noncomputable def ep1310 := nat_lit 989251805669206256309820719104

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz274 qz489 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1311 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz143 0) qz204) Bool.false 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 562949953421312 6250000001 2000000000000000

noncomputable def ep1312 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz143 0) qz204 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz501 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz725))

noncomputable def ep1313 := @Enclosure.Complex.IsNear.of_eq qz204 qz501 Bool.false 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 562949953421312 6250000001 2000000000000000

noncomputable def ep1314 := nat_lit 1452569673579232745264622979936320000000000000000000000000000000000000

noncomputable def ep1315 := nat_lit 11654711170093817857238669974464000000000000000000000000000000000000

noncomputable def ep1316 := nat_lit 2771845865875221898251042240000000000000000000000000000000000000

noncomputable def ep1317 := BSN.log_dyadic_bound 23866000000 154938000000 4 3 ep1314 1048576 320000 ep1315 ep1316 325628 178804000000 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 23866000000) (BSN.artanhQ 154938000000) 0 3 ep1315 ep1314 ep1316 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1318 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 89402000000 16000000)) 1 2 0 1 9714612554913509 1125899906842624 781250003 250000000000000 9714612554913509 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 89402000000 16000000 9714612554913509 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89402000000) qz670)) Bool.false 325968306380191603621888 37778931862957161709568 1000000003840000 320000000000000000000 9714612554913509 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 89402000000 16000000 12 178804000000 131072000000 325628 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep1317 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1319 := BSN.arctan_dyadic_bound_f 1000 299000 1 0 1048576 320000 0 1 1 0 1 1 3506 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 299000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 299000) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz502 := (@Nat.cast Real Real.instNatCast 299000)

noncomputable def ep1320 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz672 qz502)) 884279719003555 562949953421312 1 2000000000000000 3506 1048576 1 320000 925260788097176567808 882397449586083 562949953421312 6250000001 2000000000000000 qz96 (ep1319 rfl) rfl rfl

noncomputable abbrev qz205 := (@HAdd.hAdd Complex Complex Complex qz274 qz489 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz503 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz725)

noncomputable def ep1321 := @ep1312 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 562949953421312 6250000001 2000000000000000 Bool.false 9714612554913509 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 882397449586083 562949953421312 6250000001 2000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz143 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz143) qz115) (ep1313 (@congrArg Complex Complex qz205 qz503 Complex.log (BSN.w_shift_mk qz143 Bool.false 149500 1000 0 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz501 Bool.false 9714612554913509 2251799813685248 781250003 500000000000000 Bool.false 882397449586083 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz501) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 89402000000 16000000))) Bool.false 9714612554913509 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 1000 299000 4000 89402000000 16000000 rfl rfl rfl) (ep1318 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz501) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz502 qz672)) Bool.false 882397449586083 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 1000 299000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz502 qz672)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz672 qz502))) Bool.false 882397449586083 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 299000 1000 rfl rfl) ep1320)))) rfl rfl

noncomputable abbrev qz504 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz725))

noncomputable def ep1322 := @Enclosure.Complex.IsNear.of_eq qz203 qz504 Bool.false 9714914276366053 2251799813685248 781250003 500000000000000 Bool.false 874866761303459 562949953421312 6250000001 2000000000000000

noncomputable def ep1323 := nat_lit 1453920220579791245106031993120320000000000000000000000000000000000000

noncomputable def ep1324 := nat_lit 11685689302460070184126970136000000000000000000000000000000000000000

noncomputable def ep1325 := nat_lit 2788612421576775557415000000000000000000000000000000000000000000

noncomputable def ep1326 := BSN.log_dyadic_bound 23890000000 154962000000 4 3 ep1323 1048576 320000 ep1324 ep1325 325909 178852000000 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 23890000000) (BSN.artanhQ 154962000000) 0 3 ep1324 ep1323 ep1325 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_ff qz94 (Real.log (Enclosure.sfrac Bool.false 89426000000 16000000)) 1 2 0 1 9714914276366053 1125899906842624 781250003 250000000000000 9714914276366053 2251799813685248 781250003 500000000000000 qz410 (BSN.isNear_log_sfrac 89426000000 16000000 9714914276366053 1125899906842624 781250003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89426000000) qz670)) Bool.false 325978430472153932496896 37778931862957161709568 1000000003840000 320000000000000000000 9714914276366053 1125899906842624 781250003 250000000000000 (BSN.log_rat_reduce_isNear 89426000000 16000000 12 178852000000 131072000000 325909 1048576 24973259072661432 36028797018963968 320000 1000000000000000 rfl rfl rfl rfl (ep1326 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1328 := BSN.arctan_dyadic_bound_f 5000 299000 1 0 1048576 320000 0 1 1 0 1 1 17533 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 299000) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 299000) 0 0 rfl) rfl rfl rfl

noncomputable def ep1329 := @Enclosure.Real.IsNear.subLit_ff_p qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz673 qz502)) 884279719003555 562949953421312 1 2000000000000000 17533 1048576 1 320000 917364289100535824384 874866761303459 562949953421312 6250000001 2000000000000000 qz96 (ep1328 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz274 qz489 qz415)

noncomputable abbrev qz505 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz725)

noncomputable def ep1330 := @ep1308 9714914276366053 2251799813685248 781250003 500000000000000 Bool.false 874866761303459 562949953421312 6250000001 2000000000000000 Bool.false ep1309 9714763415639781 1125899906842624 781250003 250000000000000 Bool.false ep1310 878632105444771 281474976710656 6250000001 1000000000000000 (ep1311 (BSN.log_sum_c_succ qz143 0 1 rfl) (ep1321 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1322 (@congrArg Complex Complex qz206 qz505 Complex.log (BSN.w_shift_mk qz143 Bool.false 149500 1000 1 qz144 rfl)) (@Enclosure.Complex.IsNear.of_parts qz504 Bool.false 9714914276366053 2251799813685248 781250003 500000000000000 Bool.false 874866761303459 562949953421312 6250000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz504) (@HMul.hMul Real Real Real qz0 qz94 (Real.log (Enclosure.sfrac Bool.false 89426000000 16000000))) Bool.false 9714914276366053 2251799813685248 781250003 500000000000000 (Enclosure.clog_re_eq 5000 299000 4000 89426000000 16000000 rfl rfl rfl) (ep1327 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz504) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz502 qz673)) Bool.false 874866761303459 562949953421312 6250000001 2000000000000000 (Enclosure.clog_im_eq 5000 299000 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz502 qz673)) (@HSub.hSub Real Real Real qz400 qz95 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz673 qz502))) Bool.false 874866761303459 562949953421312 6250000001 2000000000000000 (BSN.arctan_recip 299000 5000 rfl rfl) ep1329)))) rfl rfl

noncomputable def ep1331 := @ep1233 1258291200000000000000 Bool.false 9714763415639781 1125899906842624 781250003 250000000000000 Bool.false 878632105444771 281474976710656 6250000001 1000000000000000 Bool.true ep1234 1059036690896759913 9007199254740992 508169691678301351 2097152000000000000000 Bool.false ep1235 6683524271897785537 27021597764222976 808559527589373871 6291456000000000000000 (@ep1236 9007199254740992 501616091653135527 2097152000000000000000 Bool.false 6767872954020483553 27021597764222976 153847585516616483 1258291200000000000000 (BSN.logGammaStirling_unfold 1 qz183) (ep1305 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1306 6250000001 1000000000000000 (BSN.log_sum_c_eq qz143 2) (ep1307 (BSN.log_sum_c_succ qz143 1 2 rfl) (ep1330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz207 := (@HDiv.hDiv Real Real Real qz272 qz455 (2 : Real))

noncomputable def ep1332 := @Enclosure.Real.IsNear.mulLit_ff qz207 (Real.log Real.pi) 149500 2000 0 1 75021 65536 1 262144 22431279 262144 299 1048576 (@Enclosure.Real.IsNear.of_eq qz207 (Enclosure.sfrac Bool.false 149500 2000) Bool.false 149500 2000 0 1 (BSN.t_half_eq qz143 Bool.false 149500 1000 qz144) (Enclosure.Real.IsNear.const Bool.false 149500 2000)) EMLast.d5 rfl

noncomputable def ep1333 := @ep1231 299 1048576 1145916788257311298945024 4371325638798947521 27021597764222976 2602559527589373871 6291456000000000000000 (@ep1232 808559527589373871 6291456000000000000000 (ep1331 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1332 rfl rfl

noncomputable def ep1334 := nat_lit 4404782573718737723538219368596509678529472362760838980090501983289587509371136

noncomputable def ep1335 := nat_lit 15094192848460096574193340917858298966427266387549416083128745333091360973056

noncomputable def ep1336 := nat_lit 13184159335459292977466271423953812437655562555507418108105248459202579806167296

noncomputable def ep1337 := BSN.cos_dyadic_bound_f 3329287014 2147483648 3 2 1048576 320313 ep1334 ep57 ep1335 ep1336 ep60 ep1335 21468 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3329287014) qz15 0 2 ep1334 ep57 ep1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3329287014) qz16 0 2 ep1336 ep60 ep1335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1338 := @ep1229 1048576 Bool.true 21468 1048576 1 160000 (@ep1230 2650465 16384 435 1048576 ep1333 rfl) (Enclosure.sfrac_false_div 2650465 16384) (BSN.cos_reduce2 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3660589784853685207040) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 21468 1048576 25 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 2650465 16384 226375608064910080 72057594037927936 25 3660589784853685207040 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21468 1048576 3660589784853685207040 2361183241434822606848 3329287014 2147483648 320313 320000 (ep1337 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz506 := (@HPow.hPow Complex Complex Complex qz548 (@Nat.cast Complex Complex.instNatCast 38) qz690)

noncomputable abbrev qz208 := qz506

noncomputable abbrev qz507 := (@Nat.cast Complex Complex.instNatCast 38)

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz274 (@HDiv.hDiv Complex Complex Complex qz404 qz507 (@HSub.hSub Complex Complex Complex qz397 qz453 (1 : Complex))) qz403)

noncomputable abbrev qz210 := qz507

noncomputable def ep1339 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz140 1 38) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 38, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz141) (@HMul.hMul Complex Complex Complex qz74 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) Bool.false 15649906588787185 466918058095542272 10887710977516832433

noncomputable def ep1340 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 38, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz141) (@HMul.hMul Complex Complex Complex qz74 qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) Bool.false 62813050757 549755813888 634908885607 68719476736000

noncomputable def ep1341 := nat_lit 4301813566994936312249712640

noncomputable def ep1342 := nat_lit 29403580247975459755360224542720

noncomputable def ep1343 := @ep1340 Bool.true 1327866088783 1099511627776 1269334015339 137438953472000 Bool.true 18849205433548649 233459029047771136 102907381219799773 1167295145238855680000 Bool.false 324365119129326553 22412066788586029056 51304077432555199 583647572619427840000 Bool.false ep1341 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 Bool.true ep1342 26742400448688804095 22412066788586029056

noncomputable def ep1344 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 38, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz141) (BSN.headSumC qz140 38) Bool.false 62813050757 549755813888 634908885607 68719476736000 Bool.true 1327866088783 1099511627776 1269334015339

noncomputable def ep1345 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 38) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 37) (@HPow.hPow Complex Complex Complex qz6 qz125 qz141)) Bool.false 62813050757 549755813888 634908885607 68719476736000 Bool.true 1327866088783 1099511627776 1269334015339 137438953472000

noncomputable def ep1346 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 37) (@HPow.hPow Complex Complex Complex qz6 qz125 qz141) Bool.true 7770293069 274877906944 3121060219007 343597383680000 Bool.true 708978882549 549755813888 3119971590257 343597383680000 Bool.false

noncomputable abbrev qz727 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 36) qz141)

noncomputable def ep1347 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 37) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 36) qz727) Bool.true 7770293069 274877906944 3121060219007 343597383680000 Bool.true 708978882549 549755813888 3119971590257 343597383680000

noncomputable def ep1348 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 36) qz727 Bool.true 215558023 17179869184 613419060967 68719476736000 Bool.true 617761334699 549755813888 613142273217 68719476736000 Bool.true

noncomputable abbrev qz728 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz141)

noncomputable def ep1349 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 35) qz728) Bool.true 215558023 17179869184 613419060967 68719476736000 Bool.true 617761334699 549755813888 613142273217 68719476736000

noncomputable def ep1350 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 35) qz728 Bool.false 35023534815 274877906944 753031308461 85899345920000 Bool.true 1339726020877 1099511627776 6021657798313 687194767360000 Bool.true

noncomputable def ep1351 := nat_lit 1358471541383943681998848

noncomputable abbrev qz729 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz141)

noncomputable def ep1352 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz140 34) qz729) Bool.false 35023534815 274877906944 753031308461 85899345920000 Bool.true 1339726020877 1099511627776 6021657798313 687194767360000

noncomputable def ep1353 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz140 34) qz729 Bool.true 15865618083 1099511627776 5912713573383 687194767360000 Bool.true 1445712198265 1099511627776 5910294588383 687194767360000 Bool.false

noncomputable abbrev qz730 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz141)

noncomputable def ep1354 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz140 34) (@HAdd.hAdd Complex Complex Complex qz4 qz170 qz730) Bool.true 15865618083 1099511627776 5912713573383 687194767360000 Bool.true 1445712198265 1099511627776 5910294588383 687194767360000

noncomputable def ep1355 := @Enclosure.Complex.IsNear.addLitP qz170 qz730 Bool.true 81020772433 1099511627776 5799826661619 687194767360000 Bool.true 1265743786915 1099511627776 5797014551619 687194767360000 Bool.false

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz269 qz455 qz678)

noncomputable def ep1356 := @Enclosure.Complex.IsNear.of_eq qz730 (Complex.mk (@HMul.hMul Real Real Real qz0 qz428 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz428 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.false 32577577175 549755813888 28221727941 171798691840000 Bool.true 89984205675 549755813888 28320009191 171798691840000 (BSN.cpow_neg_s_mk qz143 149500 1000 33 qz144 rfl)

noncomputable def ep1357 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz678 149500 1000 0 1 15746868335186131 4503599627370496 1250000001 200000000000000 4708313632220653169 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz679) Bool.false 66047152845744529997824 18889465931478580854784 1000000000800000 160000000000000000000 15746868335186131 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep678 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1358 := nat_lit 1704732317457607126514253765621622577150574011670656171872737335078669537837056

noncomputable def ep1359 := nat_lit 2270373647105294838512391798866526794255099805850643187594313908117716402176

noncomputable def ep1360 := nat_lit 5109656205078610789865736513267134677863211835400267229243023377419773180706816

noncomputable def ep1361 := BSN.cos_dyadic_bound_f 2627315132 2147483648 3 2 1048576 320313 ep1358 ep57 ep1359 ep1360 ep60 ep1359 356950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2627315132) qz15 0 2 ep1358 ep57 ep1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2627315132) qz16 0 2 ep1360 ep60 ep1359 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz731 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 274059923) qz24)

noncomputable def ep1362 := @Enclosure.Real.IsNear.cos_image qz211 qz731 Bool.false 274059923 524288 981 1048576 Bool.false 356950 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 4708313632220653169 9007199254740992 373750000299 400000000000000 274059923 524288 981 1048576 (ep1357 rfl) rfl) (Enclosure.sfrac_false_div 274059923 524288) (BSN.cos_reduce0 qz731 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92440433222567199768576) qz25) 226375608064910080 72057594037927936 Bool.false 356950 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 274059923 524288 226375608064910080 72057594037927936 83 92440433222567199768576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356950 1048576 92440433222567199768576 75557863725914323419136 2627315132 2147483648 320313 320000 (ep1361 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1363 := nat_lit 3066701872506008591854846864679827417435629141162500594820851752015110994984960

noncomputable def ep1364 := nat_lit 8028162394468042501309864582677573621331187112882790992703268556569290588880896

noncomputable def ep1365 := BSN.sin_dyadic_bound_f 2627315132 2147483648 3 2 1048576 320313 ep1363 ep64 ep1359 ep1364 ep66 ep1359 985950 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2627315132) qz19 0 2 ep1363 ep64 ep1359 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2627315132) qz20 0 2 ep1364 ep66 ep1359 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1366 := @Enclosure.Real.IsNear.sin_image qz211 qz731 Bool.false 274059923 524288 981 1048576 Bool.false 985950 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 4708313632220653169 9007199254740992 373750000299 400000000000000 274059923 524288 981 1048576 (ep1357 rfl) rfl) (Enclosure.sfrac_false_div 274059923 524288) (BSN.sin_reduce0 qz731 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92440433222567199768576) qz25) 226375608064910080 72057594037927936 Bool.false 985950 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q0 274059923 524288 226375608064910080 72057594037927936 83 92440433222567199768576 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 985950 1048576 92440433222567199768576 75557863725914323419136 2627315132 2147483648 320313 320000 (ep1365 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1367 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz428 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz428 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.false 32577577175 549755813888 28221727941 171798691840000 Bool.true 89984205675 549755813888 28320009191 171798691840000 (@Enclosure.Real.IsNear.mulLit_ff qz428 (Real.cos qz211) 182533 1048576 1 1048576 178475 524288 617221 655360000 32577577175 549755813888 28221727941 171798691840000 qz432 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.false 356950 1048576 158008576 167772160000 178475 524288 617221 655360000 (ep1362 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz428 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 182533 1048576 1 1048576 492975 524288 617221 655360000 89984205675 549755813888 28320009191 171798691840000 qz432 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.false 492975 524288 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.false 985950 1048576 158008576 167772160000 492975 524288 617221 655360000 (ep1366 rfl rfl) rfl)) rfl)

noncomputable def ep1368 := @ep1355 32577577175 549755813888 28221727941 171798691840000 Bool.true 89984205675 549755813888 28320009191 171798691840000 Bool.true 8722215782055835336704 15865618083 1099511627776 5912713573383 687194767360000 Bool.true 794788686204984696504320 1445712198265 1099511627776 5910294588383 687194767360000 EMLast.d16 (ep1356 ep1367) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz269 qz455 qz680)

noncomputable def ep1369 := @Enclosure.Complex.IsNear.of_eq qz729 (Complex.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 155959757343 1099511627776 22307378861 137438953472000 Bool.false 26496544347 274877906944 11136320993 68719476736000 (BSN.cpow_neg_s_mk qz143 149500 1000 34 qz144 rfl)

noncomputable def ep1370 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz680 149500 1000 0 1 15881309401485523 4503599627370496 1250000001 200000000000000 4748511511044171377 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz681) Bool.false 66611039547888335060992 18889465931478580854784 1000000000800000 160000000000000000000 15881309401485523 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep689 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1371 := nat_lit 1230912070860614647462087354357523546652799921186007948210697203299467157070080

noncomputable def ep1372 := nat_lit 366094488831084965661872047573386989684962887551451611262632371652247183616

noncomputable def ep1373 := nat_lit 3223224604033978510551538135240299995631176520335889895085972222896881773076736

noncomputable def ep1374 := BSN.sin_dyadic_bound_f 2091458006 2147483648 3 2 1048576 320313 ep1371 ep64 ep1372 ep1373 ep66 ep1372 867267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2091458006) qz19 0 2 ep1371 ep64 ep1372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2091458006) qz20 0 2 ep1373 ep66 ep1372 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz732 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 552799495) qz30)

noncomputable def ep1375 := @Enclosure.Real.IsNear.cos_image qz212 qz732 Bool.false 552799495 1048576 981 1048576 Bool.false 867267 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 4748511511044171377 9007199254740992 373750000299 400000000000000 552799495 1048576 981 1048576 (ep1370 rfl) rfl) (Enclosure.sfrac_false_div 552799495 1048576) (BSN.cos_reduce3 qz732 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147173273402311798947840) qz31) 226375608064910080 72057594037927936 Bool.false 867267 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 552799495 1048576 226375608064910080 72057594037927936 83 147173273402311798947840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 867267 1048576 147173273402311798947840 151115727451828646838272 2091458006 2147483648 320313 320000 (ep1374 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1376 := nat_lit 684002748028710841908120473330879031246971050831138394166504060664882752676096

noncomputable def ep1377 := nat_lit 2051276055108470355793037675897490319761543226718312279276986917251343763661056

noncomputable def ep1378 := BSN.cos_dyadic_bound_f 2091458006 2147483648 3 2 1048576 320313 ep1376 ep57 ep1372 ep1377 ep60 ep1372 589372 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2091458006) qz15 0 2 ep1376 ep57 ep1372 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2091458006) qz16 0 2 ep1377 ep60 ep1372 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1379 := @Enclosure.Real.IsNear.sin_image qz212 qz732 Bool.false 552799495 1048576 981 1048576 Bool.true 589372 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 4748511511044171377 9007199254740992 373750000299 400000000000000 552799495 1048576 981 1048576 (ep1370 rfl) rfl) (Enclosure.sfrac_false_div 552799495 1048576) (BSN.sin_reduce3 qz732 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147173273402311798947840) qz31) 226375608064910080 72057594037927936 Bool.false 589372 1048576 83 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 552799495 1048576 226375608064910080 72057594037927936 83 147173273402311798947840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 589372 1048576 147173273402311798947840 151115727451828646838272 2091458006 2147483648 320313 320000 (ep1378 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1380 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 155959757343 1099511627776 22307378861 137438953472000 Bool.false 26496544347 274877906944 11136320993 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz433 (Real.cos qz212) 179829 1048576 1 1048576 867267 1048576 617221 655360000 155959757343 1099511627776 22307378861 137438953472000 qz437 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 867267 1048576 158008576 167772160000 867267 1048576 617221 655360000 (ep1375 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz433 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 179829 1048576 1 1048576 147343 262144 617221 655360000 26496544347 274877906944 11136320993 68719476736000 qz437 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.true 147343 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.true 589372 1048576 158008576 167772160000 147343 262144 617221 655360000 (ep1379 rfl rfl) rfl)) rfl)

noncomputable def ep1381 := @ep1353 155959757343 1099511627776 22307378861 137438953472000 Bool.false 26496544347 274877906944 11136320993 68719476736000 Bool.false 154035135099640228085760 35023534815 274877906944 753031308461 85899345920000 Bool.true 368261084497083407269888 1339726020877 1099511627776 6021657798313 687194767360000 (ep1354 (BSN.head_sum_c_succ qz140 33 34 rfl rfl) (ep1368 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1369 ep1380) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz269 qz455 qz682)

noncomputable def ep1382 := @Enclosure.Complex.IsNear.of_eq qz728 (Complex.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 38472463183 274877906944 54970070991 343597383680000 Bool.false 104203351479 1099511627776 109764933857 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 35 qz144 rfl)

noncomputable def ep1383 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz682 149500 1000 0 1 16011859227414739 4503599627370496 1250000001 200000000000000 4787545908997006961 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz683) Bool.false 67158605204982549446656 18889465931478580854784 1000000000800000 160000000000000000000 16011859227414739 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep704 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1384 := nat_lit 2669332186308954984152027837982527041

noncomputable def ep1385 := BSN.cos_dyadic_bound_f 1278205423 2147483648 2 1 1048576 320313 ep1384 ep95 ep1384 ep1384 ep96 ep1384 868252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1278205423) qz15 0 1 ep1384 ep95 ep1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1278205423) qz16 0 1 ep1384 ep96 ep1384 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz733 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 557343697) qz30)

noncomputable def ep1386 := @Enclosure.Real.IsNear.cos_image qz213 qz733 Bool.false 557343697 1048576 981 1048576 Bool.true 868252 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 4787545908997006961 9007199254740992 373750000299 400000000000000 557343697 1048576 981 1048576 (ep1383 rfl) rfl) (Enclosure.sfrac_false_div 557343697 1048576) (BSN.cos_reduce2 qz733 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89945710480178748063744) qz31) 226375608064910080 72057594037927936 Bool.false 868252 1048576 84 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 557343697 1048576 226375608064910080 72057594037927936 84 89945710480178748063744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 868252 1048576 89945710480178748063744 151115727451828646838272 1278205423 2147483648 320313 320000 (ep1385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1387 := BSN.sin_dyadic_bound_f 1278205423 2147483648 2 1 1048576 320313 ep1384 ep80 ep1384 ep1384 ep81 ep1384 587919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1278205423) qz19 0 1 ep1384 ep80 ep1384 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1278205423) qz20 0 1 ep1384 ep81 ep1384 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1388 := @Enclosure.Real.IsNear.sin_image qz213 qz733 Bool.false 557343697 1048576 981 1048576 Bool.true 587919 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 4787545908997006961 9007199254740992 373750000299 400000000000000 557343697 1048576 981 1048576 (ep1383 rfl) rfl) (Enclosure.sfrac_false_div 557343697 1048576) (BSN.sin_reduce2 qz733 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89945710480178748063744) qz31) 226375608064910080 72057594037927936 Bool.false 587919 1048576 84 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 557343697 1048576 226375608064910080 72057594037927936 84 89945710480178748063744 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 587919 1048576 89945710480178748063744 151115727451828646838272 1278205423 2147483648 320313 320000 (ep1387 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1389 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 38472463183 274877906944 54970070991 343597383680000 Bool.false 104203351479 1099511627776 109764933857 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz438 (Real.cos qz213) 177241 1048576 1 1048576 217063 262144 617221 655360000 38472463183 274877906944 54970070991 343597383680000 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 868252 1048576 158008576 167772160000 217063 262144 617221 655360000 (ep1386 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz438 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 177241 1048576 1 1048576 587919 1048576 617221 655360000 104203351479 1099511627776 109764933857 687194767360000 qz442 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 587919 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 587919 1048576 158008576 167772160000 587919 1048576 617221 655360000 (ep1388 rfl rfl) rfl)) rfl)

noncomputable def ep1390 := @ep1350 38472463183 274877906944 54970070991 343597383680000 Bool.false 104203351479 1099511627776 109764933857 687194767360000 Bool.true 948034210995625787392 215558023 17179869184 613419060967 68719476736000 Bool.true ep1351 617761334699 549755813888 613142273217 68719476736000 (ep1352 (BSN.head_sum_c_succ qz140 34 35 rfl rfl) (ep1381 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1382 ep1389) rfl rfl

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz269 qz455 qz684)

noncomputable def ep1391 := @Enclosure.Complex.IsNear.of_eq qz727 (Complex.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.true 4321364701 274877906944 13491228543 85899345920000 Bool.true 45608773925 274877906944 13565056043 85899345920000 (BSN.cpow_neg_s_mk qz143 149500 1000 36 qz144 rfl)

noncomputable def ep1392 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz684 149500 1000 0 1 16138732561338579 4503599627370496 1250000001 200000000000000 4825481035840235121 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz685) Bool.false 67690750536952647254016 18889465931478580854784 1000000000800000 160000000000000000000 16138732561338579 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep719 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1393 := BSN.sin_dyadic_bound_f 202866185 2147483648 1 0 1048576 320313 0 1 1 0 1 1 98908 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 202866185) qz19 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 202866185) qz20 0 0 rfl) rfl rfl

noncomputable abbrev qz734 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 561759927) qz30)

noncomputable def ep1394 := @Enclosure.Real.IsNear.cos_image qz214 qz734 Bool.false 561759927 1048576 981 1048576 Bool.true 98908 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 4825481035840235121 9007199254740992 373750000299 400000000000000 561759927 1048576 981 1048576 (ep1392 rfl) rfl) (Enclosure.sfrac_false_div 561759927 1048576) (BSN.cos_reduce1 qz734 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14275438709602269528064) qz31) 226375608064910080 72057594037927936 Bool.false 98908 1048576 85 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 561759927 1048576 226375608064910080 72057594037927936 85 14275438709602269528064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 98908 1048576 14275438709602269528064 151115727451828646838272 202866185 2147483648 320313 320000 (ep1393 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1395 := nat_lit 1693708428041058025492791520350625

noncomputable def ep1396 := BSN.cos_dyadic_bound_f 202866185 2147483648 2 1 1048576 320313 ep1395 ep95 ep1395 ep1395 ep96 ep1395 1043900 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 202866185) qz15 0 1 ep1395 ep95 ep1395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 202866185) qz16 0 1 ep1395 ep96 ep1395 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1397 := @Enclosure.Real.IsNear.sin_image qz214 qz734 Bool.false 561759927 1048576 981 1048576 Bool.false 1043900 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 4825481035840235121 9007199254740992 373750000299 400000000000000 561759927 1048576 981 1048576 (ep1392 rfl) rfl) (Enclosure.sfrac_false_div 561759927 1048576) (BSN.sin_reduce1 qz734 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14275438709602269528064) qz31) 226375608064910080 72057594037927936 Bool.false 1043900 1048576 85 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q1 561759927 1048576 226375608064910080 72057594037927936 85 14275438709602269528064 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1043900 1048576 14275438709602269528064 151115727451828646838272 202866185 2147483648 320313 320000 (ep1396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1398 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.true 4321364701 274877906944 13491228543 85899345920000 Bool.true 45608773925 274877906944 13565056043 85899345920000 (@Enclosure.Real.IsNear.mulLit_ft qz443 (Real.cos qz214) 174763 1048576 1 1048576 24727 262144 617221 655360000 4321364701 274877906944 13491228543 85899345920000 qz447 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.true 98908 1048576 158008576 167772160000 24727 262144 617221 655360000 (ep1394 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz443 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 174763 1048576 1 1048576 260975 262144 617221 655360000 45608773925 274877906944 13565056043 85899345920000 qz447 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.false 260975 262144 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.false 1043900 1048576 158008576 167772160000 260975 262144 617221 655360000 (ep1397 rfl rfl) rfl)) rfl)

noncomputable def ep1399 := @ep1348 4321364701 274877906944 13491228543 85899345920000 Bool.true 45608773925 274877906944 13565056043 85899345920000 Bool.true 133492618446761885696 7770293069 274877906944 3121060219007 343597383680000 Bool.true 194882631302565127520256 708978882549 549755813888 3119971590257 343597383680000 (ep1349 (BSN.head_sum_c_succ qz140 35 36 rfl rfl) (ep1390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1391 ep1398) rfl rfl

noncomputable abbrev qz215 := (@HMul.hMul Real Real Real qz269 qz455 qz686)

noncomputable def ep1400 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz125 qz141) (Complex.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz215)))) Bool.false 78353636895 549755813888 13371052257 85899345920000 Bool.false 90091676315 1099511627776 106726896181 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 37 qz144 rfl)

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz134 149500 1000 0 1 16262126971752659 4503599627370496 1250000001 200000000000000 4862375964554045041 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 37 1 16262126971752659 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz450) Bool.false 68208304206130064654336 18889465931478580854784 1000000000800000 160000000000000000000 16262126971752659 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 76117 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep737 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1402 := nat_lit 1657117129795719745003784555523498843596452172759726373662679234984718512997345

noncomputable def ep1403 := nat_lit 663370470659326163137968814876409282773643519035599353134613402609635607521

noncomputable def ep1404 := nat_lit 4338994644893436613602926648289839927723360267720844770163846717546228124009441

noncomputable def ep1405 := BSN.sin_dyadic_bound_f 2252783813 2147483648 3 2 1048576 320313 ep1402 ep64 ep1403 ep1404 ep66 ep1403 909054 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2252783813) qz19 0 2 ep1402 ep64 ep1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2252783813) qz20 0 2 ep1404 ep66 ep1403 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz735 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 283027531) qz24)

noncomputable def ep1406 := @Enclosure.Real.IsNear.cos_image qz215 qz735 Bool.false 283027531 524288 981 1048576 Bool.false 909054 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 4862375964554045041 9007199254740992 373750000299 400000000000000 283027531 524288 981 1048576 (ep1401 rfl) rfl) (Enclosure.sfrac_false_div 283027531 524288) (BSN.cos_reduce3 qz735 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79262783920625588109312) qz25) 226375608064910080 72057594037927936 Bool.false 909054 1048576 85 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 283027531 524288 226375608064910080 72057594037927936 85 79262783920625588109312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 909054 1048576 79262783920625588109312 75557863725914323419136 2252783813 2147483648 320313 320000 (ep1405 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1407 := nat_lit 920915458984581781074608294764111095012595048652752696191770514281559011935201

noncomputable def ep1408 := nat_lit 2761419636012426690897548946662580466472237858920186889869042316039457764590561

noncomputable def ep1409 := BSN.cos_dyadic_bound_f 2252783813 2147483648 3 2 1048576 320313 ep1407 ep57 ep1403 ep1408 ep60 ep1403 522619 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2252783813) qz15 0 2 ep1407 ep57 ep1403 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2252783813) qz16 0 2 ep1408 ep60 ep1403 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1410 := @Enclosure.Real.IsNear.sin_image qz215 qz735 Bool.false 283027531 524288 981 1048576 Bool.true 522619 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz215 Bool.false 4862375964554045041 9007199254740992 373750000299 400000000000000 283027531 524288 981 1048576 (ep1401 rfl) rfl) (Enclosure.sfrac_false_div 283027531 524288) (BSN.sin_reduce3 qz735 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 79262783920625588109312) qz25) 226375608064910080 72057594037927936 Bool.false 522619 1048576 85 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q3 283027531 524288 226375608064910080 72057594037927936 85 79262783920625588109312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 522619 1048576 79262783920625588109312 75557863725914323419136 2252783813 2147483648 320313 320000 (ep1409 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1411 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz215)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz215))) Bool.false 78353636895 549755813888 13371052257 85899345920000 Bool.false 90091676315 1099511627776 106726896181 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz448 (Real.cos qz215) 172385 1048576 1 1048576 454527 524288 617221 655360000 78353636895 549755813888 13371052257 85899345920000 qz452 (@Enclosure.Real.IsNear.recentre' (Real.cos qz215) Bool.false 909054 1048576 158008576 167772160000 454527 524288 617221 655360000 (ep1406 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz448 (@Neg.neg Real Real.instNeg (Real.sin qz215)) 172385 1048576 1 1048576 522619 1048576 617221 655360000 90091676315 1099511627776 106726896181 687194767360000 qz452 (@Enclosure.Real.IsNear.neg (Real.sin qz215) Bool.true 522619 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz215) Bool.true 522619 1048576 158008576 167772160000 522619 1048576 617221 655360000 (ep1410 rfl rfl) rfl)) rfl)

noncomputable def ep1412 := @ep1346 78353636895 549755813888 13371052257 85899345920000 Bool.false 90091676315 1099511627776 106726896181 687194767360000 Bool.false 17265919920851394756608 62813050757 549755813888 634908885607 68719476736000 Bool.true 730002102373173432418304 1327866088783 1099511627776 1269334015339 137438953472000 (ep1347 (BSN.head_sum_c_succ qz140 36 37 rfl rfl) (ep1399 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1400 ep1411) rfl rfl

noncomputable def ep1413 := @Enclosure.Complex.IsNear.mul qz208 (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.true 18849205433548649 233459029047771136 102907381219799773 1167295145238855680000 Bool.false

noncomputable abbrev qz216 := (Complex.re qz506)

noncomputable abbrev qz217 := (Complex.im qz506)

noncomputable def ep1414 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 3448705755505065553 44824133577172058112 717938981008006689

noncomputable def ep1415 := nat_lit 162220666017972863731868927041361412096

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 169106419453 1099511627776 105611872167 687194767360000 20393701

noncomputable abbrev qz736 := (Real.log (Enclosure.sfrac Bool.false 38 1))

noncomputable abbrev qz218 := (@HMul.hMul Real Real Real qz269 qz455 qz736)

noncomputable abbrev qz219 := (Real.sin (@HMul.hMul Real Real Real qz269 qz455 qz736))

noncomputable abbrev qz508 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 38)))

noncomputable abbrev qz737 := (@Neg.neg Real Real.instNeg qz219)

noncomputable def ep1417 := @Enclosure.Complex.IsNear.of_eq qz208 (Complex.mk (@HMul.hMul Real Real Real qz0 qz508 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz508 qz737)) Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (BSN.cpow_neg_s_mk qz143 149500 1000 38 qz144 rfl)

noncomputable abbrev qz509 := (Real.sqrt (@Nat.cast Real Real.instNatCast 38))

noncomputable abbrev qz510 := (@Nat.cast Real Real.instNatCast 38)

noncomputable abbrev qz738 := (@HDiv.hDiv Real Real Real qz1 qz510 qz14)

noncomputable def ep1418 := @Enclosure.Real.IsNear.inv_image qz509 6463857 1048576 1 1048576 85050 85051 524288 (@Enclosure.Real.IsNear.of_eq qz509 (Real.sqrt qz738) Bool.false 6463857 1048576 1 1048576 (BSN.sqrt_natCast_div_one 38) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz738) Bool.false 6463857 1048576 1 1048576 6463857 1048576 1 1048576 (BSN.sqrt_enclosure 38 1 3231928 3231929 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1419 := BSN.log_dyadic_bound 6 70 3 2 360150000 524288 160000 885888 3888 90099 76 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 6) (BSN.artanhQ 70) 0 2 885888 360150000 3888 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1420 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz736 149500 1000 0 1 16382231437218003 4503599627370496 1250000001 200000000000000 4898287199728182897 9007199254740992 373750000299 400000000000000 qz145 (BSN.isNear_log_sfrac 38 1 16382231437218003 4503599627370496 1250000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz738) Bool.false 68712058846049218854912 18889465931478580854784 1000000000800000 160000000000000000000 16382231437218003 4503599627370496 1250000001 200000000000000 (BSN.log_rat_reduce_isNear 38 1 5 76 64 90099 524288 24973259072661432 36028797018963968 160000 1000000000000000 rfl rfl rfl rfl (ep1419 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1421 := nat_lit 233193929308051669866104409189401616

noncomputable def ep1422 := BSN.cos_dyadic_bound_f 694911198 2147483648 2 1 1048576 320313 ep1421 ep95 ep1421 ep1421 ep96 ep1421 994153 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 694911198) qz15 0 1 ep1421 ep95 ep1421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 694911198) qz16 0 1 ep1421 ep96 ep1421 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz511 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17819865) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep1423 := @Enclosure.Real.IsNear.cos_image qz218 qz511 Bool.false 17819865 32768 981 1048576 Bool.true 994153 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4898287199728182897 9007199254740992 373750000299 400000000000000 17819865 32768 981 1048576 (ep1420 rfl) rfl) (Enclosure.sfrac_false_div 17819865 32768) (BSN.cos_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1528125886804566999040) qz462) 226375608064910080 72057594037927936 Bool.false 994153 1048576 86 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 17819865 32768 226375608064910080 72057594037927936 86 1528125886804566999040 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 994153 1048576 1528125886804566999040 4722366482869645213696 694911198 2147483648 320313 320000 (ep1422 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1424 := BSN.sin_dyadic_bound_f 694911198 2147483648 2 1 1048576 320313 ep1421 ep80 ep1421 ep1421 ep81 ep1421 333421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 694911198) qz19 0 1 ep1421 ep80 ep1421 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 694911198) qz20 0 1 ep1421 ep81 ep1421 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1425 := @Enclosure.Real.IsNear.sin_image qz218 qz511 Bool.false 17819865 32768 981 1048576 Bool.true 333421 1048576 1 160000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4898287199728182897 9007199254740992 373750000299 400000000000000 17819865 32768 981 1048576 (ep1420 rfl) rfl) (Enclosure.sfrac_false_div 17819865 32768) (BSN.sin_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1528125886804566999040) qz462) 226375608064910080 72057594037927936 Bool.false 333421 1048576 86 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 17819865 32768 226375608064910080 72057594037927936 86 1528125886804566999040 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 333421 1048576 1528125886804566999040 4722366482869645213696 694911198 2147483648 320313 320000 (ep1424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1426 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz508 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz508 qz737) Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz508 (Real.cos qz218) 170101 1048576 1 1048576 994153 1048576 617221 655360000 169106419453 1099511627776 105611872167 687194767360000 (@Enclosure.Real.IsNear.recentre' qz508 Bool.false 170101 1048576 1 1048576 170101 1048576 1 1048576 (ep1418 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.true 994153 1048576 158008576 167772160000 994153 1048576 617221 655360000 (ep1423 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz508 qz737 170101 1048576 1 1048576 333421 1048576 617221 655360000 56715245521 1099511627776 105198914667 687194767360000 (@Enclosure.Real.IsNear.recentre' qz508 Bool.false 170101 1048576 1 1048576 170101 1048576 1 1048576 (ep1418 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.true 333421 1048576 617221 655360000 (@Enclosure.Real.IsNear.recentre' qz219 Bool.true 333421 1048576 158008576 167772160000 333421 1048576 617221 655360000 (ep1425 rfl rfl) rfl)) rfl)

noncomputable def ep1427 := @ep1416 40767312 0 1 3448705755505065553 44824133577172058112 717938981008006689 9338361161910845440000 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (ep1417 ep1426))

noncomputable def ep1428 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 20393701 40767312 0 1 Bool.false

noncomputable def ep1429 := @Enclosure.Complex.IsNear.addLitP qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) Bool.false 44625 89402 0 1 Bool.true 11362

noncomputable def ep1430 := @ep1429 44701 0 1 Bool.false 1 912 0 1 Bool.false 299 912 0 1 Bool.false 40787402 20393701 40767312 0 1 Bool.false 3003455 3003455 40767312 0 1

noncomputable abbrev qz220 := (@HDiv.hDiv Complex Complex Complex qz404 qz507 (@HSub.hSub Complex Complex Complex qz397 qz453 (1 : Complex)))

noncomputable def ep1431 := @Enclosure.Complex.IsNear.addLitP qz220 qz99 Bool.true 76000000 89402000000 0 1 Bool.true 22724000000 89402000000 0 1

noncomputable def ep1432 := @Enclosure.Complex.IsNear.of_eq qz220 (Complex.mk (Enclosure.sfrac Bool.true 76000000 89402000000) (Enclosure.sfrac Bool.true 22724000000 89402000000)) Bool.true 76000000 89402000000 0 1 Bool.true 22724000000 89402000000 0 1

noncomputable def ep1433 := @ep1431 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 89250000000 44625 89402 0 1 Bool.true 22724000000 11362 44701 0 1 (ep1432 (BSN.N_div_s_sub_one_mk qz143 149500 1000 38 qz144 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 76000000 89402000000) (Enclosure.sfrac Bool.true 22724000000 89402000000) Bool.true 76000000 89402000000 0 1 Bool.true 22724000000 89402000000 0 1 (Enclosure.Real.IsNear.const Bool.true 76000000 89402000000) (Enclosure.Real.IsNear.const Bool.true 22724000000 89402000000))) qz100 rfl

noncomputable abbrev qz221 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz507 1))

noncomputable def ep1434 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz221)) Bool.false 1 912 0 1

noncomputable def ep1435 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz221) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1436 := @ep1435 0 1 0 1 Bool.false 1 912 0 1 Bool.false 299 912 0 1 Bool.false 1 1 912 0 1 Bool.false 299 299 912 0

noncomputable def ep1437 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1438 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz221 Bool.false 1 912 0 1 Bool.false 299 912 0 1

noncomputable def ep1439 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) 1 912 0 1 0 1 0

noncomputable def ep1440 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 1 24 0 1 1 38 0 1 1

noncomputable def ep1441 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1442 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1443 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz140 Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 (BSN.ascPochhammer_one_eval qz140)

noncomputable def ep1444 := ep1443 (@Enclosure.Complex.IsNear.of_eq qz140 (Complex.mk qz94 qz143) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 (BSN.s_crit_mk qz143 Bool.false 149500 1000 qz144) (@Enclosure.Complex.IsNear.mk qz94 qz143 Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 qz410 qz145))

noncomputable def ep1445 := @ep1442 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1446 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 149500 1000 0 1 0 1 0

noncomputable def ep1447 := @ep1446 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1448 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) 299 24 0 1 0 1 0 1 299

noncomputable def ep1449 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 149500 1000 0 1 299 24 0

noncomputable def ep1450 := @ep1449 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1451 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1452 := @ep1451 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep765) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1453 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 299 24 0 1 (@ep1441 1 24 0 1 (ep1445 rfl) (ep1447 rfl) rfl rfl) (@ep1448 299 24 0 1 (ep1450 rfl) (ep1452 rfl) rfl rfl)

noncomputable def ep1454 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 299 24 0 1 ep1453

noncomputable abbrev qz222 := (@Enclosure.Complex.IsNear.of_eq (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz427 qz507 1)) (Complex.mk (Enclosure.sfrac Bool.false 1 38) qz557) Bool.false 1 38 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 38 1 38 EMLast.d17 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 38) qz557 Bool.false 1 38 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 38) qz560))

noncomputable def ep1455 := @ep1440 912 0 1 ep1454 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 38 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1456 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 299 24 0 1 0 1 0 1 0

noncomputable def ep1457 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 299 24 0 1 ep1453

noncomputable def ep1458 := @ep1456 1 0 1 ep1457 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 38 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1459 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221)) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221)) 0 1 0 1 299 912 0

noncomputable def ep1460 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.im qz221) 1 24 0 1 0 1 0 1 0

noncomputable def ep1461 := @ep1460 1 0 1 ep1454 (@Enclosure.Complex.IsNear.im_isNear qz221 Bool.false 1 38 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1462 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz101)) ↑qz136) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)))) (Complex.re qz221) 299 24 0 1 1 38 0 1 299

noncomputable def ep1463 := @ep1462 912 0 1 ep1457 (@Enclosure.Complex.IsNear.re_isNear qz221 Bool.false 1 38 0 1 Bool.false 0 1 0 1 qz222)

noncomputable def ep1464 := @ep1436 1 (@ep1437 0 1 0 1 (BSN.bern_sum_base qz140 38) qz115) (ep1438 (@ep1439 1 1 1 912 0 1 (ep1455 rfl) (ep1458 rfl) rfl rfl) (@ep1459 1 299 299 912 0 1 (ep1461 rfl) (ep1463 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1465 := ep1430 (ep1433 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1434 Bool.false 299 912 0 1 (BSN.bern_sum_succ qz140 38 0 1 1 rfl rfl) (ep1464 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1466 := @Enclosure.Real.IsNear.mulLit_ff qz217 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 56715245521 1099511627776 105198914667 687194767360000 3003455

noncomputable def ep1467 := @ep1466 40767312 0 1 170341687736275055 44824133577172058112 21064013750078299 1867672232382169088000 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (ep1417 ep1426))

noncomputable def ep1468 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))) Bool.false 20393701 40767312 0 1 Bool.false

noncomputable def ep1469 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1))))))) 507903521038210115 44824133577172058112 21146700367955799

noncomputable def ep1470 := nat_lit 29078770855256521999442034183081295872

noncomputable def ep1471 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 169106419453 1099511627776 105611872167 687194767360000 3003455

noncomputable def ep1472 := @ep1471 40767312 0 1 507903521038210115 44824133577172058112 21146700367955799 1867672232382169088000 (@Enclosure.Complex.IsNear.re_isNear qz208 Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (ep1417 ep1426))

noncomputable def ep1473 := @Enclosure.Real.IsNear.mulLit_ff qz217 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz209 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz82 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz82 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz124 qz210 (@HSub.hSub Nat Nat Nat qz123 (@HMul.hMul Nat Nat Nat qz82 2 k) 1)))))) 56715245521 1099511627776 105198914667 687194767360000 20393701

noncomputable def ep1474 := @ep1473 40767312 0 1 1156633759296863221 44824133577172058112 715131737081104189 9338361161910845440000 (@Enclosure.Complex.IsNear.im_isNear qz208 Bool.true 169106419453 1099511627776 105611872167 687194767360000 Bool.false 56715245521 1099511627776 105198914667 687194767360000 (ep1417 ep1426))

noncomputable abbrev qz739 := (ep1465 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1475 := @ep1413 324365119129326553 22412066788586029056 51304077432555199 583647572619427840000 (@ep1414 9338361161910845440000 170341687736275055 44824133577172058112 21064013750078299 1867672232382169088000 ep1415 18849205433548649 233459029047771136 102907381219799773 1167295145238855680000 (ep1427 (@ep1428 3003455 40767312 0 1 qz739) rfl) (ep1467 (@ep1468 3003455 40767312 0 1 qz739) rfl) rfl rfl) (@ep1469 1867672232382169088000 1156633759296863221 44824133577172058112 715131737081104189 9338361161910845440000 ep1470 324365119129326553 22412066788586029056 51304077432555199 583647572619427840000 (ep1472 (@ep1468 3003455 40767312 0 1 qz739) rfl) (ep1474 (@ep1428 3003455 40767312 0 1 qz739) rfl) rfl rfl)

noncomputable def ep1476 := @ep1343 85025805629704311 9119493322178560000 (@ep1344 137438953472000 (BSN.head_sum_c_eq qz140 38) (ep1345 (BSN.head_sum_c_succ qz140 37 38 rfl rfl) (ep1412 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1475 rfl rfl rfl

noncomputable def ep1477 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz140 1 38) Bool.false 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 Bool.true 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 (@ep1339 1167295145238855680000 Bool.true 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 (BSN.zetaApproximant_eq_folded' qz140 1 38 rfl) (ep1476 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1478 := @Enclosure.Real.IsNear.mulLit_tt (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) (Complex.im (zetaApproximant qz140 1 38)) 262089 262144 275971

noncomputable def ep1479 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181)) Bool.true 1048356 1048576 70648576

noncomputable def ep1480 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) qz490 Bool.false 2650465 16384 435

noncomputable def ep1481 := nat_lit 7916533278414959825109440190739430782179908439859470631296400573654784428089600

noncomputable def ep1482 := nat_lit 20709339416951197480833173185688643374049354149290200217832174009985144631992576

noncomputable def ep1483 := BSN.sin_dyadic_bound_f 3329287014 2147483648 3 2 1048576 320313 ep1481 ep64 ep1335 ep1482 ep66 ep1335 1048356 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3329287014) qz19 0 2 ep1481 ep64 ep1335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3329287014) qz20 0 2 ep1482 ep66 ep1335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1484 := @ep1480 1048576 Bool.true 1048356 1048576 1 160000 (@ep1230 2650465 16384 435 1048576 ep1333 rfl) (Enclosure.sfrac_false_div 2650465 16384) (BSN.sin_reduce2 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3660589784853685207040) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 1048356 1048576 25 1000000000000000 320000 160000 (BSN.sin_reduce_arg_pos_rat_q2 2650465 16384 226375608064910080 72057594037927936 25 3660589784853685207040 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048356 1048576 3660589784853685207040 2361183241434822606848 3329287014 2147483648 320313 320000 (ep1483 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1485 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz140 1 38) Bool.false 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 Bool.true 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 (@ep1339 1167295145238855680000 Bool.true 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 (BSN.zetaApproximant_eq_folded' qz140 1 38 rfl) (ep1476 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMLast.d18 : Enclosure.Real.IsNear (hardyZApproximantEM 1 38 qz143) Bool.true ep1215 ep1216 ep1217 ep1218 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 38 qz143) ep1219 Bool.true ep1215 ep1216 ep1217 ep1218 (@Eq.refl Real ep1219) (@ep1220 Bool.true ep1215 ep1216 ep1217 ep1218 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz400 (Complex.im (@HSub.hSub Complex Complex Complex qz75 qz179 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz180 (@Nat.cast Complex Complex.instNatCast j))))) qz181) (zetaApproximant qz140 1 38)) (@ep1221 122399767421397833351168 ep1222 ep1223 ep1224 ep1216 ep1225 ep1218 ep1226 ep1215 ep1216 ep1217 ep1218 (@ep1227 655360000 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 83993048662020821895 122399767421397833351168 ep1222 ep1223 (@ep1228 167772160000 5367 262144 275971 655360000 (ep1338 rfl rfl) rfl) ep1477 rfl) (@ep1478 655360000 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 ep1224 ep1216 ep1225 ep1218 (@ep1479 167772160000 262089 262144 275971 655360000 (ep1484 rfl rfl) rfl) ep1485 rfl) rfl rfl))

theorem EMLast.d19 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMLast.d20 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMLast.d21 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMLast.d22 : @Eq Nat (Nat.pow 37 (Nat.succ (Nat.mul 2 3))) 94931877133 := @Eq.refl Nat 94931877133

noncomputable abbrev qz740 := (@HAdd.hAdd Complex Complex Complex qz745 qz744 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz512 := qz740

noncomputable abbrev qz223 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz512) (@HAdd.hAdd Real Real Real qz419 (Complex.re qz273) qz290))

noncomputable abbrev qz224 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz225 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz513 := (@HPow.hPow Complex Complex Complex qz548 (@Nat.cast Complex Complex.instNatCast 37) (@HSub.hSub Complex Complex Complex qz660 qz549 qz555))

noncomputable abbrev qz226 := qz513

noncomputable def ep1486 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) 3864439573 231928233984 31833959 231928233984 4794129271971918765 8070450532247928832 714660002443

noncomputable def ep1487 := nat_lit 1143081703948204557232028778496

noncomputable def ep1488 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37)) 26561 1769472 1 1769472 145493 131072 1193 131072 3864439573 231928233984

noncomputable abbrev qz227 := (@HMul.hMul Real Real Real qz269 (2 : Real) Real.pi)

noncomputable abbrev qz741 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz514 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz741 qz227 2))

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz514 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1490 := nat_lit 781950621441006189802102638025

noncomputable def ep1491 := nat_lit 19807040628566084398385987584

noncomputable def ep1492 := nat_lit 26986075409044041160201671

noncomputable def ep1493 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz515 := qz741

noncomputable def ep1494 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz515 qz227 1) qz227 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1490 ep1491 ep1492 ep1493

noncomputable def ep1495 := ep1494 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz515 qz227 1) qz227 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz227) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271)) (@Enclosure.Real.IsNear.of_eq qz227 qz270 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz271) rfl

noncomputable abbrev qz516 := (@HPow.hPow Real Nat Real qz741 qz227 2)

noncomputable def ep1496 := @Enclosure.Real.IsNear.inv_image qz516 ep1490 ep1491 ep1492 ep1493 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz516 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz515 qz227 1) qz227) Bool.false ep1490 ep1491 ep1492 ep1493 (BSN.pow_succ_r qz227 1 2 rfl) ep1495) rfl rfl rfl

noncomputable def ep1497 := ep1489 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz514 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1496 rfl rfl rfl) rfl)

noncomputable def ep1498 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))))) Bool.false 145493 131072 1193 131072

noncomputable def ep1499 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))))) Bool.false 1163944 1048576 9544 1048576

noncomputable def ep1500 := nat_lit 25221855232500146725278921368541248968793

noncomputable def ep1501 := nat_lit 20468392699864213423850387130453432729600

noncomputable def ep1502 := nat_lit 289038613156220345634058198634300204859600894859703821

noncomputable def ep1503 := nat_lit 14306081182103545472759656906106181739610112000000000000

noncomputable def ep1504 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37)))) ep1500 ep1501 ep1502 ep1503 577200 586744

noncomputable def ep1505 := nat_lit 601709731593089604554183038675606987994610095929

noncomputable def ep1506 := nat_lit 488314237682467685470196289061757670045358489600

noncomputable def ep1507 := nat_lit 2584258279214735166345537596773389412328193739186743

noncomputable def ep1508 := nat_lit 128883614253185094349186098253208844500992000000000000

noncomputable def ep1509 := nat_lit 17580752292851330953423835322440157826096369

noncomputable def ep1510 := nat_lit 1098707034785552292307941650388954757602056601600

noncomputable def ep1511 := nat_lit 546486040846185542425881348113495022792847452493837

noncomputable def ep1512 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))) ep1505 ep1506 ep1507 ep1508 ep1509 ep1510 ep1511

noncomputable def ep1513 := nat_lit 3576520295525886368189914226526545434902528000000000000

noncomputable def ep1514 := nat_lit 661111299931907801266462259474221626076936324499569970590741999708418149663548115305825619148800

noncomputable def ep1515 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37)) 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 775699511146609918085077 698794846634166074736640 530892165749899801990617 ep533 ep1505

noncomputable def ep1516 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37)) 4192940769060699592537 1048192269951249112104960 ep660 ep661 4192940769060699592537 1048192269951249112104960 ep660 ep661 ep1509

noncomputable def ep1517 := @ep1486 8070450532247928832 ep1487 133072224439611257663 217902164370694078464 29928067371642025 217902164370694078464 (@ep1488 31833959 231928233984 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz514) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMLast.d19 EMLast.d20 rfl) (ep1497 rfl)) (ep1498 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 37)) (@ep1499 145493 131072 1193 131072 (@ep1504 524288 (@ep1512 ep1513 ep1514 ep1500 ep1501 ep1502 ep1503 (@ep1515 ep1506 ep1507 ep1508 ep802 ep802 rfl) (@ep1516 ep1510 ep1511 ep1513 ep810 ep810 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz228 := (@Norm.norm Complex Complex.instNorm qz512)

noncomputable abbrev qz742 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1518 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz228 qz742) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) Bool.false 4794129271971918765 8070450532247928832 714660002443 8070450532247928832 (BSN.zrb_shape_eq qz228 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) qz12 3)

noncomputable def ep1519 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz228 qz742) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) 153691665 3670016 1 3670016 31193163741 2199023255552 4447 2199023255552

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ff qz228 qz742 153691665 1048576 1 1048576 2 7 0 1 153691665 3670016

noncomputable abbrev qz517 := (Complex.re qz740)

noncomputable abbrev qz518 := (Complex.im qz740)

noncomputable abbrev qz229 := (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz269 qz517 qz517) (@HMul.hMul Real Real Real qz269 qz518 qz518))

noncomputable abbrev qz230 := qz512

noncomputable def ep1521 := @Enclosure.Real.IsNear.of_eq qz228 (Real.sqrt qz229) Bool.false 153691665 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz230)

noncomputable def ep1522 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz229) Bool.false 153691665 1048576 1 1048576 153691665

noncomputable def ep1523 := @Enclosure.Real.IsNear.sqrt_image qz229 214832909 10000 0 1 76845832 76845833 524288

noncomputable abbrev qz231 := (@HMul.hMul Real Real Real qz269 qz517 qz517)

noncomputable abbrev qz232 := (@HMul.hMul Real Real Real qz269 qz518 qz518)

noncomputable def ep1524 := @Enclosure.Real.IsNear.addLit_ff qz231 qz232 49 4 0 1 214710409 10000 0 1

noncomputable abbrev qz233 := qz517

noncomputable def ep1525 := @Enclosure.Real.IsNear.mulLit_ff qz233 qz233 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1526 := @Enclosure.Complex.IsNear.of_eq qz230 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz12) Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 146530 1000 3 qz13)

noncomputable abbrev qz519 := (ep1526 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1527 := @ep1525 0 1 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz519)

noncomputable def ep1528 := ep1527 (@Enclosure.Complex.IsNear.re_isNear qz230 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz519)

noncomputable abbrev qz234 := qz518

noncomputable def ep1529 := @Enclosure.Real.IsNear.mulLit_ff qz234 qz234 146530 1000 0 1 146530 1000 0 1 214710409 10000

noncomputable def ep1530 := @ep1529 0 1 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz519)

noncomputable def ep1531 := ep1530 (@Enclosure.Complex.IsNear.im_isNear qz230 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz519)

noncomputable def ep1532 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 31193163741 2199023255552

noncomputable def ep1533 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))))) Bool.false 31193163741 2199023255552

noncomputable def ep1534 := nat_lit 243917796018237683148756586980413930810730577638736988392998113

noncomputable def ep1535 := nat_lit 1212227918067744116474864347648193787823416688446013440000000000000

noncomputable def ep1536 := nat_lit 159009952859799301790322858299978225727481724403677691736452096586684543237

noncomputable def ep1537 := nat_lit 2772087015418216525859369884993411208643215617844590805872803840000000000000000000000

noncomputable def ep1538 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) ep1534 ep1535 ep1536 ep1537

noncomputable def ep1539 := nat_lit 2323167872585496354966765655804967263793228833172690142312759841

noncomputable def ep1540 := nat_lit 12122279180677441164748643476481937878234166884460134400000000000000

noncomputable def ep1541 := nat_lit 298848687508279277497997886437807153403062053766600660704603052068125120737

noncomputable def ep1542 := nat_lit 5544174030836433051718739769986822417286431235689181611745607680000000000000000000000

noncomputable def ep1543 := nat_lit 116010087596880476520800213999172044314076943214679741617221289

noncomputable def ep1544 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226))) ep1539 ep1540 ep1541 ep1542 ep1543

noncomputable def ep1545 := nat_lit 6390406070439775360882610054049766017300465013584907589433713701747988579

noncomputable def ep1546 := nat_lit 1848058010278811017239579923328940805762143745229727203915202560000000000000000000000

noncomputable def ep1547 := nat_lit 29568396204686095225631257853283933522688142054189065732016508188662304386821773970984130748082104104511090429263872000000000000000

noncomputable def ep1548 := nat_lit 48199251784498650606921597720721

noncomputable def ep1549 := nat_lit 3481706360490132023153786880000000

noncomputable def ep1550 := nat_lit 7939906188069877387527140600711281

noncomputable def ep1551 := nat_lit 4078298921426591451653702733004800000000000

noncomputable def ep1552 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1548 ep1549 ep1550 ep1551 ep1548 ep1549 ep1550

noncomputable def ep1553 := nat_lit 10770797909016790967709908225267

noncomputable def ep1554 := nat_lit 2279324398397769944990561122075031

noncomputable def ep1555 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1548 ep1549 ep1550 ep1551 Bool.false ep1553 ep1549 ep1554

noncomputable def ep1556 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226 Bool.false ep1548 ep1549 ep1550 ep1551 Bool.false ep1553 ep1549 ep1554 ep1551

noncomputable def ep1557 := nat_lit 2506560562847007931006834567

noncomputable def ep1558 := nat_lit 23211375736600880154358579200000

noncomputable def ep1559 := nat_lit 417222648554800669526238634831

noncomputable def ep1560 := nat_lit 27188659476177276344358018220032000000000

noncomputable def ep1561 := nat_lit 47823267700071599417270572535671

noncomputable def ep1562 := nat_lit 7877322790786657287098204805486631

noncomputable abbrev qz235 := (Complex.re qz513)

noncomputable abbrev qz236 := (Complex.im qz513)

noncomputable def ep1563 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) ep1557 ep1558 ep1559 ep1560 ep1561 ep1549 ep1562

noncomputable def ep1564 := nat_lit 1118770943393028653474479220124059665465718344444451959603200000

noncomputable def ep1565 := nat_lit 4835703278458516698824704

noncomputable def ep1566 := nat_lit 5664304057536932571741253795840000

noncomputable def ep1567 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 644118727 4800000 0 1 3891457363025881921 ep1565 647741838679378544953 ep1566 ep1557

noncomputable def ep1568 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 644118727 4800000 0 1 0 1 0 1 644118727

noncomputable def ep1569 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1932356181 20000 0 1 644118727 4800000 0

noncomputable def ep1570 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMLast.d21 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz21)

noncomputable abbrev qz520 := (@HAdd.hAdd Complex Complex Complex qz547 qz546 qz556)

noncomputable abbrev qz237 := qz520

noncomputable def ep1571 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1

noncomputable abbrev qz238 := (Complex.re qz520)

noncomputable abbrev qz239 := (Complex.im qz520)

noncomputable def ep1572 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) 214702909 4000 0 1 214710409 5000 0 1

noncomputable def ep1573 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 214702909 10000 0 1 5 2 0 1 214702909 4000

noncomputable abbrev qz521 := (@HAdd.hAdd Complex Complex Complex qz547 qz546 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz240 := qz521

noncomputable def ep1574 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1

noncomputable abbrev qz241 := (Complex.re qz521)

noncomputable abbrev qz242 := (Complex.im qz521)

noncomputable def ep1575 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) 3 4 0 1 214710409 10000 0 1

noncomputable def ep1576 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1577 := @ep1576 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep1578 := @Enclosure.Complex.IsNear.of_eq qz240 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz12) Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 146530 1000 1 qz13)

noncomputable abbrev qz522 := (ep1578 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1579 := ep1577 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz522)

noncomputable def ep1580 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 146530 1000 0 1 146530 1000 0 1 214710409 10000

noncomputable def ep1581 := @ep1580 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep1582 := ep1581 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz522)

noncomputable def ep1583 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz240 Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 (@ep1575 858811636 214702909 10000 0 1 (ep1579 rfl) (ep1582 rfl) rfl rfl)

noncomputable def ep1584 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241) 14653 200 0 1 43959 200 0 1

noncomputable def ep1585 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz242 1 2 0 1 146530 1000 0 1 14653 200

noncomputable def ep1586 := @ep1585 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep1587 := ep1586 (@Enclosure.Complex.IsNear.im_isNear qz240 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz522)

noncomputable def ep1588 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz241 146530 1000 0 1 3 2 0 1 43959 200

noncomputable def ep1589 := @ep1588 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep767)

noncomputable def ep1590 := ep1589 (@Enclosure.Complex.IsNear.re_isNear qz240 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz522)

noncomputable abbrev qz243 := (ep1574 (BSN.ascPochhammer_succ_eval_c 1 2 qz273 rfl) (ep1583 (@ep1584 11722400 14653 50 0 1 (ep1587 rfl) (ep1590 rfl) rfl rfl)))

noncomputable def ep1591 := @ep1573 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz243)

noncomputable def ep1592 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz12) Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 146530 1000 2 qz13)

noncomputable abbrev qz523 := (ep1592 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1593 := ep1591 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz523)

noncomputable def ep1594 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 14653 50 0 1 146530 1000 0 1 214710409 5000

noncomputable def ep1595 := @ep1594 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz243)

noncomputable def ep1596 := ep1595 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz523)

noncomputable def ep1597 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz237 Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 (@ep1572 1932356181000 1932356181 20000 0 1 (ep1593 rfl) (ep1596 rfl) rfl rfl)

noncomputable def ep1598 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238) 3146041725577 1000000 0 1 14653 20 0 1

noncomputable def ep1599 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz239 214702909 10000 0 1 146530 1000 0 1 3146041725577 1000000

noncomputable def ep1600 := @ep1599 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz243)

noncomputable def ep1601 := ep1600 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz523)

noncomputable def ep1602 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz238 14653 50 0 1 5 2 0 1 14653 20

noncomputable def ep1603 := @ep1602 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz243)

noncomputable def ep1604 := ep1603 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz523)

noncomputable abbrev qz244 := (ep1571 (BSN.ascPochhammer_succ_eval_c 2 3 qz273 rfl) (ep1597 (@ep1598 62906181511540 3145309075577 1000000 0 1 (ep1601 rfl) (ep1604 rfl) rfl rfl)))

noncomputable def ep1605 := @ep1569 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz244)

noncomputable def ep1606 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3145309075577 1000000 0 1 0 1 0

noncomputable def ep1607 := @ep1606 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz244)

noncomputable def ep1608 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 3145309075577 720000000 0 1 0 1 0 1 3145309075577

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3145309075577 1000000 0 1 3145309075577 720000000 0

noncomputable def ep1610 := @ep1609 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz244)

noncomputable def ep1611 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1932356181 20000 0 1 0 1 0

noncomputable def ep1612 := @ep1611 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz244)

noncomputable def ep1613 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 (@ep1568 644118727 4800000 0 1 (ep1605 rfl) (ep1607 rfl) rfl rfl) (@ep1608 3145309075577 720000000 0 1 (ep1610 rfl) (ep1612 rfl) rfl rfl)

noncomputable def ep1614 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 ep1613

noncomputable def ep1615 := @Enclosure.Complex.IsNear.re_isNear qz226 Bool.false 3891457363025881921 ep1565 647741838679378544953 ep1566 Bool.true 15204632216087866223 ep1565 2504467001972319628703 ep1566

noncomputable abbrev qz524 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 94931877133)))

noncomputable def ep1616 := @Enclosure.Complex.IsNear.of_eq qz226 (Complex.mk (@HMul.hMul Real Real Real qz0 qz524 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz524 qz687)) Bool.false 3891457363025881921 ep1565 647741838679378544953 ep1566 Bool.true 15204632216087866223 ep1565 2504467001972319628703

noncomputable abbrev qz525 := (Real.sqrt (@Nat.cast Real Real.instNatCast 94931877133))

noncomputable abbrev qz526 := (@Nat.cast Real Real.instNatCast 94931877133)

noncomputable def ep1617 := @Enclosure.Real.IsNear.inv_image qz525 677541430085473957 2199023255552 1 2199023255552 3568566 3568567 1099511627776 (@Enclosure.Real.IsNear.of_eq qz525 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz526 qz14)) Bool.false 677541430085473957 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 94931877133) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz526 qz14)) Bool.false 677541430085473957 2199023255552 1 2199023255552 677541430085473957 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 94931877133 1 338770715042736978 338770715042736979 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1618 := nat_lit 143043195604289387581424009216

noncomputable def ep1619 := nat_lit 39614081257132168796771975168

noncomputable def ep1620 := nat_lit 299865760000000000000000000

noncomputable def ep1621 := BSN.log_dyadic_bound 5 69 5 4 485539463835065745 1099511627776 299865760000 852543171681000 41015625 159629307967 74 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 69) 0 4 852543171681000 485539463835065745 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1622 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz134 146530 1000 0 1 16262128565846227 4503599627370496 1251874161 374832200000000000000 238288969875344764231 450359962737049600 18343712081133 37483220000000000000000 qz18 (BSN.isNear_log_sfrac 37 1 16262128565846227 4503599627370496 1251874161 374832200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz450) Bool.false ep1618 ep1619 1001499328800000 ep1620 16262128565846227 4503599627370496 1251874161 374832200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 159629307967 1099511627776 24973259072661432 36028797018963968 299865760000 1000000000000000 rfl rfl rfl rfl (ep1621 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1623 := nat_lit 13074983417274546722749546496

noncomputable def ep1624 := nat_lit 9903520314283042199192993792

noncomputable def ep1625 := nat_lit 75989890405053452823187494706919790316820510111541159662016680614296795544180456132539287722392635749826833430166470240197284047259279660254292556347894153852684229442747053629386004159533574710475130773232697255028219168050698245869760652935995094224471081353216

noncomputable def ep1626 := nat_lit 599205769308871494669005633404748773453705986173265619753359186119574540201718521016582654337481038554791270797803930120647421245947038870502085995962344054183037643944802456687515051311778021064186337694386596224481457310393291043136983312363285164951074766848000

noncomputable def ep1627 := nat_lit 2439951491001793962520946763958614168776664871540358260622396292511440484019442282428452580872827311737272296330374288042981992442822648642916868709732522910604082861374721585496044790407011309830495212980616447249538980627727505688694014784401504731136

noncomputable def ep1628 := nat_lit 774163808537946698102025004422919796013783879702612343768063397689358483108794689502990285206873369366889737781223638823574820867762114235594472394240007467078132509556932919666970947181664507079841871858839467026465978480034742108704408344065768395775404656295936

noncomputable def ep1629 := nat_lit 91678482704257338684357861910926562338417015884509639822263955476294904650862933715537146113634598898883064432064001308459055450629896947186819157382238640290004759523554775873189802850702037222820509667241149222345662968490173529599958446791582630237514439327744000

noncomputable def ep1630 := BSN.cos_dyadic_bound_f 5945814071890048 4503599627370496 5 4 2199023255552 600317195313 ep1625 ep1626 ep1627 ep1628 ep1629 ep1627 545240976037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 5945814071890048) (BSN.cosEvenQ 4503599627370496) 0 4 ep1625 ep1626 ep1627 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 5945814071890048) (BSN.cosOddQ 4503599627370496) 0 4 ep1628 ep1629 ep1627 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz527 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36360011272483) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1631 := @Enclosure.Real.IsNear.cos_image qz132 qz527 Bool.false 36360011272483 68719476736 539 1099511627776 Bool.false 545240976037 2199023255552 1 299865760000 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 238288969875344764231 450359962737049600 18343712081133 37483220000000000000000 36360011272483 68719476736 539 1099511627776 (ep1622 rfl) rfl) (Enclosure.sfrac_false_div 36360011272483 68719476736) (BSN.cos_reduce0 qz527 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1623) (@Nat.cast Real Real.instNatCast ep1624)) 226375608064910080 72057594037927936 Bool.false 545240976037 2199023255552 84 1000000000000000 599731520000 299865760000 (BSN.sin_reduce_arg_pos_rat_q0 36360011272483 68719476736 226375608064910080 72057594037927936 84 ep1623 ep1624 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 545240976037 2199023255552 ep1623 ep1624 5945814071890048 4503599627370496 600317195313 599731520000 (ep1630 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1632 := nat_lit 10986484475174838424430408912619986187134465237768626971456496837544342795734448276688748564990981378427139414254438973457042499767052381441225439946678134536158685300844331012293595942904079056896

noncomputable def ep1633 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1634 := nat_lit 1952252079571464114815841464646947247459006380781935612524707335170150345903729711351632461791977115693303396972638749468720800233302397216724725813743460921082784185259965358279263095095296

noncomputable def ep1635 := nat_lit 54898331928257910871168104534569748982667322231290206527982420214678140039649444553909806066967714643650459739751299149041666811887720452271620198809546756956543589385329710422225852467161759481856

noncomputable def ep1636 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1637 := BSN.sin_dyadic_bound_f 5945814071890048 4503599627370496 4 3 2199023255552 600317195313 ep1632 ep1633 ep1634 ep1635 ep1636 ep1634 2130355734731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5945814071890048) (BSN.sinEvenQ 4503599627370496) 0 3 ep1632 ep1633 ep1634 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5945814071890048) (BSN.sinOddQ 4503599627370496) 0 3 ep1635 ep1636 ep1634 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1638 := @Enclosure.Real.IsNear.sin_image qz132 qz527 Bool.false 36360011272483 68719476736 539 1099511627776 Bool.false 2130355734731 2199023255552 1 299865760000 (@Enclosure.Real.IsNear.recentre' qz132 Bool.false 238288969875344764231 450359962737049600 18343712081133 37483220000000000000000 36360011272483 68719476736 539 1099511627776 (ep1622 rfl) rfl) (Enclosure.sfrac_false_div 36360011272483 68719476736) (BSN.sin_reduce0 qz527 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1623) (@Nat.cast Real Real.instNatCast ep1624)) 226375608064910080 72057594037927936 Bool.false 2130355734731 2199023255552 84 1000000000000000 599731520000 299865760000 (BSN.sin_reduce_arg_pos_rat_q0 36360011272483 68719476736 226375608064910080 72057594037927936 84 ep1623 ep1624 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2130355734731 2199023255552 ep1623 ep1624 5945814071890048 4503599627370496 600317195313 599731520000 (ep1637 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1639 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz524 (Real.cos qz132)) (@HMul.hMul Real Real Real qz0 qz524 qz687) Bool.false 3891457363025881921 ep1565 647741838679378544953 ep1566 Bool.true 15204632216087866223 ep1565 2504467001972319628703 ep1566 (@Enclosure.Real.IsNear.mulLit_ff qz524 (Real.cos qz132) 7137133 2199023255552 1 2199023255552 545240976037 2199023255552 635652954171 1287913632390184960000 3891457363025881921 ep1565 647741838679378544953 ep1566 (@Enclosure.Real.IsNear.recentre' qz524 Bool.false 7137133 2199023255552 1 2199023255552 7137133 2199023255552 1 2199023255552 (ep1617 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz132) Bool.false 545240976037 2199023255552 162727156267776 329705889891887349760000 545240976037 2199023255552 635652954171 1287913632390184960000 (ep1631 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz524 qz687 7137133 2199023255552 1 2199023255552 2130355734731 2199023255552 635652954171 1287913632390184960000 15204632216087866223 ep1565 2504467001972319628703 ep1566 (@Enclosure.Real.IsNear.recentre' qz524 Bool.false 7137133 2199023255552 1 2199023255552 7137133 2199023255552 1 2199023255552 (ep1617 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz133 Bool.false 2130355734731 2199023255552 635652954171 1287913632390184960000 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2130355734731 2199023255552 162727156267776 329705889891887349760000 2130355734731 2199023255552 635652954171 1287913632390184960000 (ep1638 rfl rfl) rfl)) rfl)

noncomputable def ep1640 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 3145309075577 720000000 0 1 15204632216087866223 ep1565 2504467001972319628703 ep1566 ep1561

noncomputable def ep1641 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 ep1613

noncomputable def ep1642 := @Enclosure.Complex.IsNear.im_isNear qz226 Bool.false 3891457363025881921 ep1565 647741838679378544953 ep1566 Bool.true 15204632216087866223 ep1565 2504467001972319628703 ep1566

noncomputable def ep1643 := nat_lit 9793588347529705311705058121

noncomputable def ep1644 := nat_lit 1613174097123917008477289021081

noncomputable def ep1645 := nat_lit 12239836161146246764465666943417

noncomputable def ep1646 := nat_lit 2037348283829182393718967768912881

noncomputable def ep1647 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235) ep1643 ep1558 ep1644 ep1560 ep1645 ep1549 ep1646

noncomputable def ep1648 := nat_lit 250005037249183836194620794709589518295004946374607660646400000

noncomputable def ep1649 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz236 644118727 4800000 0 1 15204632216087866223 ep1565 2504467001972319628703 ep1566 ep1643

noncomputable def ep1650 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz235 3145309075577 720000000 0 1 3891457363025881921 ep1565 647741838679378544953 ep1566 ep1645

noncomputable abbrev qz528 := (@ep1616 ep1566 (BSN.cpow_neg_s_sub_mk qz12 146530 1000 37 3 94931877133 qz13 rfl EMLast.d22) ep1639)

noncomputable def ep1651 := ep1556 (@ep1563 ep1551 ep1564 ep1548 ep1549 ep1550 ep1551 (@ep1567 ep1558 ep1559 ep1560 ep1614 (ep1615 qz528) rfl) (@ep1640 ep1549 ep1562 ep1551 ep1641 (ep1642 qz528) rfl) rfl rfl) (@ep1647 ep1551 ep1648 ep1553 ep1549 ep1554 ep1551 (@ep1649 ep1558 ep1644 ep1560 ep1614 (ep1642 qz528) rfl) (@ep1650 ep1549 ep1646 ep1551 ep1641 (ep1615 qz528) rfl) rfl rfl)

noncomputable def ep1652 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) ep1553 ep1549 ep1554 ep1551 ep1553 ep1549 ep1554

noncomputable def ep1653 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226) Bool.false ep1548 ep1549 ep1550 ep1551 Bool.false ep1553 ep1549 ep1554

noncomputable def ep1654 := @ep1519 4794129271971918765 8070450532247928832 714660002443 8070450532247928832 (@ep1520 1 3670016 (ep1521 (@ep1522 1048576 1 1048576 (ep1523 (@ep1524 859331636 214832909 10000 0 1 (ep1528 rfl) (ep1531 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1532 4447 2199023255552 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)) (@ep1533 4447 2199023255552 31193163741 2199023255552 4447 2199023255552 (@ep1538 15596579647 15596584094 1099511627776 (@ep1544 ep1540 ep1545 ep1546 ep1547 ep1534 ep1535 ep1536 ep1537 (@ep1552 ep1551 ep1539 ep1540 ep1541 ep1542 (@ep1555 ep1551 ep1651) (@ep1555 ep1551 ep1651) rfl) (@ep1652 ep1551 ep1543 ep1540 ep1545 ep1546 (@ep1653 ep1551 ep1651) (@ep1653 ep1551 ep1651) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMLast.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 133072224439611257663 217902164370694078464 29928067371642025 217902164370694078464 := ep1517 (ep1518 ep1654) rfl rfl

theorem EMLast.d24 : @Eq Nat (Nat.pow 38 (Nat.succ (Nat.mul 2 3))) 114415582592 := @Eq.refl Nat 114415582592

noncomputable abbrev qz743 := (@HAdd.hAdd Complex Complex Complex qz745 qz751 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz529 := qz743

noncomputable abbrev qz245 := (@HDiv.hDiv Real Real Real qz272 (@Norm.norm Complex Complex.instNorm qz529) (@HAdd.hAdd Real Real Real qz419 (Complex.re qz453) qz290))

noncomputable abbrev qz530 := (@HPow.hPow Complex Complex Complex qz548 (@Nat.cast Complex Complex.instNatCast 38) (@HSub.hSub Complex Complex Complex qz660 qz690 qz555))

noncomputable abbrev qz246 := qz530

noncomputable def ep1655 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) 33244517869 1855425871872 270191879 1855425871872 337983361503839093 576460752303423488 55289953807

noncomputable def ep1656 := nat_lit 646267232977218355261412999168

noncomputable def ep1657 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38)) 26561 1769472 1 1769472 1251629 1048576 10125 1048576 33244517869 1855425871872

noncomputable def ep1658 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 38)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 38)) (Complex.im (zetaApproximant qz140 1 38))))) Bool.false 1251629 1048576 10125 1048576

noncomputable def ep1659 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 38)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 38)) (Complex.im (zetaApproximant qz140 1 38))))) Bool.false 1251629 1048576 10125 1048576

noncomputable def ep1660 := nat_lit 16011281100236749962953684429535925

noncomputable def ep1661 := nat_lit 11236901584663450071137214252711936

noncomputable def ep1662 := nat_lit 31406202070923193423136776814358914493353

noncomputable def ep1663 := nat_lit 1362577956098201176296399235868262400000000

noncomputable def ep1664 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 38)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 38)) (Complex.im (zetaApproximant qz140 1 38)))) ep1660 ep1661 ep1662 ep1663 620752 630877

noncomputable def ep1665 := nat_lit 244919576237764545179569220224225

noncomputable def ep1666 := nat_lit 218012472975712188207423877738921984

noncomputable def ep1667 := nat_lit 51078976271010354291422701661034538131

noncomputable def ep1668 := nat_lit 71714629268326377699810486098329600000000

noncomputable def ep1669 := nat_lit 715155981758031150581898920201288769025

noncomputable def ep1670 := nat_lit 502300737736040881629904614310476251136

noncomputable def ep1671 := nat_lit 475557836277718698306246023168738410451

noncomputable def ep1672 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz140 1 38)) (Complex.re (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz140 1 38)) (Complex.im (zetaApproximant qz140 1 38))) ep1665 ep1666 ep1667 ep1668 ep1669 ep1670 ep1671

noncomputable def ep1673 := nat_lit 21290280564034393379631238060441600000000

noncomputable def ep1674 := nat_lit 156035947430271912501219743747245157110717098397124073363825768661201715200

noncomputable def ep1675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz140 1 38)) (Complex.re (zetaApproximant qz140 1 38)) 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 15649906588787185 466918058095542272 10887710977516832433 1167295145238855680000 ep1665

noncomputable def ep1676 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz140 1 38)) (Complex.im (zetaApproximant qz140 1 38)) 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 26742400448688804095 22412066788586029056 85025805629704311 9119493322178560000 ep1669

noncomputable def ep1677 := @ep1655 576460752303423488 ep1656 9404425989155691863 15564440312192434176 2268026586467221 15564440312192434176 (@ep1657 270191879 1855425871872 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz514) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMLast.d19 EMLast.d20 rfl) (ep1497 rfl)) (ep1658 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz140 1 38)) (@ep1659 1251629 1048576 10125 1048576 (@ep1664 524288 (@ep1672 ep1673 ep1674 ep1660 ep1661 ep1662 ep1663 (@ep1675 ep1666 ep1667 ep1668 ep1477 ep1477 rfl) (@ep1676 ep1670 ep1671 ep1673 ep1485 ep1485 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz247 := (@Norm.norm Complex Complex.instNorm qz529)

noncomputable def ep1678 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz247 qz742) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) Bool.false 337983361503839093 576460752303423488 55289953807 576460752303423488 (BSN.zrb_shape_eq qz247 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) qz143 3)

noncomputable def ep1679 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz247 qz742) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) 156805067 3670016 1 3670016 15088055353 1099511627776 593 274877906944

noncomputable def ep1680 := @Enclosure.Real.IsNear.mulLit_ff qz247 qz742 156805067 1048576 1 1048576 2 7 0 1 156805067 3670016

noncomputable abbrev qz531 := (Complex.re qz743)

noncomputable abbrev qz532 := (Complex.im qz743)

noncomputable abbrev qz248 := (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz269 qz531 qz531) (@HMul.hMul Real Real Real qz269 qz532 qz532))

noncomputable abbrev qz249 := qz529

noncomputable def ep1681 := @Enclosure.Real.IsNear.of_eq qz247 (Real.sqrt qz248) Bool.false 156805067 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz249)

noncomputable def ep1682 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz248) Bool.false 156805067 1048576 1 1048576 156805067

noncomputable def ep1683 := @Enclosure.Real.IsNear.sqrt_image qz248 44725 2 0 1 78402533 78402534 524288

noncomputable abbrev qz250 := (@HMul.hMul Real Real Real qz269 qz531 qz531)

noncomputable abbrev qz251 := (@HMul.hMul Real Real Real qz269 qz532 qz532)

noncomputable def ep1684 := @Enclosure.Real.IsNear.addLit_ff qz250 qz251 49 4 0 1 89401 4 0 1

noncomputable abbrev qz252 := qz531

noncomputable def ep1685 := @Enclosure.Real.IsNear.mulLit_ff qz252 qz252 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1686 := @Enclosure.Complex.IsNear.of_eq qz249 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz143) Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 149500 1000 3 qz144)

noncomputable abbrev qz533 := (ep1686 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz143 Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz145))

noncomputable def ep1687 := @ep1685 0 1 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 qz533)

noncomputable def ep1688 := ep1687 (@Enclosure.Complex.IsNear.re_isNear qz249 Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 qz533)

noncomputable abbrev qz253 := qz532

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_ff qz253 qz253 149500 1000 0 1 149500 1000 0 1 89401 4

noncomputable def ep1690 := @ep1689 0 1 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 qz533)

noncomputable def ep1691 := ep1690 (@Enclosure.Complex.IsNear.im_isNear qz249 Bool.false 7 2 0 1 Bool.false 149500 1000 0 1 qz533)

noncomputable def ep1692 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 15088055353 1099511627776

noncomputable def ep1693 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))))) Bool.false 30176110706 2199023255552

noncomputable def ep1694 := nat_lit 9018122397107760244107601885607406345935551191645

noncomputable def ep1695 := nat_lit 47890485652059026823698344598447161988085597568237568

noncomputable def ep1696 := nat_lit 4231695409146537263869945876618527128494547879983772238065189

noncomputable def ep1697 := nat_lit 71485934953346233023637865764605691962790192723035852720046080000000000

noncomputable def ep1698 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) ep1694 ep1695 ep1696 ep1697

noncomputable def ep1699 := nat_lit 2163864440514817177260959413399411751480740923489

noncomputable def ep1700 := nat_lit 95780971304118053647396689196894323976171195136475136

noncomputable def ep1701 := nat_lit 1002360169707393327415252384240774150397757783941450129623939

noncomputable def ep1702 := nat_lit 142971869906692466047275731529211383925580385446071705440092160000000000

noncomputable def ep1703 := nat_lit 15872380353700703310954244357815400940390361459801

noncomputable def ep1704 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246))) ep1699 ep1700 ep1701 ep1702 ep1703

noncomputable def ep1705 := nat_lit 829003405398409022258293263221808900732370886225121594056271

noncomputable def ep1706 := nat_lit 15885763322965829560808414614356820436175598382896856160010240000000000

noncomputable def ep1707 := nat_lit 1727529045068805397556461192747282367418632573831396911420604919084949872900806309471182123779426877440

noncomputable def ep1708 := nat_lit 1471007967522547845584817

noncomputable def ep1709 := nat_lit 309485009821345068724781056

noncomputable def ep1710 := nat_lit 278864394141295144407312367

noncomputable def ep1711 := nat_lit 378116212171195412824520549990400000

noncomputable def ep1712 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1708 ep1709 ep1710 ep1711 ep1708 ep1709 ep1710

noncomputable def ep1713 := nat_lit 3984015606608576440724901

noncomputable def ep1714 := nat_lit 255470541298683023538012039

noncomputable def ep1715 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.true ep1708 ep1709 ep1710 ep1711 Bool.true ep1713 ep1709 ep1714

noncomputable def ep1716 := nat_lit 126038737390398470941506849996800000

noncomputable def ep1717 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246 Bool.true ep1708 ep1709 ep1710 ep1711 Bool.true ep1713 ep1709 ep1714 ep1716

noncomputable def ep1718 := nat_lit 38685626227668133590597632

noncomputable def ep1719 := nat_lit 3938710543449952216922089062400000

noncomputable def ep1720 := nat_lit 1349835566376247757678313

noncomputable def ep1721 := nat_lit 256021715752241335998485839

noncomputable abbrev qz254 := (Complex.re qz530)

noncomputable abbrev qz255 := (Complex.im qz530)

noncomputable def ep1722 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) 15146550143287510988313 ep1718 237944566552643837591943 ep1719 ep1720 ep1709 ep1721

noncomputable def ep1723 := nat_lit 56906864409499070984156907419859243745755575353344

noncomputable def ep1724 := nat_lit 12308470448281100677881528320000

noncomputable def ep1725 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 134099 960 0 1 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 15146550143287510988313

noncomputable def ep1726 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) 134099 960 0 1 0 1 0 1 134099

noncomputable def ep1727 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 402297 4 0 1 134099 960 0

noncomputable abbrev qz534 := (@HAdd.hAdd Complex Complex Complex qz547 qz689 qz556)

noncomputable abbrev qz256 := qz534

noncomputable def ep1728 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) qz256) Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1

noncomputable abbrev qz257 := (Complex.re qz534)

noncomputable abbrev qz258 := (Complex.im qz534)

noncomputable def ep1729 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) 223495 4 0 1 89401 2 0 1

noncomputable def ep1730 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 44699 2 0 1 5 2 0 1 223495 4

noncomputable abbrev qz535 := (@HAdd.hAdd Complex Complex Complex qz547 qz689 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz259 := qz535

noncomputable def ep1731 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz74 (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz259) Bool.true 44699 2 0 1 Bool.false 299 1 0 1

noncomputable abbrev qz260 := (Complex.re qz535)

noncomputable abbrev qz261 := (Complex.im qz535)

noncomputable def ep1732 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) 3 4 0 1 89401 4 0 1

noncomputable def ep1733 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1734 := @ep1733 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1735 := @Enclosure.Complex.IsNear.of_eq qz259 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz143) Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 149500 1000 1 qz144)

noncomputable abbrev qz536 := (ep1735 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz143 Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz145))

noncomputable def ep1736 := ep1734 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 qz536)

noncomputable def ep1737 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 149500 1000 0 1 149500 1000 0 1 89401 4

noncomputable def ep1738 := @ep1737 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1739 := ep1738 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 qz536)

noncomputable def ep1740 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) qz259 Bool.true 44699 2 0 1 Bool.false 299 1 0 1 (@ep1732 357592 44699 2 0 1 (ep1736 rfl) (ep1739 rfl) rfl rfl)

noncomputable def ep1741 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz261) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz260) 299 4 0 1 897 4 0 1

noncomputable def ep1742 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz261 1 2 0 1 149500 1000 0 1 299 4

noncomputable def ep1743 := @ep1742 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1744 := ep1743 (@Enclosure.Complex.IsNear.im_isNear qz259 Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 qz536)

noncomputable def ep1745 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1))) qz260 149500 1000 0 1 3 2 0 1 897 4

noncomputable def ep1746 := @ep1745 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 149500 1000 0 1 ep1444)

noncomputable def ep1747 := ep1746 (@Enclosure.Complex.IsNear.re_isNear qz259 Bool.false 3 2 0 1 Bool.false 149500 1000 0 1 qz536)

noncomputable abbrev qz262 := (ep1731 (BSN.ascPochhammer_succ_eval_c 1 2 qz453 rfl) (ep1740 (@ep1741 4784 299 1 0 1 (ep1744 rfl) (ep1747 rfl) rfl rfl)))

noncomputable def ep1748 := @ep1730 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 44699 2 0 1 Bool.false 299 1 0 1 qz262)

noncomputable def ep1749 := @Enclosure.Complex.IsNear.of_eq qz256 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz143) Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 (BSN.s_add_nat_mk qz143 Bool.false 149500 1000 2 qz144)

noncomputable abbrev qz537 := (ep1749 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz143 Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz145))

noncomputable def ep1750 := ep1748 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 qz537)

noncomputable def ep1751 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 299 1 0 1 149500 1000 0 1 89401 2

noncomputable def ep1752 := @ep1751 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 44699 2 0 1 Bool.false 299 1 0 1 qz262)

noncomputable def ep1753 := ep1752 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 qz537)

noncomputable def ep1754 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) qz256 Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1 (@ep1729 804594 402297 4 0 1 (ep1750 rfl) (ep1753 rfl) rfl rfl)

noncomputable def ep1755 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz257) 13365001 4 0 1 1495 2 0 1

noncomputable def ep1756 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz258 44699 2 0 1 149500 1000 0 1 13365001 4

noncomputable def ep1757 := @ep1756 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 44699 2 0 1 Bool.false 299 1 0 1 qz262)

noncomputable def ep1758 := ep1757 (@Enclosure.Complex.IsNear.im_isNear qz256 Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 qz537)

noncomputable def ep1759 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2))) qz257 299 1 0 1 5 2 0 1 1495 2

noncomputable def ep1760 := @ep1759 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 44699 2 0 1 Bool.false 299 1 0 1 qz262)

noncomputable def ep1761 := ep1760 (@Enclosure.Complex.IsNear.re_isNear qz256 Bool.false 5 2 0 1 Bool.false 149500 1000 0 1 qz537)

noncomputable abbrev qz263 := (ep1728 (BSN.ascPochhammer_succ_eval_c 2 3 qz453 rfl) (ep1754 (@ep1755 26724022 13362011 4 0 1 (ep1758 rfl) (ep1761 rfl) rfl rfl)))

noncomputable def ep1762 := @ep1727 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1 qz263)

noncomputable def ep1763 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 13362011 4 0 1 0 1 0

noncomputable def ep1764 := @ep1763 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1 qz263)

noncomputable def ep1765 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) 13362011 2880 0 1 0 1 0 1 13362011

noncomputable def ep1766 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 13362011 4 0 1 13362011 2880 0

noncomputable def ep1767 := @ep1766 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1 qz263)

noncomputable def ep1768 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 402297 4 0 1 0 1 0

noncomputable def ep1769 := @ep1768 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1570) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 402297 4 0 1 Bool.true 13362011 4 0 1 qz263)

noncomputable def ep1770 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 134099 960 0 1 Bool.false 13362011 2880 0 1 (@ep1726 134099 960 0 1 (ep1762 rfl) (ep1764 rfl) rfl rfl) (@ep1765 13362011 2880 0 1 (ep1767 rfl) (ep1769 rfl) rfl rfl)

noncomputable def ep1771 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 134099 960 0 1 Bool.false 13362011 2880 0 1 ep1770

noncomputable def ep1772 := nat_lit 393871054344995221692208906240000

noncomputable def ep1773 := @Enclosure.Complex.IsNear.re_isNear qz246 Bool.true 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 Bool.false 4545917563376586735 ep1565 57481253926278313047 ep1772

noncomputable abbrev qz538 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 114415582592)))

noncomputable def ep1774 := @Enclosure.Complex.IsNear.of_eq qz246 (Complex.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz538 qz737)) Bool.true 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 Bool.false 4545917563376586735 ep1565 57481253926278313047

noncomputable abbrev qz539 := (Real.sqrt (@Nat.cast Real Real.instNatCast 114415582592))

noncomputable abbrev qz540 := (@Nat.cast Real Real.instNatCast 114415582592)

noncomputable def ep1775 := @Enclosure.Real.IsNear.inv_image qz539 743827807927934079 2199023255552 1 2199023255552 3250552 3250553 1099511627776 (@Enclosure.Real.IsNear.of_eq qz539 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz540 qz14)) Bool.false 743827807927934079 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 114415582592) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz540 qz14)) Bool.false 743827807927934079 2199023255552 1 2199023255552 743827807927934079 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 114415582592 1 371913903963967039 371913903963967040 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1776 := nat_lit 144099633711214794676839120896

noncomputable def ep1777 := nat_lit 333621760000000000000000000

noncomputable def ep1778 := BSN.log_dyadic_bound 6 70 6 5 29363302133550000000000 1099511627776 333621760000 72228792332824888320 57140536320 188951355727 76 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 6) (BSN.artanhQ 70) 0 5 72228792332824888320 29363302133550000000000 57140536320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1779 := @Enclosure.Real.IsNear.mulLit_ff qz143 qz736 149500 1000 0 1 16382231673471187 4503599627370496 78255321 26064200000000000000 4898287270367884913 9007199254740992 23398340979 52128400000000000000 qz145 (BSN.isNear_log_sfrac 38 1 16382231673471187 4503599627370496 78255321 26064200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz738) Bool.false ep1776 ep1619 1001668108800000 ep1777 16382231673471187 4503599627370496 78255321 26064200000000000000 (BSN.log_rat_reduce_isNear 38 1 5 76 64 188951355727 1099511627776 24973259072661432 36028797018963968 333621760000 1000000000000000 rfl rfl rfl rfl (ep1778 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1780 := nat_lit 102553506548932149183709708288

noncomputable def ep1781 := nat_lit 316912650057057350374175801344

noncomputable def ep1782 := nat_lit 3117698187686655240049449870479321665761448859793108570802751068136492915647863590388178742337194747955107291014923218631786496

noncomputable def ep1783 := nat_lit 6823366825375442818493753656289620051425606865182673602958602092918794624677906806699937015021905992974048683225329102547866091520

noncomputable def ep1784 := nat_lit 20350060833972943019815629856097385841057315240838579793738037637246752082503565886460299109672577862160858613649365794816

noncomputable def ep1785 := nat_lit 9353053862938297774262309980178252802512664464748844035248665728334204253439425764032763306413364898709597551327542357163769856

noncomputable def ep1786 := nat_lit 307051507141894926832218914533032902314152308933220312133137094181345758110505806301497165675985769683832190745139809614653974118400

noncomputable def ep1787 := BSN.cos_dyadic_bound_f 1457372982101392 4503599627370496 3 2 2199023255552 667895125001 ep1782 ep1783 ep1784 ep1785 ep1786 ep1784 2084885713128 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1457372982101392) (BSN.cosEvenQ 4503599627370496) 0 2 ep1782 ep1783 ep1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1457372982101392) (BSN.cosOddQ 4503599627370496) 0 2 ep1785 ep1786 ep1784 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz541 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1195870915617159) (@Nat.cast Real Real.instNatCast 2199023255552))

noncomputable def ep1788 := @Enclosure.Real.IsNear.cos_image qz218 qz541 Bool.false 1195870915617159 2199023255552 247 549755813888 Bool.true 2084885713128 2199023255552 1 333621760000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4898287270367884913 9007199254740992 23398340979 52128400000000000000 1195870915617159 2199023255552 247 549755813888 (ep1779 rfl) rfl) (Enclosure.sfrac_false_div 1195870915617159 2199023255552) (BSN.cos_reduce2 qz541 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1780) (@Nat.cast Real Real.instNatCast ep1781)) 226375608064910080 72057594037927936 Bool.false 2084885713128 2199023255552 86 1000000000000000 667243520000 333621760000 (BSN.sin_reduce_arg_pos_rat_q2 1195870915617159 2199023255552 226375608064910080 72057594037927936 86 ep1780 ep1781 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2084885713128 2199023255552 ep1780 ep1781 1457372982101392 4503599627370496 667895125001 667243520000 (ep1787 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1789 := nat_lit 5611840457787312253734593914358894120461935101775402756581116932215577450764488459846012567967662808256903395139970874044579840

noncomputable def ep1790 := nat_lit 61410301428378985366443782906606580462830461786644062426627418836269151622101161260299433135197153936766438149027961922930794823680

noncomputable def ep1791 := nat_lit 14697644441725419946444761502777336634013706411853760147630878294217956828689336198585264361335796456499160631595501618762612736

noncomputable def ep1792 := nat_lit 1125855526186948065051469353287787308485225132755141144488169345331601113071854623105489607478614488840718032732179301920397905100800

noncomputable def ep1793 := BSN.sin_dyadic_bound_f 1457372982101392 4503599627370496 3 2 2199023255552 667895125001 ep1789 ep1790 ep1784 ep1791 ep1792 ep1784 699253059807 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1457372982101392) (BSN.sinEvenQ 4503599627370496) 0 2 ep1789 ep1790 ep1784 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1457372982101392) (BSN.sinOddQ 4503599627370496) 0 2 ep1791 ep1792 ep1784 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1794 := @Enclosure.Real.IsNear.sin_image qz218 qz541 Bool.false 1195870915617159 2199023255552 247 549755813888 Bool.true 699253059807 2199023255552 1 333621760000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 4898287270367884913 9007199254740992 23398340979 52128400000000000000 1195870915617159 2199023255552 247 549755813888 (ep1779 rfl) rfl) (Enclosure.sfrac_false_div 1195870915617159 2199023255552) (BSN.sin_reduce2 qz541 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1780) (@Nat.cast Real Real.instNatCast ep1781)) 226375608064910080 72057594037927936 Bool.false 699253059807 2199023255552 86 1000000000000000 667243520000 333621760000 (BSN.sin_reduce_arg_pos_rat_q2 1195870915617159 2199023255552 226375608064910080 72057594037927936 86 ep1780 ep1781 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 699253059807 2199023255552 ep1780 ep1781 1457372982101392 4503599627370496 667895125001 667243520000 (ep1793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1795 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz538 (Real.cos qz218)) (@HMul.hMul Real Real Real qz0 qz538 qz737) Bool.true 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 Bool.false 4545917563376586735 ep1565 57481253926278313047 ep1772 (@Enclosure.Real.IsNear.mulLit_ft qz538 (Real.cos qz218) 6501105 2199023255552 1 2199023255552 260610714141 274877906944 20252522103 44777954638561280000 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 (@Enclosure.Real.IsNear.recentre' qz538 Bool.false 6501105 2199023255552 1 2199023255552 6501105 2199023255552 1 2199023255552 (ep1775 rfl rfl) rfl) (@Enclosure.Real.IsNear.recentre' (Real.cos qz218) Bool.true 2084885713128 2199023255552 82954330533888 183410502199547002880000 260610714141 274877906944 20252522103 44777954638561280000 (ep1788 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz538 qz737 6501105 2199023255552 1 2199023255552 699253059807 2199023255552 20252522103 44777954638561280000 4545917563376586735 ep1565 57481253926278313047 ep1772 (@Enclosure.Real.IsNear.recentre' qz538 Bool.false 6501105 2199023255552 1 2199023255552 6501105 2199023255552 1 2199023255552 (ep1775 rfl rfl) rfl) (@Enclosure.Real.IsNear.neg qz219 Bool.true 699253059807 2199023255552 20252522103 44777954638561280000 (@Enclosure.Real.IsNear.recentre' qz219 Bool.true 699253059807 2199023255552 82954330533888 183410502199547002880000 699253059807 2199023255552 20252522103 44777954638561280000 (ep1794 rfl rfl) rfl)) rfl)

noncomputable def ep1796 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 13362011 2880 0 1 4545917563376586735 ep1565 57481253926278313047 ep1772 ep1720

noncomputable def ep1797 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 134099 960 0 1 Bool.false 13362011 2880 0 1 ep1770

noncomputable def ep1798 := @Enclosure.Complex.IsNear.im_isNear qz246 Bool.true 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 Bool.false 4545917563376586735 ep1565 57481253926278313047 ep1772

noncomputable def ep1799 := nat_lit 2569392890086665167096551

noncomputable def ep1800 := nat_lit 7903160887768636199091109

noncomputable def ep1801 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254) 40640199955415793638451 ep1709 ep1799 ep1716 503081975820499029295419 ep1718 ep1800

noncomputable def ep1802 := nat_lit 154124138642455913930681932134718174062947894034432

noncomputable def ep1803 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz255 134099 960 0 1 4545917563376586735 ep1565 57481253926278313047 ep1772 40640199955415793638451

noncomputable def ep1804 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3)))) qz254 13362011 2880 0 1 1694257616755625805 604462909807314587353088 5323184361240065271 ep1724 503081975820499029295419

noncomputable abbrev qz542 := (@ep1774 ep1772 (BSN.cpow_neg_s_sub_mk qz143 149500 1000 38 3 114415582592 qz144 rfl EMLast.d24) ep1795)

noncomputable def ep1805 := ep1717 (@ep1722 ep1711 ep1723 ep1708 ep1709 ep1710 ep1711 (@ep1725 ep1718 237944566552643837591943 ep1719 ep1771 (ep1773 qz542) rfl) (@ep1796 ep1709 ep1721 ep1711 ep1797 (ep1798 qz542) rfl) rfl rfl) (@ep1801 ep1719 ep1802 ep1713 ep1709 ep1714 ep1716 (@ep1803 ep1709 ep1799 ep1716 ep1771 (ep1798 qz542) rfl) (@ep1804 ep1718 ep1800 ep1719 ep1797 (ep1773 qz542) rfl) rfl rfl)

noncomputable def ep1806 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (Complex.im (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) ep1713 ep1709 ep1714 ep1716 ep1713 ep1709 ep1714

noncomputable def ep1807 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246) Bool.true ep1708 ep1709 ep1710 ep1711 Bool.true ep1713 ep1709 ep1714

noncomputable def ep1808 := @ep1679 337983361503839093 576460752303423488 55289953807 576460752303423488 (@ep1680 1 3670016 (ep1681 (@ep1682 1048576 1 1048576 (ep1683 (@ep1684 357800 44725 2 0 1 (ep1688 rfl) (ep1691 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1692 593 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)) (@ep1693 4744 2199023255552 15088055353 1099511627776 593 274877906944 (@ep1698 15088052981 15088057725 1099511627776 (@ep1704 ep1700 ep1705 ep1706 ep1707 ep1694 ep1695 ep1696 ep1697 (@ep1712 ep1711 ep1699 ep1700 ep1701 ep1702 (@ep1715 ep1716 ep1805) (@ep1715 ep1716 ep1805) rfl) (@ep1806 ep1716 ep1703 ep1700 ep1705 ep1706 (@ep1807 ep1716 ep1805) (@ep1807 ep1716 ep1805) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMLast.d25 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 9404425989155691863 15564440312192434176 2268026586467221 15564440312192434176 := ep1677 (ep1678 ep1808) rfl rfl

noncomputable def EMLast.d26 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz543 := (EMLast.d3 qz558 qz696 (@Enclosure.dec_le_dec qz558 qz696 146530 1000 149500 1000 (@Eq.refl Real qz558) (@Eq.refl Real qz696) rfl rfl rfl) 37 38 1 1)

noncomputable abbrev qz264 := qz543

noncomputable def ep1809 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz264 (@Enclosure.dec_nonneg qz12 146530 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 37 rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.ZIntervalEM.fstVal qz543)

noncomputable def ep1810 := @Enclosure.Real.IsNear.pos_val qz265 ep517 ep518

noncomputable def ep1811 := @Enclosure.Real.IsNear.of_eq qz265 (hardyZApproximantEM 1 37 qz12) Bool.false

noncomputable abbrev qz266 := (Zeta.Certificates.ZIntervalEM.sndVal qz543)

noncomputable def ep1812 := BSN.mul_neg_of_pos_neg_r qz265 qz266 (@ep1810 ep519 ep520 (@ep1811 ep517 ep518 ep519 ep520 (@Eq.refl Real (hardyZApproximantEM 1 37 qz12)) EMLast.d12) rfl rfl rfl)

noncomputable def ep1813 := @Enclosure.Real.IsNear.neg_val qz266 ep1215 ep1216

noncomputable def ep1814 := @Enclosure.Real.IsNear.of_eq qz266 (hardyZApproximantEM 1 38 qz143) Bool.true

noncomputable def ep1815 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz265) (BSN.hardyZErrorBoundStrong 1 37 qz12)

noncomputable def ep1816 := @Enclosure.norm_gt_of_isNear qz265 (BSN.hardyZErrorBoundStrong 1 37 qz12) Bool.false

noncomputable def ep1817 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 37 qz12) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))) Bool.false 133072224439611257663 217902164370694078464 29928067371642025 217902164370694078464 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz223 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz226)))))

noncomputable def ep1818 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz266) (BSN.hardyZErrorBoundStrong 1 38 qz143)

noncomputable def ep1819 := @Enclosure.norm_gt_of_isNear qz266 (BSN.hardyZErrorBoundStrong 1 38 qz143) Bool.true

noncomputable def ep1820 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 38 qz143) (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))) Bool.false 9404425989155691863 15564440312192434176 2268026586467221 15564440312192434176 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz419 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz140 1 38))) (@HMul.hMul Real Real Real qz0 qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz74 (@HMul.hMul Complex Complex Complex qz74 (@HDiv.hDiv Complex Complex Complex qz81 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz224)) ↑qz225) (@Polynomial.eval Complex Complex.instSemiring qz140 (@ascPochhammer Complex Complex.instSemiring 3))) qz246)))))

noncomputable def ep1821 := @List.cons EMLast.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz264 (ep1809 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 38 rfl) (ep1812 (@ep1813 ep1217 ep1218 (@ep1814 ep1215 ep1216 ep1217 ep1218 (@Eq.refl Real (hardyZApproximantEM 1 38 qz143)) EMLast.d18) rfl rfl rfl)) (ep1815 (hardyZErrorBoundEM 1 37 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 37 qz12 rfl) (@ep1816 Bool.false ep517 ep518 ep519 ep520 133072224439611257663 217902164370694078464 29928067371642025 217902164370694078464 (@ep1811 ep517 ep518 ep519 ep520 (@Eq.refl Real (hardyZApproximantEM 1 37 qz12)) EMLast.d12) (ep1817 EMLast.d23) rfl rfl rfl rfl rfl)) (ep1818 (hardyZErrorBoundEM 1 38 qz143) (BSN.hardyZErrorBoundEM_le_strong 1 38 qz143 rfl) (@ep1819 Bool.false ep1215 ep1216 ep1217 ep1218 9404425989155691863 15564440312192434176 2268026586467221 15564440312192434176 (@ep1814 ep1215 ep1216 ep1217 ep1218 (@Eq.refl Real (hardyZApproximantEM 1 38 qz143)) EMLast.d18) (ep1820 EMLast.d25) rfl rfl rfl rfl rfl)))) (@List.nil EMLast.d0)

noncomputable abbrev qz544 := (@Enclosure.dec_le_dec qz558 qz696 146530 1000 149500 1000 (@Eq.refl Real qz558) (@Eq.refl Real qz696) rfl rfl rfl)

noncomputable abbrev qz267 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1821 (@List.IsChain.singleton EMLast.d1 EMLast.d26 (EMLast.d2 qz279 qz455 qz544))))

noncomputable abbrev qz545 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1822 := And (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz545 qz267)) (@Option.some Real qz12))

noncomputable def ep1823 := ep1822 (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz545 qz267)) (@Option.some Real qz143))

noncomputable def ep1824 := @And.intro (@Eq Nat (@List.length qz545 qz267) 1) ep1823

noncomputable def ep1825 := @And.intro (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz545 qz267)) (@Option.some Real qz12))

noncomputable def ep1826 := @ep1825 (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz545 qz267)) (@Option.some Real qz143))

noncomputable abbrev qz268 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1821 (@List.IsChain.singleton EMLast.d1 EMLast.d26 (EMLast.d2 qz279 qz455 qz544)))

theorem EMLast.d27 : Zeta.Certificates.BatchSpec 1 146530 1000 149500 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz545 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz545 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz545 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz545 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz143)))) qz268 (ep1824 (@Eq.refl Nat 1) (ep1826 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz143))))

theorem solution : Zeta.Certificates.BatchSpec 1 146530 1000 149500 1000 := EMLast.d27
#print axioms solution
#check solution
