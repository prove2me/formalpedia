-- Prove2me | solution 1 for RHHeight1000.em_main_0051_0051
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-19T21:56:32.780197+00:00
-- url     : https://prove2.me/submissions/2922cd2c-e7e6-488b-9c98-569dbf6e2063

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow51.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow51.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow51.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow51.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow51.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 1250000001 500000000000000 4138529546116343 2251799813685248 1250000001 500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 400000 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 1250000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000800000 400000000000000000000 4138529546116343 2251799813685248 1250000001 500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 400000 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 1250000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000800000 400000000000000000000 4138529546116343 2251799813685248 1250000001 500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow51.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 400000 1200336 1048576 1 400000 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 400000 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 400000 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 400000 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 400000 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 400000 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 400000 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow51.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz738 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 144530 1000)))

noncomputable abbrev qz545 := qz738

noncomputable abbrev qz271 := qz545

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz739 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz546 := qz739

noncomputable abbrev qz272 := qz546

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz547 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz547

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz548 := (@Neg.neg Complex Complex.instNeg qz738)

noncomputable abbrev qz274 := qz548

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz549 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz549) Bool.false 1486432300863 549755813888 4226594522329 1717986918400000 Bool.false 60113872579 274877906944 1057200029801 429496729600000

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz549 Bool.false 1389924648223 549755813888 3783083781053 1717986918400000 Bool.true 96976147087 1099511627776 7569361415231 3435973836800000 Bool.false

noncomputable abbrev qz550 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz550) Bool.false 1389924648223 549755813888 3783083781053 1717986918400000 Bool.true 96976147087 1099511627776 7569361415231 3435973836800000

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz550 Bool.false 2750940954621 1099511627776 6619410485047 3435973836800000 Bool.true 255772984231 549755813888 3309781709711 1717986918400000 Bool.false

noncomputable def ep42 := nat_lit 3056476624907309831684096

noncomputable abbrev qz551 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep43 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz551) Bool.false 2750940954621 1099511627776 6619410485047 3435973836800000 Bool.true 255772984231 549755813888 3309781709711 1717986918400000

noncomputable def ep44 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz551 Bool.false 1326813091815 549755813888 2798167084601 1717986918400000 Bool.true 73348465139 1099511627776 5593998641077 3435973836800000 Bool.false

noncomputable def ep45 := nat_lit 1512345783465499529576448

noncomputable abbrev qz552 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz552) Bool.false 1326813091815 549755813888 2798167084601 1717986918400000 Bool.true 73348465139 1099511627776 5593998641077 3435973836800000

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz552 Bool.false 2166313887285 1099511627776 894628263427 687194767360000 Bool.true 961046917 137438953472 111840392069 85899345920000 Bool.false

noncomputable def ep48 := nat_lit 2917692844672035984506880

noncomputable abbrev qz553 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep49 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz553) Bool.false 2166313887285 1099511627776 894628263427 687194767360000 Bool.true 961046917 137438953472 111840392069 85899345920000

noncomputable def ep50 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz553 Bool.false 873086414913 549755813888 1610069970959 1717986918400000 Bool.true 362246371965 1099511627776 3221005213793 3435973836800000 Bool.false

noncomputable abbrev qz554 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz554

noncomputable abbrev qz8 := qz275

noncomputable def ep51 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 873086414913 549755813888 1610069970959 1717986918400000 Bool.true 362246371965 1099511627776 3221005213793 3435973836800000

noncomputable def ep52 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 114355290531 68719476736 1732291421 3355443200000 Bool.false 267038725525 1099511627776 1771914449479 3435973836800000 Bool.true

noncomputable abbrev qz555 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz555

noncomputable abbrev qz9 := qz276

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 114355290531 68719476736 1732291421 3355443200000 Bool.false 267038725525 1099511627776 1771914449479 3435973836800000

noncomputable def ep54 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz556 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz556

noncomputable def ep55 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz740 := (Enclosure.sfrac Bool.false 144530 1000)

noncomputable abbrev qz557 := qz740

noncomputable abbrev qz277 := qz557

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz267 qz277 (Real.log qz278))

noncomputable abbrev qz12 := qz277

noncomputable abbrev qz279 := (@Eq.refl Real qz557)

noncomputable abbrev qz13 := qz279

noncomputable abbrev qz280 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep56 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.false 45635813795 68719476736 1732291421 3355443200000 Bool.false 267038725525 1099511627776 1771914449479 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz281 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep57 := @Enclosure.Real.IsNear.inv_image qz281 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz281 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep58 := BSN.log_dyadic_bound 1 3 7 6 71816279535 524288 200000 2852596872 10395 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 1) (BSN.artanhQ 3) 0 6 2852596872 71816279535 10395 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep59 := nat_lit 3034197080474803057171176470307619867627614011574410999447150783589846658940865

noncomputable def ep60 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep61 := nat_lit 2222534972580474232310297163616401980235403082433510285985041882111372263361

noncomputable def ep62 := nat_lit 7943108249383163429548388369683625478675750806275707886660466746354751408799681

noncomputable def ep63 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz15 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.sinOddQ 2147483648)

noncomputable def ep64 := BSN.sin_dyadic_bound_f 2620330521 2147483648 3 2 1048576 400391 ep59 ep60 ep61 ep62 ep63 ep61 984784 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2620330521) qz15 0 2 ep59 ep60 ep61 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2620330521) qz16 0 2 ep62 ep63 ep61 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 144530 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable abbrev qz283 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 200000 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 200000 rfl rfl rfl (ep58 rfl)))

noncomputable abbrev qz558 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26261679) qz17)

noncomputable def ep65 := @Enclosure.Real.IsNear.cos_image qz11 qz558 Bool.false 26261679 262144 759 1048576 Bool.false 984784 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 328270989 3276800 14453 20000000 26261679 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 144530 1000 0 1 363408 524288 1 200000 328270989 3276800 14453 20000000 qz18 qz283 rfl) rfl) (Enclosure.sfrac_false_div 26261679 262144) (BSN.cos_reduce3 qz558 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46097342036983916003328) qz19) 226375608064910080 72057594037927936 Bool.false 984784 1048576 15 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 26261679 262144 226375608064910080 72057594037927936 15 46097342036983916003328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 984784 1048576 46097342036983916003328 37778931862957161709568 2620330521 2147483648 400391 400000 (ep64 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep66 := nat_lit 1686652838029370798087235948910284994006556852244643226486632676164186531528641

noncomputable def ep67 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep68 := nat_lit 5055513444142951445797087252403622178059199750569062658887927944728336850059201

noncomputable def ep69 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz20 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.cosOddQ 2147483648)

noncomputable def ep70 := BSN.cos_dyadic_bound_f 2620330521 2147483648 3 2 1048576 400391 ep66 ep67 ep61 ep68 ep69 ep61 360155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2620330521) qz20 0 2 ep66 ep67 ep61 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2620330521) qz21 0 2 ep68 ep69 ep61 rfl rfl rfl rfl) rfl rfl

noncomputable def ep71 := @Enclosure.Real.IsNear.sin_image qz11 qz558 Bool.false 26261679 262144 759 1048576 Bool.true 360155 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 328270989 3276800 14453 20000000 26261679 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 144530 1000 0 1 363408 524288 1 200000 328270989 3276800 14453 20000000 qz18 qz283 rfl) rfl) (Enclosure.sfrac_false_div 26261679 262144) (BSN.sin_reduce3 qz558 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46097342036983916003328) qz19) 226375608064910080 72057594037927936 Bool.false 360155 1048576 15 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 26261679 262144 226375608064910080 72057594037927936 15 46097342036983916003328 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 360155 1048576 46097342036983916003328 37778931862957161709568 2620330521 2147483648 400391 400000 (ep70 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz284 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep57 rfl rfl) rfl)

noncomputable def ep72 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.false 45635813795 68719476736 1732291421 3355443200000 Bool.false 267038725525 1099511627776 1771914449479 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz280 (Real.cos qz11) 741455 1048576 1 1048576 61549 65536 2388259 3276800000 45635813795 68719476736 1732291421 3355443200000 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.false 984784 1048576 152848576 209715200000 61549 65536 2388259 3276800000 (ep65 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 360155 1048576 2388259 3276800000 267038725525 1099511627776 1771914449479 3435973836800000 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.true 360155 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.true 360155 1048576 152848576 209715200000 360155 1048576 2388259 3276800000 (ep71 rfl rfl) rfl)) rfl)

noncomputable abbrev qz559 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz559

noncomputable def ep73 := @ep54 45635813795 68719476736 1732291421 3355443200000 Bool.false 267038725525 1099511627776 1771914449479 3435973836800000 Bool.false 114355290531 114355290531 68719476736 1732291421 3355443200000 Bool.false 267038725525 267038725525 1099511627776 1771914449479 3435973836800000 (ep55 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep56 ep72) rfl rfl

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz277 qz560)

noncomputable abbrev qz285 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep74 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.true 41755909335 549755813888 723136763407 1717986918400000 Bool.true 314642548745 549755813888 724545382157 1717986918400000 (BSN.cpow_neg_s_mk qz12 144530 1000 3 qz13 rfl)

noncomputable abbrev qz286 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz287 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep75 := @Enclosure.Real.IsNear.inv_image qz286 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz286 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz287 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz287 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep76 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 200000 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep77 := BSN.sin_dyadic_bound_f 283336200 2147483648 1 0 1048576 400391 0 1 1 0 1 1 137946 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 283336200) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 283336200) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz288 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 200000 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 200000 rfl rfl rfl (ep76 rfl)))

noncomputable abbrev qz561 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 41623845) qz17)

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz23 qz561 Bool.false 41623845 262144 759 1048576 Bool.true 137946 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 8324769017 52428800 14453 20000000 41623845 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz560 144530 1000 0 1 575989 524288 1 200000 8324769017 52428800 14453 20000000 qz18 qz288 rfl) rfl) (Enclosure.sfrac_false_div 41623845 262144) (BSN.cos_reduce1 qz561 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4984503157926469304320) qz19) 226375608064910080 72057594037927936 Bool.false 137946 1048576 25 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 41623845 262144 226375608064910080 72057594037927936 25 4984503157926469304320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 137946 1048576 4984503157926469304320 37778931862957161709568 283336200 2147483648 400391 400000 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 6444782422476774846862593600000000

noncomputable def ep80 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep81 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep82 := BSN.cos_dyadic_bound_f 283336200 2147483648 2 1 1048576 400391 ep79 ep80 ep79 ep79 ep81 ep79 1039462 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 283336200) qz20 0 1 ep79 ep80 ep79 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 283336200) qz21 0 1 ep79 ep81 ep79 rfl rfl rfl rfl) rfl rfl

noncomputable def ep83 := @Enclosure.Real.IsNear.sin_image qz23 qz561 Bool.false 41623845 262144 759 1048576 Bool.false 1039462 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 8324769017 52428800 14453 20000000 41623845 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz560 144530 1000 0 1 575989 524288 1 200000 8324769017 52428800 14453 20000000 qz18 qz288 rfl) rfl) (Enclosure.sfrac_false_div 41623845 262144) (BSN.sin_reduce1 qz561 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4984503157926469304320) qz19) 226375608064910080 72057594037927936 Bool.false 1039462 1048576 25 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 41623845 262144 226375608064910080 72057594037927936 25 4984503157926469304320 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039462 1048576 4984503157926469304320 37778931862957161709568 283336200 2147483648 400391 400000 (ep82 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz289 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep75 rfl rfl) rfl)

noncomputable def ep84 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.true 41755909335 549755813888 723136763407 1717986918400000 Bool.true 314642548745 549755813888 724545382157 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ft qz285 (Real.cos qz23) 605395 1048576 1 1048576 68973 524288 2388259 3276800000 41755909335 549755813888 723136763407 1717986918400000 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.true 137946 1048576 152848576 209715200000 68973 524288 2388259 3276800000 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz285 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 519731 524288 2388259 3276800000 314642548745 549755813888 724545382157 1717986918400000 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 519731 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 1039462 1048576 152848576 209715200000 519731 524288 2388259 3276800000 (ep83 rfl rfl) rfl)) rfl)

noncomputable def ep85 := @ep52 41755909335 549755813888 723136763407 1717986918400000 Bool.true 314642548745 549755813888 724545382157 1717986918400000 Bool.false 59998041578131546963968 873086414913 549755813888 1610069970959 1717986918400000 Bool.true 199147049047593760849920 362246371965 1099511627776 3221005213793 3435973836800000 (ep53 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep73 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep74 ep84) rfl rfl

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz267 qz277 qz562)

noncomputable abbrev qz290 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep86 := @Enclosure.Complex.IsNear.of_eq qz553 (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz24)))) Bool.false 420141057459 1099511627776 1253001375217 3435973836800000 Bool.false 354557996629 1099511627776 1252610468967 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 4 qz13 rfl)

noncomputable abbrev qz291 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz292 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep87 := @Enclosure.Real.IsNear.inv_image qz291 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz291 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz292 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz292 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep88 := nat_lit 318077276165597140789031982421875

noncomputable def ep89 := nat_lit 49379992292270016474244603430625

noncomputable def ep90 := nat_lit 20095619060363156210525625

noncomputable def ep91 := BSN.log_dyadic_bound 3 5 14 13 ep88 524288 200000 ep89 ep90 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep89 ep88 ep90 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep92 := nat_lit 783225466739344038802431423941077994339449220137302713966722075938708254140545

noncomputable def ep93 := nat_lit 148254086873298772511209822392974037711112851720273895943876549494357665921

noncomputable def ep94 := nat_lit 2051064763414772855993730818228472789113691870028245712176553446378387896051841

noncomputable def ep95 := BSN.sin_dyadic_bound_f 1867995537 2147483648 3 2 1048576 400391 ep92 ep60 ep93 ep94 ep63 ep93 801357 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1867995537) qz15 0 2 ep92 ep60 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1867995537) qz16 0 2 ep94 ep63 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz293 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105046861) qz25)

noncomputable abbrev qz294 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 200000 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 200000 rfl rfl rfl (ep91 rfl)))

noncomputable def ep96 := @Enclosure.Real.IsNear.cos_image qz24 qz293 Bool.false 105046861 524288 379 524288 Bool.false 801357 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 10504686101 52428800 14453 20000000 105046861 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz562 144530 1000 0 1 726817 524288 1 200000 10504686101 52428800 14453 20000000 qz18 qz294 rfl) rfl) (Enclosure.sfrac_false_div 105046861 524288) (BSN.cos_reduce3 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65724250049071087091712) qz26) 226375608064910080 72057594037927936 Bool.false 801357 1048576 31 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 105046861 524288 226375608064910080 72057594037927936 31 65724250049071087091712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 801357 1048576 65724250049071087091712 75557863725914323419136 1867995537 2147483648 400391 400000 (ep95 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep97 := nat_lit 435191150004912598789133550999440207538676728010377185046376209543502077929601

noncomputable def ep98 := nat_lit 1305276941840991198822378233353534674540607958327691007347240875531517518456961

noncomputable def ep99 := BSN.cos_dyadic_bound_f 1867995537 2147483648 3 2 1048576 400391 ep97 ep67 ep93 ep98 ep69 ep93 676267 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1867995537) qz20 0 2 ep97 ep67 ep93 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1867995537) qz21 0 2 ep98 ep69 ep93 rfl rfl rfl rfl) rfl rfl

noncomputable def ep100 := @Enclosure.Real.IsNear.sin_image qz24 qz293 Bool.false 105046861 524288 379 524288 Bool.true 676267 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 10504686101 52428800 14453 20000000 105046861 524288 379 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz562 144530 1000 0 1 726817 524288 1 200000 10504686101 52428800 14453 20000000 qz18 qz294 rfl) rfl) (Enclosure.sfrac_false_div 105046861 524288) (BSN.sin_reduce3 qz293 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65724250049071087091712) qz26) 226375608064910080 72057594037927936 Bool.false 676267 1048576 31 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 105046861 524288 226375608064910080 72057594037927936 31 65724250049071087091712 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 676267 1048576 65724250049071087091712 75557863725914323419136 1867995537 2147483648 400391 400000 (ep99 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz295 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep87 rfl rfl) rfl)

noncomputable def ep101 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz24))) Bool.false 420141057459 1099511627776 1253001375217 3435973836800000 Bool.false 354557996629 1099511627776 1252610468967 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz290 (Real.cos qz24) 524287 1048576 1 1048576 801357 1048576 1192567 1638400000 420141057459 1099511627776 1253001375217 3435973836800000 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz24) Bool.false 801357 1048576 76324288 104857600000 801357 1048576 1192567 1638400000 (ep96 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz290 (@Neg.neg Real Real.instNeg (Real.sin qz24)) 524287 1048576 1 1048576 676267 1048576 1192567 1638400000 354557996629 1099511627776 1252610468967 3435973836800000 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz24) Bool.true 676267 1048576 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz24) Bool.true 676267 1048576 76324288 104857600000 676267 1048576 1192567 1638400000 (ep100 rfl rfl) rfl)) rfl)

noncomputable def ep102 := @ep50 420141057459 1099511627776 1253001375217 3435973836800000 Bool.false 354557996629 1099511627776 1252610468967 3435973836800000 Bool.false 1190943654241242269614080 2166313887285 1099511627776 894628263427 687194767360000 Bool.true 8453458080638210932736 961046917 137438953472 111840392069 85899345920000 (ep51 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep85 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep86 ep101) rfl rfl

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz277 qz563)

noncomputable abbrev qz296 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep103 := @Enclosure.Complex.IsNear.of_eq qz552 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 487312296345 1099511627776 1123192852067 3435973836800000 Bool.true 65660089803 1099511627776 1120382958317 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 5 qz13 rfl)

noncomputable abbrev qz297 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz298 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep104 := @Enclosure.Real.IsNear.inv_image qz297 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz297 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz298 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep105 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep106 := nat_lit 765440954430599474856563326857688500

noncomputable def ep107 := nat_lit 108794268166472120024432640000

noncomputable def ep108 := BSN.log_dyadic_bound 2 3 18 17 ep105 524288 200000 ep106 ep107 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep106 ep105 ep107 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep109 := nat_lit 6843436249640776428657350254018816

noncomputable def ep110 := BSN.cos_dyadic_bound_f 287619652 2147483648 2 1 1048576 400391 ep109 ep80 ep109 ep109 ep81 ep109 1039185 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 287619652) qz20 0 1 ep109 ep80 ep109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 287619652) qz21 0 1 ep109 ep81 ep109 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 200000 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 200000 rfl rfl rfl (ep108 rfl rfl)))

noncomputable abbrev qz564 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60977785) qz17)

noncomputable def ep111 := @Enclosure.Real.IsNear.cos_image qz27 qz564 Bool.false 60977785 262144 759 1048576 Bool.false 1039185 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 381111157 1638400 14453 20000000 60977785 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz563 144530 1000 0 1 843808 524288 1 200000 381111157 1638400 14453 20000000 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 60977785 262144) (BSN.cos_reduce0 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5059858440070428098560) qz19) 226375608064910080 72057594037927936 Bool.false 1039185 1048576 37 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 60977785 262144 226375608064910080 72057594037927936 37 5059858440070428098560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1039185 1048576 5059858440070428098560 37778931862957161709568 287619652 2147483648 400391 400000 (ep110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep112 := BSN.sin_dyadic_bound_f 287619652 2147483648 1 0 1048576 400391 0 1 1 0 1 1 140019 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 287619652) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 287619652) qz16 0 0 rfl) rfl rfl

noncomputable def ep113 := @Enclosure.Real.IsNear.sin_image qz27 qz564 Bool.false 60977785 262144 759 1048576 Bool.false 140019 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 381111157 1638400 14453 20000000 60977785 262144 759 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz563 144530 1000 0 1 843808 524288 1 200000 381111157 1638400 14453 20000000 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 60977785 262144) (BSN.sin_reduce0 qz564 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5059858440070428098560) qz19) 226375608064910080 72057594037927936 Bool.false 140019 1048576 37 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 60977785 262144 226375608064910080 72057594037927936 37 5059858440070428098560 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 140019 1048576 5059858440070428098560 37778931862957161709568 287619652 2147483648 400391 400000 (ep112 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep104 rfl rfl) rfl)

noncomputable def ep114 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 487312296345 1099511627776 1123192852067 3435973836800000 Bool.true 65660089803 1099511627776 1120382958317 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz296 (Real.cos qz27) 468937 1048576 1 1048576 1039185 1048576 2388259 3276800000 487312296345 1099511627776 1123192852067 3435973836800000 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 1039185 1048576 152848576 209715200000 1039185 1048576 2388259 3276800000 (ep111 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz296 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 468937 1048576 1 1048576 140019 1048576 2388259 3276800000 65660089803 1099511627776 1120382958317 3435973836800000 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.false 140019 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.false 140019 1048576 152848576 209715200000 140019 1048576 2388259 3276800000 (ep113 rfl rfl) rfl)) rfl)

noncomputable def ep115 := @ep47 487312296345 1099511627776 1123192852067 3435973836800000 Bool.true 65660089803 1099511627776 1120382958317 3435973836800000 Bool.false ep48 1326813091815 549755813888 2798167084601 1717986918400000 Bool.true 10080936287481635012608 73348465139 1099511627776 5593998641077 3435973836800000 (ep49 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep102 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep103 ep114) rfl rfl

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz277 qz565)

noncomputable abbrev qz301 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep116 := @Enclosure.Complex.IsNear.of_eq qz551 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.false 97314770991 1099511627776 204615263169 687194767360000 Bool.true 438197503323 1099511627776 205112955669 687194767360000 (BSN.cpow_neg_s_mk qz12 144530 1000 6 qz13 rfl)

noncomputable abbrev qz302 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz303 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz566 := (@HDiv.hDiv Real Real Real qz1 qz303 qz14)

noncomputable def ep117 := @Enclosure.Real.IsNear.inv_image qz302 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz302 (Real.sqrt qz566) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz566) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep118 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 200000 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep119 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz565 144530 1000 0 1 4034681531866359 2251799813685248 2500000001 500000000000000 58313252180064486627 225179981368524800 36132500014453 50000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 2500000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz566) Bool.false 33845361775666394038272 18889465931478580854784 1000000000400000 200000000000000000000 4034681531866359 2251799813685248 2500000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep120 := nat_lit 2545984708353539407147116394000950400573655718407624061718437236960828793323776

noncomputable def ep121 := nat_lit 5057396395646300863071653436225842446472368553969414390875775007293456548096

noncomputable def ep122 := nat_lit 7627839332269325619715205875130399516828022418114933356373560160867899466875136

noncomputable def ep123 := BSN.cos_dyadic_bound_f 2903961634 2147483648 3 2 1048576 400391 ep120 ep67 ep121 ep122 ep69 ep121 227329 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2903961634) qz20 0 2 ep120 ep67 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2903961634) qz21 0 2 ep122 ep69 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz304 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8485695) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep124 := @Enclosure.Real.IsNear.cos_image qz28 qz304 Bool.false 8485695 32768 759 1048576 Bool.false 227329 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 58313252180064486627 225179981368524800 36132500014453 50000000000000000 8485695 32768 759 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 8485695 32768) (BSN.cos_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6385879167710139514880) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 227329 1048576 41 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 8485695 32768 226375608064910080 72057594037927936 41 6385879167710139514880 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 227329 1048576 6385879167710139514880 4722366482869645213696 2903961634 2147483648 400391 400000 (ep123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep125 := nat_lit 4578726557919853892174352186452730047075402398290547779580486406523657062744320

noncomputable def ep126 := nat_lit 11983714724197142373344996858955641616474622446435484180363665524216817187062016

noncomputable def ep127 := BSN.sin_dyadic_bound_f 2903961634 2147483648 3 2 1048576 400391 ep125 ep60 ep121 ep126 ep63 ep121 1023637 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2903961634) qz15 0 2 ep125 ep60 ep121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2903961634) qz16 0 2 ep126 ep63 ep121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep128 := @Enclosure.Real.IsNear.sin_image qz28 qz304 Bool.false 8485695 32768 759 1048576 Bool.false 1023637 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 58313252180064486627 225179981368524800 36132500014453 50000000000000000 8485695 32768 759 1048576 (ep119 rfl) rfl) (Enclosure.sfrac_false_div 8485695 32768) (BSN.sin_reduce0 qz304 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6385879167710139514880) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 1023637 1048576 41 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 8485695 32768 226375608064910080 72057594037927936 41 6385879167710139514880 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1023637 1048576 6385879167710139514880 4722366482869645213696 2903961634 2147483648 400391 400000 (ep127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz305 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep117 rfl rfl) rfl)

noncomputable def ep129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.false 97314770991 1099511627776 204615263169 687194767360000 Bool.true 438197503323 1099511627776 205112955669 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz301 (Real.cos qz28) 428079 1048576 1 1048576 227329 1048576 2388259 3276800000 97314770991 1099511627776 204615263169 687194767360000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.false 227329 1048576 152848576 209715200000 227329 1048576 2388259 3276800000 (ep124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz301 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 428079 1048576 1 1048576 1023637 1048576 2388259 3276800000 438197503323 1099511627776 205112955669 687194767360000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 1023637 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 1023637 1048576 152848576 209715200000 1023637 1048576 2388259 3276800000 (ep128 rfl rfl) rfl)) rfl)

noncomputable def ep130 := @ep44 97314770991 1099511627776 204615263169 687194767360000 Bool.true 438197503323 1099511627776 205112955669 687194767360000 Bool.false ep45 2750940954621 1099511627776 6619410485047 3435973836800000 Bool.true 562450740465903979200512 255772984231 549755813888 3309781709711 1717986918400000 (ep46 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep115 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep116 ep129) rfl rfl

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz277 qz567)

noncomputable abbrev qz306 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep131 := @Enclosure.Complex.IsNear.of_eq qz550 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 28908341825 1099511627776 946757077059 3435973836800000 Bool.false 414569821375 1099511627776 949797995809 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 7 qz13 rfl)

noncomputable abbrev qz307 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz568 := (@HDiv.hDiv Real Real Real qz1 qz308 qz14)

noncomputable def ep132 := @Enclosure.Real.IsNear.inv_image qz307 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz307 (Real.sqrt qz568) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz568) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep133 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 200000 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz567 144530 1000 0 1 4381796493761783 2251799813685248 2500000001 500000000000000 63330104724339049699 225179981368524800 36132500014453 50000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 2500000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz568) Bool.false 36757173121942042968064 18889465931478580854784 1000000000400000 200000000000000000000 4381796493761783 2251799813685248 2500000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep135 := BSN.sin_dyadic_bound_f 149504162 2147483648 1 0 1048576 400391 0 1 1 0 1 1 72941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 149504162) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 149504162) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz569 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73725945) qz17)

noncomputable def ep136 := @Enclosure.Real.IsNear.cos_image qz29 qz569 Bool.false 73725945 262144 759 1048576 Bool.false 72941 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 63330104724339049699 225179981368524800 36132500014453 50000000000000000 73725945 262144 759 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 73725945 262144) (BSN.cos_reduce3 qz569 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2630105043571792936960) qz19) 226375608064910080 72057594037927936 Bool.false 72941 1048576 44 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 73725945 262144 226375608064910080 72057594037927936 44 2630105043571792936960 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 72941 1048576 2630105043571792936960 37778931862957161709568 149504162 2147483648 400391 400000 (ep135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep137 := nat_lit 499589304386301016983417881195536

noncomputable def ep138 := BSN.cos_dyadic_bound_f 149504162 2147483648 2 1 1048576 400391 ep137 ep80 ep137 ep137 ep81 ep137 1046035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 149504162) qz20 0 1 ep137 ep80 ep137 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 149504162) qz21 0 1 ep137 ep81 ep137 rfl rfl rfl rfl) rfl rfl

noncomputable def ep139 := @Enclosure.Real.IsNear.sin_image qz29 qz569 Bool.false 73725945 262144 759 1048576 Bool.true 1046035 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 63330104724339049699 225179981368524800 36132500014453 50000000000000000 73725945 262144 759 1048576 (ep134 rfl) rfl) (Enclosure.sfrac_false_div 73725945 262144) (BSN.sin_reduce3 qz569 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2630105043571792936960) qz19) 226375608064910080 72057594037927936 Bool.false 1046035 1048576 44 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 73725945 262144 226375608064910080 72057594037927936 44 2630105043571792936960 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046035 1048576 2630105043571792936960 37778931862957161709568 149504162 2147483648 400391 400000 (ep138 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep132 rfl rfl) rfl)

noncomputable def ep140 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 28908341825 1099511627776 946757077059 3435973836800000 Bool.false 414569821375 1099511627776 949797995809 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz306 (Real.cos qz29) 396325 1048576 1 1048576 72941 1048576 2388259 3276800000 28908341825 1099511627776 946757077059 3435973836800000 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 72941 1048576 152848576 209715200000 72941 1048576 2388259 3276800000 (ep136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz306 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 1046035 1048576 2388259 3276800000 414569821375 1099511627776 949797995809 3435973836800000 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 1046035 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 1046035 1048576 152848576 209715200000 1046035 1048576 2388259 3276800000 (ep139 rfl rfl) rfl)) rfl)

noncomputable def ep141 := @ep41 28908341825 1099511627776 946757077059 3435973836800000 Bool.false 414569821375 1099511627776 949797995809 3435973836800000 Bool.false ep42 1389924648223 549755813888 3783083781053 1717986918400000 Bool.true 53313200669536085344256 96976147087 1099511627776 7569361415231 3435973836800000 (ep43 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep131 ep140) rfl rfl

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz277 qz570)

noncomputable abbrev qz310 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep142 := @Enclosure.Complex.IsNear.of_eq qz549 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.false 3015864145 17179869184 110877685319 429496729600000 Bool.false 337431637403 1099511627776 888238823177 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 8 qz13 rfl)

noncomputable abbrev qz311 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz571 := (@HDiv.hDiv Real Real Real qz1 qz312 qz14)

noncomputable def ep143 := @Enclosure.Real.IsNear.inv_image qz311 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz311 (Real.sqrt qz571) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz571) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep144 := BSN.log_dyadic_bound 0 16 1 0 1 524288 200000 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep145 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 144530 1000 0 1 9364972152248037 4503599627370496 5000000003 1000000000000000 135351942516440878761 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 39279540158062550581248 18889465931478580854784 1000000000600000 200000000000000000000 9364972152248037 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep146 := nat_lit 1550070747280157968884306703155641761

noncomputable def ep147 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep148 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep149 := BSN.sin_dyadic_bound_f 1115803913 2147483648 2 1 1048576 400391 ep146 ep147 ep146 ep146 ep148 ep146 520640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1115803913) qz15 0 1 ep146 ep147 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1115803913) qz16 0 1 ep146 ep148 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 157570399) qz25)

noncomputable def ep150 := @Enclosure.Real.IsNear.cos_image qz30 qz313 Bool.false 157570399 524288 759 1048576 Bool.false 520640 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 135351942516440878761 450359962737049600 72265000043359 100000000000000000 157570399 524288 759 1048576 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 157570399 524288) (BSN.cos_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39258860055756997132288) qz26) 226375608064910080 72057594037927936 Bool.false 520640 1048576 47 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 157570399 524288 226375608064910080 72057594037927936 47 39258860055756997132288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 520640 1048576 39258860055756997132288 75557863725914323419136 1115803913 2147483648 400391 400000 (ep149 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep151 := BSN.cos_dyadic_bound_f 1115803913 2147483648 2 1 1048576 400391 ep146 ep80 ep146 ep146 ep81 ep146 910189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1115803913) qz20 0 1 ep146 ep80 ep146 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1115803913) qz21 0 1 ep146 ep81 ep146 rfl rfl rfl rfl) rfl rfl

noncomputable def ep152 := @Enclosure.Real.IsNear.sin_image qz30 qz313 Bool.false 157570399 524288 759 1048576 Bool.true 910189 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 135351942516440878761 450359962737049600 72265000043359 100000000000000000 157570399 524288 759 1048576 (ep145 rfl) rfl) (Enclosure.sfrac_false_div 157570399 524288) (BSN.sin_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39258860055756997132288) qz26) 226375608064910080 72057594037927936 Bool.false 910189 1048576 47 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 157570399 524288 226375608064910080 72057594037927936 47 39258860055756997132288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 910189 1048576 39258860055756997132288 75557863725914323419136 1115803913 2147483648 400391 400000 (ep151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep143 rfl rfl) rfl)

noncomputable def ep153 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.false 3015864145 17179869184 110877685319 429496729600000 Bool.false 337431637403 1099511627776 888238823177 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz310 (Real.cos qz30) 370727 1048576 1 1048576 8135 16384 2388259 3276800000 3015864145 17179869184 110877685319 429496729600000 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.false 520640 1048576 152848576 209715200000 8135 16384 2388259 3276800000 (ep150 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 370727 1048576 1 1048576 910189 1048576 2388259 3276800000 337431637403 1099511627776 888238823177 3435973836800000 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 910189 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 910189 1048576 152848576 209715200000 910189 1048576 2388259 3276800000 (ep152 rfl rfl) rfl)) rfl)

noncomputable def ep154 := @ep39 3015864145 17179869184 110877685319 429496729600000 Bool.false 337431637403 1099511627776 888238823177 3435973836800000 Bool.false 25536712479698470305792 1486432300863 549755813888 4226594522329 1717986918400000 Bool.false 264383607565021364617216 60113872579 274877906944 1057200029801 429496729600000 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep141 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep142 ep153) rfl rfl

theorem EMRow51.d6 : Enclosure.Complex.IsNear qz3 Bool.false 1486432300863 549755813888 4226594522329 1717986918400000 Bool.false 60113872579 274877906944 1057200029801 429496729600000 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep154 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz31 := (BSN.headSumC qz271 17)

noncomputable abbrev qz572 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq qz31 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz572) Bool.false 3506039949239 1099511627776 14207966558867 3435973836800000 Bool.false 71941935661 549755813888 3553368906123 858993459200000

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz572 Bool.false 3459757029731 1099511627776 13581347054071 3435973836800000 Bool.true 63534091025 549755813888 1698022230587 429496729600000 Bool.false

noncomputable abbrev qz573 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep157 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz573) Bool.false 3459757029731 1099511627776 13581347054071 3435973836800000 Bool.true 63534091025 549755813888 1698022230587 429496729600000

noncomputable def ep158 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz573 Bool.false 1767184323367 549755813888 1616841238471 429496729600000 Bool.false 18355534753 137438953472 6467630144509 1717986918400000 Bool.true

noncomputable def ep159 := nat_lit 1902021541734495318704128

noncomputable abbrev qz574 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz574) Bool.false 1767184323367 549755813888 1616841238471 429496729600000 Bool.false 18355534753 137438953472 6467630144509 1717986918400000

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz574 Bool.false 903949713811 274877906944 6132263310661 1717986918400000 Bool.true 135503627149 1099511627776 12262816561947 3435973836800000 Bool.true

noncomputable abbrev qz575 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz575) Bool.false 903949713811 274877906944 6132263310661 1717986918400000 Bool.true 135503627149 1099511627776 12262816561947 3435973836800000

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz575 Bool.false 3310851454603 1099511627776 11566686814031 3435973836800000 Bool.true 134301364867 1099511627776 11568240607781 3435973836800000 Bool.false

noncomputable def ep164 := nat_lit 3975612885039927833657344

noncomputable abbrev qz576 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep165 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz576) Bool.false 3310851454603 1099511627776 11566686814031 3435973836800000 Bool.true 134301364867 1099511627776 11568240607781 3435973836800000

noncomputable def ep166 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz576 Bool.false 3139856103121 1099511627776 10842000259999 3435973836800000 Bool.false 133100559539 1099511627776 10842558766249 3435973836800000 Bool.false

noncomputable def ep167 := nat_lit 1820159836087540948926464

noncomputable abbrev qz577 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz577) Bool.false 3139856103121 1099511627776 10842000259999 3435973836800000 Bool.false 133100559539 1099511627776 10842558766249 3435973836800000

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz577 Bool.false 369830747027 137438953472 2521285482613 858993459200000 Bool.false 102676422779 274877906944 5042373818351 1717986918400000 Bool.false

noncomputable abbrev qz578 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz578) Bool.false 369830747027 137438953472 2521285482613 858993459200000 Bool.false 102676422779 274877906944 5042373818351 1717986918400000

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz578 Bool.false 2619054075701 1099511627776 9290018706767 3435973836800000 Bool.false 336073296941 1099511627776 9292121475517 3435973836800000 Bool.false

noncomputable def ep172 := nat_lit 3253065653322166740975616

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz579) Bool.false 2619054075701 1099511627776 9290018706767 3435973836800000 Bool.false 336073296941 1099511627776 9292121475517 3435973836800000

noncomputable def ep174 := @Enclosure.Complex.IsNear.addLitP qz3 qz579 Bool.false 1486432300863 549755813888 4226594522329 1717986918400000 Bool.false 60113872579 274877906944 1057200029801 429496729600000 Bool.true

noncomputable def ep175 := nat_lit 1439840205003686819135488

noncomputable abbrev qz580 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz267 qz277 qz580)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 353810526025 1099511627776 836829662109 3435973836800000 Bool.false 95617806625 1099511627776 834521237109 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 9 qz13 rfl)

noncomputable abbrev qz316 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz581 := (@HDiv.hDiv Real Real Real qz1 qz317 qz14)

noncomputable def ep177 := @Enclosure.Real.IsNear.inv_image qz316 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz316 (Real.sqrt qz581) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz581) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep178 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 200000 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz580 144530 1000 0 1 9895417793173221 4503599627370496 5000000003 1000000000000000 143018473364732563113 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 41504390431577613533184 18889465931478580854784 1000000000600000 200000000000000000000 9895417793173221 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep180 := nat_lit 103223890768586658847516009971201601

noncomputable def ep181 := BSN.cos_dyadic_bound_f 566819857 2147483648 2 1 1048576 400391 ep180 ep80 ep180 ep180 ep81 ep180 1012261 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 566819857) qz20 0 1 ep180 ep80 ep180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 566819857) qz21 0 1 ep180 ep81 ep180 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20811927) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep182 := @Enclosure.Real.IsNear.cos_image qz32 qz318 Bool.false 20811927 65536 379 524288 Bool.true 1012261 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 143018473364732563113 450359962737049600 72265000043359 100000000000000000 20811927 65536 379 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 20811927 65536) (BSN.cos_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2492900097309576003584) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 1012261 1048576 50 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 20811927 65536 226375608064910080 72057594037927936 50 2492900097309576003584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012261 1048576 2492900097309576003584 9444732965739290427392 566819857 2147483648 400391 400000 (ep181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep183 := BSN.sin_dyadic_bound_f 566819857 2147483648 2 1 1048576 400391 ep180 ep147 ep180 ep180 ep148 ep180 273565 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 566819857) qz15 0 1 ep180 ep147 ep180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 566819857) qz16 0 1 ep180 ep148 ep180 rfl rfl rfl rfl) rfl rfl

noncomputable def ep184 := @Enclosure.Real.IsNear.sin_image qz32 qz318 Bool.false 20811927 65536 379 524288 Bool.true 273565 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 143018473364732563113 450359962737049600 72265000043359 100000000000000000 20811927 65536 379 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 20811927 65536) (BSN.sin_reduce2 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2492900097309576003584) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 273565 1048576 50 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 20811927 65536 226375608064910080 72057594037927936 50 2492900097309576003584 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 273565 1048576 2492900097309576003584 9444732965739290427392 566819857 2147483648 400391 400000 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep177 rfl rfl) rfl)

noncomputable def ep185 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 353810526025 1099511627776 836829662109 3435973836800000 Bool.false 95617806625 1099511627776 834521237109 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz315 (Real.cos qz32) 349525 1048576 1 1048576 1012261 1048576 1192567 1638400000 353810526025 1099511627776 836829662109 3435973836800000 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 1012261 1048576 76324288 104857600000 1012261 1048576 1192567 1638400000 (ep182 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 349525 1048576 1 1048576 273565 1048576 1192567 1638400000 95617806625 1099511627776 834521237109 3435973836800000 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.true 273565 1048576 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.true 273565 1048576 76324288 104857600000 273565 1048576 1192567 1638400000 (ep184 rfl rfl) rfl)) rfl)

noncomputable def ep186 := @ep174 353810526025 1099511627776 836829662109 3435973836800000 Bool.false 95617806625 1099511627776 834521237109 3435973836800000 Bool.false ep175 2619054075701 1099511627776 9290018706767 3435973836800000 Bool.false 92379124442911477858304 336073296941 1099511627776 9292121475517 3435973836800000 EMRow51.d6 (ep176 ep185) rfl rfl

noncomputable abbrev qz582 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt qz582))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz267 qz277 qz583)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz578 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.false 339591900515 1099511627776 159024644737 687194767360000 Bool.false 74632394175 1099511627776 158525232237 687194767360000 (BSN.cpow_neg_s_mk qz12 144530 1000 10 qz13 rfl)

noncomputable abbrev qz584 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep188 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz582) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz582) (Real.sqrt qz584) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz584) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep189 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 200000 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep190 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 144530 1000 0 1 10369917190100709 4503599627370496 5000000003 1000000000000000 149876413148525547177 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 43494585150108164161536 18889465931478580854784 1000000000600000 200000000000000000000 10369917190100709 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep191 := nat_lit 4608650732503134797052750654923565201821064327275367279793293906222632525267200

noncomputable def ep192 := nat_lit 5123643542530227121439890014202982644300708470192972164470721099793666048256

noncomputable def ep193 := nat_lit 12061980305106018386465349036205389747154872091055173301668531444040562106859776

noncomputable def ep194 := BSN.sin_dyadic_bound_f 2908689502 2147483648 3 2 1048576 400391 ep191 ep60 ep192 ep193 ep63 ep192 1024135 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2908689502) qz15 0 2 ep191 ep60 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2908689502) qz16 0 2 ep193 ep63 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz35 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz36 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz320 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348958217) qz35)

noncomputable def ep195 := @Enclosure.Real.IsNear.cos_image qz34 qz320 Bool.false 348958217 1048576 759 1048576 Bool.false 1024135 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 149876413148525547177 450359962737049600 72265000043359 100000000000000000 348958217 1048576 759 1048576 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 348958217 1048576) (BSN.cos_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204680827491112760377344) qz36) 226375608064910080 72057594037927936 Bool.false 1024135 1048576 52 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 348958217 1048576 226375608064910080 72057594037927936 52 204680827491112760377344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1024135 1048576 204680827491112760377344 151115727451828646838272 2908689502 2147483648 400391 400000 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep196 := nat_lit 2562638692965088321527723648297181993298058274473067587513816935056926365614336

noncomputable def ep197 := nat_lit 7677668791810204510340291164863140014605573406478816818212509362971191764746496

noncomputable def ep198 := BSN.cos_dyadic_bound_f 2908689502 2147483648 3 2 1048576 400391 ep196 ep67 ep192 ep197 ep69 ep192 225075 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2908689502) qz20 0 2 ep196 ep67 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2908689502) qz21 0 2 ep197 ep69 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep199 := @Enclosure.Real.IsNear.sin_image qz34 qz320 Bool.false 348958217 1048576 759 1048576 Bool.true 225075 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 149876413148525547177 450359962737049600 72265000043359 100000000000000000 348958217 1048576 759 1048576 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 348958217 1048576) (BSN.sin_reduce3 qz320 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204680827491112760377344) qz36) 226375608064910080 72057594037927936 Bool.false 225075 1048576 52 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 348958217 1048576 226375608064910080 72057594037927936 52 204680827491112760377344 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 225075 1048576 204680827491112760377344 151115727451828646838272 2908689502 2147483648 400391 400000 (ep198 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz321 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep188 rfl rfl) rfl)

noncomputable def ep200 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.false 339591900515 1099511627776 159024644737 687194767360000 Bool.false 74632394175 1099511627776 158525232237 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz33 (Real.cos qz34) 331589 1048576 1 1048576 1024135 1048576 2388259 3276800000 339591900515 1099511627776 159024644737 687194767360000 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.false 1024135 1048576 152848576 209715200000 1024135 1048576 2388259 3276800000 (ep195 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 331589 1048576 1 1048576 225075 1048576 2388259 3276800000 74632394175 1099511627776 158525232237 687194767360000 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.true 225075 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.true 225075 1048576 152848576 209715200000 225075 1048576 2388259 3276800000 (ep199 rfl rfl) rfl)) rfl)

noncomputable def ep201 := @ep171 339591900515 1099511627776 159024644737 687194767360000 Bool.false 74632394175 1099511627776 158525232237 687194767360000 Bool.false ep172 369830747027 137438953472 2521285482613 858993459200000 Bool.false 451575682975820222038016 102676422779 274877906944 5042373818351 1717986918400000 (ep173 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep186 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep187 ep200) rfl rfl

noncomputable abbrev qz585 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt qz585))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz267 qz277 qz586)

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz577 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.false 181210126905 1099511627776 756858329547 3435973836800000 Bool.true 277605131577 1099511627776 757811129547 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 11 qz13 rfl)

noncomputable abbrev qz587 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep203 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz585) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz585) (Real.sqrt qz587) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz587) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep204 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 200000 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 144530 1000 0 1 10799156221662949 4503599627370496 5000000003 1000000000000000 156080204871694601897 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 45294944137145793642496 18889465931478580854784 1000000000600000 200000000000000000000 10799156221662949 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := nat_lit 737715894904582719042727698123485363239842744815764562677629116854005877144161

noncomputable def ep207 := nat_lit 425813371348527212004593265673380649072335335741590460655658312114504170081

noncomputable def ep208 := nat_lit 2212296057971051102704173907839109328421383563775810507111576033937788623092321

noncomputable def ep209 := BSN.cos_dyadic_bound_f 2131338411 2147483648 3 2 1048576 400391 ep206 ep67 ep207 ep208 ep69 ep207 573165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2131338411) qz20 0 2 ep206 ep67 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2131338411) qz21 0 2 ep208 ep69 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 363402545) qz35)

noncomputable def ep210 := @Enclosure.Real.IsNear.cos_image qz38 qz322 Bool.false 363402545 1048576 759 1048576 Bool.false 573165 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 156080204871694601897 450359962737049600 72265000043359 100000000000000000 363402545 1048576 759 1048576 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 363402545 1048576) (BSN.cos_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149979607420023487856640) qz36) 226375608064910080 72057594037927936 Bool.false 573165 1048576 55 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 363402545 1048576 226375608064910080 72057594037927936 55 149979607420023487856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 573165 1048576 149979607420023487856640 151115727451828646838272 2131338411 2147483648 400391 400000 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep211 := nat_lit 1327547960131170072507306182009734949312459072399782940451207883687518975523425

noncomputable def ep212 := nat_lit 3476221912028024002985413516166787012862704265741564173769244820009602405333601

noncomputable def ep213 := BSN.sin_dyadic_bound_f 2131338411 2147483648 3 2 1048576 400391 ep211 ep60 ep207 ep212 ep63 ep207 878061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2131338411) qz15 0 2 ep211 ep60 ep207 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2131338411) qz16 0 2 ep212 ep63 ep207 rfl rfl rfl rfl) rfl rfl

noncomputable def ep214 := @Enclosure.Real.IsNear.sin_image qz38 qz322 Bool.false 363402545 1048576 759 1048576 Bool.false 878061 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 156080204871694601897 450359962737049600 72265000043359 100000000000000000 363402545 1048576 759 1048576 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 363402545 1048576) (BSN.sin_reduce0 qz322 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149979607420023487856640) qz36) 226375608064910080 72057594037927936 Bool.false 878061 1048576 55 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 363402545 1048576 226375608064910080 72057594037927936 55 149979607420023487856640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 878061 1048576 149979607420023487856640 151115727451828646838272 2131338411 2147483648 400391 400000 (ep213 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz323 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep203 rfl rfl) rfl)

noncomputable def ep215 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.false 181210126905 1099511627776 756858329547 3435973836800000 Bool.true 277605131577 1099511627776 757811129547 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz38) 316157 1048576 1 1048576 573165 1048576 2388259 3276800000 181210126905 1099511627776 756858329547 3435973836800000 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.false 573165 1048576 152848576 209715200000 573165 1048576 2388259 3276800000 (ep210 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 316157 1048576 1 1048576 878061 1048576 2388259 3276800000 277605131577 1099511627776 757811129547 3435973836800000 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 878061 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 878061 1048576 152848576 209715200000 878061 1048576 2388259 3276800000 (ep214 rfl rfl) rfl)) rfl)

noncomputable def ep216 := @ep169 181210126905 1099511627776 756858329547 3435973836800000 Bool.true 277605131577 1099511627776 757811129547 3435973836800000 Bool.false 431538536865622352986112 3139856103121 1099511627776 10842000259999 3435973836800000 Bool.false 36586403219155573538816 133100559539 1099511627776 10842558766249 3435973836800000 (ep170 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep201 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep202 ep215) rfl rfl

noncomputable abbrev qz588 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt qz588))

noncomputable abbrev qz589 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz267 qz277 qz589)

noncomputable def ep217 := @Enclosure.Complex.IsNear.of_eq qz576 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 85497675741 549755813888 45292909627 214748364800000 Bool.true 133700962203 549755813888 181420460383 858993459200000 (BSN.cpow_neg_s_mk qz12 144530 1000 12 qz13 rfl)

noncomputable abbrev qz590 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep218 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz588) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz588) (Real.sqrt qz590) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz590) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep219 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 200000 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz589 144530 1000 0 1 11191020447815397 4503599627370496 5000000003 1000000000000000 161743818532275932841 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 46938541828353910898688 18889465931478580854784 1000000000600000 200000000000000000000 11191020447815397 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep219 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep221 := nat_lit 766012843815972632200276929864326022596798999417489044026333167638642375926016

noncomputable def ep222 := nat_lit 459085839652433281553213478525340329295609700736864604875091510856696340736

noncomputable def ep223 := nat_lit 2297120359768613030037724362635927387131805778850993402869249319894213735096576

noncomputable def ep224 := BSN.cos_dyadic_bound_f 2151477146 2147483648 3 2 1048576 400391 ep221 ep67 ep222 ep223 ep69 ep222 564906 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151477146) qz20 0 2 ep221 ep67 ep222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151477146) qz21 0 2 ep223 ep69 ep222 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz324 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 376589173) qz35)

noncomputable def ep225 := @Enclosure.Real.IsNear.cos_image qz40 qz324 Bool.false 376589173 1048576 759 1048576 Bool.false 564906 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 161743818532275932841 450359962737049600 72265000043359 100000000000000000 376589173 1048576 759 1048576 (ep220 rfl) rfl) (Enclosure.sfrac_false_div 376589173 1048576) (BSN.cos_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151396744908201437167616) qz36) 226375608064910080 72057594037927936 Bool.false 564906 1048576 57 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 376589173 1048576 226375608064910080 72057594037927936 57 151396744908201437167616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 564906 1048576 151396744908201437167616 151115727451828646838272 2151477146 2147483648 400391 400000 (ep224 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep226 := nat_lit 1378455850197028791335255902972966568410801711190890787563499628540870919594240

noncomputable def ep227 := nat_lit 3609498230585161942469822162154442842447525875508282853306034593256132042957056

noncomputable def ep228 := BSN.sin_dyadic_bound_f 2151477146 2147483648 3 2 1048576 400391 ep226 ep60 ep222 ep227 ep63 ep222 883398 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151477146) qz15 0 2 ep226 ep60 ep222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151477146) qz16 0 2 ep227 ep63 ep222 rfl rfl rfl rfl) rfl rfl

noncomputable def ep229 := @Enclosure.Real.IsNear.sin_image qz40 qz324 Bool.false 376589173 1048576 759 1048576 Bool.false 883398 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 161743818532275932841 450359962737049600 72265000043359 100000000000000000 376589173 1048576 759 1048576 (ep220 rfl) rfl) (Enclosure.sfrac_false_div 376589173 1048576) (BSN.sin_reduce0 qz324 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151396744908201437167616) qz36) 226375608064910080 72057594037927936 Bool.false 883398 1048576 57 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 376589173 1048576 226375608064910080 72057594037927936 57 151396744908201437167616 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883398 1048576 151396744908201437167616 151115727451828646838272 2151477146 2147483648 400391 400000 (ep228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz325 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep218 rfl rfl) rfl)

noncomputable def ep230 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 85497675741 549755813888 45292909627 214748364800000 Bool.true 133700962203 549755813888 181420460383 858993459200000 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 302697 1048576 1 1048576 282453 524288 2388259 3276800000 85497675741 549755813888 45292909627 214748364800000 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 564906 1048576 152848576 209715200000 282453 524288 2388259 3276800000 (ep225 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 302697 1048576 1 1048576 441699 524288 2388259 3276800000 133700962203 549755813888 181420460383 858993459200000 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 441699 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 883398 1048576 152848576 209715200000 441699 524288 2388259 3276800000 (ep229 rfl rfl) rfl)) rfl)

noncomputable def ep231 := @ep166 85497675741 549755813888 45292909627 214748364800000 Bool.true 133700962203 549755813888 181420460383 858993459200000 Bool.false ep167 3310851454603 1099511627776 11566686814031 3435973836800000 Bool.true 73832956148726833872896 134301364867 1099511627776 11568240607781 3435973836800000 (ep168 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep216 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep217 ep230) rfl rfl

noncomputable abbrev qz591 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz41 := (@Inv.inv Real Real.instInv (Real.sqrt qz591))

noncomputable abbrev qz592 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz42 := (@HMul.hMul Real Real Real qz267 qz277 qz592)

noncomputable def ep232 := @Enclosure.Complex.IsNear.of_eq qz575 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)))) Bool.false 304947400641 1099511627776 697839807291 3435973836800000 Bool.true 601131141 549755813888 347287977083 1717986918400000 (BSN.cpow_neg_s_mk qz12 144530 1000 13 qz13 rfl)

noncomputable abbrev qz593 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep233 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz591) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz591) (Real.sqrt qz593) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz593) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep234 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 200000 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep235 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz592 144530 1000 0 1 11551497052968677 4503599627370496 5000000003 1000000000000000 166953786906556288681 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 48450490295254733815808 18889465931478580854784 1000000000600000 200000000000000000000 11551497052968677 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep236 := BSN.cos_dyadic_bound_f 8467081 2147483648 1 0 1048576 400391 0 1 1 0 1 1 1048567 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 8467081) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 8467081) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz594 := (@Nat.cast Real Real.instNatCast 131072)

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48589947) qz594)

noncomputable abbrev qz327 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep237 := @Enclosure.Real.IsNear.cos_image qz42 qz326 Bool.false 48589947 131072 759 1048576 Bool.false 1048567 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 166953786906556288681 450359962737049600 72265000043359 100000000000000000 48589947 131072 759 1048576 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 48589947 131072) (BSN.cos_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74477233869814759424) qz327) 226375608064910080 72057594037927936 Bool.false 1048567 1048576 59 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 48589947 131072 226375608064910080 72057594037927936 59 74477233869814759424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048567 1048576 74477233869814759424 18889465931478580854784 8467081 2147483648 400391 400000 (ep236 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep238 := BSN.sin_dyadic_bound_f 8467081 2147483648 1 0 1048576 400391 0 1 1 0 1 1 4134 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 8467081) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 8467081) qz16 0 0 rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz42 qz326 Bool.false 48589947 131072 759 1048576 Bool.false 4134 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 166953786906556288681 450359962737049600 72265000043359 100000000000000000 48589947 131072 759 1048576 (ep235 rfl) rfl) (Enclosure.sfrac_false_div 48589947 131072) (BSN.sin_reduce0 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 74477233869814759424) qz327) 226375608064910080 72057594037927936 Bool.false 4134 1048576 59 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 48589947 131072 226375608064910080 72057594037927936 59 74477233869814759424 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 4134 1048576 74477233869814759424 18889465931478580854784 8467081 2147483648 400391 400000 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz41 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep233 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz42)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42))) Bool.false 304947400641 1099511627776 697839807291 3435973836800000 Bool.true 601131141 549755813888 347287977083 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ff qz41 (Real.cos qz42) 290823 1048576 1 1048576 1048567 1048576 2388259 3276800000 304947400641 1099511627776 697839807291 3435973836800000 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz42) Bool.false 1048567 1048576 152848576 209715200000 1048567 1048576 2388259 3276800000 (ep237 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz41 (@Neg.neg Real Real.instNeg (Real.sin qz42)) 290823 1048576 1 1048576 2067 524288 2388259 3276800000 601131141 549755813888 347287977083 1717986918400000 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz42) Bool.false 2067 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz42) Bool.false 4134 1048576 152848576 209715200000 2067 524288 2388259 3276800000 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep163 304947400641 1099511627776 697839807291 3435973836800000 Bool.true 601131141 549755813888 347287977083 1717986918400000 Bool.false ep164 903949713811 274877906944 6132263310661 1717986918400000 Bool.true 74493906828074588045312 135503627149 1099511627776 12262816561947 3435973836800000 (ep165 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep231 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep232 ep240) rfl rfl

noncomputable abbrev qz595 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz43 := (@Inv.inv Real Real.instInv (Real.sqrt qz595))

noncomputable abbrev qz596 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz44 := (@HMul.hMul Real Real Real qz267 qz277 qz596)

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz574 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)))) Bool.true 40715104255 549755813888 335101643223 1717986918400000 Bool.false 282347905173 1099511627776 672443727071 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 14 qz13 rfl)

noncomputable abbrev qz597 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz595) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz595) (Real.sqrt qz597) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz597) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 200000 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz596 144530 1000 0 1 11885250371606245 4503599627370496 5000000003 1000000000000000 34355504724165011797 90071992547409920 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz597) Bool.false 49850353174629559828480 18889465931478580854784 1000000000600000 200000000000000000000 11885250371606245 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 2107842478620458292846292737226663451518063840314331506274925865367168000000000

noncomputable def ep247 := nat_lit 3468871437773708848239235728278227954304391041743223744611210000000000000000

noncomputable def ep248 := nat_lit 6316589692985827460842399740223433898645582738859508071335555176101504000000000

noncomputable def ep249 := BSN.cos_dyadic_bound_f 2770279100 2147483648 3 2 1048576 400391 ep246 ep67 ep247 ep248 ep69 ep247 290570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2770279100) qz20 0 2 ep246 ep67 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2770279100) qz21 0 2 ep248 ep69 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 399950713) qz35)

noncomputable def ep250 := @Enclosure.Real.IsNear.cos_image qz44 qz329 Bool.false 399950713 1048576 759 1048576 Bool.true 290570 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 34355504724165011797 90071992547409920 72265000043359 100000000000000000 399950713 1048576 759 1048576 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 399950713 1048576) (BSN.cos_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194941061318035296485376) qz36) 226375608064910080 72057594037927936 Bool.false 290570 1048576 60 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 399950713 1048576 226375608064910080 72057594037927936 60 194941061318035296485376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 290570 1048576 194941061318035296485376 151115727451828646838272 2770279100 2147483648 400391 400000 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep251 := nat_lit 3791341364366605960044735538425371630369071399732402132299177589660902400000000

noncomputable def ep252 := nat_lit 9924087305299001033410491457077808567612027509041087984244666013873792000000000

noncomputable def ep253 := BSN.sin_dyadic_bound_f 2770279100 2147483648 3 2 1048576 400391 ep251 ep60 ep247 ep252 ep63 ep247 1007511 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2770279100) qz15 0 2 ep251 ep60 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2770279100) qz16 0 2 ep252 ep63 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz44 qz329 Bool.false 399950713 1048576 759 1048576 Bool.true 1007511 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 34355504724165011797 90071992547409920 72265000043359 100000000000000000 399950713 1048576 759 1048576 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 399950713 1048576) (BSN.sin_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 194941061318035296485376) qz36) 226375608064910080 72057594037927936 Bool.false 1007511 1048576 60 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 399950713 1048576 226375608064910080 72057594037927936 60 194941061318035296485376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1007511 1048576 194941061318035296485376 151115727451828646838272 2770279100 2147483648 400391 400000 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep243 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz44)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44))) Bool.true 40715104255 549755813888 335101643223 1717986918400000 Bool.false 282347905173 1099511627776 672443727071 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz44) 280243 1048576 1 1048576 145285 524288 2388259 3276800000 40715104255 549755813888 335101643223 1717986918400000 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz44) Bool.true 290570 1048576 152848576 209715200000 145285 524288 2388259 3276800000 (ep250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz44)) 280243 1048576 1 1048576 1007511 1048576 2388259 3276800000 282347905173 1099511627776 672443727071 3435973836800000 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz44) Bool.true 1007511 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz44) Bool.true 1007511 1048576 152848576 209715200000 1007511 1048576 2388259 3276800000 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep161 40715104255 549755813888 335101643223 1717986918400000 Bool.false 282347905173 1099511627776 672443727071 3435973836800000 Bool.false 485759927991369830760448 1767184323367 549755813888 1616841238471 429496729600000 Bool.false 161456991159759744794624 18355534753 137438953472 6467630144509 1717986918400000 (ep162 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep255) rfl rfl

noncomputable abbrev qz598 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz45 := (@Inv.inv Real Real.instInv (Real.sqrt qz598))

noncomputable abbrev qz599 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz46 := (@HMul.hMul Real Real Real qz267 qz277 qz599)

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz573 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)))) Bool.true 74611617003 1099511627776 646617146303 3435973836800000 Bool.true 136956230037 549755813888 324458777839 1717986918400000 (BSN.cpow_neg_s_mk qz12 144530 1000 15 qz13 rfl)

noncomputable abbrev qz600 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz598) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz598) (Real.sqrt qz600) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz600) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 200000 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz599 144530 1000 0 1 12195965485668069 4503599627370496 5000000003 1000000000000000 176268289164360601257 450359962737049600 72265000043359 100000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz600) Bool.false 51153586820399524478976 18889465931478580854784 1000000000600000 200000000000000000000 12195965485668069 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 106379686464765909133794408821769361

noncomputable def ep262 := BSN.sin_dyadic_bound_f 571103309 2147483648 2 1 1048576 400391 ep261 ep147 ep261 ep261 ep148 ep261 275583 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 571103309) qz15 0 1 ep261 ep147 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 571103309) qz16 0 1 ep261 ep148 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6412603) (@Nat.cast Real Real.instNatCast 16384))

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz46 qz331 Bool.false 6412603 16384 379 524288 Bool.true 275583 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 176268289164360601257 450359962737049600 72265000043359 100000000000000000 6412603 16384 379 524288 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 6412603 16384) (BSN.cos_reduce1 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 627934729461391425536) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 275583 1048576 62 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 6412603 16384 226375608064910080 72057594037927936 62 627934729461391425536 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 275583 1048576 627934729461391425536 2361183241434822606848 571103309 2147483648 400391 400000 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := BSN.cos_dyadic_bound_f 571103309 2147483648 2 1 1048576 400391 ep261 ep80 ep261 ep261 ep81 ep261 1011714 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 571103309) qz20 0 1 ep261 ep80 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 571103309) qz21 0 1 ep261 ep81 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep265 := @Enclosure.Real.IsNear.sin_image qz46 qz331 Bool.false 6412603 16384 379 524288 Bool.false 1011714 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 176268289164360601257 450359962737049600 72265000043359 100000000000000000 6412603 16384 379 524288 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 6412603 16384) (BSN.sin_reduce1 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 627934729461391425536) (@Nat.cast Real Real.instNatCast 2361183241434822606848)) 226375608064910080 72057594037927936 Bool.false 1011714 1048576 62 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 6412603 16384 226375608064910080 72057594037927936 62 627934729461391425536 2361183241434822606848 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011714 1048576 627934729461391425536 2361183241434822606848 571103309 2147483648 400391 400000 (ep264 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep258 rfl rfl) rfl)

noncomputable def ep266 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz46)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46))) Bool.true 74611617003 1099511627776 646617146303 3435973836800000 Bool.true 136956230037 549755813888 324458777839 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ft qz45 (Real.cos qz46) 270741 1048576 1 1048576 275583 1048576 1192567 1638400000 74611617003 1099511627776 646617146303 3435973836800000 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz46) Bool.true 275583 1048576 76324288 104857600000 275583 1048576 1192567 1638400000 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz46)) 270741 1048576 1 1048576 505857 524288 1192567 1638400000 136956230037 549755813888 324458777839 1717986918400000 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz46) Bool.false 505857 524288 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz46) Bool.false 1011714 1048576 76324288 104857600000 505857 524288 1192567 1638400000 (ep265 rfl rfl) rfl)) rfl)

noncomputable def ep267 := @ep158 74611617003 1099511627776 646617146303 3435973836800000 Bool.true 136956230037 549755813888 324458777839 1717986918400000 Bool.false ep159 3459757029731 1099511627776 13581347054071 3435973836800000 Bool.true 8732058980270787788800 63534091025 549755813888 1698022230587 429496729600000 (ep160 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep266) rfl rfl

noncomputable abbrev qz601 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz47 := (@Inv.inv Real Real.instInv (Real.sqrt qz601))

noncomputable abbrev qz602 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz48 := (@HMul.hMul Real Real Real qz267 qz277 qz602)

noncomputable def ep268 := @Enclosure.Complex.IsNear.of_eq qz572 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)))) Bool.false 11570729877 274877906944 156654876199 858993459200000 Bool.false 67738013343 274877906944 157324444949 858993459200000 (BSN.cpow_neg_s_mk qz12 144530 1000 16 qz13 rfl)

noncomputable abbrev qz603 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep269 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz601) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz601) (Real.sqrt qz603) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz603) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep270 := BSN.log_dyadic_bound 0 32 1 0 1 524288 200000 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep271 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz602 144530 1000 0 1 3121657384082679 1125899906842624 1250000001 250000000000000 45117314172146959587 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 52372720210750067441664 18889465931478580854784 1000000000800000 200000000000000000000 3121657384082679 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep272 := nat_lit 17424265018910355113911071514034176

noncomputable def ep273 := BSN.sin_dyadic_bound_f 363319424 2147483648 2 1 1048576 400391 ep272 ep147 ep272 ep272 ep148 ep272 176556 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 363319424) qz15 0 1 ep272 ep147 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 363319424) qz16 0 1 ep272 ep148 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz333 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 420187731) qz35)

noncomputable def ep274 := @Enclosure.Real.IsNear.cos_image qz48 qz333 Bool.false 420187731 1048576 759 1048576 Bool.false 176556 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 45117314172146959587 112589990684262400 18066250014453 25000000000000000 420187731 1048576 759 1048576 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 420187731 1048576) (BSN.cos_reduce3 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25566331652990966956032) qz36) 226375608064910080 72057594037927936 Bool.false 176556 1048576 63 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 420187731 1048576 226375608064910080 72057594037927936 63 25566331652990966956032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 176556 1048576 25566331652990966956032 151115727451828646838272 363319424 2147483648 400391 400000 (ep273 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep275 := BSN.cos_dyadic_bound_f 363319424 2147483648 2 1 1048576 400391 ep272 ep80 ep272 ep272 ep81 ep272 1033604 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 363319424) qz20 0 1 ep272 ep80 ep272 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 363319424) qz21 0 1 ep272 ep81 ep272 rfl rfl rfl rfl) rfl rfl

noncomputable def ep276 := @Enclosure.Real.IsNear.sin_image qz48 qz333 Bool.false 420187731 1048576 759 1048576 Bool.true 1033604 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 45117314172146959587 112589990684262400 18066250014453 25000000000000000 420187731 1048576 759 1048576 (ep271 rfl) rfl) (Enclosure.sfrac_false_div 420187731 1048576) (BSN.sin_reduce3 qz333 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25566331652990966956032) qz36) 226375608064910080 72057594037927936 Bool.false 1033604 1048576 63 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 420187731 1048576 226375608064910080 72057594037927936 63 25566331652990966956032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1033604 1048576 25566331652990966956032 151115727451828646838272 363319424 2147483648 400391 400000 (ep275 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz334 := (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep269 rfl rfl) rfl)

noncomputable def ep277 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz48)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48))) Bool.false 11570729877 274877906944 156654876199 858993459200000 Bool.false 67738013343 274877906944 157324444949 858993459200000 (@Enclosure.Real.IsNear.mulLit_ff qz47 (Real.cos qz48) 262143 1048576 1 1048576 44139 262144 2388259 3276800000 11570729877 274877906944 156654876199 858993459200000 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz48) Bool.false 176556 1048576 152848576 209715200000 44139 262144 2388259 3276800000 (ep274 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz48)) 262143 1048576 1 1048576 258401 262144 2388259 3276800000 67738013343 274877906944 157324444949 858993459200000 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz48) Bool.true 258401 262144 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz48) Bool.true 1033604 1048576 152848576 209715200000 258401 262144 2388259 3276800000 (ep276 rfl rfl) rfl)) rfl)

noncomputable def ep278 := @ep156 11570729877 274877906944 156654876199 858993459200000 Bool.false 67738013343 274877906944 157324444949 858993459200000 Bool.false 963732922908864325615616 3506039949239 1099511627776 14207966558867 3435973836800000 Bool.false 19775248695995593129984 71941935661 549755813888 3553368906123 858993459200000 (ep157 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep267 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep268 ep277) rfl rfl

theorem EMRow51.d7 : Enclosure.Complex.IsNear qz31 Bool.false 3506039949239 1099511627776 14207966558867 3435973836800000 Bool.false 71941935661 549755813888 3553368906123 858993459200000 := ep155 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep278 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz49 := (BSN.headSumC qz271 25)

noncomputable abbrev qz604 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq qz49 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz604) Bool.false 4313657170945 1099511627776 746973508127 137438953472000 Bool.true 217394862351 1099511627776 746945331627 137438953472000

noncomputable def ep280 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz604 Bool.false 2067592622807 549755813888 1816054903119 343597383680000 Bool.true 40654540095 549755813888 454011586561 85899345920000 Bool.false

noncomputable def ep281 := nat_lit 2371458108846676021084160

noncomputable abbrev qz605 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz605) Bool.false 2067592622807 549755813888 1816054903119 343597383680000 Bool.true 40654540095 549755813888 454011586561 85899345920000

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz605 Bool.false 3972741586405 1099511627776 17636048771019 3435973836800000 Bool.false 80474277159 1099511627776 17635972639769 3435973836800000 Bool.false

noncomputable def ep284 := nat_lit 4546684260560347504574464

noncomputable abbrev qz606 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep285 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz606) Bool.false 3972741586405 1099511627776 17636048771019 3435973836800000 Bool.false 80474277159 1099511627776 17635972639769 3435973836800000

noncomputable def ep286 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz606 Bool.false 3785008701427 1099511627776 17099510134247 3435973836800000 Bool.false 110428559433 549755813888 4275023971843 858993459200000 Bool.false

noncomputable def ep287 := nat_lit 2184037784200785050992640

noncomputable abbrev qz607 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz607) Bool.false 3785008701427 1099511627776 17099510134247 3435973836800000 Bool.false 110428559433 549755813888 4275023971843 858993459200000

noncomputable def ep289 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz607 Bool.false 3549939622485 1099511627776 16547323028617 3435973836800000 Bool.false 67230714191 274877906944 8276508322121 1717986918400000 Bool.false

noncomputable def ep290 := nat_lit 2080830539226162372018176

noncomputable abbrev qz608 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep291 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz608) Bool.false 3549939622485 1099511627776 16547323028617 3435973836800000 Bool.false 67230714191 274877906944 8276508322121 1717986918400000

noncomputable def ep292 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz608 Bool.false 1671259600397 549755813888 3996145861003 858993459200000 Bool.false 136926422993 1099511627776 15991282309637 3435973836800000 Bool.false

noncomputable def ep293 := nat_lit 1951599946412500640071680

noncomputable abbrev qz609 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz609) Bool.false 1671259600397 549755813888 3996145861003 858993459200000 Bool.false 136926422993 1099511627776 15991282309637 3435973836800000

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz609 Bool.false 1687114844087 549755813888 240775811273 53687091200000 Bool.true 56658380335 549755813888 240836123773 53687091200000 Bool.true

noncomputable abbrev qz610 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz610) Bool.false 1687114844087 549755813888 240775811273 53687091200000 Bool.true 56658380335 549755813888 240836123773 53687091200000

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz610 Bool.false 3632418204683 1099511627776 14816896723729 3435973836800000 Bool.true 90938967677 1099511627776 14823738336229 3435973836800000 Bool.true

noncomputable def ep298 := nat_lit 3710004776934299637121024

noncomputable abbrev qz611 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz31 qz611) Bool.false 3632418204683 1099511627776 14816896723729 3435973836800000 Bool.true 90938967677 1099511627776 14823738336229 3435973836800000

noncomputable def ep300 := @Enclosure.Complex.IsNear.addLitP qz31 qz611 Bool.false 3506039949239 1099511627776 14207966558867 3435973836800000 Bool.false 71941935661 549755813888 3553368906123 858993459200000 Bool.false

noncomputable abbrev qz612 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz612))

noncomputable abbrev qz613 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz277 qz613)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq qz611 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 31594563861 274877906944 304465082431 1717986918400000 Bool.true 234822838999 1099511627776 610262711737 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 17 qz13 rfl)

noncomputable abbrev qz614 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep302 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz612) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz612) (Real.sqrt qz614) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz614) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep303 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 200000 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep304 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz613 144530 1000 0 1 3189913004350711 1125899906842624 1250000001 250000000000000 46103812651880826083 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 53517859495200818200576 18889465931478580854784 1000000000800000 200000000000000000000 3189913004350711 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep305 := nat_lit 1023457060987369766432946589594702923596300048345969454528433908725056942530816

noncomputable def ep306 := nat_lit 819193038144323593032706376836280365176844936384286916445033699811112673536

noncomputable def ep307 := nat_lit 3068732796885820652112774356030436210058546455165139789752411658775548602245376

noncomputable def ep308 := BSN.cos_dyadic_bound_f 2312987478 2147483648 3 2 1048576 400391 ep305 ep67 ep306 ep307 ep69 ep306 496932 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2312987478) qz20 0 2 ep305 ep67 ep306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2312987478) qz21 0 2 ep307 ep69 ep306 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 214687607) qz25)

noncomputable def ep309 := @Enclosure.Real.IsNear.cos_image qz51 qz335 Bool.false 214687607 524288 759 1048576 Bool.false 496932 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 46103812651880826083 112589990684262400 18066250014453 25000000000000000 214687607 524288 759 1048576 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 214687607 524288) (BSN.cos_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81381012065181870587904) qz26) 226375608064910080 72057594037927936 Bool.false 496932 1048576 65 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 214687607 524288 226375608064910080 72057594037927936 65 81381012065181870587904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 496932 1048576 81381012065181870587904 75557863725914323419136 2312987478 2147483648 400391 400000 (ep308 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep310 := nat_lit 1841567355346750120704877696168996238181198611073637588618025008745253606416640

noncomputable def ep311 := nat_lit 4821826284798778554124055298689636169883329089581571505658678301675970024857856

noncomputable def ep312 := BSN.sin_dyadic_bound_f 2312987478 2147483648 3 2 1048576 400391 ep310 ep60 ep306 ep311 ep63 ep306 923347 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2312987478) qz15 0 2 ep310 ep60 ep306 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2312987478) qz16 0 2 ep311 ep63 ep306 rfl rfl rfl rfl) rfl rfl

noncomputable def ep313 := @Enclosure.Real.IsNear.sin_image qz51 qz335 Bool.false 214687607 524288 759 1048576 Bool.false 923347 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 46103812651880826083 112589990684262400 18066250014453 25000000000000000 214687607 524288 759 1048576 (ep304 rfl) rfl) (Enclosure.sfrac_false_div 214687607 524288) (BSN.sin_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81381012065181870587904) qz26) 226375608064910080 72057594037927936 Bool.false 923347 1048576 65 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 214687607 524288 226375608064910080 72057594037927936 65 81381012065181870587904 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 923347 1048576 81381012065181870587904 75557863725914323419136 2312987478 2147483648 400391 400000 (ep312 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz336 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep302 rfl rfl) rfl)

noncomputable def ep314 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 31594563861 274877906944 304465082431 1717986918400000 Bool.true 234822838999 1099511627776 610262711737 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 254317 1048576 1 1048576 124233 262144 2388259 3276800000 31594563861 274877906944 304465082431 1717986918400000 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 496932 1048576 152848576 209715200000 124233 262144 2388259 3276800000 (ep309 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 254317 1048576 1 1048576 923347 1048576 2388259 3276800000 234822838999 1099511627776 610262711737 3435973836800000 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.false 923347 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.false 923347 1048576 152848576 209715200000 923347 1048576 2388259 3276800000 (ep313 rfl rfl) rfl)) rfl)

noncomputable def ep315 := @ep300 31594563861 274877906944 304465082431 1717986918400000 Bool.true 234822838999 1099511627776 610262711737 3435973836800000 Bool.false 998471513248545219018752 3632418204683 1099511627776 14816896723729 3435973836800000 Bool.true 49994226189403659698176 90938967677 1099511627776 14823738336229 3435973836800000 EMRow51.d7 (ep301 ep314) rfl rfl

noncomputable abbrev qz615 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz615))

noncomputable abbrev qz616 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz277 qz616)

noncomputable def ep316 := @Enclosure.Complex.IsNear.of_eq qz610 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.true 258188516509 1099511627776 592755197743 3435973836800000 Bool.true 22377792993 1099511627776 589773585243 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 18 qz13 rfl)

noncomputable abbrev qz617 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep317 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz615) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz615) (Real.sqrt qz617) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz617) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep318 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 200000 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep319 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz616 144530 1000 0 1 3254268794313975 1125899906842624 1250000001 250000000000000 1881357875368795227 4503599627370496 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz617) Bool.false 54597570484265130393600 18889465931478580854784 1000000000800000 200000000000000000000 3254268794313975 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep318 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep320 := nat_lit 6650438643660222586536180107238859646490709384616819122122733742619147651030625

noncomputable def ep321 := nat_lit 10658715541863907528013951444390772316799475020605640170331486805983250390625

noncomputable def ep322 := nat_lit 17400558527280422352549401502334666395153230190629736188140908823459509061590625

noncomputable def ep323 := BSN.sin_dyadic_bound_f 3187594795 2147483648 3 2 1048576 400391 ep320 ep60 ep321 ep322 ep63 ep321 1044659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3187594795) qz15 0 2 ep320 ep60 ep321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3187594795) qz16 0 2 ep322 ep63 ep321 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz337 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 438037765) qz35)

noncomputable def ep324 := @Enclosure.Real.IsNear.cos_image qz53 qz337 Bool.false 438037765 1048576 379 524288 Bool.true 1044659 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 1881357875368795227 4503599627370496 18066250014453 25000000000000000 438037765 1048576 379 524288 (ep319 rfl) rfl) (Enclosure.sfrac_false_div 438037765 1048576) (BSN.cos_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224307042700701340794880) qz36) 226375608064910080 72057594037927936 Bool.false 1044659 1048576 66 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 438037765 1048576 226375608064910080 72057594037927936 66 224307042700701340794880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044659 1048576 224307042700701340794880 151115727451828646838272 3187594795 2147483648 400391 400000 (ep323 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep325 := nat_lit 3699425342274285395865884037996873480191193869240724241254999406702185695190625

noncomputable def ep326 := nat_lit 11076958595739128372541624211101838895939982657680961443424335246494590584790625

noncomputable def ep327 := BSN.cos_dyadic_bound_f 3187594795 2147483648 3 2 1048576 400391 ep325 ep67 ep321 ep326 ep69 ep321 90543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3187594795) qz20 0 2 ep325 ep67 ep321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3187594795) qz21 0 2 ep326 ep69 ep321 rfl rfl rfl rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz53 qz337 Bool.false 438037765 1048576 379 524288 Bool.false 90543 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 1881357875368795227 4503599627370496 18066250014453 25000000000000000 438037765 1048576 379 524288 (ep319 rfl) rfl) (Enclosure.sfrac_false_div 438037765 1048576) (BSN.sin_reduce1 qz337 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224307042700701340794880) qz36) 226375608064910080 72057594037927936 Bool.false 90543 1048576 66 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 438037765 1048576 226375608064910080 72057594037927936 66 224307042700701340794880 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 90543 1048576 224307042700701340794880 151115727451828646838272 3187594795 2147483648 400391 400000 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz338 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep317 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.true 258188516509 1099511627776 592755197743 3435973836800000 Bool.true 22377792993 1099511627776 589773585243 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz53) 247151 1048576 1 1048576 1044659 1048576 1192567 1638400000 258188516509 1099511627776 592755197743 3435973836800000 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.true 1044659 1048576 76324288 104857600000 1044659 1048576 1192567 1638400000 (ep324 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 247151 1048576 1 1048576 90543 1048576 1192567 1638400000 22377792993 1099511627776 589773585243 3435973836800000 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.false 90543 1048576 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.false 90543 1048576 76324288 104857600000 90543 1048576 1192567 1638400000 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep297 258188516509 1099511627776 592755197743 3435973836800000 Bool.true 22377792993 1099511627776 589773585243 3435973836800000 Bool.false ep298 1687114844087 549755813888 240775811273 53687091200000 Bool.true 124593095978575116369920 56658380335 549755813888 240836123773 53687091200000 (ep299 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep315 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep316 ep329) rfl rfl

noncomputable abbrev qz618 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz618))

noncomputable abbrev qz619 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz277 qz619)

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq qz609 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.true 7927621845 274877906944 28746576127 171798691840000 Bool.false 250243183663 1099511627776 115554077633 687194767360000 (BSN.cpow_neg_s_mk qz12 144530 1000 19 qz13 rfl)

noncomputable abbrev qz620 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz618) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz618) (Real.sqrt qz620) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz620) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 200000 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz619 144530 1000 0 1 3315143513283831 1125899906842624 1250000001 250000000000000 47913769197491209443 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 55618878793361701994496 18889465931478580854784 1000000000800000 200000000000000000000 3315143513283831 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 3319270386931495579538105560126194985802097683521483327382063930040168203943936

noncomputable def ep336 := nat_lit 8585748040176877100939863460881514377413526183539407010507570842392231673856

noncomputable def ep337 := nat_lit 9940639664714132984412436953456821928651465998197371168125176648435720148484096

noncomputable def ep338 := BSN.cos_dyadic_bound_f 3102574848 2147483648 3 2 1048576 400391 ep335 ep67 ep336 ep337 ep69 ep336 131820 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3102574848) qz20 0 2 ep335 ep67 ep336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3102574848) qz21 0 2 ep337 ep69 ep336 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111557937) qz17)

noncomputable def ep339 := @Enclosure.Real.IsNear.cos_image qz55 qz339 Bool.false 111557937 262144 759 1048576 Bool.true 131820 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 47913769197491209443 112589990684262400 18066250014453 25000000000000000 111557937 262144 759 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 111557937 262144) (BSN.cos_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54581073956177826545664) qz19) 226375608064910080 72057594037927936 Bool.false 131820 1048576 67 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 111557937 262144 226375608064910080 72057594037927936 67 54581073956177826545664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 131820 1048576 54581073956177826545664 37778931862957161709568 3102574848 2147483648 400391 400000 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep340 := nat_lit 5967818098044550541487838117458445762941845009391838463679309017398388981760000

noncomputable def ep341 := nat_lit 15616099045670679331447578147740216451093781696490989317333558978489050386661376

noncomputable def ep342 := BSN.sin_dyadic_bound_f 3102574848 2147483648 3 2 1048576 400391 ep340 ep60 ep336 ep341 ep63 ep336 1040257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3102574848) qz15 0 2 ep340 ep60 ep336 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3102574848) qz16 0 2 ep341 ep63 ep336 rfl rfl rfl rfl) rfl rfl

noncomputable def ep343 := @Enclosure.Real.IsNear.sin_image qz55 qz339 Bool.false 111557937 262144 759 1048576 Bool.true 1040257 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 47913769197491209443 112589990684262400 18066250014453 25000000000000000 111557937 262144 759 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 111557937 262144) (BSN.sin_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54581073956177826545664) qz19) 226375608064910080 72057594037927936 Bool.false 1040257 1048576 67 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 111557937 262144 226375608064910080 72057594037927936 67 54581073956177826545664 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040257 1048576 54581073956177826545664 37778931862957161709568 3102574848 2147483648 400391 400000 (ep342 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep332 rfl rfl) rfl)

noncomputable def ep344 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.true 7927621845 274877906944 28746576127 171798691840000 Bool.false 250243183663 1099511627776 115554077633 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz55) 240559 1048576 1 1048576 32955 262144 2388259 3276800000 7927621845 274877906944 28746576127 171798691840000 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.true 131820 1048576 152848576 209715200000 32955 262144 2388259 3276800000 (ep339 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 240559 1048576 1 1048576 1040257 1048576 2388259 3276800000 250243183663 1099511627776 115554077633 687194767360000 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.true 1040257 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.true 1040257 1048576 152848576 209715200000 1040257 1048576 2388259 3276800000 (ep343 rfl rfl) rfl)) rfl)

noncomputable def ep345 := @ep295 7927621845 274877906944 28746576127 171798691840000 Bool.false 250243183663 1099511627776 115554077633 687194767360000 Bool.false 459392340917193191456768 1671259600397 549755813888 3996145861003 858993459200000 Bool.false 75276097115289271926784 136926422993 1099511627776 15991282309637 3435973836800000 (ep296 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep344) rfl rfl

noncomputable abbrev qz621 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz621))

noncomputable abbrev qz622 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz277 qz622)

noncomputable def ep346 := @Enclosure.Complex.IsNear.of_eq qz608 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 207420421691 1099511627776 112547916921 687194767360000 Bool.false 131996433771 1099511627776 112346866921 687194767360000 (BSN.cpow_neg_s_mk qz12 144530 1000 20 qz13 rfl)

noncomputable abbrev qz623 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep347 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz621) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz621) (Real.sqrt qz623) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz623) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep348 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 200000 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep349 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz622 144530 1000 0 1 3372893643545847 1125899906842624 1250000001 250000000000000 48748431830168126691 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz623) Bool.false 56587765202795681021952 18889465931478580854784 1000000000800000 200000000000000000000 3372893643545847 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep350 := nat_lit 1390616551671224802839765178025666929981176829269616275094300282763788267577600

noncomputable def ep351 := nat_lit 467218911024753391201017679481960184852258450854566378579163157687814349056

noncomputable def ep352 := nat_lit 3641334518997262978137440485252823547746654705833325708253086857364141382328576

noncomputable def ep353 := BSN.sin_dyadic_bound_f 2156205014 2147483648 3 2 1048576 400391 ep350 ep60 ep351 ep352 ep63 ep351 884639 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2156205014) qz15 0 2 ep350 ep60 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2156205014) qz16 0 2 ep352 ep63 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 227002575) qz25)

noncomputable def ep354 := @Enclosure.Real.IsNear.cos_image qz57 qz341 Bool.false 227002575 524288 759 1048576 Bool.false 884639 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 48748431830168126691 112589990684262400 18066250014453 25000000000000000 227002575 524288 759 1048576 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 227002575 524288) (BSN.cos_reduce3 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75864719516294866534400) qz26) 226375608064910080 72057594037927936 Bool.false 884639 1048576 68 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 227002575 524288 226375608064910080 72057594037927936 68 75864719516294866534400 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 884639 1048576 75864719516294866534400 75557863725914323419136 2156205014 2147483648 400391 400000 (ep353 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep355 := nat_lit 772772403777802558640403328982918054516143686683499960109535340716632510587136

noncomputable def ep356 := nat_lit 2317382773511358169138807951589790243178726543148790747571447695834521903063296

noncomputable def ep357 := BSN.cos_dyadic_bound_f 2156205014 2147483648 3 2 1048576 400391 ep355 ep67 ep351 ep356 ep69 ep351 562959 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2156205014) qz20 0 2 ep355 ep67 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2156205014) qz21 0 2 ep356 ep69 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep358 := @Enclosure.Real.IsNear.sin_image qz57 qz341 Bool.false 227002575 524288 759 1048576 Bool.true 562959 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 48748431830168126691 112589990684262400 18066250014453 25000000000000000 227002575 524288 759 1048576 (ep349 rfl) rfl) (Enclosure.sfrac_false_div 227002575 524288) (BSN.sin_reduce3 qz341 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 75864719516294866534400) qz26) 226375608064910080 72057594037927936 Bool.false 562959 1048576 68 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 227002575 524288 226375608064910080 72057594037927936 68 75864719516294866534400 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 562959 1048576 75864719516294866534400 75557863725914323419136 2156205014 2147483648 400391 400000 (ep357 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz342 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep347 rfl rfl) rfl)

noncomputable def ep359 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 207420421691 1099511627776 112547916921 687194767360000 Bool.false 131996433771 1099511627776 112346866921 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 234469 1048576 1 1048576 884639 1048576 2388259 3276800000 207420421691 1099511627776 112547916921 687194767360000 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 884639 1048576 152848576 209715200000 884639 1048576 2388259 3276800000 (ep354 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 234469 1048576 1 1048576 562959 1048576 2388259 3276800000 131996433771 1099511627776 112346866921 687194767360000 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.true 562959 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.true 562959 1048576 152848576 209715200000 562959 1048576 2388259 3276800000 (ep358 rfl rfl) rfl)) rfl)

noncomputable def ep360 := @ep292 207420421691 1099511627776 112547916921 687194767360000 Bool.false 131996433771 1099511627776 112346866921 687194767360000 Bool.false ep293 3549939622485 1099511627776 16547323028617 3435973836800000 Bool.false 295683807986757731876864 67230714191 274877906944 8276508322121 1717986918400000 (ep294 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep345 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep346 ep359) rfl rfl

noncomputable abbrev qz624 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz624))

noncomputable abbrev qz625 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz277 qz625)

noncomputable def ep361 := @Enclosure.Complex.IsNear.of_eq qz607 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.false 117534539471 549755813888 55218710563 343597383680000 Bool.true 24032868949 549755813888 54707924313 343597383680000 (BSN.cpow_neg_s_mk qz12 144530 1000 21 qz13 rfl)

noncomputable abbrev qz626 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep362 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz624) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz624) (Real.sqrt qz626) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz626) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep363 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 200000 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep364 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz625 144530 1000 0 1 3427826275261687 1125899906842624 1250000001 250000000000000 49542373156357162211 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 57509381830540779323392 18889465931478580854784 1000000000800000 200000000000000000000 3427826275261687 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep363 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep365 := nat_lit 35196739367020235600627165984856241

noncomputable def ep366 := BSN.cos_dyadic_bound_f 433137323 2147483648 2 1 1048576 400391 ep365 ep80 ep365 ep365 ep81 ep365 1027319 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 433137323) qz20 0 1 ep365 ep80 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 433137323) qz21 0 1 ep365 ep81 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 461399305) qz35)

noncomputable def ep367 := @Enclosure.Real.IsNear.cos_image qz59 qz343 Bool.false 461399305 1048576 379 524288 Bool.false 1027319 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 49542373156357162211 112589990684262400 18066250014453 25000000000000000 461399305 1048576 379 524288 (ep364 rfl) rfl) (Enclosure.sfrac_false_div 461399305 1048576) (BSN.cos_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30479329508264048066560) qz36) 226375608064910080 72057594037927936 Bool.false 1027319 1048576 70 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 461399305 1048576 226375608064910080 72057594037927936 70 30479329508264048066560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1027319 1048576 30479329508264048066560 151115727451828646838272 433137323 2147483648 400391 400000 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep368 := BSN.sin_dyadic_bound_f 433137323 2147483648 2 1 1048576 400391 ep365 ep147 ep365 ep365 ep148 ep365 210061 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 433137323) qz15 0 1 ep365 ep147 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 433137323) qz16 0 1 ep365 ep148 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable def ep369 := @Enclosure.Real.IsNear.sin_image qz59 qz343 Bool.false 461399305 1048576 379 524288 Bool.false 210061 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 49542373156357162211 112589990684262400 18066250014453 25000000000000000 461399305 1048576 379 524288 (ep364 rfl) rfl) (Enclosure.sfrac_false_div 461399305 1048576) (BSN.sin_reduce0 qz343 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30479329508264048066560) qz36) 226375608064910080 72057594037927936 Bool.false 210061 1048576 70 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 461399305 1048576 226375608064910080 72057594037927936 70 30479329508264048066560 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 210061 1048576 30479329508264048066560 151115727451828646838272 433137323 2147483648 400391 400000 (ep368 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz344 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep362 rfl rfl) rfl)

noncomputable def ep370 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.false 117534539471 549755813888 55218710563 343597383680000 Bool.true 24032868949 549755813888 54707924313 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz59) 114409 524288 1 524288 1027319 1048576 1192567 1638400000 117534539471 549755813888 55218710563 343597383680000 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.false 1027319 1048576 76324288 104857600000 1027319 1048576 1192567 1638400000 (ep367 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 114409 524288 1 524288 210061 1048576 1192567 1638400000 24032868949 549755813888 54707924313 343597383680000 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 210061 1048576 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 210061 1048576 76324288 104857600000 210061 1048576 1192567 1638400000 (ep369 rfl rfl) rfl)) rfl)

noncomputable def ep371 := @ep289 117534539471 549755813888 55218710563 343597383680000 Bool.true 24032868949 549755813888 54707924313 343597383680000 Bool.false ep290 3785008701427 1099511627776 17099510134247 3435973836800000 Bool.false 30354371283784147402752 110428559433 549755813888 4275023971843 858993459200000 (ep291 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep360 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep361 ep370) rfl rfl

noncomputable abbrev qz627 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz267 qz277 qz627)

noncomputable abbrev qz345 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable def ep372 := @Enclosure.Complex.IsNear.of_eq qz606 (Complex.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 93866442489 549755813888 134134659193 858993459200000 Bool.true 140382841707 1099511627776 535876752397 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 22 qz13 rfl)

noncomputable abbrev qz346 := (Real.sqrt (@Nat.cast Real Real.instNatCast 22))

noncomputable abbrev qz347 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz628 := (@HDiv.hDiv Real Real Real qz1 qz347 qz14)

noncomputable def ep373 := @Enclosure.Real.IsNear.inv_image qz346 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq qz346 (Real.sqrt qz628) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz628) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep374 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 200000 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep375 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz627 144530 1000 0 1 3480203401436407 1125899906842624 1250000001 250000000000000 50299379760960390371 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz628) Bool.false 58388124189833310502912 18889465931478580854784 1000000000800000 200000000000000000000 3480203401436407 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep376 := nat_lit 129165257381538430906429867138039284782913040191880012551569041027529662300416

noncomputable def ep377 := nat_lit 13066102778970217181929346902013911103980618551473750054759295200715899136

noncomputable def ep378 := nat_lit 387469639939057352284925742720313826526531159338537090154597604492187555102976

noncomputable def ep379 := BSN.cos_dyadic_bound_f 1378853922 2147483648 3 2 1048576 400391 ep376 ep67 ep377 ep378 ep69 ep377 839754 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1378853922) qz20 0 2 ep376 ep67 ep377 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1378853922) qz21 0 2 ep378 ep69 ep377 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 234224739) qz25)

noncomputable def ep380 := @Enclosure.Real.IsNear.cos_image qz60 qz348 Bool.false 234224739 524288 759 1048576 Bool.false 839754 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 50299379760960390371 112589990684262400 18066250014453 25000000000000000 234224739 524288 759 1048576 (ep375 rfl) rfl) (Enclosure.sfrac_false_div 234224739 524288) (BSN.cos_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48514109480750230274048) qz26) 226375608064910080 72057594037927936 Bool.false 839754 1048576 71 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 234224739 524288 226375608064910080 72057594037927936 71 48514109480750230274048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 839754 1048576 48514109480750230274048 75557863725914323419136 1378853922 2147483648 400391 400000 (ep379 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep381 := nat_lit 3614706458202410822965970527607383056

noncomputable def ep382 := BSN.sin_dyadic_bound_f 1378853922 2147483648 2 1 1048576 400391 ep381 ep147 ep381 ep381 ep148 ep381 627951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1378853922) qz15 0 1 ep381 ep147 ep381 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1378853922) qz16 0 1 ep381 ep148 ep381 rfl rfl rfl rfl) rfl rfl

noncomputable def ep383 := @Enclosure.Real.IsNear.sin_image qz60 qz348 Bool.false 234224739 524288 759 1048576 Bool.false 627951 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 50299379760960390371 112589990684262400 18066250014453 25000000000000000 234224739 524288 759 1048576 (ep375 rfl) rfl) (Enclosure.sfrac_false_div 234224739 524288) (BSN.sin_reduce0 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48514109480750230274048) qz26) 226375608064910080 72057594037927936 Bool.false 627951 1048576 71 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 234224739 524288 226375608064910080 72057594037927936 71 48514109480750230274048 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 627951 1048576 48514109480750230274048 75557863725914323419136 1378853922 2147483648 400391 400000 (ep382 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22))) Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep373 rfl rfl) rfl)

noncomputable def ep384 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 93866442489 549755813888 134134659193 858993459200000 Bool.true 140382841707 1099511627776 535876752397 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz345 (Real.cos qz60) 223557 1048576 1 1048576 419877 524288 2388259 3276800000 93866442489 549755813888 134134659193 858993459200000 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 839754 1048576 152848576 209715200000 419877 524288 2388259 3276800000 (ep380 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz345 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 627951 1048576 2388259 3276800000 140382841707 1099511627776 535876752397 3435973836800000 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 627951 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 627951 1048576 152848576 209715200000 627951 1048576 2388259 3276800000 (ep383 rfl rfl) rfl)) rfl)

noncomputable def ep385 := @ep286 93866442489 549755813888 134134659193 858993459200000 Bool.true 140382841707 1099511627776 535876752397 3435973836800000 Bool.false ep287 3972741586405 1099511627776 17636048771019 3435973836800000 Bool.false 44241201736594533384192 80474277159 1099511627776 17635972639769 3435973836800000 (ep288 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep371 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep372 ep384) rfl rfl

noncomputable abbrev qz629 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz277 qz629)

noncomputable abbrev qz350 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23)))

noncomputable def ep386 := @Enclosure.Complex.IsNear.of_eq qz605 (Complex.mk (@HMul.hMul Real Real Real qz0 qz350 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz350 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.false 162443659209 1099511627776 524500260171 3435973836800000 Bool.true 161783357349 1099511627776 524490822671 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 23 qz13 rfl)

noncomputable abbrev qz351 := (Real.sqrt (@Nat.cast Real Real.instNatCast 23))

noncomputable abbrev qz352 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz630 := (@HDiv.hDiv Real Real Real qz1 qz352 qz14)

noncomputable def ep387 := @Enclosure.Real.IsNear.inv_image qz351 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq qz351 (Real.sqrt qz630) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz630) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep388 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 200000 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep389 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz629 144530 1000 0 1 3530250507853047 1125899906842624 1250000001 250000000000000 51022710590000088291 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz630) Bool.false 59227775304360265777152 18889465931478580854784 1000000000800000 200000000000000000000 3530250507853047 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep390 := nat_lit 286216532210809588940211401128086374424056110485629702550279221528266177126656

noncomputable def ep391 := nat_lit 64141227949288329561369055935026688388187144315588190632870142625474027776

noncomputable def ep392 := nat_lit 858521314176530190161511465272389069895391957168257931269571924299547583324416

noncomputable def ep393 := BSN.cos_dyadic_bound_f 1682256282 2147483648 3 2 1048576 400391 ep390 ep67 ep391 ep392 ep69 ep391 742963 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1682256282) qz20 0 2 ep390 ep67 ep391 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1682256282) qz21 0 2 ep392 ep69 ep391 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 475186021) qz35)

noncomputable def ep394 := @Enclosure.Real.IsNear.cos_image qz61 qz353 Bool.false 475186021 1048576 759 1048576 Bool.false 742963 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 51022710590000088291 112589990684262400 18066250014453 25000000000000000 475186021 1048576 759 1048576 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 475186021 1048576) (BSN.cos_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118378261978506195894272) qz36) 226375608064910080 72057594037927936 Bool.false 742963 1048576 72 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 475186021 1048576 226375608064910080 72057594037927936 72 118378261978506195894272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 742963 1048576 118378261978506195894272 151115727451828646838272 1682256282 2147483648 400391 400000 (ep393 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep395 := nat_lit 8008821882729589683040771790598498576

noncomputable def ep396 := BSN.sin_dyadic_bound_f 1682256282 2147483648 2 1 1048576 400391 ep395 ep147 ep395 ep395 ep148 ep395 739943 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1682256282) qz15 0 1 ep395 ep147 ep395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1682256282) qz16 0 1 ep395 ep148 ep395 rfl rfl rfl rfl) rfl rfl

noncomputable def ep397 := @Enclosure.Real.IsNear.sin_image qz61 qz353 Bool.false 475186021 1048576 759 1048576 Bool.false 739943 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 51022710590000088291 112589990684262400 18066250014453 25000000000000000 475186021 1048576 759 1048576 (ep389 rfl) rfl) (Enclosure.sfrac_false_div 475186021 1048576) (BSN.sin_reduce0 qz353 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118378261978506195894272) qz36) 226375608064910080 72057594037927936 Bool.false 739943 1048576 72 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 475186021 1048576 226375608064910080 72057594037927936 72 118378261978506195894272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 739943 1048576 118378261978506195894272 151115727451828646838272 1682256282 2147483648 400391 400000 (ep396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz354 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 23))) Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep387 rfl rfl) rfl)

noncomputable def ep398 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz350 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz350 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.false 162443659209 1099511627776 524500260171 3435973836800000 Bool.true 161783357349 1099511627776 524490822671 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz350 (Real.cos qz61) 218643 1048576 1 1048576 742963 1048576 2388259 3276800000 162443659209 1099511627776 524500260171 3435973836800000 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.false 742963 1048576 152848576 209715200000 742963 1048576 2388259 3276800000 (ep394 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz350 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 218643 1048576 1 1048576 739943 1048576 2388259 3276800000 161783357349 1099511627776 524490822671 3435973836800000 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.false 739943 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.false 739943 1048576 152848576 209715200000 739943 1048576 2388259 3276800000 (ep397 rfl rfl) rfl)) rfl)

noncomputable def ep399 := @ep283 162443659209 1099511627776 524500260171 3435973836800000 Bool.true 161783357349 1099511627776 524490822671 3435973836800000 Bool.false ep284 2067592622807 549755813888 1816054903119 343597383680000 Bool.true 89400279112676215357440 40654540095 549755813888 454011586561 85899345920000 (ep285 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep385 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep386 ep398) rfl rfl

noncomputable abbrev qz631 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz277 qz631)

noncomputable abbrev qz355 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24)))

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq qz604 (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 178471925331 1099511627776 102757734397 687194767360000 Bool.true 136085782161 1099511627776 102633965647 687194767360000 (BSN.cpow_neg_s_mk qz12 144530 1000 24 qz13 rfl)

noncomputable abbrev qz356 := (Real.sqrt (@Nat.cast Real Real.instNatCast 24))

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz632 := (@HDiv.hDiv Real Real Real qz1 qz357 qz14)

noncomputable def ep401 := @Enclosure.Real.IsNear.inv_image qz356 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq qz356 (Real.sqrt qz632) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz632) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep402 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 200000 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep403 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz631 144530 1000 0 1 3578169457974519 1125899906842624 1250000001 250000000000000 51715283176105723107 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz632) Bool.false 60031721881041427759104 18889465931478580854784 1000000000800000 200000000000000000000 3578169457974519 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep402 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep404 := nat_lit 136879068787492297759651892500511320366728883327461141735653596013752552625281

noncomputable def ep405 := nat_lit 14673154142704994753229804579511418498415484880189892049594726526154806401

noncomputable def ep406 := nat_lit 410607860054191483289449217892374938263189819012623045422861598588205348263041

noncomputable def ep407 := BSN.cos_dyadic_bound_f 1398992657 2147483648 3 2 1048576 400391 ep404 ep67 ep405 ep406 ep69 ep405 833829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1398992657) qz20 0 2 ep404 ep67 ep405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1398992657) qz21 0 2 ep406 ep69 ep405 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240818053) qz25)

noncomputable def ep408 := @Enclosure.Real.IsNear.cos_image qz62 qz358 Bool.false 240818053 524288 759 1048576 Bool.false 833829 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 51715283176105723107 112589990684262400 18066250014453 25000000000000000 240818053 524288 759 1048576 (ep403 rfl) rfl) (Enclosure.sfrac_false_div 240818053 524288) (BSN.cos_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49222678224839204929536) qz26) 226375608064910080 72057594037927936 Bool.false 833829 1048576 73 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 240818053 524288 226375608064910080 72057594037927936 73 49222678224839204929536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 833829 1048576 49222678224839204929536 75557863725914323419136 1398992657 2147483648 400391 400000 (ep407 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep409 := nat_lit 3830555330850214302022226659776283201

noncomputable def ep410 := BSN.sin_dyadic_bound_f 1398992657 2147483648 2 1 1048576 400391 ep409 ep147 ep409 ep409 ep148 ep409 635799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1398992657) qz15 0 1 ep409 ep147 ep409 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1398992657) qz16 0 1 ep409 ep148 ep409 rfl rfl rfl rfl) rfl rfl

noncomputable def ep411 := @Enclosure.Real.IsNear.sin_image qz62 qz358 Bool.false 240818053 524288 759 1048576 Bool.false 635799 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 51715283176105723107 112589990684262400 18066250014453 25000000000000000 240818053 524288 759 1048576 (ep403 rfl) rfl) (Enclosure.sfrac_false_div 240818053 524288) (BSN.sin_reduce0 qz358 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49222678224839204929536) qz26) 226375608064910080 72057594037927936 Bool.false 635799 1048576 73 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 240818053 524288 226375608064910080 72057594037927936 73 49222678224839204929536 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 635799 1048576 49222678224839204929536 75557863725914323419136 1398992657 2147483648 400391 400000 (ep410 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz359 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 24))) Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep401 rfl rfl) rfl)

noncomputable def ep412 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 178471925331 1099511627776 102757734397 687194767360000 Bool.true 136085782161 1099511627776 102633965647 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz355 (Real.cos qz62) 214039 1048576 1 1048576 833829 1048576 2388259 3276800000 178471925331 1099511627776 102757734397 687194767360000 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 833829 1048576 152848576 209715200000 833829 1048576 2388259 3276800000 (ep408 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz355 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 214039 1048576 1 1048576 635799 1048576 2388259 3276800000 136085782161 1099511627776 102633965647 687194767360000 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 635799 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 635799 1048576 152848576 209715200000 635799 1048576 2388259 3276800000 (ep411 rfl rfl) rfl)) rfl)

noncomputable def ep413 := @ep280 178471925331 1099511627776 102757734397 687194767360000 Bool.true 136085782161 1099511627776 102633965647 687194767360000 Bool.false ep281 4313657170945 1099511627776 746973508127 137438953472000 Bool.true 119514089486843734130688 217394862351 1099511627776 746945331627 137438953472000 (ep282 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep399 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep400 ep412) rfl rfl

theorem EMRow51.d8 : Enclosure.Complex.IsNear qz49 Bool.false 4313657170945 1099511627776 746973508127 137438953472000 Bool.true 217394862351 1099511627776 746945331627 137438953472000 := ep279 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep413 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz63 := (BSN.headSumC qz271 33)

noncomputable abbrev qz633 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq qz63 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz633) Bool.false 2334933179085 549755813888 5613101549413 858993459200000 Bool.false 13532537381 137438953472 5612543574413 858993459200000

noncomputable def ep415 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz633 Bool.false 4704896813999 1099511627776 22009118384501 3435973836800000 Bool.true 82924025967 1099511627776 22004253915751 3435973836800000 Bool.true

noncomputable def ep416 := nat_lit 5134572360967877736529920

noncomputable abbrev qz634 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep417 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz634) Bool.false 4704896813999 1099511627776 22009118384501 3435973836800000 Bool.true 82924025967 1099511627776 22004253915751 3435973836800000

noncomputable def ep418 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz634 Bool.false 4507746483639 1099511627776 21556066192031 3435973836800000 Bool.true 94282147957 1099511627776 21554284629531 3435973836800000 Bool.false

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep419 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz635) Bool.false 4507746483639 1099511627776 21556066192031 3435973836800000 Bool.true 94282147957 1099511627776 21554284629531 3435973836800000

noncomputable def ep420 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz635 Bool.false 2245405813651 549755813888 65934906763 10737418240000 Bool.false 52872290917 549755813888 2109439992041 343597383680000 Bool.false

noncomputable def ep421 := nat_lit 2478159836913728520978432

noncomputable abbrev qz636 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep422 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz636) Bool.false 2245405813651 549755813888 65934906763 10737418240000 Bool.false 52872290917 549755813888 2109439992041 343597383680000

noncomputable def ep423 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz636 Bool.false 4687488770357 1099511627776 20630981434091 3435973836800000 Bool.false 160561332779 1099511627776 20628487921591 3435973836800000 Bool.true

noncomputable def ep424 := nat_lit 4937699602370209463140352

noncomputable abbrev qz637 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz637) Bool.false 4687488770357 1099511627776 20630981434091 3435973836800000 Bool.false 160561332779 1099511627776 20628487921591 3435973836800000

noncomputable def ep426 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz637 Bool.false 4810105693541 1099511627776 4031156165523 687194767360000 Bool.true 7192365893 1099511627776 4030515103023 687194767360000 Bool.true

noncomputable abbrev qz638 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep427 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz638) Bool.false 4810105693541 1099511627776 4031156165523 687194767360000 Bool.true 7192365893 1099511627776 4030515103023 687194767360000

noncomputable def ep428 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz638 Bool.false 2364260288815 549755813888 1967256675829 343597383680000 Bool.true 202433301991 1099511627776 3933520281033 687194767360000 Bool.false

noncomputable def ep429 := nat_lit 2644383570439935159697408

noncomputable abbrev qz639 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep430 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz639) Bool.false 2364260288815 549755813888 1967256675829 343597383680000 Bool.true 202433301991 1099511627776 3933520281033 687194767360000

noncomputable def ep431 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz639 Bool.false 1131425264005 274877906944 2397294191343 429496729600000 Bool.true 137827788393 549755813888 4793839392061 858993459200000 Bool.false

noncomputable abbrev qz640 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep432 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz49 qz640) Bool.false 1131425264005 274877906944 2397294191343 429496729600000 Bool.true 137827788393 549755813888 4793839392061 858993459200000

noncomputable def ep433 := @Enclosure.Complex.IsNear.addLitP qz49 qz640 Bool.false 4313657170945 1099511627776 746973508127 137438953472000 Bool.true 217394862351 1099511627776 746945331627 137438953472000 Bool.false

noncomputable def ep434 := nat_lit 4976060934932112364011520

noncomputable abbrev qz641 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz277 qz641)

noncomputable abbrev qz360 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25)))

noncomputable def ep435 := @Enclosure.Complex.IsNear.of_eq qz640 (Complex.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz360 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 212043885075 1099511627776 504015827569 3435973836800000 Bool.true 58260714435 1099511627776 501724277569 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 25 qz13 rfl)

noncomputable abbrev qz361 := (Real.sqrt (@Nat.cast Real Real.instNatCast 25))

noncomputable abbrev qz362 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz642 := (@HDiv.hDiv Real Real Real qz1 qz362 qz14)

noncomputable def ep436 := @Enclosure.Real.IsNear.inv_image qz361 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq qz361 (Real.sqrt qz642) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz642) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep437 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 200000 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep438 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz641 144530 1000 0 1 3624129903009015 1125899906842624 1250000001 250000000000000 10475909897637858759 22517998136852480 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz642) Bool.false 60802810194841294602240 18889465931478580854784 1000000000800000 200000000000000000000 3624129903009015 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep437 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep439 := nat_lit 109944756459039496428636992283646881

noncomputable def ep440 := BSN.cos_dyadic_bound_f 575829129 2147483648 2 1 1048576 400391 ep439 ep80 ep439 ep439 ep81 ep439 1011105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 575829129) qz20 0 1 ep439 ep80 ep439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 575829129) qz21 0 1 ep439 ep81 ep439 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 60977821) qz594)

noncomputable def ep441 := @Enclosure.Real.IsNear.cos_image qz64 qz363 Bool.false 60977821 131072 759 1048576 Bool.false 1011105 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 10475909897637858759 22517998136852480 18066250014453 25000000000000000 60977821 131072 759 1048576 (ep438 rfl) rfl) (Enclosure.sfrac_false_div 60977821 131072) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5065046586841158909952) qz327) 226375608064910080 72057594037927936 Bool.false 1011105 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 60977821 131072 226375608064910080 72057594037927936 74 5065046586841158909952 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1011105 1048576 5065046586841158909952 18889465931478580854784 575829129 2147483648 400391 400000 (ep440 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep442 := BSN.sin_dyadic_bound_f 575829129 2147483648 2 1 1048576 400391 ep439 ep147 ep439 ep439 ep148 ep439 277809 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 575829129) qz15 0 1 ep439 ep147 ep439 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 575829129) qz16 0 1 ep439 ep148 ep439 rfl rfl rfl rfl) rfl rfl

noncomputable def ep443 := @Enclosure.Real.IsNear.sin_image qz64 qz363 Bool.false 60977821 131072 759 1048576 Bool.false 277809 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 10475909897637858759 22517998136852480 18066250014453 25000000000000000 60977821 131072 759 1048576 (ep438 rfl) rfl) (Enclosure.sfrac_false_div 60977821 131072) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5065046586841158909952) qz327) 226375608064910080 72057594037927936 Bool.false 277809 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 60977821 131072 226375608064910080 72057594037927936 74 5065046586841158909952 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 277809 1048576 5065046586841158909952 18889465931478580854784 575829129 2147483648 400391 400000 (ep442 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 25))) Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep436 rfl rfl) rfl)

noncomputable def ep444 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz360 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 212043885075 1099511627776 504015827569 3435973836800000 Bool.true 58260714435 1099511627776 501724277569 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz360 (Real.cos qz64) 209715 1048576 1 1048576 1011105 1048576 2388259 3276800000 212043885075 1099511627776 504015827569 3435973836800000 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 1011105 1048576 152848576 209715200000 1011105 1048576 2388259 3276800000 (ep441 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz360 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 209715 1048576 1 1048576 277809 1048576 2388259 3276800000 58260714435 1099511627776 501724277569 3435973836800000 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.false 277809 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.false 277809 1048576 152848576 209715200000 277809 1048576 2388259 3276800000 (ep443 rfl rfl) rfl)) rfl)

noncomputable def ep445 := @ep433 212043885075 1099511627776 504015827569 3435973836800000 Bool.true 58260714435 1099511627776 501724277569 3435973836800000 Bool.false ep434 1131425264005 274877906944 2397294191343 429496729600000 Bool.true 303086511937507018407936 137827788393 549755813888 4793839392061 858993459200000 EMRow51.d8 (ep435 ep444) rfl rfl

noncomputable abbrev qz643 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz267 qz277 qz643)

noncomputable abbrev qz365 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26)))

noncomputable def ep446 := @Enclosure.Complex.IsNear.of_eq qz639 (Complex.mk (@HMul.hMul Real Real Real qz0 qz365 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz365 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.false 101409760805 549755813888 247106613773 1717986918400000 Bool.false 73222274795 1099511627776 492243836921 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 26 qz13 rfl)

noncomputable abbrev qz366 := (Real.sqrt (@Nat.cast Real Real.instNatCast 26))

noncomputable abbrev qz367 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz644 := (@HDiv.hDiv Real Real Real qz1 qz367 qz14)

noncomputable def ep447 := @Enclosure.Real.IsNear.inv_image qz366 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq qz366 (Real.sqrt qz644) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz644) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep448 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 200000 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep449 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz643 144530 1000 0 1 3668288609262839 1125899906842624 1250000001 250000000000000 53017775269675812067 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz644) Bool.false 61543670347942250676224 18889465931478580854784 1000000000800000 200000000000000000000 3668288609262839 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep448 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep450 := nat_lit 3075714999523853569914205420592108590124400800091478451240262548480695712252160

noncomputable def ep451 := nat_lit 2283728717470096652536358797677837724238387647848360776317198290695433912576

noncomputable def ep452 := nat_lit 8051746580829426812337860092068805998772282801190689073896174067835934258135296

noncomputable def ep453 := BSN.sin_dyadic_bound_f 2629242018 2147483648 3 2 1048576 400391 ep450 ep60 ep451 ep452 ep63 ep451 986270 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2629242018) qz15 0 2 ep450 ep60 ep451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2629242018) qz16 0 2 ep452 ep63 ep451 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz368 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 493766509) qz35)

noncomputable def ep454 := @Enclosure.Real.IsNear.cos_image qz65 qz368 Bool.false 493766509 1048576 759 1048576 Bool.false 986270 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 53017775269675812067 112589990684262400 18066250014453 25000000000000000 493766509 1048576 759 1048576 (ep449 rfl) rfl) (Enclosure.sfrac_false_div 493766509 1048576) (BSN.cos_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185016459014706642812928) qz36) 226375608064910080 72057594037927936 Bool.false 986270 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 493766509 1048576 226375608064910080 72057594037927936 74 185016459014706642812928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 986270 1048576 185016459014706642812928 151115727451828646838272 2629242018 2147483648 400391 400000 (ep453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep455 := nat_lit 1709745545832127581797908059794583811279884172338753966589620170618473366323456

noncomputable def ep456 := nat_lit 5124669180061442552088651461788395758391175741720565178216226115274029231145216

noncomputable def ep457 := BSN.cos_dyadic_bound_f 2629242018 2147483648 3 2 1048576 400391 ep455 ep67 ep451 ep456 ep69 ep451 356065 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2629242018) qz20 0 2 ep455 ep67 ep451 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2629242018) qz21 0 2 ep456 ep69 ep451 rfl rfl rfl rfl) rfl rfl

noncomputable def ep458 := @Enclosure.Real.IsNear.sin_image qz65 qz368 Bool.false 493766509 1048576 759 1048576 Bool.true 356065 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 53017775269675812067 112589990684262400 18066250014453 25000000000000000 493766509 1048576 759 1048576 (ep449 rfl) rfl) (Enclosure.sfrac_false_div 493766509 1048576) (BSN.sin_reduce3 qz368 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185016459014706642812928) qz36) 226375608064910080 72057594037927936 Bool.false 356065 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 493766509 1048576 226375608064910080 72057594037927936 74 185016459014706642812928 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 356065 1048576 185016459014706642812928 151115727451828646838272 2629242018 2147483648 400391 400000 (ep457 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz369 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 26))) Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep447 rfl rfl) rfl)

noncomputable def ep459 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz365 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz365 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.false 101409760805 549755813888 247106613773 1717986918400000 Bool.false 73222274795 1099511627776 492243836921 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz365 (Real.cos qz65) 205643 1048576 1 1048576 493135 524288 2388259 3276800000 101409760805 549755813888 247106613773 1717986918400000 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.false 986270 1048576 152848576 209715200000 493135 524288 2388259 3276800000 (ep454 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz365 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 205643 1048576 1 1048576 356065 1048576 2388259 3276800000 73222274795 1099511627776 492243836921 3435973836800000 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.true 356065 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.true 356065 1048576 152848576 209715200000 356065 1048576 2388259 3276800000 (ep458 rfl rfl) rfl)) rfl)

noncomputable def ep460 := @ep431 101409760805 549755813888 247106613773 1717986918400000 Bool.false 73222274795 1099511627776 492243836921 3435973836800000 Bool.false 649882919660284134031360 2364260288815 549755813888 1967256675829 343597383680000 Bool.true 111288884694097495851008 202433301991 1099511627776 3933520281033 687194767360000 (ep432 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep445 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep446 ep459) rfl rfl

noncomputable abbrev qz645 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz66 := (@HMul.hMul Real Real Real qz267 qz277 qz645)

noncomputable abbrev qz370 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27)))

noncomputable def ep461 := @Enclosure.Complex.IsNear.of_eq qz638 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz66)))) Bool.false 81585115911 1099511627776 19328562773 137438953472000 Bool.false 97620468049 549755813888 9699482199 68719476736000 (BSN.cpow_neg_s_mk qz12 144530 1000 27 qz13 rfl)

noncomputable abbrev qz371 := (Real.sqrt (@Nat.cast Real Real.instNatCast 27))

noncomputable abbrev qz372 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz646 := (@HDiv.hDiv Real Real Real qz1 qz372 qz14)

noncomputable def ep462 := @Enclosure.Real.IsNear.inv_image qz371 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq qz371 (Real.sqrt qz646) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz646) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep463 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 200000 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep464 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz645 144530 1000 0 1 3710780868205815 1125899906842624 1250000001 250000000000000 10726383177635728839 22517998136852480 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz646) Bool.false 62256572154556490711040 18889465931478580854784 1000000000800000 200000000000000000000 3710780868205815 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep465 := nat_lit 522022350087210518052011302408567056

noncomputable def ep466 := BSN.sin_dyadic_bound_f 850006554 2147483648 2 1 1048576 400391 ep465 ep147 ep465 ep465 ep148 ep465 404289 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 850006554) qz15 0 1 ep465 ep147 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 850006554) qz16 0 1 ep465 ep148 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 499486139) qz35)

noncomputable def ep467 := @Enclosure.Real.IsNear.cos_image qz66 qz373 Bool.false 499486139 1048576 759 1048576 Bool.false 404289 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 10726383177635728839 22517998136852480 18066250014453 25000000000000000 499486139 1048576 759 1048576 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 499486139 1048576) (BSN.cos_reduce3 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59813893779929555795968) qz36) 226375608064910080 72057594037927936 Bool.false 404289 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 499486139 1048576 226375608064910080 72057594037927936 75 59813893779929555795968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 404289 1048576 59813893779929555795968 151115727451828646838272 850006554 2147483648 400391 400000 (ep466 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep468 := BSN.cos_dyadic_bound_f 850006554 2147483648 2 1 1048576 400391 ep465 ep80 ep465 ep465 ep81 ep465 967502 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 850006554) qz20 0 1 ep465 ep80 ep465 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 850006554) qz21 0 1 ep465 ep81 ep465 rfl rfl rfl rfl) rfl rfl

noncomputable def ep469 := @Enclosure.Real.IsNear.sin_image qz66 qz373 Bool.false 499486139 1048576 759 1048576 Bool.true 967502 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 10726383177635728839 22517998136852480 18066250014453 25000000000000000 499486139 1048576 759 1048576 (ep464 rfl) rfl) (Enclosure.sfrac_false_div 499486139 1048576) (BSN.sin_reduce3 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59813893779929555795968) qz36) 226375608064910080 72057594037927936 Bool.false 967502 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 499486139 1048576 226375608064910080 72057594037927936 75 59813893779929555795968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 967502 1048576 59813893779929555795968 151115727451828646838272 850006554 2147483648 400391 400000 (ep468 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz374 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 27))) Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep462 rfl rfl) rfl)

noncomputable def ep470 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz66)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz66))) Bool.false 81585115911 1099511627776 19328562773 137438953472000 Bool.false 97620468049 549755813888 9699482199 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz66) 201799 1048576 1 1048576 404289 1048576 2388259 3276800000 81585115911 1099511627776 19328562773 137438953472000 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz66) Bool.false 404289 1048576 152848576 209715200000 404289 1048576 2388259 3276800000 (ep467 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 (@Neg.neg Real Real.instNeg (Real.sin qz66)) 201799 1048576 1 1048576 483751 524288 2388259 3276800000 97620468049 549755813888 9699482199 68719476736000 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz66) Bool.true 483751 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz66) Bool.true 967502 1048576 152848576 209715200000 483751 524288 2388259 3276800000 (ep469 rfl rfl) rfl)) rfl)

noncomputable def ep471 := @ep428 81585115911 1099511627776 19328562773 137438953472000 Bool.false 97620468049 549755813888 9699482199 68719476736000 Bool.false ep429 4810105693541 1099511627776 4031156165523 687194767360000 Bool.true 3954044965286506921984 7192365893 1099511627776 4030515103023 687194767360000 (ep430 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep460 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep461 ep470) rfl rfl

noncomputable abbrev qz647 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz277 qz647)

noncomputable abbrev qz375 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28)))

noncomputable def ep472 := @Enclosure.Complex.IsNear.of_eq qz637 (Complex.mk (@HMul.hMul Real Real Real qz0 qz375 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz375 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.true 7663557699 68719476736 118800151619 858993459200000 Bool.false 10484606167 68719476736 118978101619 858993459200000 (BSN.cpow_neg_s_mk qz12 144530 1000 28 qz13 rfl)

noncomputable abbrev qz376 := (Real.sqrt (@Nat.cast Real Real.instNatCast 28))

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz648 := (@HDiv.hDiv Real Real Real qz1 qz377 qz14)

noncomputable def ep473 := @Enclosure.Real.IsNear.inv_image qz376 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq qz376 (Real.sqrt qz648) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz648) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep474 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 200000 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz647 144530 1000 0 1 3751726938922231 1125899906842624 1250000001 250000000000000 54223709448243004643 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz648) Bool.false 62943533227317076688896 18889465931478580854784 1000000000800000 200000000000000000000 3751726938922231 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep476 := nat_lit 592567766868779640312269871447670591536016669796797170766314172271348406091776

noncomputable def ep477 := nat_lit 274799326653203750103953218192135871210844079554343980549877793355003396096

noncomputable def ep478 := nat_lit 1777153701953032513436601707906627502865628321231282824337842761227335211483136

noncomputable def ep479 := BSN.cos_dyadic_bound_f 2017794612 2147483648 3 2 1048576 400391 ep476 ep67 ep477 ep478 ep69 ep477 618768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2017794612) qz20 0 2 ep476 ep67 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2017794612) qz21 0 2 ep478 ep69 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252498823) qz25)

noncomputable def ep480 := @Enclosure.Real.IsNear.cos_image qz67 qz378 Bool.false 252498823 524288 759 1048576 Bool.true 618768 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 54223709448243004643 112589990684262400 18066250014453 25000000000000000 252498823 524288 759 1048576 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 252498823 524288) (BSN.cos_reduce2 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70994836429756134588416) qz26) 226375608064910080 72057594037927936 Bool.false 618768 1048576 76 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 252498823 524288 226375608064910080 72057594037927936 76 70994836429756134588416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 618768 1048576 70994836429756134588416 75557863725914323419136 2017794612 2147483648 400391 400000 (ep479 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep481 := nat_lit 1066402140902480789562002606031253356067861330370591432194925607853743128248320

noncomputable def ep482 := nat_lit 2792513074882392118971743282014304855433866879603699098827724408903895330390016

noncomputable def ep483 := BSN.sin_dyadic_bound_f 2017794612 2147483648 3 2 1048576 400391 ep481 ep60 ep477 ep482 ep63 ep477 846544 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2017794612) qz15 0 2 ep481 ep60 ep477 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2017794612) qz16 0 2 ep482 ep63 ep477 rfl rfl rfl rfl) rfl rfl

noncomputable def ep484 := @Enclosure.Real.IsNear.sin_image qz67 qz378 Bool.false 252498823 524288 759 1048576 Bool.true 846544 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 54223709448243004643 112589990684262400 18066250014453 25000000000000000 252498823 524288 759 1048576 (ep475 rfl) rfl) (Enclosure.sfrac_false_div 252498823 524288) (BSN.sin_reduce2 qz378 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70994836429756134588416) qz26) 226375608064910080 72057594037927936 Bool.false 846544 1048576 76 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 252498823 524288 226375608064910080 72057594037927936 76 70994836429756134588416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 846544 1048576 70994836429756134588416 75557863725914323419136 2017794612 2147483648 400391 400000 (ep483 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz379 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 28))) Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep473 rfl rfl) rfl)

noncomputable def ep485 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz375 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz375 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.true 7663557699 68719476736 118800151619 858993459200000 Bool.false 10484606167 68719476736 118978101619 858993459200000 (@Enclosure.Real.IsNear.mulLit_ft qz375 (Real.cos qz67) 198163 1048576 1 1048576 38673 65536 2388259 3276800000 7663557699 68719476736 118800151619 858993459200000 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.true 618768 1048576 152848576 209715200000 38673 65536 2388259 3276800000 (ep480 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz375 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 198163 1048576 1 1048576 52909 65536 2388259 3276800000 10484606167 68719476736 118978101619 858993459200000 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 52909 65536 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 846544 1048576 152848576 209715200000 52909 65536 2388259 3276800000 (ep484 rfl rfl) rfl)) rfl)

noncomputable def ep486 := @ep426 7663557699 68719476736 118800151619 858993459200000 Bool.false 10484606167 68719476736 118978101619 858993459200000 Bool.false 322121775504809107914752 4687488770357 1099511627776 20630981434091 3435973836800000 Bool.false 11033690772607644729344 160561332779 1099511627776 20628487921591 3435973836800000 (ep427 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep471 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep472 ep485) rfl rfl

noncomputable abbrev qz649 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz68 := (@HMul.hMul Real Real Real qz267 qz277 qz649)

noncomputable abbrev qz380 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep487 := @Enclosure.Complex.IsNear.of_eq qz636 (Complex.mk (@HMul.hMul Real Real Real qz0 qz380 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz380 (@Neg.neg Real Real.instNeg (Real.sin qz68)))) Bool.true 196677143055 1099511627776 468188730069 3435973836800000 Bool.true 54816750945 1099511627776 465911998819 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 29 qz13 rfl)

noncomputable abbrev qz381 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz382 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz650 := (@HDiv.hDiv Real Real Real qz1 qz382 qz14)

noncomputable def ep488 := @Enclosure.Real.IsNear.inv_image qz381 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz381 (Real.sqrt qz650) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz650) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep489 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 200000 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep490 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz649 144530 1000 0 1 3791236343078135 1125899906842624 1250000001 250000000000000 10958947773301657031 22517998136852480 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz650) Bool.false 63606391034871975772160 18889465931478580854784 1000000000800000 200000000000000000000 3791236343078135 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep489 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep491 := nat_lit 3897977403596259163462750066172215390806997589679156930769600462216203815004705

noncomputable def ep492 := nat_lit 3666559437780966776277086679573426808536884110095756914808190541096331422241

noncomputable def ep493 := nat_lit 10203052103662366720002753937731730951566410160600494069391645092547330216995361

noncomputable def ep494 := BSN.sin_dyadic_bound_f 2789538381 2147483648 3 2 1048576 400391 ep491 ep60 ep492 ep493 ep63 ep492 1010077 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2789538381) qz15 0 2 ep491 ep60 ep492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2789538381) qz16 0 2 ep493 ep63 ep492 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 127578943) qz17)

noncomputable def ep495 := @Enclosure.Real.IsNear.cos_image qz68 qz383 Bool.false 127578943 262144 759 1048576 Bool.true 1010077 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 10958947773301657031 22517998136852480 18066250014453 25000000000000000 127578943 262144 759 1048576 (ep490 rfl) rfl) (Enclosure.sfrac_false_div 127578943 262144) (BSN.cos_reduce1 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49074078188449474543616) qz19) 226375608064910080 72057594037927936 Bool.false 1010077 1048576 77 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 127578943 262144 226375608064910080 72057594037927936 77 49074078188449474543616 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1010077 1048576 49074078188449474543616 37778931862957161709568 2789538381 2147483648 400391 400000 (ep494 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep496 := nat_lit 2167172583970268853824317630842152295696570609426240853500803897027267155634721

noncomputable def ep497 := nat_lit 6494184633035244627920398719167310033472638060058531046672795309999608804059681

noncomputable def ep498 := BSN.cos_dyadic_bound_f 2789538381 2147483648 3 2 1048576 400391 ep496 ep67 ep492 ep497 ep69 ep492 281523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2789538381) qz20 0 2 ep496 ep67 ep492 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2789538381) qz21 0 2 ep497 ep69 ep492 rfl rfl rfl rfl) rfl rfl

noncomputable def ep499 := @Enclosure.Real.IsNear.sin_image qz68 qz383 Bool.false 127578943 262144 759 1048576 Bool.false 281523 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 10958947773301657031 22517998136852480 18066250014453 25000000000000000 127578943 262144 759 1048576 (ep490 rfl) rfl) (Enclosure.sfrac_false_div 127578943 262144) (BSN.sin_reduce1 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49074078188449474543616) qz19) 226375608064910080 72057594037927936 Bool.false 281523 1048576 77 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 127578943 262144 226375608064910080 72057594037927936 77 49074078188449474543616 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 281523 1048576 49074078188449474543616 37778931862957161709568 2789538381 2147483648 400391 400000 (ep498 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz384 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep488 rfl rfl) rfl)

noncomputable def ep500 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz380 (Real.cos qz68)) (@HMul.hMul Real Real Real qz0 qz380 (@Neg.neg Real Real.instNeg (Real.sin qz68))) Bool.true 196677143055 1099511627776 468188730069 3435973836800000 Bool.true 54816750945 1099511627776 465911998819 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz380 (Real.cos qz68) 194715 1048576 1 1048576 1010077 1048576 2388259 3276800000 196677143055 1099511627776 468188730069 3435973836800000 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz68) Bool.true 1010077 1048576 152848576 209715200000 1010077 1048576 2388259 3276800000 (ep495 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz380 (@Neg.neg Real Real.instNeg (Real.sin qz68)) 194715 1048576 1 1048576 281523 1048576 2388259 3276800000 54816750945 1099511627776 465911998819 3435973836800000 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz68) Bool.false 281523 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz68) Bool.false 281523 1048576 152848576 209715200000 281523 1048576 2388259 3276800000 (ep499 rfl rfl) rfl)) rfl)

noncomputable def ep501 := @ep423 196677143055 1099511627776 468188730069 3435973836800000 Bool.true 54816750945 1099511627776 465911998819 3435973836800000 Bool.false ep424 2245405813651 549755813888 65934906763 10737418240000 Bool.false 116267397300793779421184 52872290917 549755813888 2109439992041 343597383680000 (ep425 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep486 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep487 ep500) rfl rfl

noncomputable abbrev qz651 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz277 qz651)

noncomputable abbrev qz385 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz385 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz385 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 16934856337 1099511627776 456896027871 3435973836800000 Bool.true 200026729791 1099511627776 459884709121 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 30 qz13 rfl)

noncomputable abbrev qz386 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz387 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz652 := (@HDiv.hDiv Real Real Real qz1 qz387 qz14)

noncomputable def ep503 := @Enclosure.Real.IsNear.inv_image qz386 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz386 (Real.sqrt qz652) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz652) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep504 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 200000 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep505 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz651 144530 1000 0 1 3829405717437687 1125899906842624 1250000001 250000000000000 55346400834126890211 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 64246766873087041339392 18889465931478580854784 1000000000800000 200000000000000000000 3829405717437687 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep504 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep506 := nat_lit 3719408152214410031044434761775215225852794199701674450331835177667677869947841

noncomputable def ep507 := nat_lit 10773840355033650775547514567869673566851909288236741250504063522535562394561

noncomputable def ep508 := nat_lit 11136676775933162791582209256189906330424678780528549868494497405957962485054401

noncomputable def ep509 := BSN.cos_dyadic_bound_f 3191878247 2147483648 3 2 1048576 400391 ep506 ep67 ep507 ep508 ep69 ep507 88459 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3191878247) qz20 0 2 ep506 ep67 ep507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3191878247) qz21 0 2 ep508 ep69 ep507 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz388 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 515453525) qz35)

noncomputable def ep510 := @Enclosure.Real.IsNear.cos_image qz69 qz388 Bool.false 515453525 1048576 379 524288 Bool.false 88459 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 55346400834126890211 112589990684262400 18066250014453 25000000000000000 515453525 1048576 379 524288 (ep505 rfl) rfl) (Enclosure.sfrac_false_div 515453525 1048576) (BSN.cos_reduce0 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224608463829277175971840) qz36) 226375608064910080 72057594037927936 Bool.false 88459 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 515453525 1048576 226375608064910080 72057594037927936 78 224608463829277175971840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 88459 1048576 224608463829277175971840 151115727451828646838272 3191878247 2147483648 400391 400000 (ep509 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep511 := nat_lit 6686315601701911135259544559541091667681548032032424617596900068983791715990465

noncomputable def ep512 := nat_lit 17494335596263522300614587394259641562914865564094443084062493601635349298002881

noncomputable def ep513 := BSN.sin_dyadic_bound_f 3191878247 2147483648 3 2 1048576 400391 ep511 ep60 ep507 ep512 ep63 ep507 1044837 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3191878247) qz15 0 2 ep511 ep60 ep507 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3191878247) qz16 0 2 ep512 ep63 ep507 rfl rfl rfl rfl) rfl rfl

noncomputable def ep514 := @Enclosure.Real.IsNear.sin_image qz69 qz388 Bool.false 515453525 1048576 379 524288 Bool.false 1044837 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 55346400834126890211 112589990684262400 18066250014453 25000000000000000 515453525 1048576 379 524288 (ep505 rfl) rfl) (Enclosure.sfrac_false_div 515453525 1048576) (BSN.sin_reduce0 qz388 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 224608463829277175971840) qz36) 226375608064910080 72057594037927936 Bool.false 1044837 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 515453525 1048576 226375608064910080 72057594037927936 78 224608463829277175971840 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044837 1048576 224608463829277175971840 151115727451828646838272 3191878247 2147483648 400391 400000 (ep513 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz389 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep503 rfl rfl) rfl)

noncomputable def ep515 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz385 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz385 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 16934856337 1099511627776 456896027871 3435973836800000 Bool.true 200026729791 1099511627776 459884709121 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz385 (Real.cos qz69) 191443 1048576 1 1048576 88459 1048576 1192567 1638400000 16934856337 1099511627776 456896027871 3435973836800000 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 88459 1048576 76324288 104857600000 88459 1048576 1192567 1638400000 (ep510 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz385 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 191443 1048576 1 1048576 1044837 1048576 1192567 1638400000 200026729791 1099511627776 459884709121 3435973836800000 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.false 1044837 1048576 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.false 1044837 1048576 76324288 104857600000 1044837 1048576 1192567 1638400000 (ep514 rfl rfl) rfl)) rfl)

noncomputable def ep516 := @ep420 16934856337 1099511627776 456896027871 3435973836800000 Bool.true 200026729791 1099511627776 459884709121 3435973836800000 Bool.false ep421 4507746483639 1099511627776 21556066192031 3435973836800000 Bool.true 51832158985209371426816 94282147957 1099511627776 21554284629531 3435973836800000 (ep422 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep501 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep502 ep515) rfl rfl

noncomputable abbrev qz653 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz70 := (@HMul.hMul Real Real Real qz267 qz277 qz653)

noncomputable abbrev qz390 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep517 := @Enclosure.Complex.IsNear.of_eq qz634 (Complex.mk (@HMul.hMul Real Real Real qz0 qz390 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz390 (@Neg.neg Real Real.instNeg (Real.sin qz70)))) Bool.false 24643791295 137438953472 45305219247 343597383680000 Bool.false 5679060995 549755813888 22498464311 171798691840000 (BSN.cpow_neg_s_mk qz12 144530 1000 31 qz13 rfl)

noncomputable abbrev qz391 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz392 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz654 := (@HDiv.hDiv Real Real Real qz1 qz392 qz14)

noncomputable def ep518 := @Enclosure.Real.IsNear.inv_image qz391 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz391 (Real.sqrt qz654) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz654) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep519 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 200000 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep520 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz653 144530 1000 0 1 3866325256314103 1125899906842624 1250000001 250000000000000 55879998929507730659 112589990684262400 18066250014453 25000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz654) Bool.false 64866173951437069877248 18889465931478580854784 1000000000800000 200000000000000000000 3866325256314103 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep519 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep521 := nat_lit 7184777660593239926708574880187071642782136762993742106957912881649407754240000

noncomputable def ep522 := nat_lit 12437105163520354172303402074143833882310606907639728403709270006169600000000

noncomputable def ep523 := nat_lit 18797138559860404948910157273322288095286617206180765005569480633833698099200000

noncomputable def ep524 := BSN.sin_dyadic_bound_f 3249674880 2147483648 3 2 1048576 400391 ep521 ep60 ep522 ep523 ep63 ep522 1046840 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3249674880) qz15 0 2 ep521 ep60 ep522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3249674880) qz16 0 2 ep523 ep63 ep522 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz393 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130105761) qz17)

noncomputable def ep525 := @Enclosure.Real.IsNear.cos_image qz70 qz393 Bool.false 130105761 262144 759 1048576 Bool.false 1046840 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 55879998929507730659 112589990684262400 18066250014453 25000000000000000 130105761 262144 759 1048576 (ep520 rfl) rfl) (Enclosure.sfrac_false_div 130105761 262144) (BSN.cos_reduce3 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57168885088500729249792) qz19) 226375608064910080 72057594037927936 Bool.false 1046840 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 130105761 262144 226375608064910080 72057594037927936 78 57168885088500729249792 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1046840 1048576 57168885088500729249792 37778931862957161709568 3249674880 2147483648 400391 400000 (ep524 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep526 := nat_lit 3997070747068920116692454223247992616604436249177696605378266832030190796800000

noncomputable def ep527 := nat_lit 11966338030879719641732755865595690182048687533717810359327381956078233190400000

noncomputable def ep528 := BSN.cos_dyadic_bound_f 3249674880 2147483648 3 2 1048576 400391 ep526 ep67 ep522 ep527 ep69 ep522 60310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3249674880) qz20 0 2 ep526 ep67 ep522 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3249674880) qz21 0 2 ep527 ep69 ep522 rfl rfl rfl rfl) rfl rfl

noncomputable def ep529 := @Enclosure.Real.IsNear.sin_image qz70 qz393 Bool.false 130105761 262144 759 1048576 Bool.true 60310 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 55879998929507730659 112589990684262400 18066250014453 25000000000000000 130105761 262144 759 1048576 (ep520 rfl) rfl) (Enclosure.sfrac_false_div 130105761 262144) (BSN.sin_reduce3 qz393 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 57168885088500729249792) qz19) 226375608064910080 72057594037927936 Bool.false 60310 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 130105761 262144 226375608064910080 72057594037927936 78 57168885088500729249792 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 60310 1048576 57168885088500729249792 37778931862957161709568 3249674880 2147483648 400391 400000 (ep528 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz394 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep518 rfl rfl) rfl)

noncomputable def ep530 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz390 (Real.cos qz70)) (@HMul.hMul Real Real Real qz0 qz390 (@Neg.neg Real Real.instNeg (Real.sin qz70))) Bool.false 24643791295 137438953472 45305219247 343597383680000 Bool.false 5679060995 549755813888 22498464311 171798691840000 (@Enclosure.Real.IsNear.mulLit_ff qz390 (Real.cos qz70) 188329 1048576 1 1048576 130855 131072 2388259 3276800000 24643791295 137438953472 45305219247 343597383680000 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz70) Bool.false 1046840 1048576 152848576 209715200000 130855 131072 2388259 3276800000 (ep525 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz390 (@Neg.neg Real Real.instNeg (Real.sin qz70)) 188329 1048576 1 1048576 30155 524288 2388259 3276800000 5679060995 549755813888 22498464311 171798691840000 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz70) Bool.true 30155 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz70) Bool.true 60310 1048576 152848576 209715200000 30155 524288 2388259 3276800000 (ep529 rfl rfl) rfl)) rfl)

noncomputable def ep531 := @ep418 24643791295 137438953472 45305219247 343597383680000 Bool.false 5679060995 549755813888 22498464311 171798691840000 Bool.false 646636094309769599254528 4704896813999 1099511627776 22009118384501 3435973836800000 Bool.true 45587965386357731229696 82924025967 1099511627776 22004253915751 3435973836800000 (ep419 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep516 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep517 ep530) rfl rfl

noncomputable abbrev qz655 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz277 qz655)

noncomputable abbrev qz395 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep532 := @Enclosure.Complex.IsNear.of_eq qz633 (Complex.mk (@HMul.hMul Real Real Real qz0 qz395 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz395 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 35030455829 1099511627776 443287813151 3435973836800000 Bool.false 191184325015 1099511627776 445920381901 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 32 qz13 rfl)

noncomputable abbrev qz396 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz397 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz656 := (@HDiv.hDiv Real Real Real qz1 qz397 qz14)

noncomputable def ep533 := @Enclosure.Real.IsNear.inv_image qz396 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz396 (Real.sqrt qz656) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz656) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep534 := BSN.log_dyadic_bound 0 64 1 0 1 524288 200000 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep535 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz655 144530 1000 0 1 15608286920413395 4503599627370496 1000000001 200000000000000 45117314172146959587 90071992547409920 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz656) Bool.false 65465900263437584302080 18889465931478580854784 1000000001000000 200000000000000000000 15608286920413395 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep534 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep536 := nat_lit 2839499041710267980006507738270123894408017464521440046006636537040307283435776

noncomputable def ep537 := nat_lit 6287824578920217882792239596460054379232624486307739207981248685403145380096

noncomputable def ep538 := nat_lit 8505921475972963504253938735617451574465587144591704659603947113750115559547136

noncomputable def ep539 := BSN.cos_dyadic_bound_f 2984094362 2147483648 3 2 1048576 400391 ep536 ep67 ep537 ep538 ep69 ep537 188983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2984094362) qz20 0 2 ep536 ep67 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2984094362) qz21 0 2 ep538 ep69 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz398 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65654333) qz594)

noncomputable def ep540 := @Enclosure.Real.IsNear.cos_image qz71 qz398 Bool.false 65654333 131072 759 1048576 Bool.true 188983 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 45117314172146959587 90071992547409920 14453000014453 20000000000000000 65654333 131072 759 1048576 (ep535 rfl) rfl) (Enclosure.sfrac_false_div 65654333 131072) (BSN.cos_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26248371599592386461696) qz327) 226375608064910080 72057594037927936 Bool.false 188983 1048576 79 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 65654333 131072 226375608064910080 72057594037927936 79 26248371599592386461696 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 188983 1048576 26248371599592386461696 18889465931478580854784 2984094362 2147483648 400391 400000 (ep539 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep541 := nat_lit 5106068015415346189705480137209054966431045336549545891445560767724230593880320

noncomputable def ep542 := nat_lit 13362854991055273953608879590486589585943504013223360042687356179501379796214016

noncomputable def ep543 := BSN.sin_dyadic_bound_f 2984094362 2147483648 3 2 1048576 400391 ep541 ep60 ep537 ep542 ep63 ep537 1031405 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2984094362) qz15 0 2 ep541 ep60 ep537 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2984094362) qz16 0 2 ep542 ep63 ep537 rfl rfl rfl rfl) rfl rfl

noncomputable def ep544 := @Enclosure.Real.IsNear.sin_image qz71 qz398 Bool.false 65654333 131072 759 1048576 Bool.true 1031405 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 45117314172146959587 90071992547409920 14453000014453 20000000000000000 65654333 131072 759 1048576 (ep535 rfl) rfl) (Enclosure.sfrac_false_div 65654333 131072) (BSN.sin_reduce2 qz398 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26248371599592386461696) qz327) 226375608064910080 72057594037927936 Bool.false 1031405 1048576 79 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 65654333 131072 226375608064910080 72057594037927936 79 26248371599592386461696 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031405 1048576 26248371599592386461696 18889465931478580854784 2984094362 2147483648 400391 400000 (ep543 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz399 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep533 rfl rfl) rfl)

noncomputable def ep545 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz395 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz395 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 35030455829 1099511627776 443287813151 3435973836800000 Bool.false 191184325015 1099511627776 445920381901 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz395 (Real.cos qz71) 185363 1048576 1 1048576 188983 1048576 2388259 3276800000 35030455829 1099511627776 443287813151 3435973836800000 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 188983 1048576 152848576 209715200000 188983 1048576 2388259 3276800000 (ep540 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz395 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 185363 1048576 1 1048576 1031405 1048576 2388259 3276800000 191184325015 1099511627776 445920381901 3435973836800000 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.true 1031405 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.true 1031405 1048576 152848576 209715200000 1031405 1048576 2388259 3276800000 (ep544 rfl rfl) rfl)) rfl)

noncomputable def ep546 := @ep415 35030455829 1099511627776 443287813151 3435973836800000 Bool.false 191184325015 1099511627776 445920381901 3435973836800000 Bool.false ep416 2334933179085 549755813888 5613101549413 858993459200000 Bool.false 119033457629783023157248 13532537381 137438953472 5612543574413 858993459200000 (ep417 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep531 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep532 ep545) rfl rfl

theorem EMRow51.d9 : Enclosure.Complex.IsNear qz63 Bool.false 2334933179085 549755813888 5613101549413 858993459200000 Bool.false 13532537381 137438953472 5612543574413 858993459200000 := ep414 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep546 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow51.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow51.d11 : @Eq Nat (Nat.pow 37 1) 37 := @Eq.refl Nat 37

noncomputable def ep547 := nat_lit 11645857852227225357839029133

noncomputable def ep548 := nat_lit 2784663283527030813428285440

noncomputable def ep549 := nat_lit 205621375155695745824092336512689

noncomputable def ep550 := nat_lit 23593509519264269205504000000000000

noncomputable abbrev qz741 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz657 := qz741

noncomputable abbrev qz400 := qz657

noncomputable abbrev qz72 := qz400

noncomputable abbrev qz658 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz401 := qz658

noncomputable abbrev qz73 := qz401

noncomputable abbrev qz742 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz743 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz659 := (@HAdd.hAdd Complex Complex Complex qz739 (@HAdd.hAdd Complex Complex Complex qz739 qz742 (@HMul.hMul Complex Complex Complex qz741 Complex.I (@HDiv.hDiv Complex Complex Complex qz743 (↑qz740) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz402 := qz659

noncomputable abbrev qz74 := (Complex.Stirling.logGammaStirling 1 qz402)

noncomputable abbrev qz660 := (@HAdd.hAdd Complex Complex Complex qz739 qz742 (@HMul.hMul Complex Complex Complex qz741 Complex.I (@HDiv.hDiv Complex Complex Complex qz743 (↑qz740) (2 : Complex))))

noncomputable abbrev qz403 := qz660

noncomputable abbrev qz75 := qz403

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz404 := (@instHSub Real Real.instSub)

noncomputable def ep551 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76))) (zetaApproximant qz5 1 37))

noncomputable def ep552 := @Enclosure.Real.IsNear.of_eq ep551 (@HSub.hSub Real Real Real qz404 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 37))))

noncomputable def ep553 := nat_lit 582294484163935286377008925

noncomputable def ep554 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 37))) ep553

noncomputable def ep555 := nat_lit 139233164176351540671414272

noncomputable def ep556 := nat_lit 75719330617278479480905768343620011

noncomputable def ep557 := nat_lit 8702072761021971291963392000000000000

noncomputable def ep558 := nat_lit 724119515883808623281730640860691

noncomputable def ep559 := nat_lit 52212436566131827751780352000000000000

noncomputable def ep560 := nat_lit 1621489638313606008193519022326356763922846058519986176

noncomputable def ep561 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.re (zetaApproximant qz5 1 37)) 1048575 1048576 1250759

noncomputable def ep562 := nat_lit 113167187617250542904029049

noncomputable def ep563 := nat_lit 15933971120035347824640000000

noncomputable def ep564 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.true 1048575 1048576 80048576

noncomputable abbrev qz405 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 161414965) qz35)

noncomputable def ep565 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz405 Bool.false 161414965 1048576 395

noncomputable def ep566 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) Bool.false 2773087996454021113 18014398509481984 118083315447542084977 314572800000000000000000

noncomputable def ep567 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76 106582725936074614609 450359962737049600 31365315447542084977 314572800000000000000000 1084278513 13107200

noncomputable def ep568 := nat_lit 908685474678053638307840000

noncomputable def ep569 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25595029096446227291 225179981368524800 9817680371892390991 52428800000000000000000 Bool.false 106582725936074614609 450359962737049600

noncomputable def ep570 := @Enclosure.Complex.IsNear.subLitP qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 23667300461769855091 225179981368524800 9686608371263245391 52428800000000000000000 Bool.false 107988226778650747409 450359962737049600 29792451447227512177

noncomputable def ep571 := nat_lit 28817440875323058038355440470851584

noncomputable def ep572 := nat_lit 30000370300614833364104565703573504

noncomputable abbrev qz744 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz661 := qz744

noncomputable abbrev qz406 := (@HSub.hSub Complex Complex Complex qz658 qz659 qz661)

noncomputable abbrev qz407 := (Complex.log qz659)

noncomputable abbrev qz77 := (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 qz406 qz407) qz402)

noncomputable abbrev qz408 := qz661

noncomputable abbrev qz78 := (@HMul.hMul Complex Complex Complex qz400 qz408 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz662 := qz743

noncomputable abbrev qz409 := qz662

noncomputable abbrev qz79 := qz409

noncomputable abbrev qz80 := (@instHMul Nat instMulNat)

noncomputable abbrev qz663 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz410 := qz663

noncomputable abbrev qz81 := qz410

noncomputable abbrev qz82 := qz402

noncomputable abbrev qz83 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz84 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz411 := (@instHSub Int Int.instSub)

noncomputable abbrev qz412 := (@instHMul Int Int.instMul)

noncomputable def ep573 := @Enclosure.Complex.IsNear.of_eq qz74 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 23667300461769855091

noncomputable def ep574 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz77 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 23667308538849202291 225179981368524800

noncomputable def ep575 := nat_lit 1626404503486515614312065662976

noncomputable def ep576 := nat_lit 74208944378773822580417877770240

noncomputable def ep577 := @ep574 36951469735889 200000000000000000 Bool.false 21597749122865976221 90071992547409920 18941250086893 200000000000000000 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400 Bool.true ep575 23667300461769855091 225179981368524800 9686608371263245391 52428800000000000000000 Bool.false ep576

noncomputable def ep578 := @Enclosure.Complex.IsNear.addLitP qz77 qz78 Bool.true 23874234909209727091 225179981368524800 73140000018653 400000000000000000

noncomputable def ep579 := nat_lit 3102121464804042642685952

noncomputable def ep580 := @ep578 Bool.false 21597749122865976221 90071992547409920 18941250086893 200000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep579 23667308538849202291 225179981368524800 36951469735889 200000000000000000 Bool.false 21597749122865976221 21597749122865976221 90071992547409920

noncomputable abbrev qz85 := (@HMul.hMul Complex Complex Complex qz400 qz406 qz407)

noncomputable def ep581 := @Enclosure.Complex.IsNear.subLitP qz85 qz82 Bool.true 23367579951130546291 225179981368524800 73140000018653 400000000000000000 Bool.false 140534008321522770449

noncomputable def ep582 := @ep581 450359962737049600 18941250086893 200000000000000000 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 Bool.true 95496939636838908364000 23874234909209727091 225179981368524800 73140000018653 400000000000000000 Bool.false 431954982457319524420000 21597749122865976221 90071992547409920 18941250086893 200000000000000000

noncomputable abbrev qz86 := qz406

noncomputable abbrev qz87 := qz407

noncomputable def ep583 := @Enclosure.Complex.IsNear.mul qz86 qz87 Bool.true 23367579951130546291 225179981368524800 73140000018653 400000000000000000 Bool.false 140534008321522770449 450359962737049600 18941250086893

noncomputable abbrev qz88 := (Complex.re qz406)

noncomputable abbrev qz89 := (Complex.re qz407)

noncomputable abbrev qz90 := (Complex.im qz406)

noncomputable abbrev qz91 := (Complex.im qz407)

noncomputable def ep584 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz88 qz89) (@HMul.hMul Real Real Real qz0 qz90 qz91) 67476913526104131 9007199254740992 4375000021 2000000000000000 12527251394641574783 112589990684262400

noncomputable def ep585 := nat_lit 105238224360461801406027896335630336

noncomputable def ep586 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz89 7000 4000 0 1 9639559075157733 2251799813685248 625000003 500000000000000

noncomputable def ep587 := @Enclosure.Complex.IsNear.re_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable abbrev qz664 := (Enclosure.sfrac Bool.false 289060 4000)

noncomputable abbrev qz413 := qz664

noncomputable def ep588 := @Enclosure.Complex.IsNear.of_eq qz86 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz413) Bool.false 7000 4000 0 1 Bool.false 289060 4000 0

noncomputable abbrev qz665 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz414 := (Complex.log (Complex.mk qz665 qz664))

noncomputable def ep589 := @Enclosure.Complex.IsNear.of_eq qz87 qz414 Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000

noncomputable def ep590 := nat_lit 1156978038421400796819911409123086857504841107980821729280000000000000

noncomputable def ep591 := nat_lit 5728949035783701728984880619731350768724894775738822656000000000000

noncomputable def ep592 := nat_lit 527546955325799617195938504920727015328707455447040000000000000

noncomputable def ep593 := BSN.log_dyadic_bound 18100683600 149172683600 4 3 ep590 1048576 400000 ep591 ep592 255729 167273367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18100683600) (BSN.artanhQ 149172683600) 0 3 ep591 ep590 ep592 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz92 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz415 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz666 := (Real.log (Enclosure.sfrac Bool.false 83636683600 16000000))

noncomputable abbrev qz667 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep594 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz666 1 2 0 1 9639559075157733 1125899906842624 625000003 250000000000000 9639559075157733 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 83636683600 16000000 9639559075157733 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83636683600) qz667)) Bool.false 323449929497363041222656 37778931862957161709568 1000000004800000 400000000000000000000 9639559075157733 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 83636683600 16000000 12 167273367200 131072000000 255729 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep593 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep595 := BSN.arctan_dyadic_bound_f 9000 289060 1 0 1048576 400000 0 1 1 0 1 1 32637 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz93 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz94 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz415 BSN.pi_near_15 rfl)

noncomputable abbrev qz416 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 289060)))

noncomputable def ep596 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz416 884279719003555 562949953421312 1 2000000000000000 32637 1048576 1 400000 908861493004060327936 866757863048611 562949953421312 5000000001 2000000000000000 qz94 (ep595 rfl) rfl rfl

noncomputable abbrev qz417 := (Complex.mk qz665 qz664)

noncomputable abbrev qz418 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 289060) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep597 := @Enclosure.Complex.IsNear.re_isNear qz87 Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (ep589 (@congrArg Complex Complex qz82 qz417 Complex.log (BSN.w_shift_mk qz12 Bool.false 144530 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz414 Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz414) (@HMul.hMul Real Real Real qz0 qz92 qz666) Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 9000 289060 4000 83636683600 16000000 rfl rfl rfl) (ep594 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz414) qz418 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 9000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz418 (@HSub.hSub Real Real Real qz404 qz93 qz416) Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 289060 9000 rfl rfl) ep596))))

noncomputable def ep598 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz91 289060 4000 0 1 866757863048611 562949953421312 5000000001 2000000000000000

noncomputable def ep599 := @Enclosure.Complex.IsNear.im_isNear qz86 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable def ep600 := @Enclosure.Complex.IsNear.im_isNear qz87 Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (ep589 (@congrArg Complex Complex qz82 qz417 Complex.log (BSN.w_shift_mk qz12 Bool.false 144530 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz414 Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz414) (@HMul.hMul Real Real Real qz0 qz92 qz666) Bool.false 9639559075157733 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 9000 289060 4000 83636683600 16000000 rfl rfl rfl) (ep594 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz414) qz418 Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 9000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz418 (@HSub.hSub Real Real Real qz404 qz93 qz416) Bool.false 866757863048611 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 289060 9000 rfl rfl) ep596))))

noncomputable abbrev qz95 := (@ep588 1 (BSN.w_sub_half_mk qz277 Bool.false 144530 1000 2 qz279 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz413 Bool.false 7000 4000 0 1 Bool.false 289060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 289060 4000)))

noncomputable def ep601 := @ep584 72265000014453 400000000000000000 ep585 23367579951130546291 225179981368524800 73140000018653 400000000000000000 (@ep586 67476913526104131 9007199254740992 4375000021 2000000000000000 (ep587 qz95) ep597 rfl) (@ep598 12527251394641574783 112589990684262400 72265000014453 400000000000000000 (ep599 qz95) ep600 rfl) rfl

noncomputable def ep602 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz88 qz91) (@HMul.hMul Real Real Real qz0 qz90 qz89) 6067305041340277 2251799813685248 35000000007 8000000000000000 139320547313254715049 450359962737049600

noncomputable def ep603 := nat_lit 316454453754846066506606961441636352

noncomputable def ep604 := @Enclosure.Real.IsNear.mulLit_ff qz88 qz91 7000 4000 0 1 866757863048611 562949953421312 5000000001 2000000000000000

noncomputable def ep605 := @Enclosure.Real.IsNear.mulLit_ff qz90 qz89 289060 4000 0 1 9639559075157733 2251799813685248 625000003 500000000000000

noncomputable def ep606 := @ep602 9033125043359 100000000000000000 ep603 140534008321522770449 450359962737049600 18941250086893 200000000000000000 (@ep604 6067305041340277 2251799813685248 35000000007 8000000000000000 (ep587 qz95) ep600 rfl) (@ep605 139320547313254715049 450359962737049600 9033125043359 100000000000000000 (ep599 qz95) ep597 rfl) rfl

noncomputable def ep607 := @Enclosure.Complex.IsNear.of_eq qz82 qz417 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 144530 1000 2 qz13 rfl)

noncomputable abbrev qz419 := (ep607 (@Enclosure.Complex.IsNear.mk qz665 qz664 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 289060 4000)))

noncomputable abbrev qz96 := qz419

noncomputable def ep608 := ep582 (@ep583 200000000000000000 (ep601 rfl) (ep606 rfl)) qz96 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz97 := qz408

noncomputable def ep609 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz97) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz97) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep610 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz97) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz98 := (@Enclosure.Complex.IsNear.of_eq qz408 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz556) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz556 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz415 qz559))

noncomputable def ep611 := ep610 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow51.d4)

noncomputable def ep612 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz97) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep613 := ep612 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep614 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz97) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz97) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep615 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz97) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep616 := ep615 (@Enclosure.Complex.IsNear.re_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz97) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep618 := ep617 (@Enclosure.Complex.IsNear.im_isNear qz97 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz98) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow51.d4)

noncomputable def ep619 := @ep580 18941250086893 200000000000000000 (ep608 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz97 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep609 131072 1 524288 (ep611 rfl) (ep613 rfl) rfl rfl) (@ep614 1 0 1 (ep616 rfl) (ep618 rfl) rfl rfl))

noncomputable abbrev qz99 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz420 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz100 := (@HMul.hMul Complex Complex Complex qz400 (@HMul.hMul Complex Complex Complex qz400 (2 : Complex) qz420) (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 (2 : Complex) qz420) (1 : Complex)))

noncomputable abbrev qz421 := (@HPow.hPow Complex Int Complex qz663 qz659 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz101 := qz421

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101)) Bool.false 2464929 68719476736 3 68719476736

noncomputable def ep621 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101) Bool.false 0 1 0 1 Bool.false

noncomputable def ep622 := @ep621 0 1 0 1 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400 Bool.false 2464929 2464929 68719476736 3 68719476736 Bool.true 3958402093 3958402093 3435973836800 14453

noncomputable def ep623 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz82 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep624 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz101 Bool.false 2464929 68719476736 3 68719476736 Bool.true 3958402093 3435973836800 14453 10307921510400

noncomputable abbrev qz102 := (Complex.re qz421)

noncomputable abbrev qz103 := (Complex.im qz421)

noncomputable def ep625 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103) 2464929 68719476736 3 68719476736 0 1 0

noncomputable def ep626 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102 1 12 0 1 7394787 17179869184 9 17179869184 2464929

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz422 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep628 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep627 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz422)

noncomputable def ep629 := @Enclosure.Complex.IsNear.re_isNear qz101 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453 858993459200

noncomputable abbrev qz668 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz423 := (@HPow.hPow Complex Nat Complex qz668 qz659 1)

noncomputable abbrev qz104 := (@Inv.inv Complex Complex.instInv qz423)

noncomputable def ep630 := @Enclosure.Complex.IsNear.of_eq qz101 qz104 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453

noncomputable def ep631 := @Enclosure.Complex.IsNear.of_parts qz104 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453

noncomputable abbrev qz105 := (Complex.re qz423)

noncomputable abbrev qz106 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz107 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz108 := qz423

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ff qz105 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) 9000 4000 0 1 821643 4294967296 1 4294967296

noncomputable def ep633 := @Enclosure.Complex.IsNear.re_isNear qz108 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable def ep634 := @Enclosure.Complex.IsNear.of_eq qz108 qz82 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0

noncomputable def ep635 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) Bool.false 821643 4294967296 1 4294967296 821643 4294967296 1

noncomputable abbrev qz109 := (Complex.im qz423)

noncomputable abbrev qz424 := (@instHAdd Real Real.instAdd)

noncomputable def ep636 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 qz105 qz105) (@HMul.hMul Real Real Real qz0 qz109 qz109)) Bool.false 209091709 40000 0 1

noncomputable def ep637 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz105 qz105) (@HMul.hMul Real Real Real qz0 qz109 qz109) 81 16 0 1 208889209 40000

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff qz105 qz105 9000 4000 0 1 9000 4000 0 1

noncomputable def ep639 := @Enclosure.Real.IsNear.mulLit_ff qz109 qz109 289060 4000 0 1 289060 4000 0 1

noncomputable def ep640 := @Enclosure.Complex.IsNear.im_isNear qz108 Bool.false 9000 4000 0 1 Bool.false 289060 4000 0 1

noncomputable abbrev qz110 := (ep633 (@ep634 1 (BSN.pow_one_c qz402) qz419))

noncomputable abbrev qz111 := (ep640 (@ep634 1 (BSN.pow_one_c qz402) qz419))

noncomputable def ep641 := @ep637 0 1 3345467344 209091709 40000 0 1 (@ep638 81 16 0 1 qz110 qz110 rfl) (@ep639 208889209 40000 0 1 qz111 qz111 rfl)

noncomputable def ep642 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108) 209091709 40000 0 1 410821 410822 2147483648 (ep636 (Enclosure.Complex.normSq_eq_mul_add_mul qz108) (ep641 rfl rfl)) rfl

noncomputable def ep643 := @Enclosure.Real.IsNear.of_eq (Complex.re qz104) (@HMul.hMul Real Real Real qz0 qz105 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108))) Bool.false 7394787 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz108) (@ep632 7394787 17179869184 9 17179869184 qz110 (@ep635 4294967296 (ep642 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep644 := @Enclosure.Real.IsNear.of_eq (Complex.im qz104) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz109) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108))) Bool.true 11875206279 858993459200 14453 858993459200 (Enclosure.Complex.inv_im_eq_mul qz108)

noncomputable def ep645 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz109) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz108)) 289060 4000 0 1 821643 4294967296 1

noncomputable def ep646 := @ep645 4294967296 11875206279 858993459200 14453 858993459200 (@Enclosure.Real.IsNear.neg qz109 Bool.false 289060 4000 0 1 qz111) (@ep635 4294967296 (ep642 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep647 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103 0 1 0 1 11875206279 858993459200 14453 858993459200 0

noncomputable def ep648 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep627 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz422)

noncomputable def ep649 := @Enclosure.Complex.IsNear.im_isNear qz101 Bool.false 7394787 17179869184 9 17179869184 Bool.true 11875206279 858993459200 14453 858993459200

noncomputable abbrev qz112 := (@ep630 858993459200 (BSN.zpow_one_sub_two_mul qz402 1 1 rfl rfl) (@ep631 858993459200 ep643 (ep644 ep646)))

noncomputable def ep650 := @ep625 1 2464929 2464929 68719476736 3 68719476736 (@ep626 68719476736 3 68719476736 ep628 (ep629 qz112) rfl) (@ep647 1 0 1 ep648 (ep649 qz112) rfl) rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102) 3958402093 3435973836800 14453 10307921510400 0 1 0

noncomputable def ep652 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz103 1 12 0 1 11875206279 858993459200 14453 858993459200 3958402093

noncomputable def ep653 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz102 0 1 0 1 7394787 17179869184 9 17179869184 0

noncomputable def ep654 := @ep651 1 3958402093 3958402093 3435973836800 14453 10307921510400 (@ep652 3435973836800 14453 10307921510400 ep628 (ep649 qz112) rfl) (@ep653 1 0 1 ep648 (ep629 qz112) rfl) rfl

noncomputable abbrev qz113 := (@Enclosure.Complex.IsNear.mk qz556 qz556 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz559 qz559)

noncomputable def ep655 := @ep622 10307921510400 (@ep623 0 1 0 1 (BSN.stirling_sum_base qz82) qz113) (ep624 (ep650 rfl) (ep654 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep656 := @ep577 107988226778650747409 450359962737049600 29792451447227512177 314572800000000000000000 (ep619 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep620 Bool.true 3958402093 3435973836800 14453 10307921510400 (BSN.stirling_sum_succ qz82 0 1 rfl) (ep655 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep657 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9638643173381861 1125899906842624 625000003 250000000000000 Bool.false 878438026610083 281474976710656

noncomputable abbrev qz114 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz403 qz420))

noncomputable def ep658 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz114) Bool.false 9638643173381861 1125899906842624 625000003 250000000000000 Bool.false 878438026610083 281474976710656 5000000001 1000000000000000

noncomputable def ep659 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz114 Bool.false 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 562949953421312 5000000001 2000000000000000 Bool.false

noncomputable def ep660 := nat_lit 43408589803999724269331132973056

noncomputable def ep661 := nat_lit 989033292327310912086492577792

noncomputable abbrev qz115 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz403 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep662 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz115) Bool.false 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 562949953421312 5000000001 2000000000000000

noncomputable def ep663 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz115 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz425 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz664))

noncomputable def ep664 := @Enclosure.Complex.IsNear.of_eq qz115 qz425 Bool.false 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 562949953421312 5000000001 2000000000000000

noncomputable def ep665 := nat_lit 1153260163240354830251032192219273955985555773252117729280000000000000

noncomputable def ep666 := nat_lit 5665856001819777994319944578467967153204588907758022656000000000000

noncomputable def ep667 := nat_lit 513710956408620598139643930132710501502374783447040000000000000

noncomputable def ep668 := BSN.log_dyadic_bound 18020683600 149092683600 4 3 ep665 1048576 400000 ep666 ep667 254725 167113367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18020683600) (BSN.artanhQ 149092683600) 0 3 ep666 ep665 ep667 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep669 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 83556683600 16000000)) 1 2 0 1 9638481038366437 1125899906842624 625000003 250000000000000 9638481038366437 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 83556683600 16000000 9638481038366437 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83556683600) qz667)) Bool.false 323413756585156001398784 37778931862957161709568 1000000004800000 400000000000000000000 9638481038366437 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 83556683600 16000000 12 167113367200 131072000000 254725 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep668 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep670 := BSN.arctan_dyadic_bound_f 1000 289060 1 0 1048576 400000 0 1 1 0 1 1 3627 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz426 := (@Nat.cast Real Real.instNatCast 289060)

noncomputable abbrev qz669 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable def ep671 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz669 qz426)) 884279719003555 562949953421312 1 2000000000000000 3627 1048576 1 400000 925192671152812589056 882332488205731 562949953421312 5000000001 2000000000000000 qz94 (ep670 rfl) rfl rfl

noncomputable abbrev qz116 := (@HAdd.hAdd Complex Complex Complex qz272 qz403 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz427 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz664)

noncomputable def ep672 := @ep663 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 562949953421312 5000000001 2000000000000000 Bool.false 9638481038366437 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 882332488205731 562949953421312 5000000001 2000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz113) (ep664 (@congrArg Complex Complex qz116 qz427 Complex.log (BSN.w_shift_mk qz12 Bool.false 144530 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz425 Bool.false 9638481038366437 2251799813685248 625000003 500000000000000 Bool.false 882332488205731 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz425) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 83556683600 16000000))) Bool.false 9638481038366437 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 1000 289060 4000 83556683600 16000000 rfl rfl rfl) (ep669 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz425) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz669)) Bool.false 882332488205731 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 1000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz669)) (@HSub.hSub Real Real Real qz404 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz669 qz426))) Bool.false 882332488205731 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 289060 1000 rfl rfl) ep671)))) rfl rfl

noncomputable abbrev qz428 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz664))

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq qz114 qz428 Bool.false 9638805308397285 2251799813685248 625000003 500000000000000 Bool.false 874543565014435 562949953421312 5000000001 2000000000000000

noncomputable def ep674 := nat_lit 1154374478885351619545224531027566262688860482790728929280000000000000

noncomputable def ep675 := nat_lit 5684734606284847285519654569436490428372169692152262656000000000000

noncomputable def ep676 := nat_lit 517829618908272375316618734159904951294434585047040000000000000

noncomputable def ep677 := BSN.log_dyadic_bound 18044683600 149116683600 4 3 ep674 1048576 400000 ep675 ep676 255027 167161367200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 18044683600) (BSN.artanhQ 149116683600) 0 3 ep675 ep674 ep676 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep678 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 83580683600 16000000)) 1 2 0 1 9638805308397285 1125899906842624 625000003 250000000000000 9638805308397285 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 83580683600 16000000 9638805308397285 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83580683600) qz667)) Bool.false 323424637281855728517120 37778931862957161709568 1000000004800000 400000000000000000000 9638805308397285 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 83580683600 16000000 12 167161367200 131072000000 255027 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep677 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep679 := BSN.arctan_dyadic_bound_f 5000 289060 1 0 1048576 400000 0 1 1 0 1 1 18135 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 289060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 289060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz670 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep680 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz670 qz426)) 884279719003555 562949953421312 1 2000000000000000 18135 1048576 1 400000 917025393228576194560 874543565014435 562949953421312 5000000001 2000000000000000 qz94 (ep679 rfl) rfl rfl

noncomputable abbrev qz117 := (@HAdd.hAdd Complex Complex Complex qz272 qz403 qz420)

noncomputable abbrev qz429 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz664)

noncomputable def ep681 := @ep659 9638805308397285 2251799813685248 625000003 500000000000000 Bool.false 874543565014435 562949953421312 5000000001 2000000000000000 Bool.false ep660 9638643173381861 1125899906842624 625000003 250000000000000 Bool.false ep661 878438026610083 281474976710656 5000000001 1000000000000000 (ep662 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep672 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep673 (@congrArg Complex Complex qz117 qz429 Complex.log (BSN.w_shift_mk qz12 Bool.false 144530 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz428 Bool.false 9638805308397285 2251799813685248 625000003 500000000000000 Bool.false 874543565014435 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz428) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 83580683600 16000000))) Bool.false 9638805308397285 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 5000 289060 4000 83580683600 16000000 rfl rfl rfl) (ep678 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz428) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz670)) Bool.false 874543565014435 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 5000 289060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz426 qz670)) (@HSub.hSub Real Real Real qz404 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz670 qz426))) Bool.false 874543565014435 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 289060 5000 rfl rfl) ep680)))) rfl rfl

noncomputable def ep682 := @ep570 314572800000000000000000 Bool.false 9638643173381861 1125899906842624 625000003 250000000000000 Bool.false 878438026610083 281474976710656 5000000001 1000000000000000 Bool.true ep571 25595029096446227291 225179981368524800 9817680371892390991 52428800000000000000000 Bool.false ep572 106582725936074614609 450359962737049600 31365315447542084977 314572800000000000000000 (@ep573 225179981368524800 9686608371263245391 52428800000000000000000 Bool.false 107988226778650747409 450359962737049600 29792451447227512177 314572800000000000000000 (BSN.logGammaStirling_unfold 1 qz82) (ep656 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep657 5000000001 1000000000000000 (BSN.log_sum_c_eq qz12 2) (ep658 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep681 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz118 := (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real))

noncomputable def ep683 := @Enclosure.Real.IsNear.mulLit_ff qz118 (Real.log Real.pi) 144530 2000 0 1 75021 65536 1 262144 1084278513 13107200 14453 52428800 (@Enclosure.Real.IsNear.of_eq qz118 (Enclosure.sfrac Bool.false 144530 2000) Bool.false 144530 2000 0 1 (BSN.t_half_eq qz12 Bool.false 144530 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 144530 2000)) EMRow51.d5 rfl

noncomputable def ep684 := @ep567 14453 52428800 ep568 2773087996454021113 18014398509481984 118083315447542084977 314572800000000000000000 (@ep569 31365315447542084977 314572800000000000000000 (ep682 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep683 rfl rfl

noncomputable def ep685 := nat_lit 8328380085751228669187526868463175687454186091993780953618714597251550644330625

noncomputable def ep686 := nat_lit 16702247111967114706728188730316660152314015770337461294724999552435062890625

noncomputable def ep687 := nat_lit 21785382300690985471680248540411614112609598024926975179286126326859642538090625

noncomputable def ep688 := BSN.sin_dyadic_bound_f 3371683985 2147483648 3 2 1048576 400391 ep685 ep60 ep686 ep687 ep63 ep686 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3371683985) qz15 0 2 ep685 ep60 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3371683985) qz16 0 2 ep687 ep63 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable def ep689 := @ep565 1048576 Bool.true 1048575 1048576 1 200000 (@ep566 161414965 1048576 395 1048576 ep684 rfl) (Enclosure.sfrac_false_div 161414965 1048576) (BSN.cos_reduce1 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237261167812391175454720) qz36) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 24 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 161414965 1048576 226375608064910080 72057594037927936 24 237261167812391175454720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 237261167812391175454720 151115727451828646838272 3371683985 2147483648 400391 400000 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep690 := nat_lit 226298507013335175388273723

noncomputable def ep691 := nat_lit 31867942240070695649280000000

noncomputable abbrev qz671 := (@Nat.cast Complex Complex.instNatCast 37)

noncomputable abbrev qz430 := (@HPow.hPow Complex Complex Complex qz547 qz671 qz548)

noncomputable abbrev qz119 := qz430

noncomputable abbrev qz431 := qz671

noncomputable abbrev qz120 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz409 qz431 (@HSub.hSub Complex Complex Complex qz401 qz271 (1 : Complex))) qz408)

noncomputable abbrev qz121 := (@instHSub Nat instSubNat)

noncomputable abbrev qz432 := qz668

noncomputable abbrev qz122 := qz432

noncomputable abbrev qz123 := qz431

noncomputable def ep692 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 37) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz72 qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false 1665959471179272688297 398349278000883695616 ep562

noncomputable def ep693 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz72 qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 4509731117901 1099511627776 24166998188857 3435973836800000

noncomputable def ep694 := nat_lit 2183221712901983422656523

noncomputable def ep695 := nat_lit 117231475837770641396557691861598208

noncomputable def ep696 := nat_lit 11666203742334314873670389427339264

noncomputable def ep697 := @ep693 Bool.false 4845779985 1099511627776 24163915288857 3435973836800000 Bool.false 2054362276754389559209 25494353792056556519424 1095248339091137501220449 ep563 Bool.true 13606590550470314370189 679849434454841507184640 ep694 ep691 Bool.false ep695 1665959471179272688297 398349278000883695616 ep562 ep563 Bool.true ep696 10610350493456567049789 679849434454841507184640

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 37) Bool.false 4509731117901 1099511627776 24166998188857 3435973836800000 Bool.false 4845779985 1099511627776 24163915288857

noncomputable abbrev qz672 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 36) qz7)

noncomputable def ep699 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 37) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 36) qz672) Bool.false 4509731117901 1099511627776 24166998188857 3435973836800000 Bool.false 4845779985 1099511627776 24163915288857 3435973836800000

noncomputable def ep700 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 36) qz672 Bool.false 4675773094675 1099511627776 23747193574231 3435973836800000 Bool.false 82379035409 1099511627776 23745693330481 3435973836800000 Bool.true

noncomputable def ep701 := nat_lit 2479250901137704341209088

noncomputable abbrev qz673 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz7)

noncomputable def ep702 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 35) qz673) Bool.false 4675773094675 1099511627776 23747193574231 3435973836800000 Bool.false 82379035409 1099511627776 23745693330481 3435973836800000

noncomputable def ep703 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 35) qz673 Bool.false 4638140931073 1099511627776 23323230266303 3435973836800000 Bool.true 99621594405 1099511627776 23319184610053 3435973836800000 Bool.false

noncomputable def ep704 := nat_lit 2570533443218667103846400

noncomputable abbrev qz674 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz7)

noncomputable def ep705 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 34) qz674) Bool.false 4638140931073 1099511627776 23323230266303 3435973836800000 Bool.true 99621594405 1099511627776 23319184610053 3435973836800000

noncomputable def ep706 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 34) qz674 Bool.false 2248604561801 549755813888 11445650295479 1717986918400000 Bool.false 25656997761 1099511627776 22887526950333 3435973836800000 Bool.false

noncomputable def ep707 := nat_lit 2549844942489283224141824

noncomputable abbrev qz675 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep708 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz63 qz675) Bool.false 2248604561801 549755813888 11445650295479 1717986918400000 Bool.false 25656997761 1099511627776 22887526950333 3435973836800000

noncomputable def ep709 := @Enclosure.Complex.IsNear.addLitP qz63 qz675 Bool.false 2334933179085 549755813888 5613101549413 858993459200000 Bool.false 13532537381 137438953472 5612543574413 858993459200000 Bool.true

noncomputable abbrev qz676 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz124 := (@HMul.hMul Real Real Real qz267 qz277 qz676)

noncomputable abbrev qz433 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep710 := @Enclosure.Complex.IsNear.of_eq qz675 (Complex.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz124)))) Bool.true 21582154321 137438953472 219447196653 1717986918400000 Bool.true 82603301287 1099511627776 437352652681 3435973836800000 (BSN.cpow_neg_s_mk qz12 144530 1000 33 qz13 rfl)

noncomputable abbrev qz434 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz435 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz677 := (@HDiv.hDiv Real Real Real qz1 qz435 qz14)

noncomputable def ep711 := @Enclosure.Real.IsNear.inv_image qz434 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz434 (Real.sqrt qz677) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz677) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep712 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 200000 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep713 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz676 144530 1000 0 1 15746868335186131 4503599627370496 1000000001 200000000000000 227589488048445151343 450359962737049600 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz677) Bool.false 66047152845744529997824 18889465931478580854784 1000000001000000 200000000000000000000 15746868335186131 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep712 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep714 := nat_lit 2188655913083002059607280468051261719802658750441119630023405239756178455592960

noncomputable def ep715 := nat_lit 1156893113539527487075925798302046667539395666253589638545473036810599858176

noncomputable def ep716 := nat_lit 5730320993033560444944754488841767857259518658171855123979844862063726412496896

noncomputable def ep717 := BSN.sin_dyadic_bound_f 2414969524 2147483648 3 2 1048576 400391 ep714 ep60 ep715 ep716 ep63 ep715 945896 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2414969524) qz15 0 2 ep714 ep60 ep715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2414969524) qz16 0 2 ep716 ep63 ep715 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 529898069) qz35)

noncomputable def ep718 := @Enclosure.Real.IsNear.cos_image qz124 qz436 Bool.false 529898069 1048576 759 1048576 Bool.true 945896 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 227589488048445151343 450359962737049600 14453000014453 20000000000000000 529898069 1048576 759 1048576 (ep713 rfl) rfl) (Enclosure.sfrac_false_div 529898069 1048576) (BSN.cos_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169938372638812288319488) qz36) 226375608064910080 72057594037927936 Bool.false 945896 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 529898069 1048576 226375608064910080 72057594037927936 80 169938372638812288319488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 945896 1048576 169938372638812288319488 151115727451828646838272 2414969524 2147483648 400391 400000 (ep717 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep719 := nat_lit 1216434126429907600887189560383279642853716814985623612074578676769792741933056

noncomputable def ep720 := nat_lit 3646988593062643747687416829553234835226071653624363656946645084235757026082816

noncomputable def ep721 := BSN.cos_dyadic_bound_f 2414969524 2147483648 3 2 1048576 400391 ep719 ep67 ep715 ep720 ep69 ep715 452539 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2414969524) qz20 0 2 ep719 ep67 ep715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2414969524) qz21 0 2 ep720 ep69 ep715 rfl rfl rfl rfl) rfl rfl

noncomputable def ep722 := @Enclosure.Real.IsNear.sin_image qz124 qz436 Bool.false 529898069 1048576 759 1048576 Bool.false 452539 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz124 Bool.false 227589488048445151343 450359962737049600 14453000014453 20000000000000000 529898069 1048576 759 1048576 (ep713 rfl) rfl) (Enclosure.sfrac_false_div 529898069 1048576) (BSN.sin_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 169938372638812288319488) qz36) 226375608064910080 72057594037927936 Bool.false 452539 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 529898069 1048576 226375608064910080 72057594037927936 80 169938372638812288319488 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 452539 1048576 169938372638812288319488 151115727451828646838272 2414969524 2147483648 400391 400000 (ep721 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz437 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep711 rfl rfl) rfl)

noncomputable def ep723 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz124)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz124))) Bool.true 21582154321 137438953472 219447196653 1717986918400000 Bool.true 82603301287 1099511627776 437352652681 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz433 (Real.cos qz124) 182533 1048576 1 1048576 118237 131072 2388259 3276800000 21582154321 137438953472 219447196653 1717986918400000 qz437 (@Enclosure.Real.IsNear.recentre' (Real.cos qz124) Bool.true 945896 1048576 152848576 209715200000 118237 131072 2388259 3276800000 (ep718 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz433 (@Neg.neg Real Real.instNeg (Real.sin qz124)) 182533 1048576 1 1048576 452539 1048576 2388259 3276800000 82603301287 1099511627776 437352652681 3435973836800000 qz437 (@Enclosure.Real.IsNear.neg (Real.sin qz124) Bool.false 452539 1048576 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz124) Bool.false 452539 1048576 152848576 209715200000 452539 1048576 2388259 3276800000 (ep722 rfl rfl) rfl)) rfl)

noncomputable def ep724 := @ep709 21582154321 137438953472 219447196653 1717986918400000 Bool.true 82603301287 1099511627776 437352652681 3435973836800000 Bool.false 309045857746294587523072 2248604561801 549755813888 11445650295479 1717986918400000 Bool.false 3526270921505287176192 25656997761 1099511627776 22887526950333 3435973836800000 EMRow51.d9 (ep710 ep723) rfl rfl

noncomputable abbrev qz678 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz125 := (@HMul.hMul Real Real Real qz267 qz277 qz678)

noncomputable abbrev qz438 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34)))

noncomputable def ep725 := @Enclosure.Complex.IsNear.of_eq qz674 (Complex.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz125)))) Bool.false 140931807471 1099511627776 86385935069 687194767360000 Bool.true 62639296083 549755813888 10791441493 85899345920000 (BSN.cpow_neg_s_mk qz12 144530 1000 34 qz13 rfl)

noncomputable abbrev qz439 := (Real.sqrt (@Nat.cast Real Real.instNatCast 34))

noncomputable abbrev qz440 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz679 := (@HDiv.hDiv Real Real Real qz1 qz440 qz14)

noncomputable def ep726 := @Enclosure.Real.IsNear.inv_image qz439 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz439 (Real.sqrt qz679) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz679) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep727 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 200000 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep728 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz678 144530 1000 0 1 15881309401485523 4503599627370496 1000000001 200000000000000 229532564779670263919 450359962737049600 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz679) Bool.false 66611039547888335060992 18889465931478580854784 1000000001000000 200000000000000000000 15881309401485523 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep729 := nat_lit 211913799081140129566393441441569357091921232222828098335225176205625203260961

noncomputable def ep730 := nat_lit 35165503402841481577486426735450464300935186007822936952238578015130254881

noncomputable def ep731 := nat_lit 635671066236614705736025351471237170347161826296468649131771051460845349273121

noncomputable def ep732 := BSN.cos_dyadic_bound_f 1560502989 2147483648 3 2 1048576 400391 ep729 ep67 ep730 ep731 ep69 ep730 783699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1560502989) qz20 0 2 ep729 ep67 ep730 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1560502989) qz21 0 2 ep731 ep69 ep730 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 534422147) qz35)

noncomputable def ep733 := @Enclosure.Real.IsNear.cos_image qz125 qz441 Bool.false 534422147 1048576 759 1048576 Bool.false 783699 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 229532564779670263919 450359962737049600 14453000014453 20000000000000000 534422147 1048576 759 1048576 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 534422147 1048576) (BSN.cos_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109810635671840713867264) qz36) 226375608064910080 72057594037927936 Bool.false 783699 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 534422147 1048576 226375608064910080 72057594037927936 81 109810635671840713867264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 783699 1048576 109810635671840713867264 151115727451828646838272 1560502989 2147483648 400391 400000 (ep732 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep734 := nat_lit 5930050876918467179154336548416042641

noncomputable def ep735 := BSN.sin_dyadic_bound_f 1560502989 2147483648 2 1 1048576 400391 ep734 ep147 ep734 ep734 ep148 ep734 696654 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1560502989) qz15 0 1 ep734 ep147 ep734 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1560502989) qz16 0 1 ep734 ep148 ep734 rfl rfl rfl rfl) rfl rfl

noncomputable def ep736 := @Enclosure.Real.IsNear.sin_image qz125 qz441 Bool.false 534422147 1048576 759 1048576 Bool.false 696654 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz125 Bool.false 229532564779670263919 450359962737049600 14453000014453 20000000000000000 534422147 1048576 759 1048576 (ep728 rfl) rfl) (Enclosure.sfrac_false_div 534422147 1048576) (BSN.sin_reduce0 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109810635671840713867264) qz36) 226375608064910080 72057594037927936 Bool.false 696654 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 534422147 1048576 226375608064910080 72057594037927936 81 109810635671840713867264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 696654 1048576 109810635671840713867264 151115727451828646838272 1560502989 2147483648 400391 400000 (ep735 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz442 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 34))) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep726 rfl rfl) rfl)

noncomputable def ep737 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz125)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz125))) Bool.false 140931807471 1099511627776 86385935069 687194767360000 Bool.true 62639296083 549755813888 10791441493 85899345920000 (@Enclosure.Real.IsNear.mulLit_ff qz438 (Real.cos qz125) 179829 1048576 1 1048576 783699 1048576 2388259 3276800000 140931807471 1099511627776 86385935069 687194767360000 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz125) Bool.false 783699 1048576 152848576 209715200000 783699 1048576 2388259 3276800000 (ep733 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz438 (@Neg.neg Real Real.instNeg (Real.sin qz125)) 179829 1048576 1 1048576 348327 524288 2388259 3276800000 62639296083 549755813888 10791441493 85899345920000 qz442 (@Enclosure.Real.IsNear.neg (Real.sin qz125) Bool.false 348327 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz125) Bool.false 696654 1048576 152848576 209715200000 348327 524288 2388259 3276800000 (ep736 rfl rfl) rfl)) rfl)

noncomputable def ep738 := @ep706 140931807471 1099511627776 86385935069 687194767360000 Bool.true 62639296083 549755813888 10791441493 85899345920000 Bool.false ep707 4638140931073 1099511627776 23323230266303 3435973836800000 Bool.true 54767550712941002096640 99621594405 1099511627776 23319184610053 3435973836800000 (ep708 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep724 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep725 ep737) rfl rfl

noncomputable abbrev qz680 := (Real.log (Enclosure.sfrac Bool.false 35 1))

noncomputable abbrev qz126 := (@HMul.hMul Real Real Real qz267 qz277 qz680)

noncomputable abbrev qz443 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35)))

noncomputable def ep739 := @Enclosure.Complex.IsNear.of_eq qz673 (Complex.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz126)))) Bool.false 18816081801 549755813888 52995413491 429496729600000 Bool.false 91000314907 549755813888 106627180107 858993459200000 (BSN.cpow_neg_s_mk qz12 144530 1000 35 qz13 rfl)

noncomputable abbrev qz444 := (Real.sqrt (@Nat.cast Real Real.instNatCast 35))

noncomputable abbrev qz445 := (@Nat.cast Real Real.instNatCast 35)

noncomputable abbrev qz681 := (@HDiv.hDiv Real Real Real qz1 qz445 qz14)

noncomputable def ep740 := @Enclosure.Real.IsNear.inv_image qz444 6203459 1048576 1 1048576 88620 88621 524288 (@Enclosure.Real.IsNear.of_eq qz444 (Real.sqrt qz681) Bool.false 6203459 1048576 1 1048576 (BSN.sqrt_natCast_div_one 35) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz681) Bool.false 6203459 1048576 1 1048576 6203459 1048576 1 1048576 (BSN.sqrt_enclosure 35 1 3101729 3101730 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep741 := BSN.log_dyadic_bound 3 67 2 1 13467 524288 200000 9 9 46982 70 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 3) (BSN.artanhQ 67) 0 1 9 13467 9 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep742 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz680 144530 1000 0 1 16011859227414739 4503599627370496 1000000001 200000000000000 231419401413825222767 450359962737049600 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz681) Bool.false 67158605204982549446656 18889465931478580854784 1000000001000000 200000000000000000000 16011859227414739 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep741 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep743 := nat_lit 36758142790324581021507208302725601

noncomputable def ep744 := BSN.sin_dyadic_bound_f 437863143 2147483648 2 1 1048576 400391 ep743 ep147 ep743 ep743 ep148 ep743 212322 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 437863143) qz15 0 1 ep743 ep147 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 437863143) qz16 0 1 ep743 ep148 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 538815281) qz35)

noncomputable def ep745 := @Enclosure.Real.IsNear.cos_image qz126 qz446 Bool.false 538815281 1048576 759 1048576 Bool.false 212322 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 231419401413825222767 450359962737049600 14453000014453 20000000000000000 538815281 1048576 759 1048576 (ep742 rfl) rfl) (Enclosure.sfrac_false_div 538815281 1048576) (BSN.cos_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30811879517464268111872) qz36) 226375608064910080 72057594037927936 Bool.false 212322 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 538815281 1048576 226375608064910080 72057594037927936 81 30811879517464268111872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 212322 1048576 30811879517464268111872 151115727451828646838272 437863143 2147483648 400391 400000 (ep744 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep746 := BSN.cos_dyadic_bound_f 437863143 2147483648 2 1 1048576 400391 ep743 ep80 ep743 ep743 ep81 ep743 1026854 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 437863143) qz20 0 1 ep743 ep80 ep743 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 437863143) qz21 0 1 ep743 ep81 ep743 rfl rfl rfl rfl) rfl rfl

noncomputable def ep747 := @Enclosure.Real.IsNear.sin_image qz126 qz446 Bool.false 538815281 1048576 759 1048576 Bool.true 1026854 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz126 Bool.false 231419401413825222767 450359962737049600 14453000014453 20000000000000000 538815281 1048576 759 1048576 (ep742 rfl) rfl) (Enclosure.sfrac_false_div 538815281 1048576) (BSN.sin_reduce3 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30811879517464268111872) qz36) 226375608064910080 72057594037927936 Bool.false 1026854 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 538815281 1048576 226375608064910080 72057594037927936 81 30811879517464268111872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1026854 1048576 30811879517464268111872 151115727451828646838272 437863143 2147483648 400391 400000 (ep746 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz447 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 35))) Bool.false 177241 1048576 1 1048576 177241 1048576 1 1048576 (ep740 rfl rfl) rfl)

noncomputable def ep748 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz126)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz126))) Bool.false 18816081801 549755813888 52995413491 429496729600000 Bool.false 91000314907 549755813888 106627180107 858993459200000 (@Enclosure.Real.IsNear.mulLit_ff qz443 (Real.cos qz126) 177241 1048576 1 1048576 106161 524288 2388259 3276800000 18816081801 549755813888 52995413491 429496729600000 qz447 (@Enclosure.Real.IsNear.recentre' (Real.cos qz126) Bool.false 212322 1048576 152848576 209715200000 106161 524288 2388259 3276800000 (ep745 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 (@Neg.neg Real Real.instNeg (Real.sin qz126)) 177241 1048576 1 1048576 513427 524288 2388259 3276800000 91000314907 549755813888 106627180107 858993459200000 qz447 (@Enclosure.Real.IsNear.neg (Real.sin qz126) Bool.true 513427 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz126) Bool.true 1026854 1048576 152848576 209715200000 513427 524288 2388259 3276800000 (ep747 rfl rfl) rfl)) rfl)

noncomputable def ep749 := @ep703 18816081801 549755813888 52995413491 429496729600000 Bool.false 91000314907 549755813888 106627180107 858993459200000 Bool.false ep704 4675773094675 1099511627776 23747193574231 3435973836800000 Bool.false 45288353658583165960192 82379035409 1099511627776 23745693330481 3435973836800000 (ep705 (BSN.head_sum_c_succ qz5 34 35 rfl rfl) (ep738 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep739 ep748) rfl rfl

noncomputable abbrev qz682 := (Real.log (Enclosure.sfrac Bool.false 36 1))

noncomputable abbrev qz127 := (@HMul.hMul Real Real Real qz267 qz277 qz682)

noncomputable abbrev qz448 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36)))

noncomputable def ep750 := @Enclosure.Complex.IsNear.of_eq qz672 (Complex.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz127)))) Bool.true 83020988387 549755813888 209902307313 1717986918400000 Bool.true 302864279 4294967296 52277744797 429496729600000 (BSN.cpow_neg_s_mk qz12 144530 1000 36 qz13 rfl)

noncomputable abbrev qz449 := (Real.sqrt (@Nat.cast Real Real.instNatCast 36))

noncomputable abbrev qz450 := (@Nat.cast Real Real.instNatCast 36)

noncomputable abbrev qz683 := (@HDiv.hDiv Real Real Real qz1 qz450 qz14)

noncomputable def ep751 := @Enclosure.Real.IsNear.inv_image qz449 6291457 1048576 1 1048576 87381 87382 524288 (@Enclosure.Real.IsNear.of_eq qz449 (Real.sqrt qz683) Bool.false 6291457 1048576 1 1048576 (BSN.sqrt_natCast_div_one 36) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz683) Bool.false 6291457 1048576 1 1048576 6291457 1048576 1 1048576 (BSN.sqrt_enclosure 36 1 3145728 3145729 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep752 := BSN.log_dyadic_bound 4 68 3 2 320720640 524288 200000 370688 768 61752 72 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 68) 0 2 370688 320720640 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep753 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz682 144530 1000 0 1 16138732561338579 4503599627370496 1000000001 200000000000000 233253101709026482287 450359962737049600 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz683) Bool.false 67690750536952647254016 18889465931478580854784 1000000001000000 200000000000000000000 16138732561338579 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep752 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep754 := nat_lit 2262628128983992482687348174977717141542199885318478237825903290473335787649185

noncomputable def ep755 := nat_lit 1236371858296255884233477627982638935983256487941490703882504614730951588001

noncomputable def ep756 := nat_lit 5923929069092262564178105304020144431476074427234585352213936943768219807938721

noncomputable def ep757 := BSN.sin_dyadic_bound_f 2435110307 2147483648 3 2 1048576 400391 ep754 ep60 ep755 ep756 ep63 ep755 950098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2435110307) qz15 0 2 ep754 ep60 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2435110307) qz16 0 2 ep756 ep63 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 271542349) qz25)

noncomputable def ep758 := @Enclosure.Real.IsNear.cos_image qz127 qz451 Bool.false 271542349 524288 379 524288 Bool.true 950098 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 233253101709026482287 450359962737049600 14453000014453 20000000000000000 271542349 524288 379 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 271542349 524288) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85677827121089156743168) qz26) 226375608064910080 72057594037927936 Bool.false 950098 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 271542349 524288 226375608064910080 72057594037927936 82 85677827121089156743168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 950098 1048576 85677827121089156743168 75557863725914323419136 2435110307 2147483648 400391 400000 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := nat_lit 1257565125817016381885963865044501807050548050282684127993894052313955860510881

noncomputable def ep760 := nat_lit 3770222633734456633889424639877540143279677637872169402573917147712405678356641

noncomputable def ep761 := BSN.cos_dyadic_bound_f 2435110307 2147483648 3 2 1048576 400391 ep759 ep67 ep755 ep760 ep69 ep755 443648 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2435110307) qz20 0 2 ep759 ep67 ep755 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2435110307) qz21 0 2 ep760 ep69 ep755 rfl rfl rfl rfl) rfl rfl

noncomputable def ep762 := @Enclosure.Real.IsNear.sin_image qz127 qz451 Bool.false 271542349 524288 379 524288 Bool.false 443648 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz127 Bool.false 233253101709026482287 450359962737049600 14453000014453 20000000000000000 271542349 524288 379 524288 (ep753 rfl) rfl) (Enclosure.sfrac_false_div 271542349 524288) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85677827121089156743168) qz26) 226375608064910080 72057594037927936 Bool.false 443648 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 271542349 524288 226375608064910080 72057594037927936 82 85677827121089156743168 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 443648 1048576 85677827121089156743168 75557863725914323419136 2435110307 2147483648 400391 400000 (ep761 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz452 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 36))) Bool.false 174763 1048576 1 1048576 174763 1048576 1 1048576 (ep751 rfl rfl) rfl)

noncomputable def ep763 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz127)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz127))) Bool.true 83020988387 549755813888 209902307313 1717986918400000 Bool.true 302864279 4294967296 52277744797 429496729600000 (@Enclosure.Real.IsNear.mulLit_ft qz448 (Real.cos qz127) 174763 1048576 1 1048576 475049 524288 1192567 1638400000 83020988387 549755813888 209902307313 1717986918400000 qz452 (@Enclosure.Real.IsNear.recentre' (Real.cos qz127) Bool.true 950098 1048576 76324288 104857600000 475049 524288 1192567 1638400000 (ep758 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz448 (@Neg.neg Real Real.instNeg (Real.sin qz127)) 174763 1048576 1 1048576 1733 4096 1192567 1638400000 302864279 4294967296 52277744797 429496729600000 qz452 (@Enclosure.Real.IsNear.neg (Real.sin qz127) Bool.false 1733 4096 1192567 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz127) Bool.false 443648 1048576 76324288 104857600000 1733 4096 1192567 1638400000 (ep762 rfl rfl) rfl)) rfl)

noncomputable def ep764 := @ep700 83020988387 549755813888 209902307313 1717986918400000 Bool.true 302864279 4294967296 52277744797 429496729600000 Bool.false ep701 4509731117901 1099511627776 24166998188857 3435973836800000 Bool.false 20812466559186370560 4845779985 1099511627776 24163915288857 3435973836800000 (ep702 (BSN.head_sum_c_succ qz5 35 36 rfl rfl) (ep749 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep750 ep763) rfl rfl

noncomputable def ep765 := @Enclosure.Complex.IsNear.mul qz119 (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 2054362276754389559209 25494353792056556519424 1095248339091137501220449 ep563 Bool.true

noncomputable abbrev qz128 := (Complex.re qz430)

noncomputable abbrev qz129 := (Complex.im qz430)

noncomputable def ep766 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 15566978580230291008225 203954830336452452155392 208027608687485381027

noncomputable def ep767 := nat_lit 3445182944872507637760000

noncomputable def ep768 := nat_lit 7966985560017673912320000000

noncomputable def ep769 := nat_lit 3351976876840397599454359690707882662820839424

noncomputable def ep770 := @Enclosure.Real.IsNear.mulLit_ff qz128 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 167761117145 1099511627776 414743594099 3435973836800000 92792530505

noncomputable abbrev qz684 := (Real.log (Enclosure.sfrac Bool.false 37 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz277 qz684)

noncomputable abbrev qz131 := (Real.sin (@HMul.hMul Real Real Real qz267 qz277 qz684))

noncomputable abbrev qz685 := (@Nat.cast Real Real.instNatCast 37)

noncomputable abbrev qz453 := (@Inv.inv Real Real.instInv (Real.sqrt qz685))

noncomputable abbrev qz686 := (@Neg.neg Real Real.instNeg qz131)

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq qz119 (Complex.mk (@HMul.hMul Real Real Real qz0 qz453 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz453 qz686)) Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (BSN.cpow_neg_s_mk qz12 144530 1000 37 qz13 rfl)

noncomputable abbrev qz454 := (Real.sqrt qz685)

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 qz685 qz14)

noncomputable def ep772 := @Enclosure.Real.IsNear.inv_image qz454 6378239 1048576 1 1048576 86192 86193 524288 (@Enclosure.Real.IsNear.of_eq qz454 (Real.sqrt qz455) Bool.false 6378239 1048576 1 1048576 (BSN.sqrt_natCast_div_one 37) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz455) Bool.false 6378239 1048576 1 1048576 6378239 1048576 1 1048576 (BSN.sqrt_enclosure 37 1 3189119 3189120 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep773 := BSN.log_dyadic_bound 5 69 3 2 340006815 524288 200000 597000 1875 76117 74 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 5) (BSN.artanhQ 69) 0 2 597000 340006815 1875 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz132 := qz684

noncomputable abbrev qz456 := (Real.log (@HDiv.hDiv Real Real Real qz1 qz685 qz14))

noncomputable def ep774 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz132 144530 1000 0 1 16262126971752659 4503599627370496 1000000001 200000000000000 235036521122741180527 450359962737049600 14453000014453 20000000000000000 qz18 (BSN.isNear_log_sfrac 37 1 16262126971752659 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz456 Bool.false 68208304206130064654336 18889465931478580854784 1000000001000000 200000000000000000000 16262126971752659 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 76117 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep773 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep775 := nat_lit 450660503659873803673065412677878016

noncomputable def ep776 := BSN.cos_dyadic_bound_f 819336636 2147483648 2 1 1048576 400391 ep775 ep80 ep775 ep775 ep81 ep775 973177 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 819336636) qz20 0 1 ep775 ep80 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 819336636) qz21 0 1 ep775 ep81 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 136809261) qz17)

noncomputable def ep777 := @Enclosure.Real.IsNear.cos_image qz130 qz457 Bool.false 136809261 262144 759 1048576 Bool.false 973177 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 235036521122741180527 450359962737049600 14453000014453 20000000000000000 136809261 262144 759 1048576 (ep774 rfl) rfl) (Enclosure.sfrac_false_div 136809261 262144) (BSN.cos_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14413922545348171005952) qz19) 226375608064910080 72057594037927936 Bool.false 973177 1048576 83 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 136809261 262144 226375608064910080 72057594037927936 83 14413922545348171005952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 973177 1048576 14413922545348171005952 37778931862957161709568 819336636 2147483648 400391 400000 (ep776 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep778 := BSN.sin_dyadic_bound_f 819336636 2147483648 2 1 1048576 400391 ep775 ep147 ep775 ep775 ep148 ep775 390430 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 819336636) qz15 0 1 ep775 ep147 ep775 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 819336636) qz16 0 1 ep775 ep148 ep775 rfl rfl rfl rfl) rfl rfl

noncomputable def ep779 := @Enclosure.Real.IsNear.sin_image qz130 qz457 Bool.false 136809261 262144 759 1048576 Bool.false 390430 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 235036521122741180527 450359962737049600 14453000014453 20000000000000000 136809261 262144 759 1048576 (ep774 rfl) rfl) (Enclosure.sfrac_false_div 136809261 262144) (BSN.sin_reduce0 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14413922545348171005952) qz19) 226375608064910080 72057594037927936 Bool.false 390430 1048576 83 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 136809261 262144 226375608064910080 72057594037927936 83 14413922545348171005952 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 390430 1048576 14413922545348171005952 37778931862957161709568 819336636 2147483648 400391 400000 (ep778 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz458 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz685)) Bool.false 172385 1048576 1 1048576 172385 1048576 1 1048576 (ep772 rfl rfl) rfl)

noncomputable def ep780 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz453 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz453 qz686) Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (@Enclosure.Real.IsNear.mulLit_ff qz453 (Real.cos qz130) 172385 1048576 1 1048576 973177 1048576 2388259 3276800000 167761117145 1099511627776 414743594099 3435973836800000 qz458 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 973177 1048576 152848576 209715200000 973177 1048576 2388259 3276800000 (ep777 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz453 qz686 172385 1048576 1 1048576 195215 524288 2388259 3276800000 33652137775 549755813888 103230627431 858993459200000 qz458 (@Enclosure.Real.IsNear.neg qz131 Bool.false 195215 524288 2388259 3276800000 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 390430 1048576 152848576 209715200000 195215 524288 2388259 3276800000 (ep779 rfl rfl) rfl)) rfl)

noncomputable def ep781 := @ep770 185495837592 0 1 15566978580230291008225 203954830336452452155392 208027608687485381027 ep767 (@Enclosure.Complex.IsNear.re_isNear qz119 Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (ep771 ep780))

noncomputable def ep782 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 92792530505 185495837592 0 1 Bool.false

noncomputable def ep783 := @Enclosure.Complex.IsNear.addLitP qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 208521709 417783418 0 1 Bool.true 53476100

noncomputable def ep784 := @ep783 208891709 0 1 Bool.false 1 888 0 1 Bool.false 14453 44400 0 1 Bool.false 185585061010 92792530505 185495837592 0 1 Bool.false 644773030177 644773030177 9274791879600 0 1

noncomputable abbrev qz133 := (@HDiv.hDiv Complex Complex Complex qz409 qz431 (@HSub.hSub Complex Complex Complex qz401 qz271 (1 : Complex)))

noncomputable def ep785 := @Enclosure.Complex.IsNear.addLitP qz133 qz97 Bool.true 74000000 83556683600 0 1 Bool.true 21390440000 83556683600 0 1

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq qz133 (Complex.mk (Enclosure.sfrac Bool.true 74000000 83556683600) (Enclosure.sfrac Bool.true 21390440000 83556683600)) Bool.true 74000000 83556683600 0 1 Bool.true 21390440000 83556683600 0 1

noncomputable def ep787 := @ep785 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 83408683600 208521709 417783418 0 1 Bool.true 21390440000 53476100 208891709 0 1 (ep786 (BSN.N_div_s_sub_one_mk qz12 144530 1000 37 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 74000000 83556683600) (Enclosure.sfrac Bool.true 21390440000 83556683600) Bool.true 74000000 83556683600 0 1 Bool.true 21390440000 83556683600 0 1 (Enclosure.Real.IsNear.const Bool.true 74000000 83556683600) (Enclosure.Real.IsNear.const Bool.true 21390440000 83556683600))) qz98 rfl

noncomputable abbrev qz134 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz459 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz668 qz671 1))

noncomputable abbrev qz135 := qz459

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz135)) Bool.false 1 888 0 1

noncomputable def ep789 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz135) Bool.false 0 1 0 1 Bool.false

noncomputable def ep790 := @ep789 0 1 0 1 Bool.false 1 888 0 1 Bool.false 14453 44400 0 1 Bool.false 1 1 888 0 1 Bool.false 14453 14453 44400 0

noncomputable def ep791 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep792 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz135 Bool.false 1 888 0 1 Bool.false 14453 44400 0 1

noncomputable abbrev qz136 := (Complex.re qz459)

noncomputable abbrev qz137 := (Complex.im qz459)

noncomputable def ep793 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 1 888 0 1 0 1 0

noncomputable def ep794 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 1 24 0 1 1 37 0 1 1

noncomputable def ep795 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep796 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep797 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow51.d10 rfl) qz422

noncomputable def ep798 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep799 := ep798 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz92 qz12) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 144530 1000 qz13) (@Enclosure.Complex.IsNear.mk qz92 qz12 Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 qz415 qz18))

noncomputable def ep800 := @ep796 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep801 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 144530 1000 0 1 0 1 0

noncomputable def ep802 := @ep801 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep803 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 14453 1200 0 1 0 1 0 1 14453

noncomputable def ep804 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 144530 1000 0 1 14453 1200 0

noncomputable def ep805 := @ep804 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep806 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep807 := @ep806 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep808 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 (@ep795 1 24 0 1 (ep800 rfl) (ep802 rfl) rfl rfl) (@ep803 14453 1200 0 1 (ep805 rfl) (ep807 rfl) rfl rfl)

noncomputable def ep809 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 ep808

noncomputable abbrev qz138 := (@Enclosure.Complex.IsNear.re_isNear qz459 Bool.false 1 37 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz459 (Complex.mk (Enclosure.sfrac Bool.false 1 37) qz556) Bool.false 1 37 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 37 1 37 EMRow51.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 37) qz556 Bool.false 1 37 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 37) qz559)))

noncomputable def ep810 := @ep794 888 0 1 ep809 qz138

noncomputable def ep811 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 14453 1200 0 1 0 1 0 1 0

noncomputable def ep812 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14453 1200 0 1 ep808

noncomputable abbrev qz139 := (@Enclosure.Complex.IsNear.im_isNear qz459 Bool.false 1 37 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz459 (Complex.mk (Enclosure.sfrac Bool.false 1 37) qz556) Bool.false 1 37 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 37 1 37 EMRow51.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 37) qz556 Bool.false 1 37 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 37) qz559)))

noncomputable def ep813 := @ep811 1 0 1 ep812 qz139

noncomputable def ep814 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) 0 1 0 1 14453 44400 0

noncomputable def ep815 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 0 1 0 1 0

noncomputable def ep816 := @ep815 1 0 1 ep809 qz139

noncomputable def ep817 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 14453 1200 0 1 1 37 0 1 14453

noncomputable def ep818 := @ep817 44400 0 1 ep812 qz138

noncomputable def ep819 := @ep790 1 (@ep791 0 1 0 1 (BSN.bern_sum_base qz5 37) qz113) (ep792 (@ep793 1 1 1 888 0 1 (ep810 rfl) (ep813 rfl) rfl rfl) (@ep814 1 14453 14453 44400 0 1 (ep816 rfl) (ep818 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep820 := ep784 (ep787 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep788 Bool.false 14453 44400 0 1 (BSN.bern_sum_succ qz5 37 0 1 1 rfl rfl) (ep819 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep821 := @Enclosure.Real.IsNear.mulLit_tf qz129 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 33652137775 549755813888 103230627431 858993459200000 644773030177

noncomputable def ep822 := @ep821 9274791879600 0 1 867919633804825465447 203954830336452452155392 66560324455758806985287 ep768 (@Enclosure.Complex.IsNear.im_isNear qz119 Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (ep771 ep780))

noncomputable def ep823 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 92792530505 185495837592 0 1 Bool.false

noncomputable def ep824 := nat_lit 2039548303364524521553920

noncomputable def ep825 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 21633568769492063416933 ep824 7227445511181404489879

noncomputable def ep826 := nat_lit 861295736218126909440000000

noncomputable def ep827 := nat_lit 31867942240070695649280000

noncomputable def ep828 := nat_lit 4162694800768125215397865357124411766060613632

noncomputable def ep829 := @Enclosure.Real.IsNear.mulLit_ff qz128 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 167761117145 1099511627776 414743594099 3435973836800000 644773030177

noncomputable def ep830 := @ep829 9274791879600 0 1 21633568769492063416933 ep824 7227445511181404489879 ep826 (@Enclosure.Complex.IsNear.re_isNear qz119 Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (ep771 ep780))

noncomputable def ep831 := @Enclosure.Real.IsNear.mulLit_tf qz129 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz120 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 33652137775 549755813888 103230627431 858993459200000 92792530505

noncomputable def ep832 := @ep831 185495837592 0 1 3122667021045150326375 101977415168226226077696 1915806228988271456531 ep827 (@Enclosure.Complex.IsNear.im_isNear qz119 Bool.false 167761117145 1099511627776 414743594099 3435973836800000 Bool.true 33652137775 549755813888 103230627431 858993459200000 (ep771 ep780))

noncomputable abbrev qz687 := (ep820 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep833 := @ep765 13606590550470314370189 679849434454841507184640 ep694 ep691 (@ep766 ep767 867919633804825465447 203954830336452452155392 66560324455758806985287 ep768 ep769 2054362276754389559209 25494353792056556519424 1095248339091137501220449 ep563 (ep781 (@ep782 644773030177 9274791879600 0 1 qz687) rfl) (ep822 (@ep823 644773030177 9274791879600 0 1 qz687) rfl) rfl rfl) (@ep825 ep826 3122667021045150326375 101977415168226226077696 1915806228988271456531 ep827 ep828 13606590550470314370189 679849434454841507184640 ep694 ep691 (ep830 (@ep823 644773030177 9274791879600 0 1 qz687) rfl) (ep832 (@ep782 644773030177 9274791879600 0 1 qz687) rfl) rfl rfl)

noncomputable def ep834 := @ep697 ep690 ep691 (@ep698 3435973836800000 (BSN.head_sum_c_eq qz5 37) (ep699 (BSN.head_sum_c_succ qz5 36 37 rfl rfl) (ep764 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep833 rfl rfl rfl

noncomputable def ep835 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 37) Bool.false 1665959471179272688297 398349278000883695616 ep562 ep563 Bool.true 10610350493456567049789 679849434454841507184640 ep690 ep691 (@ep692 ep563 Bool.true 10610350493456567049789 679849434454841507184640 ep690 ep691 (BSN.zetaApproximant_eq_folded' qz5 1 37 rfl) (ep834 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) (Complex.im (zetaApproximant qz5 1 37)) 3 4096 1250759

noncomputable def ep837 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76)) Bool.false 768 1048576 80048576

noncomputable def ep838 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) qz405 Bool.false 161414965 1048576 395

noncomputable def ep839 := nat_lit 4634301046356001311640505233026349453097798502561139401474719220496388163690625

noncomputable def ep840 := nat_lit 13869498644844069705508059321618415038988767476142743281834707662384294365290625

noncomputable def ep841 := BSN.cos_dyadic_bound_f 3371683985 2147483648 3 2 1048576 400391 ep839 ep67 ep686 ep840 ep69 ep686 768 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3371683985) qz20 0 2 ep839 ep67 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3371683985) qz21 0 2 ep840 ep69 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable def ep842 := @ep838 1048576 Bool.false 768 1048576 1 200000 (@ep566 161414965 1048576 395 1048576 ep684 rfl) (Enclosure.sfrac_false_div 161414965 1048576) (BSN.sin_reduce1 qz405 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237261167812391175454720) qz36) 226375608064910080 72057594037927936 Bool.false 768 1048576 24 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 161414965 1048576 226375608064910080 72057594037927936 24 237261167812391175454720 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 768 1048576 237261167812391175454720 151115727451828646838272 3371683985 2147483648 400391 400000 (ep841 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep843 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 37) Bool.false 1665959471179272688297 398349278000883695616 ep562 ep563 Bool.true 10610350493456567049789 679849434454841507184640 ep690 ep691 (@ep692 ep563 Bool.true 10610350493456567049789 679849434454841507184640 ep690 ep691 (BSN.zetaApproximant_eq_folded' qz5 1 37 rfl) (ep834 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow51.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 37 qz12) Bool.true ep547 ep548 ep549 ep550 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 37 qz12) ep551 Bool.true ep547 ep548 ep549 ep550 (@Eq.refl Real ep551) (@ep552 Bool.true ep547 ep548 ep549 ep550 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz74 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz75 (@Nat.cast Complex Complex.instNatCast j))))) qz76) (zetaApproximant qz5 1 37)) (@ep554 ep555 ep556 ep557 31831051480369701149367 ep548 ep558 ep559 ep560 ep547 ep548 ep549 ep550 (@ep561 3276800000 1665959471179272688297 398349278000883695616 ep562 ep563 ep553 ep555 ep556 ep557 (@ep564 209715200000 1048575 1048576 1250759 3276800000 (ep689 rfl rfl) rfl) ep835 rfl) (@ep836 3276800000 10610350493456567049789 679849434454841507184640 ep690 ep691 31831051480369701149367 ep548 ep558 ep559 (@ep837 209715200000 3 4096 1250759 3276800000 (ep842 rfl rfl) rfl) ep843 rfl) rfl rfl))

noncomputable abbrev qz745 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 146530 1000)))

noncomputable abbrev qz688 := qz745

noncomputable abbrev qz460 := qz688

noncomputable abbrev qz140 := (BSN.headSumC qz460 9)

noncomputable abbrev qz141 := qz460

noncomputable abbrev qz689 := (@Neg.neg Complex Complex.instNeg qz745)

noncomputable abbrev qz461 := qz689

noncomputable abbrev qz142 := qz461

noncomputable abbrev qz690 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz142)

noncomputable def ep844 := @Enclosure.Complex.IsNear.of_eq qz140 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 8) qz690) Bool.true 75625302037 274877906944 1071554442301 429496729600000 Bool.true 29399003275 68719476736 4285694009829 1717986918400000

noncomputable def ep845 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 8) qz690 Bool.false 10751288437 137438953472 1917755592089 858993459200000 Bool.true 457201371007 1099511627776 7673138640231 3435973836800000 Bool.true

noncomputable abbrev qz691 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz142)

noncomputable def ep846 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 7) qz691) Bool.false 10751288437 137438953472 1917755592089 858993459200000 Bool.true 457201371007 1099511627776 7673138640231 3435973836800000

noncomputable def ep847 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 7) qz691 Bool.false 97453110899 274877906944 1677118515793 858993459200000 Bool.true 86819181841 549755813888 3355374959711 1717986918400000 Bool.true

noncomputable abbrev qz692 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz142)

noncomputable def ep848 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 6) qz692) Bool.false 97453110899 274877906944 1677118515793 858993459200000 Bool.true 86819181841 549755813888 3355374959711 1717986918400000

noncomputable def ep849 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 6) qz692 Bool.false 145185274027 549755813888 2835333484601 1717986918400000 Bool.true 305678851381 549755813888 2835236690851 1717986918400000 Bool.false

noncomputable abbrev qz693 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz142)

noncomputable def ep850 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 5) qz693) Bool.false 145185274027 549755813888 2835333484601 1717986918400000 Bool.true 305678851381 549755813888 2835236690851 1717986918400000

noncomputable def ep851 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 5) qz693 Bool.false 771158992855 1099511627776 906572655927 687194767360000 Bool.true 714443654535 1099511627776 907037340927 687194767360000 Bool.true

noncomputable abbrev qz694 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz142)

noncomputable def ep852 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 4) qz694) Bool.false 771158992855 1099511627776 906572655927 687194767360000 Bool.true 714443654535 1099511627776 907037340927 687194767360000

noncomputable def ep853 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 4) qz694 Bool.false 517566913673 549755813888 1631385164709 1717986918400000 Bool.true 14513271015 68719476736 1631896420959 1717986918400000 Bool.true

noncomputable def ep854 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz142)) Bool.false 517566913673 549755813888 1631385164709 1717986918400000 Bool.true 14513271015 68719476736 1631896420959 1717986918400000

noncomputable def ep855 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz142) Bool.false 747987515413 549755813888 897815216927 1717986918400000 Bool.true 668788702725 1099511627776 1796778199479 3435973836800000 Bool.true

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz142)) Bool.false 747987515413 549755813888 897815216927 1717986918400000 Bool.true 668788702725 1099511627776 1796778199479 3435973836800000

noncomputable def ep857 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz142) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep858 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz141)

noncomputable abbrev qz746 := (Enclosure.sfrac Bool.false 146530 1000)

noncomputable abbrev qz695 := qz746

noncomputable abbrev qz462 := qz695

noncomputable abbrev qz143 := (@HMul.hMul Real Real Real qz267 qz462 (Real.log qz278))

noncomputable abbrev qz144 := qz462

noncomputable abbrev qz463 := (@Eq.refl Real qz695)

noncomputable abbrev qz145 := qz463

noncomputable def ep859 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz142) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz143)))) Bool.false 198231701525 549755813888 897815216927 1717986918400000 Bool.true 668788702725 1099511627776 1796778199479 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 2 qz145 rfl)

noncomputable def ep860 := nat_lit 874884406130210524817754712925423789523555284584765504755651482084709920013121

noncomputable def ep861 := nat_lit 598755083042738188635710355365239730286432742569724988171087259026505464641

noncomputable def ep862 := nat_lit 2623455708224546098075992718065540889110092988269157064290612271736076749110081

noncomputable def ep863 := BSN.cos_dyadic_bound_f 2224109431 2147483648 3 2 1048576 400391 ep860 ep67 ep861 ep862 ep69 ep861 534710 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2224109431) qz20 0 2 ep860 ep67 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2224109431) qz21 0 2 ep862 ep69 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz146 := (Enclosure.Real.IsNear.const Bool.false 146530 1000)

noncomputable abbrev qz696 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26625087) qz17)

noncomputable def ep864 := @Enclosure.Real.IsNear.cos_image qz143 qz696 Bool.false 26625087 262144 769 1048576 Bool.false 534710 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 332813589 3276800 14653 20000000 26625087 262144 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 (Real.log qz278) 146530 1000 0 1 363408 524288 1 200000 332813589 3276800 14653 20000000 qz146 qz283 rfl) rfl) (Enclosure.sfrac_false_div 26625087 262144) (BSN.cos_reduce0 qz696 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39126946904686758723584) qz19) 226375608064910080 72057594037927936 Bool.false 534710 1048576 16 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 26625087 262144 226375608064910080 72057594037927936 16 39126946904686758723584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 534710 1048576 39126946904686758723584 37778931862957161709568 2224109431 2147483648 400391 400000 (ep863 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep865 := nat_lit 1574312926967944754121049914981470629358170366058522128569635797945256651651905

noncomputable def ep866 := nat_lit 4122231110019690875154482436757069831612839591427206972463435805722962602621761

noncomputable def ep867 := BSN.sin_dyadic_bound_f 2224109431 2147483648 3 2 1048576 400391 ep865 ep60 ep861 ep866 ep63 ep861 901995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2224109431) qz15 0 2 ep865 ep60 ep861 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2224109431) qz16 0 2 ep866 ep63 ep861 rfl rfl rfl rfl) rfl rfl

noncomputable def ep868 := @Enclosure.Real.IsNear.sin_image qz143 qz696 Bool.false 26625087 262144 769 1048576 Bool.false 901995 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz143 Bool.false 332813589 3276800 14653 20000000 26625087 262144 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 (Real.log qz278) 146530 1000 0 1 363408 524288 1 200000 332813589 3276800 14653 20000000 qz146 qz283 rfl) rfl) (Enclosure.sfrac_false_div 26625087 262144) (BSN.sin_reduce0 qz696 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39126946904686758723584) qz19) 226375608064910080 72057594037927936 Bool.false 901995 1048576 16 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 26625087 262144 226375608064910080 72057594037927936 16 39126946904686758723584 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 901995 1048576 39126946904686758723584 37778931862957161709568 2224109431 2147483648 400391 400000 (ep867 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep869 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz143)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz143))) Bool.false 198231701525 549755813888 897815216927 1717986918400000 Bool.true 668788702725 1099511627776 1796778199479 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz280 (Real.cos qz143) 741455 1048576 1 1048576 267355 524288 2419509 3276800000 198231701525 549755813888 897815216927 1717986918400000 qz284 (@Enclosure.Real.IsNear.recentre' (Real.cos qz143) Bool.false 534710 1048576 154848576 209715200000 267355 524288 2419509 3276800000 (ep864 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz280 (@Neg.neg Real Real.instNeg (Real.sin qz143)) 741455 1048576 1 1048576 901995 1048576 2419509 3276800000 668788702725 1099511627776 1796778199479 3435973836800000 qz284 (@Enclosure.Real.IsNear.neg (Real.sin qz143) Bool.false 901995 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz143) Bool.false 901995 1048576 154848576 209715200000 901995 1048576 2419509 3276800000 (ep868 rfl rfl) rfl)) rfl)

noncomputable def ep870 := @ep857 198231701525 549755813888 897815216927 1717986918400000 Bool.true 668788702725 1099511627776 1796778199479 3435973836800000 Bool.false 747987515413 747987515413 549755813888 897815216927 1717986918400000 Bool.true 668788702725 668788702725 1099511627776 1796778199479 3435973836800000 (ep858 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep859 ep869) rfl rfl

noncomputable abbrev qz147 := (@HMul.hMul Real Real Real qz267 qz462 qz560)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz142) (Complex.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz147)))) Bool.true 57605150435 137438953472 366784973891 858993459200000 Bool.false 436576366485 1099511627776 1467014642439 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 3 qz145 rfl)

noncomputable def ep872 := nat_lit 251390696682103333830244636414788499672287283925523145817296699617356880158976

noncomputable def ep873 := nat_lit 49484583831173271192642680372085207413323586476624897934802031643867095296

noncomputable def ep874 := nat_lit 754073120878647654948348623883621328602035204603616187656020494788782906286336

noncomputable def ep875 := BSN.cos_dyadic_bound_f 1628578662 2147483648 3 2 1048576 400391 ep872 ep67 ep873 ep874 ep69 ep873 761224 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1628578662) qz20 0 2 ep872 ep67 ep873 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1628578662) qz21 0 2 ep874 ep69 ep873 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21099917) qz594)

noncomputable def ep876 := @Enclosure.Real.IsNear.cos_image qz147 qz464 Bool.false 21099917 131072 769 1048576 Bool.true 761224 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 8439966817 52428800 14653 20000000 21099917 131072 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz560 146530 1000 0 1 575989 524288 1 200000 8439966817 52428800 14653 20000000 qz146 qz288 rfl) rfl) (Enclosure.sfrac_false_div 21099917 131072) (BSN.cos_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14325129410991414575104) qz327) 226375608064910080 72057594037927936 Bool.false 761224 1048576 25 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 21099917 131072 226375608064910080 72057594037927936 25 14325129410991414575104 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 761224 1048576 14325129410991414575104 18889465931478580854784 1628578662 2147483648 400391 400000 (ep875 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep877 := nat_lit 7034527975008221629656864985094539536

noncomputable def ep878 := BSN.sin_dyadic_bound_f 1628578662 2147483648 2 1 1048576 400391 ep877 ep147 ep877 ep877 ep148 ep877 721143 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1628578662) qz15 0 1 ep877 ep147 ep877 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1628578662) qz16 0 1 ep877 ep148 ep877 rfl rfl rfl rfl) rfl rfl

noncomputable def ep879 := @Enclosure.Real.IsNear.sin_image qz147 qz464 Bool.false 21099917 131072 769 1048576 Bool.true 721143 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz147 Bool.false 8439966817 52428800 14653 20000000 21099917 131072 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz560 146530 1000 0 1 575989 524288 1 200000 8439966817 52428800 14653 20000000 qz146 qz288 rfl) rfl) (Enclosure.sfrac_false_div 21099917 131072) (BSN.sin_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14325129410991414575104) qz327) 226375608064910080 72057594037927936 Bool.false 721143 1048576 25 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 21099917 131072 226375608064910080 72057594037927936 25 14325129410991414575104 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 721143 1048576 14325129410991414575104 18889465931478580854784 1628578662 2147483648 400391 400000 (ep878 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep880 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz285 (Real.cos qz147)) (@HMul.hMul Real Real Real qz0 qz285 (@Neg.neg Real Real.instNeg (Real.sin qz147))) Bool.true 57605150435 137438953472 366784973891 858993459200000 Bool.false 436576366485 1099511627776 1467014642439 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz285 (Real.cos qz147) 605395 1048576 1 1048576 95153 131072 2419509 3276800000 57605150435 137438953472 366784973891 858993459200000 qz289 (@Enclosure.Real.IsNear.recentre' (Real.cos qz147) Bool.true 761224 1048576 154848576 209715200000 95153 131072 2419509 3276800000 (ep876 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz285 (@Neg.neg Real Real.instNeg (Real.sin qz147)) 605395 1048576 1 1048576 721143 1048576 2419509 3276800000 436576366485 1099511627776 1467014642439 3435973836800000 qz289 (@Enclosure.Real.IsNear.neg (Real.sin qz147) Bool.true 721143 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz147) Bool.true 721143 1048576 154848576 209715200000 721143 1048576 2419509 3276800000 (ep879 rfl rfl) rfl)) rfl)

noncomputable def ep881 := @ep855 57605150435 137438953472 366784973891 858993459200000 Bool.false 436576366485 1099511627776 1467014642439 3435973836800000 Bool.false 71133854966950087622656 517566913673 549755813888 1631385164709 1717986918400000 Bool.true 255320163808910235402240 14513271015 68719476736 1631896420959 1717986918400000 (ep856 (BSN.head_sum_c_succ qz141 2 3 rfl rfl) (ep870 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep871 ep880) rfl rfl

noncomputable abbrev qz148 := (@HMul.hMul Real Real Real qz267 qz462 qz562)

noncomputable def ep882 := @Enclosure.Complex.IsNear.of_eq qz694 (Complex.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz148)))) Bool.true 263974834491 1099511627776 1270092950217 3435973836800000 Bool.true 482231318295 1099511627776 1271393862717 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 4 qz145 rfl)

noncomputable def ep883 := nat_lit 1338261770127830520098044265038918801

noncomputable def ep884 := BSN.sin_dyadic_bound_f 1075561549 2147483648 2 1 1048576 400391 ep883 ep147 ep883 ep883 ep148 ep883 503493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1075561549) qz15 0 1 ep883 ep147 ep883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1075561549) qz16 0 1 ep883 ep148 ep883 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106500495) qz25)

noncomputable def ep885 := @Enclosure.Real.IsNear.cos_image qz148 qz465 Bool.false 106500495 524288 769 1048576 Bool.true 503493 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 10650049501 52428800 14653 20000000 106500495 524288 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz562 146530 1000 0 1 726817 524288 1 200000 10650049501 52428800 14653 20000000 qz146 qz294 rfl) rfl) (Enclosure.sfrac_false_div 106500495 524288) (BSN.cos_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37842957750258609684480) qz26) 226375608064910080 72057594037927936 Bool.false 503493 1048576 32 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 106500495 524288 226375608064910080 72057594037927936 32 37842957750258609684480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 503493 1048576 37842957750258609684480 75557863725914323419136 1075561549 2147483648 400391 400000 (ep884 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep886 := BSN.cos_dyadic_bound_f 1075561549 2147483648 2 1 1048576 400391 ep883 ep80 ep883 ep883 ep81 ep883 919785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1075561549) qz20 0 1 ep883 ep80 ep883 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1075561549) qz21 0 1 ep883 ep81 ep883 rfl rfl rfl rfl) rfl rfl

noncomputable def ep887 := @Enclosure.Real.IsNear.sin_image qz148 qz465 Bool.false 106500495 524288 769 1048576 Bool.false 919785 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz148 Bool.false 10650049501 52428800 14653 20000000 106500495 524288 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz562 146530 1000 0 1 726817 524288 1 200000 10650049501 52428800 14653 20000000 qz146 qz294 rfl) rfl) (Enclosure.sfrac_false_div 106500495 524288) (BSN.sin_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37842957750258609684480) qz26) 226375608064910080 72057594037927936 Bool.false 919785 1048576 32 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 106500495 524288 226375608064910080 72057594037927936 32 37842957750258609684480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 919785 1048576 37842957750258609684480 75557863725914323419136 1075561549 2147483648 400391 400000 (ep886 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep888 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz290 (Real.cos qz148)) (@HMul.hMul Real Real Real qz0 qz290 (@Neg.neg Real Real.instNeg (Real.sin qz148))) Bool.true 263974834491 1099511627776 1270092950217 3435973836800000 Bool.true 482231318295 1099511627776 1271393862717 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz290 (Real.cos qz148) 524287 1048576 1 1048576 503493 1048576 2419509 3276800000 263974834491 1099511627776 1270092950217 3435973836800000 qz295 (@Enclosure.Real.IsNear.recentre' (Real.cos qz148) Bool.true 503493 1048576 154848576 209715200000 503493 1048576 2419509 3276800000 (ep885 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz290 (@Neg.neg Real Real.instNeg (Real.sin qz148)) 524287 1048576 1 1048576 919785 1048576 2419509 3276800000 482231318295 1099511627776 1271393862717 3435973836800000 qz295 (@Enclosure.Real.IsNear.neg (Real.sin qz148) Bool.false 919785 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz148) Bool.false 919785 1048576 154848576 209715200000 919785 1048576 2419509 3276800000 (ep887 rfl rfl) rfl)) rfl)

noncomputable def ep889 := @ep853 263974834491 1099511627776 1270092950217 3435973836800000 Bool.true 482231318295 1099511627776 1271393862717 3435973836800000 Bool.false 423949139754050901770240 771158992855 1099511627776 906572655927 687194767360000 Bool.true 49096194097000753397760 714443654535 1099511627776 907037340927 687194767360000 (ep854 (BSN.head_sum_c_succ qz141 3 4 rfl rfl) (ep881 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep882 ep888) rfl rfl

noncomputable abbrev qz149 := (@HMul.hMul Real Real Real qz267 qz462 qz563)

noncomputable def ep890 := @Enclosure.Complex.IsNear.of_eq qz693 (Complex.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz149)))) Bool.true 480788444801 1099511627776 1137803689567 3435973836800000 Bool.false 103085951773 1099511627776 1135286677067 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 5 qz145 rfl)

noncomputable def ep891 := nat_lit 42325297735158145843505318085001216

noncomputable def ep892 := BSN.cos_dyadic_bound_f 453575936 2147483648 2 1 1048576 400391 ep891 ep80 ep891 ep891 ep81 ep891 1025273 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 453575936) qz20 0 1 ep891 ep80 ep891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 453575936) qz21 0 1 ep891 ep81 ep891 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz697 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61821593) qz17)

noncomputable def ep893 := @Enclosure.Real.IsNear.cos_image qz149 qz697 Bool.false 61821593 262144 769 1048576 Bool.true 1025273 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 386384957 1638400 14653 20000000 61821593 262144 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz563 146530 1000 0 1 843808 524288 1 200000 386384957 1638400 14653 20000000 qz146 qz299 rfl) rfl) (Enclosure.sfrac_false_div 61821593 262144) (BSN.cos_reduce2 qz697 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7979392258846643716096) qz19) 226375608064910080 72057594037927936 Bool.false 1025273 1048576 37 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 61821593 262144 226375608064910080 72057594037927936 37 7979392258846643716096 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1025273 1048576 7979392258846643716096 37778931862957161709568 453575936 2147483648 400391 400000 (ep892 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep894 := BSN.sin_dyadic_bound_f 453575936 2147483648 2 1 1048576 400391 ep891 ep147 ep891 ep891 ep148 ep891 219829 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 453575936) qz15 0 1 ep891 ep147 ep891 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 453575936) qz16 0 1 ep891 ep148 ep891 rfl rfl rfl rfl) rfl rfl

noncomputable def ep895 := @Enclosure.Real.IsNear.sin_image qz149 qz697 Bool.false 61821593 262144 769 1048576 Bool.true 219829 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz149 Bool.false 386384957 1638400 14653 20000000 61821593 262144 769 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz144 qz563 146530 1000 0 1 843808 524288 1 200000 386384957 1638400 14653 20000000 qz146 qz299 rfl) rfl) (Enclosure.sfrac_false_div 61821593 262144) (BSN.sin_reduce2 qz697 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7979392258846643716096) qz19) 226375608064910080 72057594037927936 Bool.false 219829 1048576 37 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 61821593 262144 226375608064910080 72057594037927936 37 7979392258846643716096 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 219829 1048576 7979392258846643716096 37778931862957161709568 453575936 2147483648 400391 400000 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz296 (Real.cos qz149)) (@HMul.hMul Real Real Real qz0 qz296 (@Neg.neg Real Real.instNeg (Real.sin qz149))) Bool.true 480788444801 1099511627776 1137803689567 3435973836800000 Bool.false 103085951773 1099511627776 1135286677067 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz296 (Real.cos qz149) 468937 1048576 1 1048576 1025273 1048576 2419509 3276800000 480788444801 1099511627776 1137803689567 3435973836800000 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz149) Bool.true 1025273 1048576 154848576 209715200000 1025273 1048576 2419509 3276800000 (ep893 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz296 (@Neg.neg Real Real.instNeg (Real.sin qz149)) 468937 1048576 1 1048576 219829 1048576 2419509 3276800000 103085951773 1099511627776 1135286677067 3435973836800000 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz149) Bool.true 219829 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz149) Bool.true 219829 1048576 154848576 209715200000 219829 1048576 2419509 3276800000 (ep895 rfl rfl) rfl)) rfl)

noncomputable def ep897 := @ep851 480788444801 1099511627776 1137803689567 3435973836800000 Bool.false 103085951773 1099511627776 1135286677067 3435973836800000 Bool.false 319265793949062769147904 145185274027 549755813888 2835333484601 1717986918400000 Bool.true 672194902917242591117312 305678851381 549755813888 2835236690851 1717986918400000 (ep852 (BSN.head_sum_c_succ qz141 4 5 rfl rfl) (ep889 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep890 ep896) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz462 qz565)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq qz692 (Complex.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.false 49720947771 549755813888 103780709397 343597383680000 Bool.false 54714917385 137438953472 26006913443 85899345920000 (BSN.cpow_neg_s_mk qz144 146530 1000 6 qz145 rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz565 146530 1000 0 1 4034681531866359 2251799813685248 2500000001 500000000000000 59120188486437758427 225179981368524800 36632500014653 50000000000000000 qz146 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 2500000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz566) Bool.false 33845361775666394038272 18889465931478580854784 1000000000400000 200000000000000000000 4034681531866359 2251799813685248 2500000001 500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep118 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep900 := nat_lit 52963795057280872388077900543672576

noncomputable def ep901 := BSN.sin_dyadic_bound_f 479727676 2147483648 2 1 1048576 400391 ep900 ep147 ep900 ep900 ep148 ep900 232298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 479727676) qz15 0 1 ep900 ep147 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 479727676) qz16 0 1 ep900 ep148 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 137649915) qz25)

noncomputable def ep902 := @Enclosure.Real.IsNear.cos_image qz150 qz466 Bool.false 137649915 524288 385 524288 Bool.false 232298 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 59120188486437758427 225179981368524800 36632500014653 50000000000000000 137649915 524288 385 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 137649915 524288) (BSN.cos_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16878917060933137203200) qz26) 226375608064910080 72057594037927936 Bool.false 232298 1048576 41 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 137649915 524288 226375608064910080 72057594037927936 41 16878917060933137203200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 232298 1048576 16878917060933137203200 75557863725914323419136 479727676 2147483648 400391 400000 (ep901 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep903 := BSN.cos_dyadic_bound_f 479727676 2147483648 2 1 1048576 400391 ep900 ep80 ep900 ep900 ep81 ep900 1022520 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 479727676) qz20 0 1 ep900 ep80 ep900 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 479727676) qz21 0 1 ep900 ep81 ep900 rfl rfl rfl rfl) rfl rfl

noncomputable def ep904 := @Enclosure.Real.IsNear.sin_image qz150 qz466 Bool.false 137649915 524288 385 524288 Bool.true 1022520 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 59120188486437758427 225179981368524800 36632500014653 50000000000000000 137649915 524288 385 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 137649915 524288) (BSN.sin_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16878917060933137203200) qz26) 226375608064910080 72057594037927936 Bool.false 1022520 1048576 41 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 137649915 524288 226375608064910080 72057594037927936 41 16878917060933137203200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1022520 1048576 16878917060933137203200 75557863725914323419136 479727676 2147483648 400391 400000 (ep903 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep905 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz301 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz301 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.false 49720947771 549755813888 103780709397 343597383680000 Bool.false 54714917385 137438953472 26006913443 85899345920000 (@Enclosure.Real.IsNear.mulLit_ff qz301 (Real.cos qz150) 428079 1048576 1 1048576 116149 524288 1211317 1638400000 49720947771 549755813888 103780709397 343597383680000 qz305 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.false 232298 1048576 77524288 104857600000 116149 524288 1211317 1638400000 (ep902 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz301 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 428079 1048576 1 1048576 127815 131072 1211317 1638400000 54714917385 137438953472 26006913443 85899345920000 qz305 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.true 127815 131072 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.true 1022520 1048576 77524288 104857600000 127815 131072 1211317 1638400000 (ep904 rfl rfl) rfl)) rfl)

noncomputable def ep906 := @ep849 49720947771 549755813888 103780709397 343597383680000 Bool.false 54714917385 137438953472 26006913443 85899345920000 Bool.false 107150828596394536730624 97453110899 274877906944 1677118515793 858993459200000 Bool.true 11932337493522306301952 86819181841 549755813888 3355374959711 1717986918400000 (ep850 (BSN.head_sum_c_succ qz141 5 6 rfl rfl) (ep897 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep898 ep905) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz462 qz567)

noncomputable def ep907 := @Enclosure.Complex.IsNear.of_eq qz691 (Complex.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 75950534025 274877906944 30079634537 107374182400000 Bool.true 283563007325 1099511627776 962388720809 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 7 qz145 rfl)

noncomputable def ep908 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz567 146530 1000 0 1 4381796493761783 2251799813685248 2500000001 500000000000000 64206464023091406299 225179981368524800 36632500014653 50000000000000000 qz146 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 2500000001 500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz568) Bool.false 36757173121942042968064 18889465931478580854784 1000000000400000 200000000000000000000 4381796493761783 2251799813685248 2500000001 500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep133 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep909 := nat_lit 9608192222157311060012475452033725456

noncomputable def ep910 := BSN.sin_dyadic_bound_f 1760598878 2147483648 2 1 1048576 400391 ep909 ep147 ep909 ep909 ep148 ep909 766548 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1760598878) qz15 0 1 ep909 ep147 ep909 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1760598878) qz16 0 1 ep909 ep148 ep909 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 149492323) qz25)

noncomputable def ep911 := @Enclosure.Real.IsNear.cos_image qz151 qz467 Bool.false 149492323 524288 385 524288 Bool.true 766548 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 64206464023091406299 225179981368524800 36632500014653 50000000000000000 149492323 524288 385 524288 (ep908 rfl) rfl) (Enclosure.sfrac_false_div 149492323 524288) (BSN.cos_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61945566036055258300416) qz26) 226375608064910080 72057594037927936 Bool.false 766548 1048576 45 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 149492323 524288 226375608064910080 72057594037927936 45 61945566036055258300416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 766548 1048576 61945566036055258300416 75557863725914323419136 1760598878 2147483648 400391 400000 (ep910 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep912 := nat_lit 343389648432417251657588490489312104873029824524046285116122883892244474921216

noncomputable def ep913 := nat_lit 92317357777924247090517630491994998669212171115368132504616149630382407936

noncomputable def ep914 := nat_lit 1029984310581695906478584436206952324621751049229908119083359419377472659947776

noncomputable def ep915 := BSN.cos_dyadic_bound_f 1760598878 2147483648 3 2 1048576 400391 ep912 ep67 ep913 ep914 ep69 ep913 715481 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1760598878) qz20 0 2 ep912 ep67 ep913 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1760598878) qz21 0 2 ep914 ep69 ep913 rfl rfl rfl rfl) rfl rfl

noncomputable def ep916 := @Enclosure.Real.IsNear.sin_image qz151 qz467 Bool.false 149492323 524288 385 524288 Bool.false 715481 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 64206464023091406299 225179981368524800 36632500014653 50000000000000000 149492323 524288 385 524288 (ep908 rfl) rfl) (Enclosure.sfrac_false_div 149492323 524288) (BSN.sin_reduce1 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 61945566036055258300416) qz26) 226375608064910080 72057594037927936 Bool.false 715481 1048576 45 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 149492323 524288 226375608064910080 72057594037927936 45 61945566036055258300416 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 715481 1048576 61945566036055258300416 75557863725914323419136 1760598878 2147483648 400391 400000 (ep915 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep917 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz306 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz306 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 75950534025 274877906944 30079634537 107374182400000 Bool.true 283563007325 1099511627776 962388720809 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz306 (Real.cos qz151) 396325 1048576 1 1048576 191637 262144 1211317 1638400000 75950534025 274877906944 30079634537 107374182400000 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 766548 1048576 77524288 104857600000 191637 262144 1211317 1638400000 (ep911 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz306 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 396325 1048576 1 1048576 715481 1048576 1211317 1638400000 283563007325 1099511627776 962388720809 3435973836800000 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.false 715481 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.false 715481 1048576 77524288 104857600000 715481 1048576 1211317 1638400000 (ep916 rfl rfl) rfl)) rfl)

noncomputable def ep918 := @ep847 75950534025 274877906944 30079634537 107374182400000 Bool.true 283563007325 1099511627776 962388720809 3435973836800000 Bool.false 5910583325027578413056 10751288437 137438953472 1917755592089 858993459200000 Bool.true 251349111828662731145216 457201371007 1099511627776 7673138640231 3435973836800000 (ep848 (BSN.head_sum_c_succ qz141 6 7 rfl rfl) (ep906 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep907 ep917) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz462 qz570)

noncomputable def ep919 := @Enclosure.Complex.IsNear.of_eq qz690 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 97127878911 274877906944 225353292513 858993459200000 Bool.true 13182681393 1099511627776 898249379427 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 8 qz145 rfl)

noncomputable def ep920 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz570 146530 1000 0 1 9364972152248037 4503599627370496 5000000003 1000000000000000 137224936946890486161 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz571) Bool.false 39279540158062550581248 18889465931478580854784 1000000000600000 200000000000000000000 9364972152248037 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep144 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep921 := nat_lit 7645005387254326157806700920807886339516202144375636528997342946064000000000000

noncomputable def ep922 := nat_lit 14078361172062283849145778284489075747870968478862441878906250000000000000000

noncomputable def ep923 := nat_lit 19999839619958943858499885437274339052283976429160889812903383311120000000000000

noncomputable def ep924 := BSN.sin_dyadic_bound_f 3300418500 2147483648 3 2 1048576 400391 ep921 ep60 ep922 ep923 ep63 ep922 1047972 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3300418500) qz15 0 2 ep921 ep60 ep922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3300418500) qz16 0 2 ep923 ep63 ep922 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 319501703) qz35)

noncomputable def ep925 := @Enclosure.Real.IsNear.cos_image qz152 qz468 Bool.false 319501703 1048576 385 524288 Bool.true 1047972 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 137224936946890486161 450359962737049600 73265000043959 100000000000000000 319501703 1048576 385 524288 (ep920 rfl) rfl) (Enclosure.sfrac_false_div 319501703 1048576) (BSN.cos_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232246305162911941656576) qz36) 226375608064910080 72057594037927936 Bool.false 1047972 1048576 48 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 319501703 1048576 226375608064910080 72057594037927936 48 232246305162911941656576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047972 1048576 232246305162911941656576 151115727451828646838272 3300418500 2147483648 400391 400000 (ep924 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep926 := nat_lit 4253482264551097769381120857464154222285832732865959156944704414480000000000000

noncomputable def ep927 := nat_lit 12732290071309168740445071015823484515361756261640152587076300743440000000000000

noncomputable def ep928 := BSN.cos_dyadic_bound_f 3300418500 2147483648 3 2 1048576 400391 ep926 ep67 ep922 ep927 ep69 ep922 35559 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3300418500) qz20 0 2 ep926 ep67 ep922 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3300418500) qz21 0 2 ep927 ep69 ep922 rfl rfl rfl rfl) rfl rfl

noncomputable def ep929 := @Enclosure.Real.IsNear.sin_image qz152 qz468 Bool.false 319501703 1048576 385 524288 Bool.false 35559 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 137224936946890486161 450359962737049600 73265000043959 100000000000000000 319501703 1048576 385 524288 (ep920 rfl) rfl) (Enclosure.sfrac_false_div 319501703 1048576) (BSN.sin_reduce1 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 232246305162911941656576) qz36) 226375608064910080 72057594037927936 Bool.false 35559 1048576 48 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 319501703 1048576 226375608064910080 72057594037927936 48 232246305162911941656576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 35559 1048576 232246305162911941656576 151115727451828646838272 3300418500 2147483648 400391 400000 (ep928 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep930 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 97127878911 274877906944 225353292513 858993459200000 Bool.true 13182681393 1099511627776 898249379427 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz152) 370727 1048576 1 1048576 261993 262144 1211317 1638400000 97127878911 274877906944 225353292513 858993459200000 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 1047972 1048576 77524288 104857600000 261993 262144 1211317 1638400000 (ep925 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz310 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 370727 1048576 1 1048576 35559 1048576 1211317 1638400000 13182681393 1099511627776 898249379427 3435973836800000 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 35559 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 35559 1048576 77524288 104857600000 35559 1048576 1211317 1638400000 (ep929 rfl rfl) rfl)) rfl)

noncomputable def ep931 := @ep845 97127878911 274877906944 225353292513 858993459200000 Bool.true 13182681393 1099511627776 898249379427 3435973836800000 Bool.true 10393862367969189822464 75625302037 274877906944 1071554442301 429496729600000 Bool.true 517192735134195279462400 29399003275 68719476736 4285694009829 1717986918400000 (ep846 (BSN.head_sum_c_succ qz141 7 8 rfl rfl) (ep918 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep919 ep930) rfl rfl

theorem EMRow51.d13 : Enclosure.Complex.IsNear qz140 Bool.true 75625302037 274877906944 1071554442301 429496729600000 Bool.true 29399003275 68719476736 4285694009829 1717986918400000 := ep844 (BSN.head_sum_c_succ qz141 8 9 rfl rfl) (ep931 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz153 := (BSN.headSumC qz460 17)

noncomputable abbrev qz698 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz142)

noncomputable def ep932 := @Enclosure.Complex.IsNear.of_eq qz153 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 16) qz698) Bool.false 55841465275 1099511627776 14405775946367 3435973836800000 Bool.false 106378857499 1099511627776 14407717358867 3435973836800000

noncomputable def ep933 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 16) qz698 Bool.false 203901404533 1099511627776 13768931960321 3435973836800000 Bool.true 3912945607 34359738368 6884938787973 1717986918400000 Bool.true

noncomputable abbrev qz699 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz142)

noncomputable def ep934 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 15) qz699) Bool.false 203901404533 1099511627776 13768931960321 3435973836800000 Bool.true 3912945607 34359738368 6884938787973 1717986918400000

noncomputable def ep935 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 15) qz699 Bool.false 21667467425 549755813888 409750497899 107374182400000 Bool.false 54453968681 549755813888 6556056269509 1717986918400000 Bool.false

noncomputable abbrev qz700 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz142)

noncomputable def ep936 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 14) qz700) Bool.false 21667467425 549755813888 409750497899 107374182400000 Bool.false 54453968681 549755813888 6556056269509 1717986918400000

noncomputable def ep937 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 14) qz700 Bool.false 162671172389 549755813888 388435706721 107374182400000 Bool.false 13152876313 549755813888 6216131398161 1717986918400000 Bool.true

noncomputable abbrev qz701 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz142)

noncomputable def ep938 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 13) qz701) Bool.false 162671172389 549755813888 388435706721 107374182400000 Bool.false 13152876313 549755813888 6216131398161 1717986918400000

noncomputable def ep939 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 13) qz701 Bool.false 50148163909 274877906944 5862475424203 1717986918400000 Bool.true 31495011485 137438953472 2931405360539 858993459200000 Bool.false

noncomputable abbrev qz702 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz142)

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 12) qz702) Bool.false 50148163909 274877906944 5862475424203 1717986918400000 Bool.true 31495011485 137438953472 2931405360539 858993459200000

noncomputable def ep941 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 12) qz702 Bool.true 12691455205 137438953472 1373681403203 429496729600000 Bool.true 87310818829 274877906944 5496118284687 1717986918400000 Bool.false

noncomputable abbrev qz703 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz142)

noncomputable def ep942 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 11) qz703) Bool.true 12691455205 137438953472 1373681403203 429496729600000 Bool.true 87310818829 274877906944 5496118284687 1717986918400000

noncomputable def ep943 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 11) qz703 Bool.true 98316852583 274877906944 5110810243351 1717986918400000 Bool.true 31668644607 68719476736 2556433276363 858993459200000 Bool.false

noncomputable abbrev qz704 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz142)

noncomputable def ep944 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 10) qz704) Bool.true 98316852583 274877906944 5110810243351 1717986918400000 Bool.true 31668644607 68719476736 2556433276363 858993459200000

noncomputable def ep945 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 10) qz704 Bool.true 282721937923 1099511627776 9418293681767 3435973836800000 Bool.true 836353155075 1099511627776 9420341344267 3435973836800000 Bool.true

noncomputable abbrev qz705 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz142)

noncomputable def ep946 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 10) (@HAdd.hAdd Complex Complex Complex qz4 qz140 qz705) Bool.true 282721937923 1099511627776 9418293681767 3435973836800000 Bool.true 836353155075 1099511627776 9420341344267 3435973836800000

noncomputable def ep947 := @Enclosure.Complex.IsNear.addLitP qz140 qz705 Bool.true 75625302037 274877906944 1071554442301 429496729600000 Bool.true 29399003275 68719476736 4285694009829 1717986918400000 Bool.false

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz462 qz580)

noncomputable def ep948 := @Enclosure.Complex.IsNear.of_eq qz705 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.false 19779270225 1099511627776 845858143359 3435973836800000 Bool.true 365969102675 1099511627776 848953324609 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 9 qz145 rfl)

noncomputable def ep949 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz580 146530 1000 0 1 9895417793173221 4503599627370496 5000000003 1000000000000000 144997556923367207313 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz581) Bool.false 41504390431577613533184 18889465931478580854784 1000000000600000 200000000000000000000 9895417793173221 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep950 := nat_lit 4034870497621045675084574991866787538845173485479811056098711836532238367415841

noncomputable def ep951 := nat_lit 12672705963404463164344896689018815567072834339965135426161126681231376342561

noncomputable def ep952 := nat_lit 12079266080936328098925035182222324985401374787759502897443813256234252349562401

noncomputable def ep953 := BSN.cos_dyadic_bound_f 3257306829 2147483648 3 2 1048576 400391 ep950 ep67 ep951 ep952 ep69 ep951 56589 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3257306829) qz20 0 2 ep950 ep67 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3257306829) qz21 0 2 ep952 ep69 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 337598745) qz35)

noncomputable def ep954 := @Enclosure.Real.IsNear.cos_image qz154 qz469 Bool.false 337598745 1048576 769 1048576 Bool.false 56589 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 144997556923367207313 450359962737049600 73265000043959 100000000000000000 337598745 1048576 769 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 337598745 1048576) (BSN.cos_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 229212590984592170680320) qz36) 226375608064910080 72057594037927936 Bool.false 56589 1048576 51 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 337598745 1048576 226375608064910080 72057594037927936 51 229212590984592170680320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 56589 1048576 229212590984592170680320 151115727451828646838272 3257306829 2147483648 400391 400000 (ep953 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep955 := nat_lit 7252628730947158644620759068009002517467654006391687792636752404413043960274465

noncomputable def ep956 := nat_lit 18974462295206570176502572488241357082449547332570667332882471615978835762830881

noncomputable def ep957 := BSN.sin_dyadic_bound_f 3257306829 2147483648 3 2 1048576 400391 ep955 ep60 ep951 ep956 ep63 ep951 1047047 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3257306829) qz15 0 2 ep955 ep60 ep951 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3257306829) qz16 0 2 ep956 ep63 ep951 rfl rfl rfl rfl) rfl rfl

noncomputable def ep958 := @Enclosure.Real.IsNear.sin_image qz154 qz469 Bool.false 337598745 1048576 769 1048576 Bool.false 1047047 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 144997556923367207313 450359962737049600 73265000043959 100000000000000000 337598745 1048576 769 1048576 (ep949 rfl) rfl) (Enclosure.sfrac_false_div 337598745 1048576) (BSN.sin_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 229212590984592170680320) qz36) 226375608064910080 72057594037927936 Bool.false 1047047 1048576 51 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 337598745 1048576 226375608064910080 72057594037927936 51 229212590984592170680320 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1047047 1048576 229212590984592170680320 151115727451828646838272 3257306829 2147483648 400391 400000 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.false 19779270225 1099511627776 845858143359 3435973836800000 Bool.true 365969102675 1099511627776 848953324609 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz154) 349525 1048576 1 1048576 56589 1048576 2419509 3276800000 19779270225 1099511627776 845858143359 3435973836800000 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.false 56589 1048576 154848576 209715200000 56589 1048576 2419509 3276800000 (ep954 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 349525 1048576 1 1048576 1047047 1048576 2419509 3276800000 365969102675 1099511627776 848953324609 3435973836800000 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.false 1047047 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.false 1047047 1048576 154848576 209715200000 1047047 1048576 2419509 3276800000 (ep958 rfl rfl) rfl)) rfl)

noncomputable def ep960 := @ep947 19779270225 1099511627776 845858143359 3435973836800000 Bool.true 365969102675 1099511627776 848953324609 3435973836800000 Bool.true 77714014543425738637312 282721937923 1099511627776 9418293681767 3435973836800000 Bool.true 57473751183256662835200 836353155075 1099511627776 9420341344267 3435973836800000 EMRow51.d13 (ep948 ep959) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz462 qz583)

noncomputable def ep961 := @Enclosure.Complex.IsNear.of_eq qz704 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 110545472409 1099511627776 160665360987 687194767360000 Bool.false 329654841363 1099511627776 161078352237 687194767360000 (BSN.cpow_neg_s_mk qz144 146530 1000 10 qz145 rfl)

noncomputable def ep962 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz583 146530 1000 0 1 10369917190100709 4503599627370496 5000000003 1000000000000000 151950396586545688977 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz584) Bool.false 43494585150108164161536 18889465931478580854784 1000000000600000 200000000000000000000 10369917190100709 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep963 := nat_lit 1841527776837463670829766335374578779781392527154186953752205709125313139572736

noncomputable def ep964 := nat_lit 2648797808001230405179222167615774285587533072497277096227342018953038790656

noncomputable def ep965 := nat_lit 5519285734896388551678940561788504790773002515317566307064162443338033341136896

noncomputable def ep966 := BSN.cos_dyadic_bound_f 2678434936 2147483648 3 2 1048576 400391 ep963 ep67 ep964 ep965 ep69 ep964 333381 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2678434936) qz20 0 2 ep963 ep67 ep964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2678434936) qz21 0 2 ep965 ep69 ep964 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 176893543) qz25)

noncomputable def ep967 := @Enclosure.Real.IsNear.cos_image qz155 qz470 Bool.false 176893543 524288 769 1048576 Bool.true 333381 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 151950396586545688977 450359962737049600 73265000043959 100000000000000000 176893543 524288 769 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 176893543 524288) (BSN.cos_reduce2 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94239051406484686503936) qz26) 226375608064910080 72057594037927936 Bool.false 333381 1048576 53 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 176893543 524288 226375608064910080 72057594037927936 53 94239051406484686503936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 333381 1048576 94239051406484686503936 75557863725914323419136 2678434936 2147483648 400391 400000 (ep966 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep968 := nat_lit 3312630960061033623169436025940149184178036522419538695076988402810401220198400

noncomputable def ep969 := nat_lit 8671649698946895592406804184429012800194382505171891467045839644091793513906176

noncomputable def ep970 := BSN.sin_dyadic_bound_f 2678434936 2147483648 3 2 1048576 400391 ep968 ep60 ep964 ep969 ep63 ep964 994167 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2678434936) qz15 0 2 ep968 ep60 ep964 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2678434936) qz16 0 2 ep969 ep63 ep964 rfl rfl rfl rfl) rfl rfl

noncomputable def ep971 := @Enclosure.Real.IsNear.sin_image qz155 qz470 Bool.false 176893543 524288 769 1048576 Bool.true 994167 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 151950396586545688977 450359962737049600 73265000043959 100000000000000000 176893543 524288 769 1048576 (ep962 rfl) rfl) (Enclosure.sfrac_false_div 176893543 524288) (BSN.sin_reduce2 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94239051406484686503936) qz26) 226375608064910080 72057594037927936 Bool.false 994167 1048576 53 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 176893543 524288 226375608064910080 72057594037927936 53 94239051406484686503936 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994167 1048576 94239051406484686503936 75557863725914323419136 2678434936 2147483648 400391 400000 (ep970 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep972 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 110545472409 1099511627776 160665360987 687194767360000 Bool.false 329654841363 1099511627776 161078352237 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz155) 331589 1048576 1 1048576 333381 1048576 2419509 3276800000 110545472409 1099511627776 160665360987 687194767360000 qz321 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 333381 1048576 154848576 209715200000 333381 1048576 2419509 3276800000 (ep967 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz33 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 331589 1048576 1 1048576 994167 1048576 2419509 3276800000 329654841363 1099511627776 161078352237 687194767360000 qz321 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.true 994167 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.true 994167 1048576 154848576 209715200000 994167 1048576 2419509 3276800000 (ep971 rfl rfl) rfl)) rfl)

noncomputable def ep973 := @ep945 110545472409 1099511627776 160665360987 687194767360000 Bool.false 329654841363 1099511627776 161078352237 687194767360000 Bool.true 432402090485389440581632 98316852583 274877906944 5110810243351 1717986918400000 Bool.true 557120687700835420864512 31668644607 68719476736 2556433276363 858993459200000 (ep946 (BSN.head_sum_c_succ qz141 9 10 rfl rfl) (ep960 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep961 ep972) rfl rfl

noncomputable abbrev qz156 := (@HMul.hMul Real Real Real qz267 qz462 qz586)

noncomputable def ep974 := @Enclosure.Complex.IsNear.of_eq qz703 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156)))) Bool.false 72933942173 274877906944 383915369461 1717986918400000 Bool.false 39363759599 274877906944 383251731961 1717986918400000 (BSN.cpow_neg_s_mk qz144 146530 1000 11 qz145 rfl)

noncomputable def ep975 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz586 146530 1000 0 1 10799156221662949 4503599627370496 5000000003 1000000000000000 158240036116027191697 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz587) Bool.false 45294944137145793642496 18889465931478580854784 1000000000600000 200000000000000000000 10799156221662949 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep976 := nat_lit 1833458015842859904886938430043365984321679462941686629019750187549799412203520

noncomputable def ep977 := nat_lit 811997471670227185434100036760217897129854309670342693067166434707070058496

noncomputable def ep978 := nat_lit 4800599188443833668784612107196918177580474067393522521167713174117091775676416

noncomputable def ep979 := BSN.sin_dyadic_bound_f 2310438084 2147483648 3 2 1048576 400391 ep976 ep60 ep977 ep978 ep63 ep977 922756 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2310438084) qz15 0 2 ep976 ep60 ep977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2310438084) qz16 0 2 ep978 ep63 ep977 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 184215647) qz25)

noncomputable def ep980 := @Enclosure.Real.IsNear.cos_image qz156 qz471 Bool.false 184215647 524288 769 1048576 Bool.false 922756 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 158240036116027191697 450359962737049600 73265000043959 100000000000000000 184215647 524288 769 1048576 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 184215647 524288) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81291313267241086091264) qz26) 226375608064910080 72057594037927936 Bool.false 922756 1048576 55 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 184215647 524288 226375608064910080 72057594037927936 55 81291313267241086091264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 922756 1048576 81291313267241086091264 75557863725914323419136 2310438084 2147483648 400391 400000 (ep979 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep981 := nat_lit 1018948674344553381464047616707096754799657414660790501763446622609758371250176

noncomputable def ep982 := nat_lit 3055222028090319690021274650047769828604712535363030819904205534959860973633536

noncomputable def ep983 := BSN.cos_dyadic_bound_f 2310438084 2147483648 3 2 1048576 400391 ep981 ep67 ep977 ep982 ep69 ep977 498028 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2310438084) qz20 0 2 ep981 ep67 ep977 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2310438084) qz21 0 2 ep982 ep69 ep977 rfl rfl rfl rfl) rfl rfl

noncomputable def ep984 := @Enclosure.Real.IsNear.sin_image qz156 qz471 Bool.false 184215647 524288 769 1048576 Bool.true 498028 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz156 Bool.false 158240036116027191697 450359962737049600 73265000043959 100000000000000000 184215647 524288 769 1048576 (ep975 rfl) rfl) (Enclosure.sfrac_false_div 184215647 524288) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 81291313267241086091264) qz26) 226375608064910080 72057594037927936 Bool.false 498028 1048576 55 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 184215647 524288 226375608064910080 72057594037927936 55 81291313267241086091264 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498028 1048576 81291313267241086091264 75557863725914323419136 2310438084 2147483648 400391 400000 (ep983 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep985 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz156)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156))) Bool.false 72933942173 274877906944 383915369461 1717986918400000 Bool.false 39363759599 274877906944 383251731961 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz156) 316157 1048576 1 1048576 230689 262144 2419509 3276800000 72933942173 274877906944 383915369461 1717986918400000 qz323 (@Enclosure.Real.IsNear.recentre' (Real.cos qz156) Bool.false 922756 1048576 154848576 209715200000 230689 262144 2419509 3276800000 (ep980 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz37 (@Neg.neg Real Real.instNeg (Real.sin qz156)) 316157 1048576 1 1048576 124507 262144 2419509 3276800000 39363759599 274877906944 383251731961 1717986918400000 qz323 (@Enclosure.Real.IsNear.neg (Real.sin qz156) Bool.true 124507 262144 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz156) Bool.true 498028 1048576 154848576 209715200000 124507 262144 2419509 3276800000 (ep984 rfl rfl) rfl)) rfl)

noncomputable def ep986 := @ep943 72933942173 274877906944 383915369461 1717986918400000 Bool.false 39363759599 274877906944 383251731961 1717986918400000 Bool.true 6977201285647868887040 12691455205 137438953472 1373681403203 429496729600000 Bool.true 5999953783320576262144 87310818829 274877906944 5496118284687 1717986918400000 (ep944 (BSN.head_sum_c_succ qz141 10 11 rfl rfl) (ep973 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep974 ep985) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz462 qz589)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq qz702 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 75531074319 274877906944 367749811391 1717986918400000 Bool.false 24320795859 274877906944 366692436391 1717986918400000 (BSN.cpow_neg_s_mk qz144 146530 1000 12 qz145 rfl)

noncomputable def ep988 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz589 146530 1000 0 1 11191020447815397 4503599627370496 5000000003 1000000000000000 163982022621839012241 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz590) Bool.false 46938541828353910898688 18889465931478580854784 1000000000600000 200000000000000000000 11191020447815397 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep219 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep989 := nat_lit 3442498859726380149650973735597749530354458724665829692536032948387845373123105

noncomputable def ep990 := nat_lit 2860375834876052637060280121160780026738901211287787415380781905389405035041

noncomputable def ep991 := nat_lit 9011437357455482021006833615893178935646957486449373729398041217930869321456161

noncomputable def ep992 := BSN.sin_dyadic_bound_f 2704287667 2147483648 3 2 1048576 400391 ep989 ep60 ep990 ep991 ep63 ep990 998108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2704287667) qz15 0 2 ep989 ep60 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2704287667) qz16 0 2 ep991 ep63 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190900199) qz25)

noncomputable def ep993 := @Enclosure.Real.IsNear.cos_image qz157 qz472 Bool.false 190900199 524288 769 1048576 Bool.false 998108 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 163982022621839012241 450359962737049600 73265000043959 100000000000000000 190900199 524288 769 1048576 (ep988 rfl) rfl) (Enclosure.sfrac_false_div 190900199 524288) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95148663540994998796288) qz26) 226375608064910080 72057594037927936 Bool.false 998108 1048576 57 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 190900199 524288 226375608064910080 72057594037927936 57 95148663540994998796288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 998108 1048576 95148663540994998796288 75557863725914323419136 2704287667 2147483648 400391 400000 (ep992 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep994 := nat_lit 1913770644663489439867012199830376752431027692019366623593520874395642720639521

noncomputable def ep995 := nat_lit 5735591182320716214326916039248808697239605273635524295949801059376149351848481

noncomputable def ep996 := BSN.cos_dyadic_bound_f 2704287667 2147483648 3 2 1048576 400391 ep994 ep67 ep990 ep995 ep69 ep990 321388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2704287667) qz20 0 2 ep994 ep67 ep990 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2704287667) qz21 0 2 ep995 ep69 ep990 rfl rfl rfl rfl) rfl rfl

noncomputable def ep997 := @Enclosure.Real.IsNear.sin_image qz157 qz472 Bool.false 190900199 524288 769 1048576 Bool.true 321388 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 163982022621839012241 450359962737049600 73265000043959 100000000000000000 190900199 524288 769 1048576 (ep988 rfl) rfl) (Enclosure.sfrac_false_div 190900199 524288) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 95148663540994998796288) qz26) 226375608064910080 72057594037927936 Bool.false 321388 1048576 57 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 190900199 524288 226375608064910080 72057594037927936 57 95148663540994998796288 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 321388 1048576 95148663540994998796288 75557863725914323419136 2704287667 2147483648 400391 400000 (ep996 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep998 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 75531074319 274877906944 367749811391 1717986918400000 Bool.false 24320795859 274877906944 366692436391 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz157) 302697 1048576 1 1048576 249527 262144 2419509 3276800000 75531074319 274877906944 367749811391 1717986918400000 qz325 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 998108 1048576 154848576 209715200000 249527 262144 2419509 3276800000 (ep993 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 302697 1048576 1 1048576 80347 262144 2419509 3276800000 24320795859 274877906944 366692436391 1717986918400000 qz325 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 80347 262144 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 321388 1048576 154848576 209715200000 80347 262144 2419509 3276800000 (ep997 rfl rfl) rfl)) rfl)

noncomputable def ep999 := @ep941 75531074319 274877906944 367749811391 1717986918400000 Bool.false 24320795859 274877906944 366692436391 1717986918400000 Bool.false 6892311166195280642048 50148163909 274877906944 5862475424203 1717986918400000 Bool.true 17314565672348082503680 31495011485 137438953472 2931405360539 858993459200000 (ep942 (BSN.head_sum_c_succ qz141 11 12 rfl rfl) (ep986 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep987 ep998) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz462 qz592)

noncomputable def ep1000 := @Enclosure.Complex.IsNear.of_eq qz701 (Complex.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.false 62374844571 549755813888 352495883333 1717986918400000 Bool.false 139132922253 549755813888 353320677083 1717986918400000 (BSN.cpow_neg_s_mk qz144 146530 1000 13 qz145 rfl)

noncomputable def ep1001 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz592 146530 1000 0 1 11551497052968677 4503599627370496 5000000003 1000000000000000 169264086317150024081 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz593) Bool.false 48450490295254733815808 18889465931478580854784 1000000000600000 200000000000000000000 11551497052968677 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1002 := nat_lit 670964683449965926030805783486837776

noncomputable def ep1003 := BSN.sin_dyadic_bound_f 905054882 2147483648 2 1 1048576 400391 ep1002 ep147 ep1002 ep1002 ep148 ep1002 428954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 905054882) qz15 0 1 ep1002 ep147 ep1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 905054882) qz16 0 1 ep1002 ep148 ep1002 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 394098661) qz35)

noncomputable def ep1004 := @Enclosure.Real.IsNear.cos_image qz158 qz473 Bool.false 394098661 1048576 769 1048576 Bool.false 428954 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 169264086317150024081 450359962737049600 73265000043959 100000000000000000 394098661 1048576 769 1048576 (ep1001 rfl) rfl) (Enclosure.sfrac_false_div 394098661 1048576) (BSN.cos_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63687575515160245174272) qz36) 226375608064910080 72057594037927936 Bool.false 428954 1048576 59 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 394098661 1048576 226375608064910080 72057594037927936 59 63687575515160245174272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 428954 1048576 63687575515160245174272 151115727451828646838272 905054882 2147483648 400391 400000 (ep1003 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1005 := BSN.cos_dyadic_bound_f 905054882 2147483648 2 1 1048576 400391 ep1002 ep80 ep1002 ep1002 ep81 ep1002 956822 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 905054882) qz20 0 1 ep1002 ep80 ep1002 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 905054882) qz21 0 1 ep1002 ep81 ep1002 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1006 := @Enclosure.Real.IsNear.sin_image qz158 qz473 Bool.false 394098661 1048576 769 1048576 Bool.true 956822 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 169264086317150024081 450359962737049600 73265000043959 100000000000000000 394098661 1048576 769 1048576 (ep1001 rfl) rfl) (Enclosure.sfrac_false_div 394098661 1048576) (BSN.sin_reduce3 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63687575515160245174272) qz36) 226375608064910080 72057594037927936 Bool.false 956822 1048576 59 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 394098661 1048576 226375608064910080 72057594037927936 59 63687575515160245174272 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956822 1048576 63687575515160245174272 151115727451828646838272 905054882 2147483648 400391 400000 (ep1005 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz41 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz41 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.false 62374844571 549755813888 352495883333 1717986918400000 Bool.false 139132922253 549755813888 353320677083 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ff qz41 (Real.cos qz158) 290823 1048576 1 1048576 214477 524288 2419509 3276800000 62374844571 549755813888 352495883333 1717986918400000 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.false 428954 1048576 154848576 209715200000 214477 524288 2419509 3276800000 (ep1004 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz41 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 290823 1048576 1 1048576 478411 524288 2419509 3276800000 139132922253 549755813888 353320677083 1717986918400000 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.true 478411 524288 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.true 956822 1048576 154848576 209715200000 478411 524288 2419509 3276800000 (ep1006 rfl rfl) rfl)) rfl)

noncomputable def ep1008 := @ep939 62374844571 549755813888 352495883333 1717986918400000 Bool.false 139132922253 549755813888 353320677083 1717986918400000 Bool.false 44714711386414924169216 162671172389 549755813888 388435706721 107374182400000 Bool.false 1807717555605377908736 13152876313 549755813888 6216131398161 1717986918400000 (ep940 (BSN.head_sum_c_succ qz141 12 13 rfl rfl) (ep999 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1000 ep1007) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz462 qz596)

noncomputable def ep1009 := @Enclosure.Complex.IsNear.of_eq qz700 (Complex.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 35250926241 137438953472 10657395589 53687091200000 Bool.false 2581318273 34359738368 84981217837 429496729600000 (BSN.cpow_neg_s_mk qz144 146530 1000 14 qz145 rfl)

noncomputable def ep1010 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz596 146530 1000 0 1 11885250371606245 4503599627370496 5000000003 1000000000000000 34830914739029261597 90071992547409920 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz597) Bool.false 49850353174629559828480 18889465931478580854784 1000000000600000 200000000000000000000 11885250371606245 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1011 := nat_lit 140191031581765804905518879267642001

noncomputable def ep1012 := BSN.cos_dyadic_bound_f 611899443 2147483648 2 1 1048576 400391 ep1011 ep80 ep1011 ep1011 ep81 ep1011 1006296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 611899443) qz20 0 1 ep1011 ep80 ep1011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 611899443) qz21 0 1 ep1011 ep81 ep1011 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202742607) qz25)

noncomputable def ep1013 := @Enclosure.Real.IsNear.cos_image qz159 qz474 Bool.false 202742607 524288 385 524288 Bool.true 1006296 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 34830914739029261597 90071992547409920 73265000043959 100000000000000000 202742607 524288 385 524288 (ep1010 rfl) rfl) (Enclosure.sfrac_false_div 202742607 524288) (BSN.cos_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21529297714981543870464) qz26) 226375608064910080 72057594037927936 Bool.false 1006296 1048576 61 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 202742607 524288 226375608064910080 72057594037927936 61 21529297714981543870464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1006296 1048576 21529297714981543870464 75557863725914323419136 611899443 2147483648 400391 400000 (ep1012 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1014 := BSN.sin_dyadic_bound_f 611899443 2147483648 2 1 1048576 400391 ep1011 ep147 ep1011 ep1011 ep148 ep1011 294752 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 611899443) qz15 0 1 ep1011 ep147 ep1011 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 611899443) qz16 0 1 ep1011 ep148 ep1011 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1015 := @Enclosure.Real.IsNear.sin_image qz159 qz474 Bool.false 202742607 524288 385 524288 Bool.true 294752 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 34830914739029261597 90071992547409920 73265000043959 100000000000000000 202742607 524288 385 524288 (ep1010 rfl) rfl) (Enclosure.sfrac_false_div 202742607 524288) (BSN.sin_reduce2 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21529297714981543870464) qz26) 226375608064910080 72057594037927936 Bool.false 294752 1048576 61 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 202742607 524288 226375608064910080 72057594037927936 61 21529297714981543870464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 294752 1048576 21529297714981543870464 75557863725914323419136 611899443 2147483648 400391 400000 (ep1014 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1016 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz43 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz43 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 35250926241 137438953472 10657395589 53687091200000 Bool.false 2581318273 34359738368 84981217837 429496729600000 (@Enclosure.Real.IsNear.mulLit_ft qz43 (Real.cos qz159) 280243 1048576 1 1048576 125787 131072 1211317 1638400000 35250926241 137438953472 10657395589 53687091200000 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 1006296 1048576 77524288 104857600000 125787 131072 1211317 1638400000 (ep1013 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz43 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 280243 1048576 1 1048576 9211 32768 1211317 1638400000 2581318273 34359738368 84981217837 429496729600000 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 9211 32768 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 294752 1048576 77524288 104857600000 9211 32768 1211317 1638400000 (ep1015 rfl rfl) rfl)) rfl)

noncomputable def ep1017 := @ep937 35250926241 137438953472 10657395589 53687091200000 Bool.false 2581318273 34359738368 84981217837 429496729600000 Bool.false 2977954047280650649600 21667467425 549755813888 409750497899 107374182400000 Bool.false 1871024116978426052608 54453968681 549755813888 6556056269509 1717986918400000 (ep938 (BSN.head_sum_c_succ qz141 13 14 rfl rfl) (ep1008 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1009 ep1016) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz462 qz599)

noncomputable def ep1018 := @Enclosure.Complex.IsNear.of_eq qz699 (Complex.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 160566469683 1099511627776 656916027553 3435973836800000 Bool.true 117061098393 549755813888 5138789351 26843545600000 (BSN.cpow_neg_s_mk qz144 146530 1000 15 qz145 rfl)

noncomputable def ep1019 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz599 146530 1000 0 1 12195965485668069 4503599627370496 5000000003 1000000000000000 178707482261494215057 450359962737049600 73265000043959 100000000000000000 qz146 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 5000000003 1000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz600) Bool.false 51153586820399524478976 18889465931478580854784 1000000000600000 200000000000000000000 12195965485668069 4503599627370496 5000000003 1000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1020 := nat_lit 672099895075192754039459470398491798876051718656443194375333499892251323157441

noncomputable def ep1021 := nat_lit 353470552639909571247581981169056203879372087919924782794415953293406260161

noncomputable def ep1022 := nat_lit 2015592744120298442975883247233137284220396411793489733560411667770167156952001

noncomputable def ep1023 := BSN.cos_dyadic_bound_f 2082304103 2147483648 3 2 1048576 400391 ep1020 ep67 ep1021 ep1022 ep69 ep1021 593063 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2082304103) qz20 0 2 ep1020 ep67 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2082304103) qz21 0 2 ep1022 ep69 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 416085781) qz35)

noncomputable def ep1024 := @Enclosure.Real.IsNear.cos_image qz160 qz475 Bool.false 416085781 1048576 769 1048576 Bool.false 593063 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 178707482261494215057 450359962737049600 73265000043959 100000000000000000 416085781 1048576 769 1048576 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 416085781 1048576) (BSN.cos_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146529124732047428943872) qz36) 226375608064910080 72057594037927936 Bool.false 593063 1048576 63 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 416085781 1048576 226375608064910080 72057594037927936 63 146529124732047428943872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 593063 1048576 146529124732047428943872 151115727451828646838272 2082304103 2147483648 400391 400000 (ep1023 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1025 := nat_lit 1209497034693235029614028981132349993013789595911261810049364767043417656675265

noncomputable def ep1026 := nat_lit 3167158043301817604921389341662833414515549005910958195719050097379809300204481

noncomputable def ep1027 := BSN.sin_dyadic_bound_f 2082304103 2147483648 3 2 1048576 400391 ep1025 ep60 ep1021 ep1026 ep63 ep1021 864746 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2082304103) qz15 0 2 ep1025 ep60 ep1021 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2082304103) qz16 0 2 ep1026 ep63 ep1021 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1028 := @Enclosure.Real.IsNear.sin_image qz160 qz475 Bool.false 416085781 1048576 769 1048576 Bool.false 864746 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 178707482261494215057 450359962737049600 73265000043959 100000000000000000 416085781 1048576 769 1048576 (ep1019 rfl) rfl) (Enclosure.sfrac_false_div 416085781 1048576) (BSN.sin_reduce0 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 146529124732047428943872) qz36) 226375608064910080 72057594037927936 Bool.false 864746 1048576 63 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 416085781 1048576 226375608064910080 72057594037927936 63 146529124732047428943872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 864746 1048576 146529124732047428943872 151115727451828646838272 2082304103 2147483648 400391 400000 (ep1027 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1029 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz45 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz45 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 160566469683 1099511627776 656916027553 3435973836800000 Bool.true 117061098393 549755813888 5138789351 26843545600000 (@Enclosure.Real.IsNear.mulLit_ff qz45 (Real.cos qz160) 270741 1048576 1 1048576 593063 1048576 2419509 3276800000 160566469683 1099511627776 656916027553 3435973836800000 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 593063 1048576 154848576 209715200000 593063 1048576 2419509 3276800000 (ep1024 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz45 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 270741 1048576 1 1048576 432373 524288 2419509 3276800000 117061098393 549755813888 5138789351 26843545600000 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 432373 524288 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 864746 1048576 154848576 209715200000 432373 524288 2419509 3276800000 (ep1028 rfl rfl) rfl)) rfl)

noncomputable def ep1030 := @ep935 160566469683 1099511627776 656916027553 3435973836800000 Bool.true 117061098393 549755813888 5138789351 26843545600000 Bool.false 112095982601945747554304 203901404533 1099511627776 13768931960321 3435973836800000 Bool.true 34418633550012147040256 3912945607 34359738368 6884938787973 1717986918400000 (ep936 (BSN.head_sum_c_succ qz141 14 15 rfl rfl) (ep1017 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1018 ep1029) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz462 qz602)

noncomputable def ep1031 := @Enclosure.Complex.IsNear.of_eq qz698 (Complex.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 74029969629 549755813888 318421993023 1717986918400000 Bool.false 231593116923 1099511627776 637839782921 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 16 qz145 rfl)

noncomputable def ep1032 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz602 146530 1000 0 1 3121657384082679 1125899906842624 1250000001 250000000000000 45741645648963495387 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 52372720210750067441664 18889465931478580854784 1000000000800000 200000000000000000000 3121657384082679 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep270 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1033 := nat_lit 766357641745461591370594703481828188882530802505141977388430885179288551301376

noncomputable def ep1034 := nat_lit 459498972611444303607290813483718848843658785951908005464818973691256381696

noncomputable def ep1035 := nat_lit 2298153927291161885504569528818517128949905089943522116154363017590483141140736

noncomputable def ep1036 := BSN.cos_dyadic_bound_f 2151719066 2147483648 3 2 1048576 400391 ep1033 ep67 ep1034 ep1035 ep69 ep1034 564806 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2151719066) qz20 0 2 ep1033 ep67 ep1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2151719066) qz21 0 2 ep1035 ep69 ep1034 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 426002271) qz35)

noncomputable def ep1037 := @Enclosure.Real.IsNear.cos_image qz161 qz476 Bool.false 426002271 1048576 385 524288 Bool.true 564806 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 45741645648963495387 112589990684262400 18316250014653 25000000000000000 426002271 1048576 385 524288 (ep1032 rfl) rfl) (Enclosure.sfrac_false_div 426002271 1048576) (BSN.cos_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151413768520764512796672) qz36) 226375608064910080 72057594037927936 Bool.false 564806 1048576 64 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 426002271 1048576 226375608064910080 72057594037927936 64 151413768520764512796672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 564806 1048576 151413768520764512796672 151115727451828646838272 2151719066 2147483648 400391 400000 (ep1036 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1038 := nat_lit 1379076155963741709024184633616503764909480517480494032894803738143766387237120

noncomputable def ep1039 := nat_lit 3611122172044619280476547950535679077579083050604990806525161988228649932431616

noncomputable def ep1040 := BSN.sin_dyadic_bound_f 2151719066 2147483648 3 2 1048576 400391 ep1038 ep60 ep1034 ep1039 ep63 ep1034 883461 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2151719066) qz15 0 2 ep1038 ep60 ep1034 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2151719066) qz16 0 2 ep1039 ep63 ep1034 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1041 := @Enclosure.Real.IsNear.sin_image qz161 qz476 Bool.false 426002271 1048576 385 524288 Bool.true 883461 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 45741645648963495387 112589990684262400 18316250014653 25000000000000000 426002271 1048576 385 524288 (ep1032 rfl) rfl) (Enclosure.sfrac_false_div 426002271 1048576) (BSN.sin_reduce2 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 151413768520764512796672) qz36) 226375608064910080 72057594037927936 Bool.false 883461 1048576 64 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 426002271 1048576 226375608064910080 72057594037927936 64 151413768520764512796672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 883461 1048576 151413768520764512796672 151115727451828646838272 2151719066 2147483648 400391 400000 (ep1040 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1042 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz47 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz47 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 74029969629 549755813888 318421993023 1717986918400000 Bool.false 231593116923 1099511627776 637839782921 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz47 (Real.cos qz161) 262143 1048576 1 1048576 282403 524288 1211317 1638400000 74029969629 549755813888 318421993023 1717986918400000 qz334 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 564806 1048576 77524288 104857600000 282403 524288 1211317 1638400000 (ep1037 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz47 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 262143 1048576 1 1048576 883461 1048576 1211317 1638400000 231593116923 1099511627776 637839782921 3435973836800000 qz334 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 883461 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 883461 1048576 77524288 104857600000 883461 1048576 1211317 1638400000 (ep1041 rfl rfl) rfl)) rfl)

noncomputable def ep1043 := @ep933 74029969629 549755813888 318421993023 1717986918400000 Bool.false 231593116923 1099511627776 637839782921 3435973836800000 Bool.false 30699170190956114739200 55841465275 1099511627776 14405775946367 3435973836800000 Bool.false 3655149711552394821632 106378857499 1099511627776 14407717358867 3435973836800000 (ep934 (BSN.head_sum_c_succ qz141 15 16 rfl rfl) (ep1030 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1031 ep1042) rfl rfl

theorem EMRow51.d14 : Enclosure.Complex.IsNear qz153 Bool.false 55841465275 1099511627776 14405775946367 3435973836800000 Bool.false 106378857499 1099511627776 14407717358867 3435973836800000 := ep932 (BSN.head_sum_c_succ qz141 16 17 rfl rfl) (ep1043 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz162 := (BSN.headSumC qz460 25)

noncomputable abbrev qz706 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz142)

noncomputable def ep1044 := @Enclosure.Complex.IsNear.of_eq qz162 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 24) qz706) Bool.false 221973231291 274877906944 189356693313 34359738368000 Bool.true 91071763311 549755813888 378576082751 68719476736000

noncomputable def ep1045 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 24) qz706 Bool.false 719810024815 1099511627776 3683068718113 687194767360000 Bool.true 4177101895 137438953472 920438049997 171798691840000 Bool.false

noncomputable abbrev qz707 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz142)

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 23) qz707) Bool.false 719810024815 1099511627776 3683068718113 687194767360000 Bool.true 4177101895 137438953472 920438049997 171798691840000

noncomputable def ep1047 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 23) qz707 Bool.false 277702350305 549755813888 8941649702697 1717986918400000 Bool.false 126372518029 1099511627776 17876782789769 3435973836800000 Bool.false

noncomputable abbrev qz708 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz142)

noncomputable def ep1048 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 22) qz708) Bool.false 277702350305 549755813888 8941649702697 1717986918400000 Bool.false 126372518029 1099511627776 17876782789769 3435973836800000

noncomputable def ep1049 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 22) qz708 Bool.false 354461608945 1099511627776 17339589921747 3435973836800000 Bool.false 247090615345 1099511627776 17334194734247 3435973836800000 Bool.false

noncomputable abbrev qz709 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz142)

noncomputable def ep1050 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 21) qz709) Bool.false 354461608945 1099511627776 17339589921747 3435973836800000 Bool.false 247090615345 1099511627776 17334194734247 3435973836800000

noncomputable def ep1051 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 21) qz709 Bool.false 114535410317 1099511627776 16779404459867 3435973836800000 Bool.false 248902625087 1099511627776 16780513191117 3435973836800000 Bool.false

noncomputable abbrev qz710 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz142)

noncomputable def ep1052 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 20) qz710) Bool.false 114535410317 1099511627776 16779404459867 3435973836800000 Bool.false 248902625087 1099511627776 16780513191117 3435973836800000

noncomputable def ep1053 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 20) qz710 Bool.true 46158856709 1099511627776 16209960453387 3435973836800000 Bool.false 15707065289 274877906944 4052682729753 858993459200000 Bool.false

noncomputable abbrev qz711 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz142)

noncomputable def ep1054 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 19) qz711) Bool.true 46158856709 1099511627776 16209960453387 3435973836800000 Bool.false 15707065289 274877906944 4052682729753 858993459200000

noncomputable def ep1055 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 19) qz711 Bool.false 4953370737 68719476736 3906385608493 858993459200000 Bool.true 156029670895 1099511627776 15625098993347 3435973836800000 Bool.true

noncomputable abbrev qz712 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz142)

noncomputable def ep1056 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 18) qz712) Bool.false 4953370737 68719476736 3906385608493 858993459200000 Bool.true 156029670895 1099511627776 15625098993347 3435973836800000

noncomputable def ep1057 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 18) qz712 Bool.false 294756010487 1099511627776 15024831117479 3435973836800000 Bool.true 6041127709 549755813888 3756323105151 858993459200000 Bool.true

noncomputable abbrev qz713 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz142)

noncomputable def ep1058 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 18) (@HAdd.hAdd Complex Complex Complex qz4 qz153 qz713) Bool.false 294756010487 1099511627776 15024831117479 3435973836800000 Bool.true 6041127709 549755813888 3756323105151 858993459200000

noncomputable def ep1059 := @Enclosure.Complex.IsNear.addLitP qz153 qz713 Bool.false 55841465275 1099511627776 14405775946367 3435973836800000 Bool.false 106378857499 1099511627776 14407717358867 3435973836800000 Bool.false

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz462 qz613)

noncomputable def ep1060 := @Enclosure.Complex.IsNear.of_eq qz713 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 59728636303 274877906944 77381896389 429496729600000 Bool.true 118461112917 1099511627776 617575061737 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 17 qz145 rfl)

noncomputable def ep1061 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz613 146530 1000 0 1 3189913004350711 1125899906842624 1250000001 250000000000000 46741795252750968283 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 53517859495200818200576 18889465931478580854784 1000000000800000 200000000000000000000 3189913004350711 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep303 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1062 := nat_lit 954796015032198317970748643314331281

noncomputable def ep1063 := BSN.cos_dyadic_bound_f 988502221 2147483648 2 1 1048576 400391 ep1062 ep80 ep1062 ep1062 ep81 ep1062 939436 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 988502221) qz20 0 1 ep1062 ep80 ep1062 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 988502221) qz21 0 1 ep1062 ep81 ep1062 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217658445) qz25)

noncomputable def ep1064 := @Enclosure.Real.IsNear.cos_image qz163 qz477 Bool.false 217658445 524288 385 524288 Bool.false 939436 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 46741795252750968283 112589990684262400 18316250014653 25000000000000000 217658445 524288 385 524288 (ep1061 rfl) rfl) (Enclosure.sfrac_false_div 217658445 524288) (BSN.cos_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34779829973539073556480) qz26) 226375608064910080 72057594037927936 Bool.false 939436 1048576 66 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 217658445 524288 226375608064910080 72057594037927936 66 34779829973539073556480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 939436 1048576 34779829973539073556480 75557863725914323419136 988502221 2147483648 400391 400000 (ep1063 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1065 := BSN.sin_dyadic_bound_f 988502221 2147483648 2 1 1048576 400391 ep1062 ep147 ep1062 ep1062 ep148 ep1062 465801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 988502221) qz15 0 1 ep1062 ep147 ep1062 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 988502221) qz16 0 1 ep1062 ep148 ep1062 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1066 := @Enclosure.Real.IsNear.sin_image qz163 qz477 Bool.false 217658445 524288 385 524288 Bool.false 465801 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 46741795252750968283 112589990684262400 18316250014653 25000000000000000 217658445 524288 385 524288 (ep1061 rfl) rfl) (Enclosure.sfrac_false_div 217658445 524288) (BSN.sin_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34779829973539073556480) qz26) 226375608064910080 72057594037927936 Bool.false 465801 1048576 66 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 217658445 524288 226375608064910080 72057594037927936 66 34779829973539073556480 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 465801 1048576 34779829973539073556480 75557863725914323419136 988502221 2147483648 400391 400000 (ep1065 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1067 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 59728636303 274877906944 77381896389 429496729600000 Bool.true 118461112917 1099511627776 617575061737 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz163) 254317 1048576 1 1048576 234859 262144 1211317 1638400000 59728636303 274877906944 77381896389 429496729600000 qz336 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 939436 1048576 77524288 104857600000 234859 262144 1211317 1638400000 (ep1064 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz50 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 254317 1048576 1 1048576 465801 1048576 1211317 1638400000 118461112917 1099511627776 617575061737 3435973836800000 qz336 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.false 465801 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.false 465801 1048576 77524288 104857600000 465801 1048576 1211317 1638400000 (ep1066 rfl rfl) rfl)) rfl)

noncomputable def ep1068 := @ep1059 59728636303 274877906944 77381896389 429496729600000 Bool.true 118461112917 1099511627776 617575061737 3435973836800000 Bool.false 81021915221830274121728 294756010487 1099511627776 15024831117479 3435973836800000 Bool.true 13284580321850575290368 6041127709 549755813888 3756323105151 858993459200000 EMRow51.d14 (ep1060 ep1067) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz462 qz616)

noncomputable def ep1069 := @Enclosure.Complex.IsNear.of_eq qz712 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 215502078695 1099511627776 600711316493 3435973836800000 Bool.true 143947415477 1099511627776 599806572743 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 18 qz145 rfl)

noncomputable def ep1070 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz616 146530 1000 0 1 3254268794313975 1125899906842624 1250000001 250000000000000 1907392025723307027 4503599627370496 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz617) Bool.false 54597570484265130393600 18889465931478580854784 1000000000800000 200000000000000000000 3254268794313975 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep318 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1071 := nat_lit 1271796496403823100526600265263060202746543564030902751731336998457116350644480

noncomputable def ep1072 := nat_lit 390810119429734484257512468325566985778573787683807438616190519336640348416

noncomputable def ep1073 := nat_lit 3330262845626174264595155198359297232073496405377066756776694497023045405409536

noncomputable def ep1074 := BSN.sin_dyadic_bound_f 2108607394 2147483648 3 2 1048576 400391 ep1071 ep60 ep1072 ep1073 ep63 ep1072 871945 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2108607394) qz15 0 2 ep1071 ep60 ep1072 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2108607394) qz16 0 2 ep1073 ep63 ep1072 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 444099313) qz35)

noncomputable def ep1075 := @Enclosure.Real.IsNear.cos_image qz164 qz478 Bool.false 444099313 1048576 769 1048576 Bool.true 871945 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 1907392025723307027 4503599627370496 18316250014653 25000000000000000 444099313 1048576 769 1048576 (ep1070 rfl) rfl) (Enclosure.sfrac_false_div 444099313 1048576) (BSN.cos_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148380054342444741820416) qz36) 226375608064910080 72057594037927936 Bool.false 871945 1048576 67 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 444099313 1048576 226375608064910080 72057594037927936 67 148380054342444741820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 871945 1048576 148380054342444741820416 151115727451828646838272 2108607394 2147483648 400391 400000 (ep1074 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1076 := nat_lit 706727302499648271174447930687622586852870235033916554267905528262547590512896

noncomputable def ep1077 := nat_lit 2119400287260085344554828767126216626587053557526382047926484203748969490841856

noncomputable def ep1078 := BSN.cos_dyadic_bound_f 2108607394 2147483648 3 2 1048576 400391 ep1076 ep67 ep1072 ep1077 ep69 ep1072 582427 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2108607394) qz20 0 2 ep1076 ep67 ep1072 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2108607394) qz21 0 2 ep1077 ep69 ep1072 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1079 := @Enclosure.Real.IsNear.sin_image qz164 qz478 Bool.false 444099313 1048576 769 1048576 Bool.false 582427 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 1907392025723307027 4503599627370496 18316250014653 25000000000000000 444099313 1048576 769 1048576 (ep1070 rfl) rfl) (Enclosure.sfrac_false_div 444099313 1048576) (BSN.sin_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 148380054342444741820416) qz36) 226375608064910080 72057594037927936 Bool.false 582427 1048576 67 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 444099313 1048576 226375608064910080 72057594037927936 67 148380054342444741820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 582427 1048576 148380054342444741820416 151115727451828646838272 2108607394 2147483648 400391 400000 (ep1078 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 215502078695 1099511627776 600711316493 3435973836800000 Bool.true 143947415477 1099511627776 599806572743 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz164) 247151 1048576 1 1048576 871945 1048576 2419509 3276800000 215502078695 1099511627776 600711316493 3435973836800000 qz338 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 871945 1048576 154848576 209715200000 871945 1048576 2419509 3276800000 (ep1075 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz52 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 247151 1048576 1 1048576 582427 1048576 2419509 3276800000 143947415477 1099511627776 599806572743 3435973836800000 qz338 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 582427 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 582427 1048576 154848576 209715200000 582427 1048576 2419509 3276800000 (ep1079 rfl rfl) rfl)) rfl)

noncomputable def ep1081 := @ep1057 215502078695 1099511627776 600711316493 3435973836800000 Bool.true 143947415477 1099511627776 599806572743 3435973836800000 Bool.false 87140619552269996654592 4953370737 68719476736 3906385608493 858993459200000 Bool.true 85778218713557510389760 156029670895 1099511627776 15625098993347 3435973836800000 (ep1058 (BSN.head_sum_c_succ qz141 17 18 rfl rfl) (ep1068 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1069 ep1080) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz462 qz619)

noncomputable def ep1082 := @Enclosure.Complex.IsNear.of_eq qz711 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.true 125412788501 1099511627776 116883603883 687194767360000 Bool.false 218857932051 1099511627776 117126385133 687194767360000 (BSN.cpow_neg_s_mk qz144 146530 1000 19 qz145 rfl)

noncomputable def ep1083 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz619 146530 1000 0 1 3315143513283831 1125899906842624 1250000001 250000000000000 48576797900147975643 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 55618878793361701994496 18889465931478580854784 1000000000800000 200000000000000000000 3315143513283831 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1084 := nat_lit 925870875671266386431529031871326077224125674131389300431620511825249766998016

noncomputable def ep1085 := nat_lit 670523634778947832433542793759208855462929012386877770367037560818537332736

noncomputable def ep1086 := nat_lit 2776271579744241263629720010026459813961451164369394145754127460354112226328576

noncomputable def ep1087 := BSN.cos_dyadic_bound_f 2255806072 2147483648 3 2 1048576 400391 ep1084 ep67 ep1085 ep1086 ep69 ep1085 521339 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2255806072) qz20 0 2 ep1084 ep67 ep1085 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2255806072) qz21 0 2 ep1086 ep69 ep1085 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113101671) qz17)

noncomputable def ep1088 := @Enclosure.Real.IsNear.cos_image qz165 qz479 Bool.false 113101671 262144 385 524288 Bool.true 521339 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 48576797900147975643 112589990684262400 18316250014653 25000000000000000 113101671 262144 385 524288 (ep1083 rfl) rfl) (Enclosure.sfrac_false_div 113101671 262144) (BSN.cos_reduce2 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39684560102999963205632) qz19) 226375608064910080 72057594037927936 Bool.false 521339 1048576 68 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 113101671 262144 226375608064910080 72057594037927936 68 39684560102999963205632 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 521339 1048576 39684560102999963205632 37778931862957161709568 2255806072 2147483648 400391 400000 (ep1087 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1089 := nat_lit 1666031157300456337310805423133379571919055870226591238560623291236794750730240

noncomputable def ep1090 := nat_lit 4362329326092505444085312277016574445450587298859112584601990559093137191469056

noncomputable def ep1091 := BSN.sin_dyadic_bound_f 2255806072 2147483648 3 2 1048576 400391 ep1089 ep60 ep1085 ep1090 ep63 ep1085 909789 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2255806072) qz15 0 2 ep1089 ep60 ep1085 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2255806072) qz16 0 2 ep1090 ep63 ep1085 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1092 := @Enclosure.Real.IsNear.sin_image qz165 qz479 Bool.false 113101671 262144 385 524288 Bool.true 909789 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 48576797900147975643 112589990684262400 18316250014653 25000000000000000 113101671 262144 385 524288 (ep1083 rfl) rfl) (Enclosure.sfrac_false_div 113101671 262144) (BSN.sin_reduce2 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 39684560102999963205632) qz19) 226375608064910080 72057594037927936 Bool.false 909789 1048576 68 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 113101671 262144 226375608064910080 72057594037927936 68 39684560102999963205632 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 909789 1048576 39684560102999963205632 37778931862957161709568 2255806072 2147483648 400391 400000 (ep1091 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1093 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.true 125412788501 1099511627776 116883603883 687194767360000 Bool.false 218857932051 1099511627776 117126385133 687194767360000 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz165) 240559 1048576 1 1048576 521339 1048576 1211317 1638400000 125412788501 1099511627776 116883603883 687194767360000 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.true 521339 1048576 77524288 104857600000 521339 1048576 1211317 1638400000 (ep1088 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz54 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 240559 1048576 1 1048576 909789 1048576 1211317 1638400000 218857932051 1099511627776 117126385133 687194767360000 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 909789 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 909789 1048576 77524288 104857600000 909789 1048576 1211317 1638400000 (ep1092 rfl rfl) rfl)) rfl)

noncomputable def ep1094 := @ep1055 125412788501 1099511627776 116883603883 687194767360000 Bool.false 218857932051 1099511627776 117126385133 687194767360000 Bool.true 3172012479774483021824 46158856709 1099511627776 16209960453387 3435973836800000 Bool.false 69080403693969191469056 15707065289 274877906944 4052682729753 858993459200000 (ep1056 (BSN.head_sum_c_succ qz141 18 19 rfl rfl) (ep1081 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1082 ep1093) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz462 qz622)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq qz710 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 80347133513 549755813888 7118050081 42949672960000 Bool.false 186074363931 1099511627776 113956454421 687194767360000 (BSN.cpow_neg_s_mk qz144 146530 1000 20 qz145 rfl)

noncomputable def ep1096 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz622 146530 1000 0 1 3372893643545847 1125899906842624 1250000001 250000000000000 49423010558877296091 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz623) Bool.false 56587765202795681021952 18889465931478580854784 1000000000800000 200000000000000000000 3372893643545847 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep348 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1097 := nat_lit 5476024498359332071188296323880442001

noncomputable def ep1098 := BSN.sin_dyadic_bound_f 1529735501 2147483648 2 1 1048576 400391 ep1097 ep147 ep1097 ep1097 ep148 ep1097 685354 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1529735501) qz15 0 1 ep1097 ep147 ep1097 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1529735501) qz16 0 1 ep1097 ep148 ep1097 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz480 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 230143827) qz25)

noncomputable def ep1099 := @Enclosure.Real.IsNear.cos_image qz166 qz480 Bool.false 230143827 524288 769 1048576 Bool.false 685354 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 49423010558877296091 112589990684262400 18316250014653 25000000000000000 230143827 524288 769 1048576 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 230143827 524288) (BSN.cos_reduce3 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53822783085410972073984) qz26) 226375608064910080 72057594037927936 Bool.false 685354 1048576 69 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 230143827 524288 226375608064910080 72057594037927936 69 53822783085410972073984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 685354 1048576 53822783085410972073984 75557863725914323419136 1529735501 2147483648 400391 400000 (ep1098 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1100 := nat_lit 195686417494276244965353377647607396231647573855875691385387590194566860046881

noncomputable def ep1101 := nat_lit 29986844306631574453617500818289756498167028462816316454581302763124884001

noncomputable def ep1102 := nat_lit 586999278794215471747152897941185609181946387510701441523253607978174330372641

noncomputable def ep1103 := BSN.cos_dyadic_bound_f 1529735501 2147483648 3 2 1048576 400391 ep1100 ep67 ep1101 ep1102 ep69 ep1101 793599 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1529735501) qz20 0 2 ep1100 ep67 ep1101 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1529735501) qz21 0 2 ep1102 ep69 ep1101 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1104 := @Enclosure.Real.IsNear.sin_image qz166 qz480 Bool.false 230143827 524288 769 1048576 Bool.true 793599 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 49423010558877296091 112589990684262400 18316250014653 25000000000000000 230143827 524288 769 1048576 (ep1096 rfl) rfl) (Enclosure.sfrac_false_div 230143827 524288) (BSN.sin_reduce3 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53822783085410972073984) qz26) 226375608064910080 72057594037927936 Bool.false 793599 1048576 69 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 230143827 524288 226375608064910080 72057594037927936 69 53822783085410972073984 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 793599 1048576 53822783085410972073984 75557863725914323419136 1529735501 2147483648 400391 400000 (ep1103 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 80347133513 549755813888 7118050081 42949672960000 Bool.false 186074363931 1099511627776 113956454421 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz166) 234469 1048576 1 1048576 342677 524288 2419509 3276800000 80347133513 549755813888 7118050081 42949672960000 qz342 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 685354 1048576 154848576 209715200000 342677 524288 2419509 3276800000 (ep1099 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 234469 1048576 1 1048576 793599 1048576 2419509 3276800000 186074363931 1099511627776 113956454421 687194767360000 qz342 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 793599 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 793599 1048576 154848576 209715200000 793599 1048576 2419509 3276800000 (ep1104 rfl rfl) rfl)) rfl)

noncomputable def ep1106 := @ep1053 80347133513 549755813888 7118050081 42949672960000 Bool.false 186074363931 1099511627776 113956454421 687194767360000 Bool.false 62966507717818367082496 114535410317 1099511627776 16779404459867 3435973836800000 Bool.false 68417832616781705904128 248902625087 1099511627776 16780513191117 3435973836800000 (ep1054 (BSN.head_sum_c_succ qz141 19 20 rfl rfl) (ep1094 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1095 ep1105) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz462 qz625)

noncomputable def ep1107 := @Enclosure.Complex.IsNear.of_eq qz709 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 59981549657 274877906944 14004636547 85899345920000 Bool.true 906004871 549755813888 55368154313 343597383680000 (BSN.cpow_neg_s_mk qz144 146530 1000 21 qz145 rfl)

noncomputable def ep1108 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz625 146530 1000 0 1 3427826275261687 1125899906842624 1250000001 250000000000000 50227938411409499611 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz626) Bool.false 57509381830540779323392 18889465931478580854784 1000000000800000 200000000000000000000 3427826275261687 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep363 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1109 := BSN.cos_dyadic_bound_f 16219170 2147483648 1 0 1048576 400391 0 1 1 0 1 1 1048546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 16219170) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 16219170) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 467784129) qz35)

noncomputable def ep1110 := @Enclosure.Real.IsNear.cos_image qz167 qz481 Bool.false 467784129 1048576 769 1048576 Bool.false 1048546 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 50227938411409499611 112589990684262400 18316250014653 25000000000000000 467784129 1048576 769 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 467784129 1048576) (BSN.cos_reduce0 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1141322690417831968768) qz36) 226375608064910080 72057594037927936 Bool.false 1048546 1048576 71 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 467784129 1048576 226375608064910080 72057594037927936 71 1141322690417831968768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048546 1048576 1141322690417831968768 151115727451828646838272 16219170 2147483648 400391 400000 (ep1109 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1111 := BSN.sin_dyadic_bound_f 16219170 2147483648 1 0 1048576 400391 0 1 1 0 1 1 7919 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 16219170) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 16219170) qz16 0 0 rfl) rfl rfl

noncomputable def ep1112 := @Enclosure.Real.IsNear.sin_image qz167 qz481 Bool.false 467784129 1048576 769 1048576 Bool.false 7919 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 50227938411409499611 112589990684262400 18316250014653 25000000000000000 467784129 1048576 769 1048576 (ep1108 rfl) rfl) (Enclosure.sfrac_false_div 467784129 1048576) (BSN.sin_reduce0 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1141322690417831968768) qz36) 226375608064910080 72057594037927936 Bool.false 7919 1048576 71 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 467784129 1048576 226375608064910080 72057594037927936 71 1141322690417831968768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 7919 1048576 1141322690417831968768 151115727451828646838272 16219170 2147483648 400391 400000 (ep1111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1113 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 59981549657 274877906944 14004636547 85899345920000 Bool.true 906004871 549755813888 55368154313 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz58 (Real.cos qz167) 114409 524288 1 524288 524273 524288 2419509 3276800000 59981549657 274877906944 14004636547 85899345920000 qz344 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 1048546 1048576 154848576 209715200000 524273 524288 2419509 3276800000 (ep1110 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 114409 524288 1 524288 7919 1048576 2419509 3276800000 906004871 549755813888 55368154313 343597383680000 qz344 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.false 7919 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.false 7919 1048576 154848576 209715200000 7919 1048576 2419509 3276800000 (ep1112 rfl rfl) rfl)) rfl)

noncomputable def ep1114 := @ep1051 59981549657 274877906944 14004636547 85899345920000 Bool.true 906004871 549755813888 55368154313 343597383680000 Bool.false 97433665158804228014080 354461608945 1099511627776 17339589921747 3435973836800000 Bool.false 135839502343077216911360 247090615345 1099511627776 17334194734247 3435973836800000 (ep1052 (BSN.head_sum_c_succ qz141 20 21 rfl rfl) (ep1106 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1107 ep1113) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz462 qz627)

noncomputable def ep1115 := @Enclosure.Complex.IsNear.of_eq qz708 (Complex.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 200943091665 1099511627776 543709483647 3435973836800000 Bool.true 30179524329 274877906944 271294027761 1717986918400000 (BSN.cpow_neg_s_mk qz144 146530 1000 22 qz145 rfl)

noncomputable def ep1116 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz627 146530 1000 0 1 3480203401436407 1125899906842624 1250000001 250000000000000 50995420441247671771 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz628) Bool.false 58388124189833310502912 18889465931478580854784 1000000000800000 200000000000000000000 3480203401436407 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep374 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1117 := nat_lit 1821519197433820115311945111506250000

noncomputable def ep1118 := BSN.cos_dyadic_bound_f 1161738650 2147483648 2 1 1048576 400391 ep1117 ep80 ep1117 ep1117 ep81 ep1117 898845 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1161738650) qz20 0 1 ep1117 ep80 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1161738650) qz21 0 1 ep1117 ep81 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237465931) qz25)

noncomputable def ep1119 := @Enclosure.Real.IsNear.cos_image qz168 qz482 Bool.false 237465931 524288 769 1048576 Bool.false 898845 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 50995420441247671771 112589990684262400 18316250014653 25000000000000000 237465931 524288 769 1048576 (ep1116 rfl) rfl) (Enclosure.sfrac_false_div 237465931 524288) (BSN.cos_reduce0 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40875044946167371661312) qz26) 226375608064910080 72057594037927936 Bool.false 898845 1048576 72 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 237465931 524288 226375608064910080 72057594037927936 72 40875044946167371661312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 898845 1048576 40875044946167371661312 75557863725914323419136 1161738650 2147483648 400391 400000 (ep1118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1120 := BSN.sin_dyadic_bound_f 1161738650 2147483648 2 1 1048576 400391 ep1117 ep147 ep1117 ep1117 ep148 ep1117 539988 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1161738650) qz15 0 1 ep1117 ep147 ep1117 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1161738650) qz16 0 1 ep1117 ep148 ep1117 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1121 := @Enclosure.Real.IsNear.sin_image qz168 qz482 Bool.false 237465931 524288 769 1048576 Bool.false 539988 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 50995420441247671771 112589990684262400 18316250014653 25000000000000000 237465931 524288 769 1048576 (ep1116 rfl) rfl) (Enclosure.sfrac_false_div 237465931 524288) (BSN.sin_reduce0 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 40875044946167371661312) qz26) 226375608064910080 72057594037927936 Bool.false 539988 1048576 72 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 237465931 524288 226375608064910080 72057594037927936 72 40875044946167371661312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 539988 1048576 40875044946167371661312 75557863725914323419136 1161738650 2147483648 400391 400000 (ep1120 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1122 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz345 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz345 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 200943091665 1099511627776 543709483647 3435973836800000 Bool.true 30179524329 274877906944 271294027761 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ff qz345 (Real.cos qz168) 223557 1048576 1 1048576 898845 1048576 2419509 3276800000 200943091665 1099511627776 543709483647 3435973836800000 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 898845 1048576 154848576 209715200000 898845 1048576 2419509 3276800000 (ep1119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz345 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 223557 1048576 1 1048576 134997 262144 2419509 3276800000 30179524329 274877906944 271294027761 1717986918400000 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 134997 262144 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 539988 1048576 154848576 209715200000 134997 262144 2419509 3276800000 (ep1121 rfl rfl) rfl)) rfl)

noncomputable def ep1123 := @ep1049 200943091665 1099511627776 543709483647 3435973836800000 Bool.true 30179524329 274877906944 271294027761 1717986918400000 Bool.false 610673926442143040143360 277702350305 549755813888 8941649702697 1717986918400000 Bool.false 34737013251054424293376 126372518029 1099511627776 17876782789769 3435973836800000 (ep1050 (BSN.head_sum_c_succ qz141 21 22 rfl rfl) (ep1114 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1115 ep1122) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz462 qz629)

noncomputable def ep1124 := @Enclosure.Complex.IsNear.of_eq qz707 (Complex.mk (@HMul.hMul Real Real Real qz0 qz350 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz350 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 164405324205 1099511627776 532044185171 3435973836800000 Bool.true 159789333189 1099511627776 531978210171 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 23 qz145 rfl)

noncomputable def ep1125 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz629 146530 1000 0 1 3530250507853047 1125899906842624 1250000001 250000000000000 51728760691570697691 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz630) Bool.false 59227775304360265777152 18889465931478580854784 1000000000800000 200000000000000000000 3530250507853047 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep388 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1126 := nat_lit 268794129364421876427637805488997560182864080620597135738932550235031524693121

noncomputable def ep1127 := nat_lit 56571701827746141712115746402974672065154435193546302182382824784602944641

noncomputable def ep1128 := nat_lit 806269244689610136999489184974186731204461932991404314612432885055525368190081

noncomputable def ep1129 := BSN.cos_dyadic_bound_f 1656055569 2147483648 3 2 1048576 400391 ep1126 ep67 ep1127 ep1128 ep69 ep1127 751935 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1656055569) qz20 0 2 ep1126 ep67 ep1127 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1656055569) qz21 0 2 ep1128 ep69 ep1127 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz483 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 481761625) qz35)

noncomputable def ep1130 := @Enclosure.Real.IsNear.cos_image qz169 qz483 Bool.false 481761625 1048576 385 524288 Bool.false 751935 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 51728760691570697691 112589990684262400 18316250014653 25000000000000000 481761625 1048576 385 524288 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 481761625 1048576) (BSN.cos_reduce0 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116534550741771763056640) qz36) 226375608064910080 72057594037927936 Bool.false 751935 1048576 73 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 481761625 1048576 226375608064910080 72057594037927936 73 116534550741771763056640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 751935 1048576 116534550741771763056640 151115727451828646838272 1656055569 2147483648 400391 400000 (ep1129 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1131 := nat_lit 7521416211575193882910683294989165121

noncomputable def ep1132 := BSN.sin_dyadic_bound_f 1656055569 2147483648 2 1 1048576 400391 ep1131 ep147 ep1131 ep1131 ep148 ep1131 730823 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1656055569) qz15 0 1 ep1131 ep147 ep1131 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1656055569) qz16 0 1 ep1131 ep148 ep1131 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1133 := @Enclosure.Real.IsNear.sin_image qz169 qz483 Bool.false 481761625 1048576 385 524288 Bool.false 730823 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 51728760691570697691 112589990684262400 18316250014653 25000000000000000 481761625 1048576 385 524288 (ep1125 rfl) rfl) (Enclosure.sfrac_false_div 481761625 1048576) (BSN.sin_reduce0 qz483 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116534550741771763056640) qz36) 226375608064910080 72057594037927936 Bool.false 730823 1048576 73 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 481761625 1048576 226375608064910080 72057594037927936 73 116534550741771763056640 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730823 1048576 116534550741771763056640 151115727451828646838272 1656055569 2147483648 400391 400000 (ep1132 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1134 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz350 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz350 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 164405324205 1099511627776 532044185171 3435973836800000 Bool.true 159789333189 1099511627776 531978210171 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz350 (Real.cos qz169) 218643 1048576 1 1048576 751935 1048576 1211317 1638400000 164405324205 1099511627776 532044185171 3435973836800000 qz354 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 751935 1048576 77524288 104857600000 751935 1048576 1211317 1638400000 (ep1130 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz350 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 218643 1048576 1 1048576 730823 1048576 1211317 1638400000 159789333189 1099511627776 531978210171 3435973836800000 qz354 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 730823 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 730823 1048576 77524288 104857600000 730823 1048576 1211317 1638400000 (ep1133 rfl rfl) rfl)) rfl)

noncomputable def ep1135 := @ep1047 164405324205 1099511627776 532044185171 3435973836800000 Bool.true 159789333189 1099511627776 531978210171 3435973836800000 Bool.false 395719746036911801630720 719810024815 1099511627776 3683068718113 687194767360000 Bool.true 36742176831661313884160 4177101895 137438953472 920438049997 171798691840000 (ep1048 (BSN.head_sum_c_succ qz141 22 23 rfl rfl) (ep1123 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1124 ep1134) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz462 qz631)

noncomputable def ep1136 := @Enclosure.Complex.IsNear.of_eq qz706 (Complex.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 168082900349 1099511627776 104065148147 687194767360000 Bool.true 74363355731 549755813888 52004313761 343597383680000 (BSN.cpow_neg_s_mk qz144 146530 1000 24 qz145 rfl)

noncomputable def ep1137 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz631 146530 1000 0 1 3578169457974519 1125899906842624 1250000001 250000000000000 52430917067700626907 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz632) Bool.false 60031721881041427759104 18889465931478580854784 1000000000800000 200000000000000000000 3578169457974519 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep402 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1138 := nat_lit 209256285384941225791364853044920120416869931532940360512970130150082979289921

noncomputable def ep1139 := nat_lit 34289187522508932239701954604400292495068691252619327962923947420284869441

noncomputable def ep1140 := nat_lit 627700277779778659509615155225551560665619657216315842882984542555408368130881

noncomputable def ep1141 := BSN.cos_dyadic_bound_f 1555588233 2147483648 3 2 1048576 400391 ep1138 ep67 ep1139 ep1140 ep69 ep1139 785291 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1555588233) qz20 0 2 ep1138 ep67 ep1139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1555588233) qz21 0 2 ep1140 ep69 ep1139 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz484 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 244150483) qz25)

noncomputable def ep1142 := @Enclosure.Real.IsNear.cos_image qz170 qz484 Bool.false 244150483 524288 769 1048576 Bool.false 785291 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 52430917067700626907 112589990684262400 18316250014653 25000000000000000 244150483 524288 769 1048576 (ep1137 rfl) rfl) (Enclosure.sfrac_false_div 244150483 524288) (BSN.cos_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54732395219921284366336) qz26) 226375608064910080 72057594037927936 Bool.false 785291 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 244150483 524288 226375608064910080 72057594037927936 74 54732395219921284366336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 785291 1048576 54732395219921284366336 75557863725914323419136 1555588233 2147483648 400391 400000 (ep1141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1143 := nat_lit 5855697014233995717085030230423919521

noncomputable def ep1144 := BSN.sin_dyadic_bound_f 1555588233 2147483648 2 1 1048576 400391 ep1143 ep147 ep1143 ep1143 ep148 ep1143 694858 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1555588233) qz15 0 1 ep1143 ep147 ep1143 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1555588233) qz16 0 1 ep1143 ep148 ep1143 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1145 := @Enclosure.Real.IsNear.sin_image qz170 qz484 Bool.false 244150483 524288 769 1048576 Bool.false 694858 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 52430917067700626907 112589990684262400 18316250014653 25000000000000000 244150483 524288 769 1048576 (ep1137 rfl) rfl) (Enclosure.sfrac_false_div 244150483 524288) (BSN.sin_reduce0 qz484 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54732395219921284366336) qz26) 226375608064910080 72057594037927936 Bool.false 694858 1048576 74 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 244150483 524288 226375608064910080 72057594037927936 74 54732395219921284366336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 694858 1048576 54732395219921284366336 75557863725914323419136 1555588233 2147483648 400391 400000 (ep1144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1146 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz355 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz355 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 168082900349 1099511627776 104065148147 687194767360000 Bool.true 74363355731 549755813888 52004313761 343597383680000 (@Enclosure.Real.IsNear.mulLit_ff qz355 (Real.cos qz170) 214039 1048576 1 1048576 785291 1048576 2419509 3276800000 168082900349 1099511627776 104065148147 687194767360000 qz359 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 785291 1048576 154848576 209715200000 785291 1048576 2419509 3276800000 (ep1142 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz355 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 214039 1048576 1 1048576 347429 524288 2419509 3276800000 74363355731 549755813888 52004313761 343597383680000 qz359 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 347429 524288 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 694858 1048576 154848576 209715200000 347429 524288 2419509 3276800000 (ep1145 rfl rfl) rfl)) rfl)

noncomputable def ep1147 := @ep1045 168082900349 1099511627776 104065148147 687194767360000 Bool.true 74363355731 549755813888 52004313761 343597383680000 Bool.false 976248595437863791755264 221973231291 274877906944 189356693313 34359738368000 Bool.true 12516807840313525665792 91071763311 549755813888 378576082751 68719476736000 (ep1046 (BSN.head_sum_c_succ qz141 23 24 rfl rfl) (ep1135 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1136 ep1146) rfl rfl

theorem EMRow51.d15 : Enclosure.Complex.IsNear qz162 Bool.false 221973231291 274877906944 189356693313 34359738368000 Bool.true 91071763311 549755813888 378576082751 68719476736000 := ep1044 (BSN.head_sum_c_succ qz141 24 25 rfl rfl) (ep1147 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz171 := (BSN.headSumC qz460 33)

noncomputable abbrev qz714 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz142)

noncomputable def ep1148 := @Enclosure.Complex.IsNear.of_eq qz171 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 32) qz714) Bool.false 1361036149053 1099511627776 22767399088277 3435973836800000 Bool.false 21616452021 549755813888 1422372820947 214748364800000

noncomputable def ep1149 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 32) qz714 Bool.false 1273518491507 1099511627776 22316854515751 3435973836800000 Bool.true 130315985153 1099511627776 22305970178251 3435973836800000 Bool.false

noncomputable abbrev qz715 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz142)

noncomputable def ep1150 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 31) qz715) Bool.false 1273518491507 1099511627776 22316854515751 3435973836800000 Bool.true 130315985153 1099511627776 22305970178251 3435973836800000

noncomputable def ep1151 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 31) qz715 Bool.false 1102858894945 1099511627776 21858356579531 3435973836800000 Bool.true 30955488043 1099511627776 21848655329531 3435973836800000 Bool.false

noncomputable abbrev qz716 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz142)

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 30) qz716) Bool.false 1102858894945 1099511627776 21858356579531 3435973836800000 Bool.true 30955488043 1099511627776 21848655329531 3435973836800000

noncomputable def ep1153 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 30) qz716 Bool.false 1187407015693 1099511627776 4278755197207 687194767360000 Bool.false 75556752731 549755813888 133640517901 21474836480000 Bool.true

noncomputable abbrev qz717 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz142)

noncomputable def ep1154 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 29) qz717) Bool.false 1187407015693 1099511627776 4278755197207 687194767360000 Bool.false 75556752731 549755813888 133640517901 21474836480000

noncomputable def ep1155 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 29) qz717 Bool.false 1388296817773 1099511627776 20919434771591 3435973836800000 Bool.false 57321692981 549755813888 653461888663 107374182400000 Bool.true

noncomputable abbrev qz718 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz142)

noncomputable def ep1156 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 28) qz718) Bool.false 1388296817773 1099511627776 20919434771591 3435973836800000 Bool.false 57321692981 549755813888 653461888663 107374182400000

noncomputable def ep1157 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 28) qz718 Bool.false 1439697922017 1099511627776 4087709068023 687194767360000 Bool.true 21671861939 274877906944 2042752663699 343597383680000 Bool.true

noncomputable abbrev qz719 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz142)

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 27) qz719) Bool.false 1439697922017 1099511627776 4087709068023 687194767360000 Bool.true 21671861939 274877906944 2042752663699 343597383680000

noncomputable def ep1159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 27) qz719 Bool.false 1302685683771 1099511627776 3989507213533 687194767360000 Bool.true 123970698137 549755813888 996807098227 171798691840000 Bool.false

noncomputable abbrev qz720 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz142)

noncomputable def ep1160 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 26) qz720) Bool.false 1302685683771 1099511627776 3989507213533 687194767360000 Bool.true 123970698137 549755813888 996807098227 171798691840000

noncomputable def ep1161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 26) qz720 Bool.false 1088439814509 1099511627776 19446722827619 3435973836800000 Bool.true 272353482447 1099511627776 19438213483869 3435973836800000 Bool.false

noncomputable abbrev qz721 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz142)

noncomputable def ep1162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 26) (@HAdd.hAdd Complex Complex Complex qz4 qz162 qz721) Bool.false 1088439814509 1099511627776 19446722827619 3435973836800000 Bool.true 272353482447 1099511627776 19438213483869 3435973836800000

noncomputable def ep1163 := @Enclosure.Complex.IsNear.addLitP qz162 qz721 Bool.false 221973231291 274877906944 189356693313 34359738368000 Bool.true 91071763311 549755813888 378576082751 68719476736000 Bool.false

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz462 qz641)

noncomputable def ep1164 := @Enclosure.Complex.IsNear.of_eq qz721 (Complex.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz360 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 200546889345 1099511627776 511053496319 3435973836800000 Bool.true 90209955825 1099511627776 509409346319 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 25 qz145 rfl)

noncomputable def ep1165 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz641 146530 1000 0 1 3624129903009015 1125899906842624 1250000001 250000000000000 10620875093758219359 22517998136852480 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz642) Bool.false 60802810194841294602240 18889465931478580854784 1000000000800000 200000000000000000000 3624129903009015 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep437 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1166 := nat_lit 678992247999495787538242706589351936

noncomputable def ep1167 := BSN.cos_dyadic_bound_f 907749888 2147483648 2 1 1048576 400391 ep1166 ep80 ep1166 ep1166 ep81 ep1166 956283 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 907749888) qz20 0 1 ep1166 ep80 ep1166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 907749888) qz21 0 1 ep1166 ep81 ep1166 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 123643259) qz17)

noncomputable def ep1168 := @Enclosure.Real.IsNear.cos_image qz172 qz485 Bool.false 123643259 262144 385 524288 Bool.false 956283 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 10620875093758219359 22517998136852480 18316250014653 25000000000000000 123643259 262144 385 524288 (ep1165 rfl) rfl) (Enclosure.sfrac_false_div 123643259 262144) (BSN.cos_reduce0 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15969304926422824910848) qz19) 226375608064910080 72057594037927936 Bool.false 956283 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 123643259 262144 226375608064910080 72057594037927936 75 15969304926422824910848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956283 1048576 15969304926422824910848 37778931862957161709568 907749888 2147483648 400391 400000 (ep1167 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1169 := BSN.sin_dyadic_bound_f 907749888 2147483648 2 1 1048576 400391 ep1166 ep147 ep1166 ep1166 ep148 ep1166 430155 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 907749888) qz15 0 1 ep1166 ep147 ep1166 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 907749888) qz16 0 1 ep1166 ep148 ep1166 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1170 := @Enclosure.Real.IsNear.sin_image qz172 qz485 Bool.false 123643259 262144 385 524288 Bool.false 430155 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 10620875093758219359 22517998136852480 18316250014653 25000000000000000 123643259 262144 385 524288 (ep1165 rfl) rfl) (Enclosure.sfrac_false_div 123643259 262144) (BSN.sin_reduce0 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15969304926422824910848) qz19) 226375608064910080 72057594037927936 Bool.false 430155 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 123643259 262144 226375608064910080 72057594037927936 75 15969304926422824910848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 430155 1048576 15969304926422824910848 37778931862957161709568 907749888 2147483648 400391 400000 (ep1169 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1171 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz360 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz360 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 200546889345 1099511627776 511053496319 3435973836800000 Bool.true 90209955825 1099511627776 509409346319 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz360 (Real.cos qz172) 209715 1048576 1 1048576 956283 1048576 1211317 1638400000 200546889345 1099511627776 511053496319 3435973836800000 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 956283 1048576 77524288 104857600000 956283 1048576 1211317 1638400000 (ep1168 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz360 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 209715 1048576 1 1048576 430155 1048576 1211317 1638400000 90209955825 1099511627776 509409346319 3435973836800000 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 430155 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 430155 1048576 77524288 104857600000 430155 1048576 1211317 1638400000 (ep1170 rfl rfl) rfl)) rfl)

noncomputable def ep1172 := @ep1163 200546889345 1099511627776 511053496319 3435973836800000 Bool.true 90209955825 1099511627776 509409346319 3435973836800000 Bool.false 299188058046749523050496 1088439814509 1099511627776 19446722827619 3435973836800000 Bool.true 149727910407881606823936 272353482447 1099511627776 19438213483869 3435973836800000 EMRow51.d15 (ep1164 ep1171) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz462 qz643)

noncomputable def ep1173 := @Enclosure.Complex.IsNear.of_eq qz720 (Complex.mk (@HMul.hMul Real Real Real qz0 qz365 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz365 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 107122934631 549755813888 250406620023 1717986918400000 Bool.false 24412086173 1099511627776 497928480671 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 26 qz145 rfl)

noncomputable def ep1174 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz643 146530 1000 0 1 3668288609262839 1125899906842624 1250000001 250000000000000 53751432991528379867 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz644) Bool.false 61543670347942250676224 18889465931478580854784 1000000000800000 200000000000000000000 3668288609262839 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep448 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1175 := nat_lit 6178914185852818943651503308078631906683349784343433279774110094526414480482560

noncomputable def ep1176 := nat_lit 9202952433589829235558106452576853159419507514432590241249543724142706565376

noncomputable def ep1177 := nat_lit 16167970468531570843182081253568435326674474994447529634255884319634854495396096

noncomputable def ep1178 := BSN.sin_dyadic_bound_f 3129614874 2147483648 3 2 1048576 400391 ep1175 ep60 ep1176 ep1177 ep63 ep1176 1041834 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3129614874) qz15 0 2 ep1175 ep60 ep1176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3129614874) qz16 0 2 ep1177 ep63 ep1176 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz486 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 500599229) qz35)

noncomputable def ep1179 := @Enclosure.Real.IsNear.cos_image qz173 qz486 Bool.false 500599229 1048576 769 1048576 Bool.false 1041834 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 53751432991528379867 112589990684262400 18316250014653 25000000000000000 500599229 1048576 769 1048576 (ep1174 rfl) rfl) (Enclosure.sfrac_false_div 500599229 1048576) (BSN.cos_reduce3 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220227068475283968360448) qz36) 226375608064910080 72057594037927936 Bool.false 1041834 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 500599229 1048576 226375608064910080 72057594037927936 75 220227068475283968360448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1041834 1048576 220227068475283968360448 151115727451828646838272 3129614874 2147483648 400391 400000 (ep1178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1180 := nat_lit 3436820304333161559466638774022607438450491883530544084426172071947627025408256

noncomputable def ep1181 := nat_lit 10292055008132305019928800109162668609032636635562767072796017128394595663094016

noncomputable def ep1182 := BSN.cos_dyadic_bound_f 3129614874 2147483648 3 2 1048576 400391 ep1180 ep67 ep1176 ep1181 ep69 ep1176 118711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3129614874) qz20 0 2 ep1180 ep67 ep1176 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3129614874) qz21 0 2 ep1181 ep69 ep1176 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1183 := @Enclosure.Real.IsNear.sin_image qz173 qz486 Bool.false 500599229 1048576 769 1048576 Bool.true 118711 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 53751432991528379867 112589990684262400 18316250014653 25000000000000000 500599229 1048576 769 1048576 (ep1174 rfl) rfl) (Enclosure.sfrac_false_div 500599229 1048576) (BSN.sin_reduce3 qz486 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 220227068475283968360448) qz36) 226375608064910080 72057594037927936 Bool.false 118711 1048576 75 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 500599229 1048576 226375608064910080 72057594037927936 75 220227068475283968360448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 118711 1048576 220227068475283968360448 151115727451828646838272 3129614874 2147483648 400391 400000 (ep1182 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1184 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz365 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz365 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 107122934631 549755813888 250406620023 1717986918400000 Bool.false 24412086173 1099511627776 497928480671 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz365 (Real.cos qz173) 205643 1048576 1 1048576 520917 524288 2419509 3276800000 107122934631 549755813888 250406620023 1717986918400000 qz369 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1041834 1048576 154848576 209715200000 520917 524288 2419509 3276800000 (ep1179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz365 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 205643 1048576 1 1048576 118711 1048576 2419509 3276800000 24412086173 1099511627776 497928480671 3435973836800000 qz369 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 118711 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 118711 1048576 154848576 209715200000 118711 1048576 2419509 3276800000 (ep1183 rfl rfl) rfl)) rfl)

noncomputable def ep1185 := @ep1161 107122934631 549755813888 250406620023 1717986918400000 Bool.false 24412086173 1099511627776 497928480671 3435973836800000 Bool.false 716159028321771898011648 1302685683771 1099511627776 3989507213533 687194767360000 Bool.true 272614448210280001306624 123970698137 549755813888 996807098227 171798691840000 (ep1162 (BSN.head_sum_c_succ qz141 25 26 rfl rfl) (ep1172 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1173 ep1184) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz462 qz645)

noncomputable def ep1186 := @Enclosure.Complex.IsNear.of_eq qz719 (Complex.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 68506119123 549755813888 9820185449 68719476736000 Bool.false 80626974259 549755813888 9827693449 68719476736000 (BSN.cpow_neg_s_mk qz144 146530 1000 27 qz145 rfl)

noncomputable def ep1187 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz645 146530 1000 0 1 3710780868205815 1125899906842624 1250000001 250000000000000 10874814412363961439 22517998136852480 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz646) Bool.false 62256572154556490711040 18889465931478580854784 1000000000800000 200000000000000000000 3710780868205815 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep463 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1188 := nat_lit 5233018378836350531447434356979434561

noncomputable def ep1189 := BSN.sin_dyadic_bound_f 1512474513 2147483648 2 1 1048576 400391 ep1188 ep147 ep1188 ep1188 ep148 ep1188 678954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1512474513) qz15 0 1 ep1188 ep147 ep1188 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1512474513) qz16 0 1 ep1188 ep148 ep1188 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz487 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 506398007) qz35)

noncomputable def ep1190 := @Enclosure.Real.IsNear.cos_image qz174 qz487 Bool.false 506398007 1048576 385 524288 Bool.false 678954 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 10874814412363961439 22517998136852480 18316250014653 25000000000000000 506398007 1048576 385 524288 (ep1187 rfl) rfl) (Enclosure.sfrac_false_div 506398007 1048576) (BSN.cos_reduce3 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106430932146334721900544) qz36) 226375608064910080 72057594037927936 Bool.false 678954 1048576 76 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 506398007 1048576 226375608064910080 72057594037927936 76 106430932146334721900544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 678954 1048576 106430932146334721900544 151115727451828646838272 1512474513 2147483648 400391 400000 (ep1189 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1191 := nat_lit 187001291890929826052668780577832126239787348116168809076612733535093346998401

noncomputable def ep1192 := nat_lit 27384481353239026287728464073496393136817708922149803863049647491281262721

noncomputable def ep1193 := nat_lit 560949106710083000105430884805349385933088408930662127622112101310297478469761

noncomputable def ep1194 := BSN.cos_dyadic_bound_f 1512474513 2147483648 3 2 1048576 400391 ep1191 ep67 ep1192 ep1193 ep69 ep1192 799082 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1512474513) qz20 0 2 ep1191 ep67 ep1192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1512474513) qz21 0 2 ep1193 ep69 ep1192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1195 := @Enclosure.Real.IsNear.sin_image qz174 qz487 Bool.false 506398007 1048576 385 524288 Bool.true 799082 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 10874814412363961439 22517998136852480 18316250014653 25000000000000000 506398007 1048576 385 524288 (ep1187 rfl) rfl) (Enclosure.sfrac_false_div 506398007 1048576) (BSN.sin_reduce3 qz487 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 106430932146334721900544) qz36) 226375608064910080 72057594037927936 Bool.false 799082 1048576 76 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 506398007 1048576 226375608064910080 72057594037927936 76 106430932146334721900544 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 799082 1048576 106430932146334721900544 151115727451828646838272 1512474513 2147483648 400391 400000 (ep1194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1196 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz370 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz370 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 68506119123 549755813888 9820185449 68719476736000 Bool.false 80626974259 549755813888 9827693449 68719476736000 (@Enclosure.Real.IsNear.mulLit_ff qz370 (Real.cos qz174) 201799 1048576 1 1048576 339477 524288 1211317 1638400000 68506119123 549755813888 9820185449 68719476736000 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 678954 1048576 77524288 104857600000 339477 524288 1211317 1638400000 (ep1190 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz370 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 201799 1048576 1 1048576 399541 524288 1211317 1638400000 80626974259 549755813888 9827693449 68719476736000 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 399541 524288 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 799082 1048576 77524288 104857600000 399541 524288 1211317 1638400000 (ep1195 rfl rfl) rfl)) rfl)

noncomputable def ep1197 := @ep1159 68506119123 549755813888 9820185449 68719476736000 Bool.false 80626974259 549755813888 9827693449 68719476736000 Bool.false 791482302871318189572096 1439697922017 1099511627776 4087709068023 687194767360000 Bool.true 23828464197486629617664 21671861939 274877906944 2042752663699 343597383680000 (ep1160 (BSN.head_sum_c_succ qz141 26 27 rfl rfl) (ep1185 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1186 ep1196) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz462 qz647)

noncomputable def ep1198 := @Enclosure.Complex.IsNear.of_eq qz718 (Complex.mk (@HMul.hMul Real Real Real qz0 qz375 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz375 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.true 12850276061 274877906944 120222357869 858993459200000 Bool.false 100665416859 549755813888 241626900113 1717986918400000 (BSN.cpow_neg_s_mk qz144 146530 1000 28 qz145 rfl)

noncomputable def ep1199 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz647 146530 1000 0 1 3751726938922231 1125899906842624 1250000001 250000000000000 54974054836027450843 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz648) Bool.false 62943533227317076688896 18889465931478580854784 1000000000800000 200000000000000000000 3751726938922231 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep474 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1200 := nat_lit 2316973868087800559175285204095533687112182619197886886985828941846894575190625

noncomputable def ep1201 := nat_lit 4189986424168304813906685506214838615911638591101563783892334786153250390625

noncomputable def ep1202 := nat_lit 6942541631415065067898042241274171384104724580411457533389702155968377224790625

noncomputable def ep1203 := BSN.cos_dyadic_bound_f 2836459435 2147483648 3 2 1048576 400391 ep1200 ep67 ep1201 ep1202 ep69 ep1201 259388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2836459435) qz20 0 2 ep1200 ep67 ep1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2836459435) qz21 0 2 ep1202 ep69 ep1201 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz488 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 255992891) qz25)

noncomputable def ep1204 := @Enclosure.Real.IsNear.cos_image qz175 qz488 Bool.false 255992891 524288 385 524288 Bool.true 259388 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 54974054836027450843 112589990684262400 18316250014653 25000000000000000 255992891 524288 385 524288 (ep1199 rfl) rfl) (Enclosure.sfrac_false_div 255992891 524288) (BSN.cos_reduce2 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99799044195043405463552) qz26) 226375608064910080 72057594037927936 Bool.false 259388 1048576 77 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 255992891 524288 226375608064910080 72057594037927936 77 99799044195043405463552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 259388 1048576 99799044195043405463552 75557863725914323419136 2836459435 2147483648 400391 400000 (ep1203 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1205 := nat_lit 4167200973418706362664388018966988765909199403683315145547378227495487635030625

noncomputable def ep1206 := nat_lit 10907313999981291789660405415998717981526903404308803801735879196643933781590625

noncomputable def ep1207 := BSN.sin_dyadic_bound_f 2836459435 2147483648 3 2 1048576 400391 ep1205 ep60 ep1201 ep1206 ep63 ep1201 1015986 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2836459435) qz15 0 2 ep1205 ep60 ep1201 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2836459435) qz16 0 2 ep1206 ep63 ep1201 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1208 := @Enclosure.Real.IsNear.sin_image qz175 qz488 Bool.false 255992891 524288 385 524288 Bool.true 1015986 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 54974054836027450843 112589990684262400 18316250014653 25000000000000000 255992891 524288 385 524288 (ep1199 rfl) rfl) (Enclosure.sfrac_false_div 255992891 524288) (BSN.sin_reduce2 qz488 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99799044195043405463552) qz26) 226375608064910080 72057594037927936 Bool.false 1015986 1048576 77 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 255992891 524288 226375608064910080 72057594037927936 77 99799044195043405463552 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1015986 1048576 99799044195043405463552 75557863725914323419136 2836459435 2147483648 400391 400000 (ep1207 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1209 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz375 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz375 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.true 12850276061 274877906944 120222357869 858993459200000 Bool.false 100665416859 549755813888 241626900113 1717986918400000 (@Enclosure.Real.IsNear.mulLit_ft qz375 (Real.cos qz175) 198163 1048576 1 1048576 64847 262144 1211317 1638400000 12850276061 274877906944 120222357869 858993459200000 qz379 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.true 259388 1048576 77524288 104857600000 64847 262144 1211317 1638400000 (ep1204 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz375 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 198163 1048576 1 1048576 507993 524288 1211317 1638400000 100665416859 549755813888 241626900113 1717986918400000 qz379 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 507993 524288 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 1015986 1048576 77524288 104857600000 507993 524288 1211317 1638400000 (ep1208 rfl rfl) rfl)) rfl)

noncomputable def ep1210 := @ep1157 12850276061 274877906944 120222357869 858993459200000 Bool.false 100665416859 549755813888 241626900113 1717986918400000 Bool.false 381612123486458019315712 1388296817773 1099511627776 20919434771591 3435973836800000 Bool.false 15756466989103855960064 57321692981 549755813888 653461888663 107374182400000 (ep1158 (BSN.head_sum_c_succ qz141 27 28 rfl rfl) (ep1197 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1198 ep1209) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz462 qz649)

noncomputable def ep1211 := @Enclosure.Complex.IsNear.of_eq qz717 (Complex.mk (@HMul.hMul Real Real Real qz0 qz380 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz380 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 6277806315 34359738368 118585303611 858993459200000 Bool.false 9117529875 274877906944 7370350421 53687091200000 (BSN.cpow_neg_s_mk qz144 146530 1000 29 qz145 rfl)

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz649 146530 1000 0 1 3791236343078135 1125899906842624 1250000001 250000000000000 11110597227024782431 22517998136852480 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz650) Bool.false 63606391034871975772160 18889465931478580854784 1000000000800000 200000000000000000000 3791236343078135 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep489 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1213 := nat_lit 22121739100106367237280624215900625

noncomputable def ep1214 := BSN.cos_dyadic_bound_f 385660195 2147483648 2 1 1048576 400391 ep1213 ep80 ep1213 ep1213 ep81 ep1213 1031712 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 385660195) qz20 0 1 ep1213 ep80 ep1213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 385660195) qz21 0 1 ep1213 ep81 ep1213 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz489 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 129344375) qz17)

noncomputable def ep1215 := @Enclosure.Real.IsNear.cos_image qz176 qz489 Bool.false 129344375 262144 769 1048576 Bool.true 1031712 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 11110597227024782431 22517998136852480 18316250014653 25000000000000000 129344375 262144 769 1048576 (ep1212 rfl) rfl) (Enclosure.sfrac_false_div 129344375 262144) (BSN.cos_reduce2 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6784605900744918302720) qz19) 226375608064910080 72057594037927936 Bool.false 1031712 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 129344375 262144 226375608064910080 72057594037927936 78 6784605900744918302720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1031712 1048576 6784605900744918302720 37778931862957161709568 385660195 2147483648 400391 400000 (ep1214 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1216 := BSN.sin_dyadic_bound_f 385660195 2147483648 2 1 1048576 400391 ep1213 ep147 ep1213 ep1213 ep148 ep1213 187300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 385660195) qz15 0 1 ep1213 ep147 ep1213 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 385660195) qz16 0 1 ep1213 ep148 ep1213 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1217 := @Enclosure.Real.IsNear.sin_image qz176 qz489 Bool.false 129344375 262144 769 1048576 Bool.true 187300 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 11110597227024782431 22517998136852480 18316250014653 25000000000000000 129344375 262144 769 1048576 (ep1212 rfl) rfl) (Enclosure.sfrac_false_div 129344375 262144) (BSN.sin_reduce2 qz489 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6784605900744918302720) qz19) 226375608064910080 72057594037927936 Bool.false 187300 1048576 78 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 129344375 262144 226375608064910080 72057594037927936 78 6784605900744918302720 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 187300 1048576 6784605900744918302720 37778931862957161709568 385660195 2147483648 400391 400000 (ep1216 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1218 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz380 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz380 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 6277806315 34359738368 118585303611 858993459200000 Bool.false 9117529875 274877906944 7370350421 53687091200000 (@Enclosure.Real.IsNear.mulLit_ft qz380 (Real.cos qz176) 194715 1048576 1 1048576 32241 32768 2419509 3276800000 6277806315 34359738368 118585303611 858993459200000 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 1031712 1048576 154848576 209715200000 32241 32768 2419509 3276800000 (ep1215 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz380 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 194715 1048576 1 1048576 46825 262144 2419509 3276800000 9117529875 274877906944 7370350421 53687091200000 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 46825 262144 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 187300 1048576 154848576 209715200000 46825 262144 2419509 3276800000 (ep1217 rfl rfl) rfl)) rfl)

noncomputable def ep1219 := @ep1155 6277806315 34359738368 118585303611 858993459200000 Bool.false 9117529875 274877906944 7370350421 53687091200000 Bool.false 40798994395539150209024 1187407015693 1099511627776 4278755197207 687194767360000 Bool.false 20768882046182635864064 75556752731 549755813888 133640517901 21474836480000 (ep1156 (BSN.head_sum_c_succ qz141 28 29 rfl rfl) (ep1210 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1211 ep1218) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz462 qz651)

noncomputable def ep1220 := @Enclosure.Complex.IsNear.of_eq qz716 (Complex.mk (@HMul.hMul Real Real Real qz0 qz385 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz385 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 21137030187 274877906944 58072574187 429496729600000 Bool.true 182068993505 1099511627776 466172465371 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 30 qz145 rfl)

noncomputable def ep1221 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz651 146530 1000 0 1 3829405717437687 1125899906842624 1250000001 250000000000000 56112281977614427611 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz652) Bool.false 64246766873087041339392 18889465931478580854784 1000000000800000 200000000000000000000 3829405717437687 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep504 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1222 := nat_lit 759717373309820352356406630002770176

noncomputable def ep1223 := BSN.sin_dyadic_bound_f 933604668 2147483648 2 1 1048576 400391 ep1222 ep147 ep1222 ep1222 ep148 ep1222 441636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 933604668) qz15 0 1 ep1222 ep147 ep1222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 933604668) qz16 0 1 ep1222 ep148 ep1222 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz490 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 522586349) qz35)

noncomputable def ep1224 := @Enclosure.Real.IsNear.cos_image qz177 qz490 Bool.false 522586349 1048576 769 1048576 Bool.true 441636 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 56112281977614427611 112589990684262400 18316250014653 25000000000000000 522586349 1048576 769 1048576 (ep1221 rfl) rfl) (Enclosure.sfrac_false_div 522586349 1048576) (BSN.cos_reduce1 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65696588089900000083968) qz36) 226375608064910080 72057594037927936 Bool.false 441636 1048576 79 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 522586349 1048576 226375608064910080 72057594037927936 79 65696588089900000083968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441636 1048576 65696588089900000083968 151115727451828646838272 933604668 2147483648 400391 400000 (ep1223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1225 := BSN.cos_dyadic_bound_f 933604668 2147483648 2 1 1048576 400391 ep1222 ep80 ep1222 ep1222 ep81 ep1222 951035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 933604668) qz20 0 1 ep1222 ep80 ep1222 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 933604668) qz21 0 1 ep1222 ep81 ep1222 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1226 := @Enclosure.Real.IsNear.sin_image qz177 qz490 Bool.false 522586349 1048576 769 1048576 Bool.false 951035 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 56112281977614427611 112589990684262400 18316250014653 25000000000000000 522586349 1048576 769 1048576 (ep1221 rfl) rfl) (Enclosure.sfrac_false_div 522586349 1048576) (BSN.sin_reduce1 qz490 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65696588089900000083968) qz36) 226375608064910080 72057594037927936 Bool.false 951035 1048576 79 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q1 522586349 1048576 226375608064910080 72057594037927936 79 65696588089900000083968 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 951035 1048576 65696588089900000083968 151115727451828646838272 933604668 2147483648 400391 400000 (ep1225 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1227 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz385 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz385 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 21137030187 274877906944 58072574187 429496729600000 Bool.true 182068993505 1099511627776 466172465371 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz385 (Real.cos qz177) 191443 1048576 1 1048576 110409 262144 2419509 3276800000 21137030187 274877906944 58072574187 429496729600000 qz389 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 441636 1048576 154848576 209715200000 110409 262144 2419509 3276800000 (ep1224 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz385 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 191443 1048576 1 1048576 951035 1048576 2419509 3276800000 182068993505 1099511627776 466172465371 3435973836800000 qz389 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 951035 1048576 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 951035 1048576 154848576 209715200000 951035 1048576 2419509 3276800000 (ep1226 rfl rfl) rfl)) rfl)

noncomputable def ep1228 := @ep1153 21137030187 274877906944 58072574187 429496729600000 Bool.true 182068993505 1099511627776 466172465371 3435973836800000 Bool.false 303151544697054381998080 1102858894945 1099511627776 21858356579531 3435973836800000 Bool.true 17017959523379717341184 30955488043 1099511627776 21848655329531 3435973836800000 (ep1154 (BSN.head_sum_c_succ qz141 29 30 rfl rfl) (ep1219 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1220 ep1227) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz462 qz653)

noncomputable def ep1229 := @Enclosure.Complex.IsNear.of_eq qz715 (Complex.mk (@HMul.hMul Real Real Real qz0 qz390 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz390 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 85329798281 549755813888 22924896811 171798691840000 Bool.true 49680248555 549755813888 5716435609 42949672960000 (BSN.cpow_neg_s_mk qz144 146530 1000 31 qz145 rfl)

noncomputable def ep1230 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz653 146530 1000 0 1 3866325256314103 1125899906842624 1250000001 250000000000000 56653263980770551259 112589990684262400 18316250014653 25000000000000000 qz146 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 1250000001 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz654) Bool.false 64866173951437069877248 18889465931478580854784 1000000000800000 200000000000000000000 3866325256314103 1125899906842624 1250000001 250000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep519 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1231 := nat_lit 1643429811648113181499110220161125136

noncomputable def ep1232 := BSN.cos_dyadic_bound_f 1132238166 2147483648 2 1 1048576 400391 ep1231 ep80 ep1231 ep1231 ep81 ep1231 906178 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1132238166) qz20 0 1 ep1231 ep80 ep1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1132238166) qz21 0 1 ep1231 ep81 ep1231 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz491 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 131906159) qz17)

noncomputable def ep1233 := @Enclosure.Real.IsNear.cos_image qz178 qz491 Bool.false 131906159 262144 769 1048576 Bool.false 906178 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 56653263980770551259 112589990684262400 18316250014653 25000000000000000 131906159 262144 769 1048576 (ep1230 rfl) rfl) (Enclosure.sfrac_false_div 131906159 262144) (BSN.cos_reduce0 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19918544467056549429248) qz19) 226375608064910080 72057594037927936 Bool.false 906178 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 131906159 262144 226375608064910080 72057594037927936 80 19918544467056549429248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 906178 1048576 19918544467056549429248 37778931862957161709568 1132238166 2147483648 400391 400000 (ep1232 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1234 := BSN.sin_dyadic_bound_f 1132238166 2147483648 2 1 1048576 400391 ep1231 ep147 ep1231 ep1231 ep148 ep1231 527590 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1132238166) qz15 0 1 ep1231 ep147 ep1231 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1132238166) qz16 0 1 ep1231 ep148 ep1231 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1235 := @Enclosure.Real.IsNear.sin_image qz178 qz491 Bool.false 131906159 262144 769 1048576 Bool.false 527590 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 56653263980770551259 112589990684262400 18316250014653 25000000000000000 131906159 262144 769 1048576 (ep1230 rfl) rfl) (Enclosure.sfrac_false_div 131906159 262144) (BSN.sin_reduce0 qz491 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19918544467056549429248) qz19) 226375608064910080 72057594037927936 Bool.false 527590 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 131906159 262144 226375608064910080 72057594037927936 80 19918544467056549429248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 527590 1048576 19918544467056549429248 37778931862957161709568 1132238166 2147483648 400391 400000 (ep1234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1236 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz390 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz390 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 85329798281 549755813888 22924896811 171798691840000 Bool.true 49680248555 549755813888 5716435609 42949672960000 (@Enclosure.Real.IsNear.mulLit_ff qz390 (Real.cos qz178) 188329 1048576 1 1048576 453089 524288 2419509 3276800000 85329798281 549755813888 22924896811 171798691840000 qz394 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 906178 1048576 154848576 209715200000 453089 524288 2419509 3276800000 (ep1233 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz390 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 188329 1048576 1 1048576 263795 524288 2419509 3276800000 49680248555 549755813888 5716435609 42949672960000 qz394 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 263795 524288 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 527590 1048576 154848576 209715200000 263795 524288 2419509 3276800000 (ep1235 rfl rfl) rfl)) rfl)

noncomputable def ep1237 := @ep1151 85329798281 549755813888 22924896811 171798691840000 Bool.true 49680248555 549755813888 5716435609 42949672960000 Bool.false 700124194799848800649216 1273518491507 1099511627776 22316854515751 3435973836800000 Bool.true 71641970480404039204864 130315985153 1099511627776 22305970178251 3435973836800000 (ep1152 (BSN.head_sum_c_succ qz141 30 31 rfl rfl) (ep1228 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1229 ep1236) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz462 qz655)

noncomputable def ep1238 := @Enclosure.Complex.IsNear.of_eq qz714 (Complex.mk (@HMul.hMul Real Real Real qz0 qz395 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz395 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 43758828773 549755813888 225272286263 1717986918400000 Bool.false 173548889195 1099511627776 451994956901 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 32 qz145 rfl)

noncomputable def ep1239 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz655 146530 1000 0 1 15608286920413395 4503599627370496 1000000001 200000000000000 45741645648963495387 90071992547409920 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz656) Bool.false 65465900263437584302080 18889465931478580854784 1000000001000000 200000000000000000000 15608286920413395 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep534 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1240 := nat_lit 1012133343245449818318708148559097921

noncomputable def ep1241 := BSN.sin_dyadic_bound_f 1003019631 2147483648 2 1 1048576 400391 ep1240 ep147 ep1240 ep1240 ep148 ep1240 472142 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1003019631) qz15 0 1 ep1240 ep147 ep1240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1003019631) qz16 0 1 ep1240 ep148 ep1240 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz492 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 532502839) qz35)

noncomputable def ep1242 := @Enclosure.Real.IsNear.cos_image qz179 qz492 Bool.false 532502839 1048576 385 524288 Bool.false 472142 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 45741645648963495387 90071992547409920 14653000014653 20000000000000000 532502839 1048576 385 524288 (ep1239 rfl) rfl) (Enclosure.sfrac_false_div 532502839 1048576) (BSN.cos_reduce3 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70581231878617083936768) qz36) 226375608064910080 72057594037927936 Bool.false 472142 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 532502839 1048576 226375608064910080 72057594037927936 80 70581231878617083936768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 472142 1048576 70581231878617083936768 151115727451828646838272 1003019631 2147483648 400391 400000 (ep1241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1243 := BSN.cos_dyadic_bound_f 1003019631 2147483648 2 1 1048576 400391 ep1240 ep80 ep1240 ep1240 ep81 ep1240 936265 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1003019631) qz20 0 1 ep1240 ep80 ep1240 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1003019631) qz21 0 1 ep1240 ep81 ep1240 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1244 := @Enclosure.Real.IsNear.sin_image qz179 qz492 Bool.false 532502839 1048576 385 524288 Bool.true 936265 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 45741645648963495387 90071992547409920 14653000014653 20000000000000000 532502839 1048576 385 524288 (ep1239 rfl) rfl) (Enclosure.sfrac_false_div 532502839 1048576) (BSN.sin_reduce3 qz492 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70581231878617083936768) qz36) 226375608064910080 72057594037927936 Bool.false 936265 1048576 80 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 532502839 1048576 226375608064910080 72057594037927936 80 70581231878617083936768 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 936265 1048576 70581231878617083936768 151115727451828646838272 1003019631 2147483648 400391 400000 (ep1243 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1245 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz395 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz395 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 43758828773 549755813888 225272286263 1717986918400000 Bool.false 173548889195 1099511627776 451994956901 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz395 (Real.cos qz179) 185363 1048576 1 1048576 236071 524288 1211317 1638400000 43758828773 549755813888 225272286263 1717986918400000 qz399 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 472142 1048576 77524288 104857600000 236071 524288 1211317 1638400000 (ep1242 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz395 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 185363 1048576 1 1048576 936265 1048576 1211317 1638400000 173548889195 1099511627776 451994956901 3435973836800000 qz399 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 936265 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 936265 1048576 77524288 104857600000 936265 1048576 1211317 1638400000 (ep1244 rfl rfl) rfl)) rfl)

noncomputable def ep1246 := @ep1149 43758828773 549755813888 225272286263 1717986918400000 Bool.false 173548889195 1099511627776 451994956901 3435973836800000 Bool.false 748237535853621295448064 1361036149053 1099511627776 22767399088277 3435973836800000 Bool.false 47535080696703029870592 21616452021 549755813888 1422372820947 214748364800000 (ep1150 (BSN.head_sum_c_succ qz141 31 32 rfl rfl) (ep1237 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1238 ep1245) rfl rfl

theorem EMRow51.d16 : Enclosure.Complex.IsNear qz171 Bool.false 1361036149053 1099511627776 22767399088277 3435973836800000 Bool.false 21616452021 549755813888 1422372820947 214748364800000 := ep1148 (BSN.head_sum_c_succ qz141 32 33 rfl rfl) (ep1246 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1247 := nat_lit 813379634825211858382809089863

noncomputable def ep1248 := nat_lit 732739505104267325983047024640

noncomputable def ep1249 := nat_lit 273352804415949988500445003839632063

noncomputable def ep1250 := nat_lit 35778296147669303026515968000000000000

noncomputable abbrev qz722 := (@HAdd.hAdd Complex Complex Complex qz739 (@HAdd.hAdd Complex Complex Complex qz739 qz742 (@HMul.hMul Complex Complex Complex qz741 Complex.I (@HDiv.hDiv Complex Complex Complex qz743 (↑qz746) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz493 := qz722

noncomputable abbrev qz180 := (Complex.Stirling.logGammaStirling 1 qz493)

noncomputable abbrev qz723 := (@HAdd.hAdd Complex Complex Complex qz739 qz742 (@HMul.hMul Complex Complex Complex qz741 Complex.I (@HDiv.hDiv Complex Complex Complex qz743 (↑qz746) (2 : Complex))))

noncomputable abbrev qz494 := qz723

noncomputable abbrev qz181 := qz494

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz462 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1251 := Complex.re (@HMul.hMul Complex Complex Complex qz72 (Complex.exp (@HMul.hMul Complex Complex Complex qz72 Complex.I ↑(@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182))) (zetaApproximant qz141 1 37))

noncomputable def ep1252 := @Enclosure.Real.IsNear.of_eq ep1251 (@HSub.hSub Real Real Real qz404 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz141 1 37))))

noncomputable def ep1253 := nat_lit 162675822980111298971211923055

noncomputable def ep1254 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz141 1 37))) ep1253

noncomputable def ep1255 := nat_lit 146547901020853465196609404928

noncomputable def ep1256 := nat_lit 273152247057291637832979578010408219

noncomputable def ep1257 := nat_lit 183184876276066831495761756160

noncomputable def ep1258 := nat_lit 50139339664587666866356457305961

noncomputable def ep1259 := nat_lit 8944574036917325756628992000000000000

noncomputable def ep1260 := nat_lit 29799769554185770908192087298263185572078257219498426761216

noncomputable def ep1261 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.re (zetaApproximant qz141 1 37)) 1048575 1048576 79149

noncomputable def ep1262 := nat_lit 78645000580007379513279441

noncomputable def ep1263 := nat_lit 10918669478658844917760000000

noncomputable def ep1264 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) Bool.false 1048575 1048576 5065536

noncomputable abbrev qz724 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82355059) qz25)

noncomputable def ep1265 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) qz724 Bool.false 82355059 524288 25

noncomputable def ep1266 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) Bool.false 70742457305542380089 450359962737049600 239352627931818027929 629145600000000000000000

noncomputable def ep1267 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182 108513523716687612473 450359962737049600 63516627931818027929 629145600000000000000000 1099282713 13107200

noncomputable def ep1268 := nat_lit 927235536395205084302540800

noncomputable def ep1269 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 25949511650167800331 225179981368524800 19897502455018851407 104857600000000000000000 Bool.false 108513523716687612473 450359962737049600

noncomputable def ep1270 := @Enclosure.Complex.IsNear.subLitP qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 24015594719237168931 225179981368524800 19635358453760560207 104857600000000000000000 Bool.false 109919151690295706873 450359962737049600 60370899931188882329

noncomputable def ep1271 := nat_lit 29216552749535512581610661472108544

noncomputable def ep1272 := nat_lit 30543841560945863230741327577612288

noncomputable abbrev qz495 := (@HSub.hSub Complex Complex Complex qz658 qz722 qz661)

noncomputable abbrev qz496 := (Complex.log qz722)

noncomputable abbrev qz183 := (@HSub.hSub Complex Complex Complex qz401 (@HMul.hMul Complex Complex Complex qz400 qz495 qz496) qz493)

noncomputable abbrev qz184 := qz493

noncomputable def ep1273 := @Enclosure.Complex.IsNear.of_eq qz180 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz183 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k)))))) Bool.true 24015594719237168931

noncomputable def ep1274 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz183 qz78) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) Bool.true 24015602577536048931 225179981368524800

noncomputable def ep1275 := nat_lit 3300678205219646164040712978432

noncomputable def ep1276 := nat_lit 30214346349688523621679195226112

noncomputable def ep1277 := @ep1274 37451469735989 200000000000000000 Bool.false 109919663457644545273 450359962737049600 19191250088093 200000000000000000 Bool.false 4796325 137438953472 3 137438953472 Bool.true 312358001 274877906944 14653 20615843020800 Bool.true ep1275 24015594719237168931 225179981368524800 19635358453760560207 104857600000000000000000 Bool.false ep1276

noncomputable def ep1278 := @Enclosure.Complex.IsNear.addLitP qz183 qz78 Bool.true 24222528947896573731 225179981368524800 74140000018853 400000000000000000

noncomputable def ep1279 := nat_lit 3147773061042805005484032

noncomputable def ep1280 := @ep1278 Bool.false 109919663457644545273 450359962737049600 19191250088093 200000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1279 24015602577536048931 225179981368524800 37451469735989 200000000000000000 Bool.false 109919663457644545273 109919663457644545273 450359962737049600

noncomputable abbrev qz185 := (@HMul.hMul Complex Complex Complex qz400 qz495 qz496)

noncomputable def ep1281 := @Enclosure.Complex.IsNear.subLitP qz185 qz184 Bool.true 23715873989817392931 225179981368524800 74140000018853 400000000000000000 Bool.false 142915286127574484217

noncomputable def ep1282 := @ep1281 450359962737049600 19191250088093 200000000000000000 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 Bool.true 96890115791586294924000 24222528947896573731 225179981368524800 74140000018853 400000000000000000 Bool.false 439678653830578181092000 109919663457644545273 450359962737049600 19191250088093 200000000000000000

noncomputable abbrev qz186 := qz495

noncomputable abbrev qz187 := qz496

noncomputable def ep1283 := @Enclosure.Complex.IsNear.mul qz186 qz187 Bool.true 23715873989817392931 225179981368524800 74140000018853 400000000000000000 Bool.false 142915286127574484217 450359962737049600 19191250088093

noncomputable abbrev qz188 := (Complex.re qz495)

noncomputable abbrev qz189 := (Complex.re qz496)

noncomputable abbrev qz190 := (Complex.im qz495)

noncomputable abbrev qz191 := (Complex.im qz496)

noncomputable def ep1284 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz188 qz189) (@HMul.hMul Real Real Real qz0 qz190 qz191) 67693334780665923 9007199254740992 4375000021 2000000000000000 12704103679667020503 112589990684262400

noncomputable def ep1285 := nat_lit 106806801263307249051895421548363776

noncomputable def ep1286 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz189 7000 4000 0 1 9670476397237989 2251799813685248 625000003 500000000000000

noncomputable def ep1287 := @Enclosure.Complex.IsNear.re_isNear qz186 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable abbrev qz725 := (Enclosure.sfrac Bool.false 293060 4000)

noncomputable abbrev qz497 := qz725

noncomputable def ep1288 := @Enclosure.Complex.IsNear.of_eq qz186 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz497) Bool.false 7000 4000 0 1 Bool.false 293060 4000 0

noncomputable abbrev qz498 := (Complex.log (Complex.mk qz665 qz725))

noncomputable def ep1289 := @Enclosure.Complex.IsNear.of_eq qz187 qz498 Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000

noncomputable def ep1290 := nat_lit 1269653194440197434919221656422111334666844934826288353280000000000000

noncomputable def ep1291 := nat_lit 7780480299006913012299851812511533026174033932029587456000000000000

noncomputable def ep1292 := nat_lit 1090422431871862388851262689736955396133030750679040000000000000

noncomputable def ep1293 := BSN.log_dyadic_bound 20429163600 151501163600 4 3 ep1290 1048576 400000 ep1291 ep1292 284523 171930327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20429163600) (BSN.artanhQ 151501163600) 0 3 ep1291 ep1290 ep1292 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz726 := (Real.log (Enclosure.sfrac Bool.false 85965163600 16000000))

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_ff qz92 qz726 1 2 0 1 9670476397237989 1125899906842624 625000003 250000000000000 9670476397237989 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 85965163600 16000000 9670476397237989 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85965163600) qz667)) Bool.false 324487342678727089717248 37778931862957161709568 1000000004800000 400000000000000000000 9670476397237989 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 85965163600 16000000 12 171930327200 131072000000 284523 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep1293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1295 := BSN.arctan_dyadic_bound_f 9000 293060 1 0 1048576 400000 0 1 1 0 1 1 32192 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz499 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 293060)))

noncomputable def ep1296 := @Enclosure.Real.IsNear.subLit_ff_p qz93 qz499 884279719003555 562949953421312 1 2000000000000000 32192 1048576 1 400000 909112005733332811776 866996770604451 562949953421312 5000000001 2000000000000000 qz94 (ep1295 rfl) rfl rfl

noncomputable abbrev qz500 := (Complex.mk qz665 qz725)

noncomputable abbrev qz501 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293060) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1297 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (ep1289 (@congrArg Complex Complex qz184 qz500 Complex.log (BSN.w_shift_mk qz144 Bool.false 146530 1000 2 qz145 rfl)) (@Enclosure.Complex.IsNear.of_parts qz498 Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz498) (@HMul.hMul Real Real Real qz0 qz92 qz726) Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 9000 293060 4000 85965163600 16000000 rfl rfl rfl) (ep1294 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz498) qz501 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 9000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz501 (@HSub.hSub Real Real Real qz404 qz93 qz499) Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 293060 9000 rfl rfl) ep1296))))

noncomputable def ep1298 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz191 293060 4000 0 1 866996770604451 562949953421312 5000000001 2000000000000000

noncomputable def ep1299 := @Enclosure.Complex.IsNear.im_isNear qz186 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable def ep1300 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (ep1289 (@congrArg Complex Complex qz184 qz500 Complex.log (BSN.w_shift_mk qz144 Bool.false 146530 1000 2 qz145 rfl)) (@Enclosure.Complex.IsNear.of_parts qz498 Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz498) (@HMul.hMul Real Real Real qz0 qz92 qz726) Bool.false 9670476397237989 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 9000 293060 4000 85965163600 16000000 rfl rfl rfl) (ep1294 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz498) qz501 Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 9000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz501 (@HSub.hSub Real Real Real qz404 qz93 qz499) Bool.false 866996770604451 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 293060 9000 rfl rfl) ep1296))))

noncomputable abbrev qz192 := (@ep1288 1 (BSN.w_sub_half_mk qz462 Bool.false 146530 1000 2 qz463 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz497 Bool.false 7000 4000 0 1 Bool.false 293060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 293060 4000)))

noncomputable def ep1301 := @ep1284 73265000014653 400000000000000000 ep1285 23715873989817392931 225179981368524800 74140000018853 400000000000000000 (@ep1286 67693334780665923 9007199254740992 4375000021 2000000000000000 (ep1287 qz192) ep1297 rfl) (@ep1298 12704103679667020503 112589990684262400 73265000014653 400000000000000000 (ep1299 qz192) ep1300 rfl) rfl

noncomputable def ep1302 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz188 qz191) (@HMul.hMul Real Real Real qz0 qz190 qz189) 6068977394231157 2251799813685248 35000000007 8000000000000000 141701490648728252817 450359962737049600

noncomputable def ep1303 := nat_lit 321816614674846131691760211581730816

noncomputable def ep1304 := @Enclosure.Real.IsNear.mulLit_ff qz188 qz191 7000 4000 0 1 866996770604451 562949953421312 5000000001 2000000000000000

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_ff qz190 qz189 293060 4000 0 1 9670476397237989 2251799813685248 625000003 500000000000000

noncomputable def ep1306 := @ep1302 9158125043959 100000000000000000 ep1303 142915286127574484217 450359962737049600 19191250088093 200000000000000000 (@ep1304 6068977394231157 2251799813685248 35000000007 8000000000000000 (ep1287 qz192) ep1300 rfl) (@ep1305 141701490648728252817 450359962737049600 9158125043959 100000000000000000 (ep1299 qz192) ep1297 rfl) rfl

noncomputable def ep1307 := @Enclosure.Complex.IsNear.of_eq qz184 qz500 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 (BSN.w_shift_mk qz144 Bool.false 146530 1000 2 qz145 rfl)

noncomputable abbrev qz502 := (ep1307 (@Enclosure.Complex.IsNear.mk qz665 qz725 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 293060 4000)))

noncomputable abbrev qz193 := qz502

noncomputable def ep1308 := ep1282 (@ep1283 200000000000000000 (ep1301 rfl) (ep1306 rfl)) qz193 rfl rfl rfl rfl rfl rfl

noncomputable def ep1309 := @ep1280 19191250088093 200000000000000000 (ep1308 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz97 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep609 131072 1 524288 (ep611 rfl) (ep613 rfl) rfl rfl) (@ep614 1 0 1 (ep616 rfl) (ep618 rfl) rfl rfl))

noncomputable abbrev qz503 := (@HPow.hPow Complex Int Complex qz663 qz722 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz194 := qz503

noncomputable def ep1310 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz194)) Bool.false 4796325 137438953472 3 137438953472

noncomputable def ep1311 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz194) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1312 := @ep1311 0 1 0 1 Bool.false 4796325 137438953472 3 137438953472 Bool.true 312358001 274877906944 14653 20615843020800 Bool.false 4796325 4796325 137438953472 3 137438953472 Bool.true 312358001 312358001 274877906944 14653

noncomputable def ep1313 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz73 (@HMul.hMul Complex Complex Complex qz72 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz81 qz184 (@HSub.hSub Int Int Int qz411 qz83 (@HMul.hMul Int Int Int qz412 qz84 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1314 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100) qz194 Bool.false 4796325 137438953472 3 137438953472 Bool.true 312358001 274877906944 14653 20615843020800

noncomputable abbrev qz195 := (Complex.re qz503)

noncomputable abbrev qz196 := (Complex.im qz503)

noncomputable def ep1315 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz195) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz196) 4796325 137438953472 3 137438953472 0 1 0

noncomputable def ep1316 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz195 1 12 0 1 14388975 34359738368 9 34359738368 4796325

noncomputable def ep1317 := @Enclosure.Complex.IsNear.re_isNear qz194 Bool.false 14388975 34359738368 9 34359738368 Bool.true 937074003 68719476736 14653 1717986918400

noncomputable abbrev qz504 := (@HPow.hPow Complex Nat Complex qz668 qz722 1)

noncomputable abbrev qz197 := (@Inv.inv Complex Complex.instInv qz504)

noncomputable def ep1318 := @Enclosure.Complex.IsNear.of_eq qz194 qz197 Bool.false 14388975 34359738368 9 34359738368 Bool.true 937074003 68719476736 14653

noncomputable def ep1319 := @Enclosure.Complex.IsNear.of_parts qz197 Bool.false 14388975 34359738368 9 34359738368 Bool.true 937074003 68719476736 14653

noncomputable abbrev qz198 := (Complex.re qz504)

noncomputable abbrev qz199 := qz504

noncomputable def ep1320 := @Enclosure.Real.IsNear.mulLit_ff qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199)) 9000 4000 0 1 1598775 8589934592 1 8589934592

noncomputable def ep1321 := @Enclosure.Complex.IsNear.re_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable def ep1322 := @Enclosure.Complex.IsNear.of_eq qz199 qz184 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0

noncomputable def ep1323 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199)) Bool.false 1598775 8589934592 1 8589934592 1598775 8589934592 1

noncomputable abbrev qz200 := (Complex.im qz504)

noncomputable def ep1324 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200)) Bool.false 214912909 40000 0 1

noncomputable def ep1325 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz198 qz198) (@HMul.hMul Real Real Real qz0 qz200 qz200) 81 16 0 1 214710409 40000

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ff qz198 qz198 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1327 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 293060 4000 0 1 293060 4000 0 1

noncomputable def ep1328 := @Enclosure.Complex.IsNear.im_isNear qz199 Bool.false 9000 4000 0 1 Bool.false 293060 4000 0 1

noncomputable abbrev qz201 := (ep1321 (@ep1322 1 (BSN.pow_one_c qz493) qz502))

noncomputable abbrev qz202 := (ep1328 (@ep1322 1 (BSN.pow_one_c qz493) qz502))

noncomputable def ep1329 := @ep1325 0 1 3438606544 214912909 40000 0 1 (@ep1326 81 16 0 1 qz201 qz201 rfl) (@ep1327 214710409 40000 0 1 qz202 qz202 rfl)

noncomputable def ep1330 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199) 214912909 40000 0 1 799387 799388 4294967296 (ep1324 (Enclosure.Complex.normSq_eq_mul_add_mul qz199) (ep1329 rfl rfl)) rfl

noncomputable def ep1331 := @Enclosure.Real.IsNear.of_eq (Complex.re qz197) (@HMul.hMul Real Real Real qz0 qz198 (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199))) Bool.false 14388975 34359738368 9 34359738368 (Enclosure.Complex.inv_re_eq_mul qz199) (@ep1320 14388975 34359738368 9 34359738368 qz201 (@ep1323 8589934592 (ep1330 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1332 := @Enclosure.Real.IsNear.of_eq (Complex.im qz197) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199))) Bool.true 937074003 68719476736 14653 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz199)

noncomputable def ep1333 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz200) (@Inv.inv Real Real.instInv (@DFunLike.coe qz106 Complex (fun (x : Complex) => Real) qz107 Complex.normSq qz199)) 293060 4000 0 1 1598775 8589934592 1

noncomputable def ep1334 := @ep1333 8589934592 937074003 68719476736 14653 1717986918400 (@Enclosure.Real.IsNear.neg qz200 Bool.false 293060 4000 0 1 qz202) (@ep1323 8589934592 (ep1330 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1335 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz196 0 1 0 1 937074003 68719476736 14653 1717986918400 0

noncomputable def ep1336 := @Enclosure.Complex.IsNear.im_isNear qz194 Bool.false 14388975 34359738368 9 34359738368 Bool.true 937074003 68719476736 14653 1717986918400

noncomputable abbrev qz203 := (@ep1318 1717986918400 (BSN.zpow_one_sub_two_mul qz493 1 1 rfl rfl) (@ep1319 1717986918400 ep1331 (ep1332 ep1334)))

noncomputable def ep1337 := @ep1315 1 4796325 4796325 137438953472 3 137438953472 (@ep1316 137438953472 3 137438953472 ep628 (ep1317 qz203) rfl) (@ep1335 1 0 1 ep648 (ep1336 qz203) rfl) rfl

noncomputable def ep1338 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz196) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz195) 312358001 274877906944 14653 20615843020800 0 1 0

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz196 1 12 0 1 937074003 68719476736 14653 1717986918400 312358001

noncomputable def ep1340 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 (@Rat.cast Complex Complex.instRatCast (bernoulli qz99)) qz100)) qz195 0 1 0 1 14388975 34359738368 9 34359738368 0

noncomputable def ep1341 := @ep1338 1 312358001 312358001 274877906944 14653 20615843020800 (@ep1339 274877906944 14653 20615843020800 ep628 (ep1336 qz203) rfl) (@ep1340 1 0 1 ep648 (ep1317 qz203) rfl) rfl

noncomputable def ep1342 := @ep1312 20615843020800 (@ep1313 0 1 0 1 (BSN.stirling_sum_base qz184) qz113) (ep1314 (ep1337 rfl) (ep1341 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1343 := @ep1277 109919151690295706873 450359962737049600 60370899931188882329 629145600000000000000000 (ep1309 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1310 Bool.true 312358001 274877906944 14653 20615843020800 (BSN.stirling_sum_succ qz184 0 1 rfl) (ep1342 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1344 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz144 2) Bool.false 9669584654653157 1125899906842624 625000003 250000000000000 Bool.false 878517483505059 281474976710656

noncomputable abbrev qz204 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz494 qz420))

noncomputable def ep1345 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz144 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz144 1) qz204) Bool.false 9669584654653157 1125899906842624 625000003 250000000000000 Bool.false 878517483505059 281474976710656 5000000001 1000000000000000

noncomputable def ep1346 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz144 1) qz204 Bool.false 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 562949953421312 5000000001 2000000000000000 Bool.false

noncomputable def ep1347 := nat_lit 43547937847523424115782815055872

noncomputable def ep1348 := nat_lit 989122752837962394645420834816

noncomputable abbrev qz205 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz494 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1349 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz144 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz144 0) qz205) Bool.false 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 562949953421312 5000000001 2000000000000000

noncomputable def ep1350 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz144 0) qz205 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz505 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz725))

noncomputable def ep1351 := @Enclosure.Complex.IsNear.of_eq qz205 qz505 Bool.false 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 562949953421312 5000000001 2000000000000000

noncomputable def ep1352 := nat_lit 1265635868377839008238392995333859302133032558561584353280000000000000

noncomputable def ep1353 := nat_lit 7702793682663886153601240019714668133129091596848787456000000000000

noncomputable def ep1354 := nat_lit 1065051575828602550327721796097828810855050078679040000000000000

noncomputable def ep1355 := BSN.log_dyadic_bound 20349163600 151421163600 4 3 ep1352 1048576 400000 ep1353 ep1354 283546 171770327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20349163600) (BSN.artanhQ 151421163600) 0 3 ep1353 ep1352 ep1354 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1356 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 85885163600 16000000)) 1 2 0 1 9669427351475941 1125899906842624 625000003 250000000000000 9669427351475941 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 85885163600 16000000 9669427351475941 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85885163600) qz667)) Bool.false 324452142544039561920512 37778931862957161709568 1000000004800000 400000000000000000000 9669427351475941 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 85885163600 16000000 12 171770327200 131072000000 283546 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep1355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1357 := BSN.arctan_dyadic_bound_f 1000 293060 1 0 1048576 400000 0 1 1 0 1 1 3578 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz506 := (@Nat.cast Real Real.instNatCast 293060)

noncomputable def ep1358 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz669 qz506)) 884279719003555 562949953421312 1 2000000000000000 3578 1048576 1 400000 925220255700530233344 882358794880419 562949953421312 5000000001 2000000000000000 qz94 (ep1357 rfl) rfl rfl

noncomputable abbrev qz206 := (@HAdd.hAdd Complex Complex Complex qz272 qz494 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz507 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz725)

noncomputable def ep1359 := @ep1350 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 562949953421312 5000000001 2000000000000000 Bool.false 9669427351475941 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 882358794880419 562949953421312 5000000001 2000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz144 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz144) qz113) (ep1351 (@congrArg Complex Complex qz206 qz507 Complex.log (BSN.w_shift_mk qz144 Bool.false 146530 1000 0 qz145 rfl)) (@Enclosure.Complex.IsNear.of_parts qz505 Bool.false 9669427351475941 2251799813685248 625000003 500000000000000 Bool.false 882358794880419 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz505) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 85885163600 16000000))) Bool.false 9669427351475941 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 1000 293060 4000 85885163600 16000000 rfl rfl rfl) (ep1356 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz505) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz506 qz669)) Bool.false 882358794880419 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 1000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz506 qz669)) (@HSub.hSub Real Real Real qz404 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz669 qz506))) Bool.false 882358794880419 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 293060 1000 rfl rfl) ep1358)))) rfl rfl

noncomputable abbrev qz508 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz725))

noncomputable def ep1360 := @Enclosure.Complex.IsNear.of_eq qz204 qz508 Bool.false 9669741957830373 2251799813685248 625000003 500000000000000 Bool.false 874676172129699 562949953421312 5000000001 2000000000000000

noncomputable def ep1361 := nat_lit 1266839952353897299621096060191582395123900244560995553280000000000000

noncomputable def ep1362 := nat_lit 7726043614444295238413749925489936036614876121403027456000000000000

noncomputable def ep1363 := nat_lit 1072610625883402030057319786115501905634604280279040000000000000

noncomputable def ep1364 := BSN.log_dyadic_bound 20373163600 151445163600 4 3 ep1361 1048576 400000 ep1362 ep1363 283839 171818327200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 20373163600) (BSN.artanhQ 151445163600) 0 3 ep1362 ep1361 ep1363 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_ff qz92 (Real.log (Enclosure.sfrac Bool.false 85909163600 16000000)) 1 2 0 1 9669741957830373 1125899906842624 625000003 250000000000000 9669741957830373 2251799813685248 625000003 500000000000000 qz415 (BSN.isNear_log_sfrac 85909163600 16000000 9669741957830373 1125899906842624 625000003 250000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85909163600) qz667)) Bool.false 324462698981566118363136 37778931862957161709568 1000000004800000 400000000000000000000 9669741957830373 1125899906842624 625000003 250000000000000 (BSN.log_rat_reduce_isNear 85909163600 16000000 12 171818327200 131072000000 283839 1048576 24973259072661432 36028797018963968 400000 1000000000000000 rfl rfl rfl rfl (ep1364 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1366 := BSN.arctan_dyadic_bound_f 5000 293060 1 0 1048576 400000 0 1 1 0 1 1 17888 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 293060) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 293060) 0 0 rfl) rfl rfl rfl

noncomputable def ep1367 := @Enclosure.Real.IsNear.subLit_ff_p qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz670 qz506)) 884279719003555 562949953421312 1 2000000000000000 17888 1048576 1 400000 917164441867071258624 874676172129699 562949953421312 5000000001 2000000000000000 qz94 (ep1366 rfl) rfl rfl

noncomputable abbrev qz207 := (@HAdd.hAdd Complex Complex Complex qz272 qz494 qz420)

noncomputable abbrev qz509 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz725)

noncomputable def ep1368 := @ep1346 9669741957830373 2251799813685248 625000003 500000000000000 Bool.false 874676172129699 562949953421312 5000000001 2000000000000000 Bool.false ep1347 9669584654653157 1125899906842624 625000003 250000000000000 Bool.false ep1348 878517483505059 281474976710656 5000000001 1000000000000000 (ep1349 (BSN.log_sum_c_succ qz144 0 1 rfl) (ep1359 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1360 (@congrArg Complex Complex qz207 qz509 Complex.log (BSN.w_shift_mk qz144 Bool.false 146530 1000 1 qz145 rfl)) (@Enclosure.Complex.IsNear.of_parts qz508 Bool.false 9669741957830373 2251799813685248 625000003 500000000000000 Bool.false 874676172129699 562949953421312 5000000001 2000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz508) (@HMul.hMul Real Real Real qz0 qz92 (Real.log (Enclosure.sfrac Bool.false 85909163600 16000000))) Bool.false 9669741957830373 2251799813685248 625000003 500000000000000 (Enclosure.clog_re_eq 5000 293060 4000 85909163600 16000000 rfl rfl rfl) (ep1365 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz508) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz506 qz670)) Bool.false 874676172129699 562949953421312 5000000001 2000000000000000 (Enclosure.clog_im_eq 5000 293060 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz506 qz670)) (@HSub.hSub Real Real Real qz404 qz93 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz670 qz506))) Bool.false 874676172129699 562949953421312 5000000001 2000000000000000 (BSN.arctan_recip 293060 5000 rfl rfl) ep1367)))) rfl rfl

noncomputable def ep1369 := @ep1270 629145600000000000000000 Bool.false 9669584654653157 1125899906842624 625000003 250000000000000 Bool.false 878517483505059 281474976710656 5000000001 1000000000000000 Bool.true ep1271 25949511650167800331 225179981368524800 19897502455018851407 104857600000000000000000 Bool.false ep1272 108513523716687612473 450359962737049600 63516627931818027929 629145600000000000000000 (@ep1273 225179981368524800 19635358453760560207 104857600000000000000000 Bool.false 109919151690295706873 450359962737049600 60370899931188882329 629145600000000000000000 (BSN.logGammaStirling_unfold 1 qz184) (ep1343 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1344 5000000001 1000000000000000 (BSN.log_sum_c_eq qz144 2) (ep1345 (BSN.log_sum_c_succ qz144 1 2 rfl) (ep1368 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz208 := (@HDiv.hDiv Real Real Real qz270 qz462 (2 : Real))

noncomputable def ep1370 := @Enclosure.Real.IsNear.mulLit_ff qz208 (Real.log Real.pi) 146530 2000 0 1 75021 65536 1 262144 1099282713 13107200 14653 52428800 (@Enclosure.Real.IsNear.of_eq qz208 (Enclosure.sfrac Bool.false 146530 2000) Bool.false 146530 2000 0 1 (BSN.t_half_eq qz144 Bool.false 146530 1000 qz145) (Enclosure.Real.IsNear.const Bool.false 146530 2000)) EMRow51.d5 rfl

noncomputable def ep1371 := @ep1267 14653 52428800 ep1268 70742457305542380089 450359962737049600 239352627931818027929 629145600000000000000000 (@ep1269 63516627931818027929 629145600000000000000000 (ep1369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1370 rfl rfl

noncomputable def ep1372 := nat_lit 8347746859401489388635245041151530999698311943033988968077464462264726034453025

noncomputable def ep1373 := nat_lit 16779859881707055492460990912702361029294554640973351204331353807573646709281

noncomputable def ep1374 := nat_lit 21835979144338279832771181122490586890876721048051252347776822828338210852704801

noncomputable def ep1375 := BSN.sin_dyadic_bound_f 3373638477 2147483648 3 2 1048576 400391 ep1372 ep60 ep1373 ep1374 ep63 ep1373 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3373638477) qz15 0 2 ep1372 ep60 ep1373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3373638477) qz16 0 2 ep1374 ep63 ep1373 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1376 := @ep1265 65536 Bool.false 1048575 1048576 1 200000 (@ep1266 82355059 524288 25 65536 ep1371 rfl) (Enclosure.sfrac_false_div 82355059 524288) (BSN.cos_reduce3 qz724 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118699351470784787775488) qz26) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 24 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 82355059 524288 226375608064910080 72057594037927936 24 118699351470784787775488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118699351470784787775488 75557863725914323419136 3373638477 2147483648 400391 400000 (ep1375 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1377 := nat_lit 39305993639239819355585033

noncomputable def ep1378 := nat_lit 5459334739329422458880000000

noncomputable abbrev qz510 := (@HPow.hPow Complex Complex Complex qz547 qz671 qz689)

noncomputable abbrev qz209 := qz510

noncomputable abbrev qz210 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz409 qz431 (@HSub.hSub Complex Complex Complex qz401 qz460 (1 : Complex))) qz408)

noncomputable def ep1379 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz141 1 37) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz142) (@HMul.hMul Complex Complex Complex qz72 qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) Bool.false 775699511146609918085077 698794846634166074736640 ep1262

noncomputable def ep1380 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz142) (@HMul.hMul Complex Complex Complex qz72 qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) Bool.false 1184516556929 1099511627776 24506684251357 3435973836800000

noncomputable def ep1381 := nat_lit 852890632165856527217829033124298752

noncomputable def ep1382 := nat_lit 4610187130158283107539696811507712

noncomputable def ep1383 := @ep1380 Bool.false 79729143955 1099511627776 24495296920107 3435973836800000 Bool.false 22879763883816416560517 698794846634166074736640 768858889817819234087041 ep1263 Bool.true 80200752121181398614337 1048192269951249112104960 386015846081451602238833 ep1378 Bool.false ep1381 775699511146609918085077 698794846634166074736640 ep1262 ep1263 Bool.true ep1382 4192940769060699592537 1048192269951249112104960

noncomputable def ep1384 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 37, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz142) (BSN.headSumC qz141 37) Bool.false 1184516556929 1099511627776 24506684251357 3435973836800000 Bool.false 79729143955 1099511627776 24495296920107

noncomputable abbrev qz727 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 36) qz142)

noncomputable def ep1385 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 37) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 36) qz727) Bool.false 1184516556929 1099511627776 24506684251357 3435973836800000 Bool.false 79729143955 1099511627776 24495296920107 3435973836800000

noncomputable def ep1386 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 36) qz727 Bool.false 1349764410631 1099511627776 24080886324231 3435973836800000 Bool.false 517464679 1099511627776 24071037436731 3435973836800000 Bool.true

noncomputable abbrev qz728 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 35) qz142)

noncomputable def ep1387 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 36) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 35) qz728) Bool.false 1349764410631 1099511627776 24080886324231 3435973836800000 Bool.false 517464679 1099511627776 24071037436731 3435973836800000

noncomputable def ep1388 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 35) qz728 Bool.false 1190300682931 1099511627776 23648682266303 3435973836800000 Bool.true 23734495001 274877906944 2954995241491 429496729600000 Bool.false

noncomputable abbrev qz729 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 34) qz142)

noncomputable def ep1389 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 35) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz141 34) qz729) Bool.false 1190300682931 1099511627776 23648682266303 3435973836800000 Bool.true 23734495001 274877906944 2954995241491 429496729600000

noncomputable def ep1390 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz141 34) qz729 Bool.false 1176247406239 1099511627776 23212775781583 3435973836800000 Bool.false 93101832307 1099511627776 23201031975333 3435973836800000 Bool.false

noncomputable abbrev qz730 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz142)

noncomputable def ep1391 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz141 34) (@HAdd.hAdd Complex Complex Complex qz4 qz171 qz730) Bool.false 1176247406239 1099511627776 23212775781583 3435973836800000 Bool.false 93101832307 1099511627776 23201031975333 3435973836800000

noncomputable def ep1392 := @Enclosure.Complex.IsNear.addLitP qz171 qz730 Bool.false 1361036149053 1099511627776 22767399088277 3435973836800000 Bool.false 21616452021 549755813888 1422372820947 214748364800000 Bool.true

noncomputable abbrev qz211 := (@HMul.hMul Real Real Real qz267 qz462 qz676)

noncomputable def ep1393 := @Enclosure.Complex.IsNear.of_eq qz730 (Complex.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz211)))) Bool.true 92394371407 549755813888 222688346653 1717986918400000 Bool.false 49868928265 1099511627776 443066840181 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 33 qz145 rfl)

noncomputable def ep1394 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz676 146530 1000 0 1 15746868335186131 4503599627370496 1000000001 200000000000000 230738861715482377543 450359962737049600 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz677) Bool.false 66047152845744529997824 18889465931478580854784 1000000001000000 200000000000000000000 15746868335186131 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep712 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1395 := nat_lit 102668827469450806797980097596850081

noncomputable def ep1396 := BSN.cos_dyadic_bound_f 566056329 2147483648 2 1 1048576 400391 ep1395 ep80 ep1395 ep1395 ep81 ep1395 1012358 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 566056329) qz20 0 1 ep1395 ep80 ep1395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 566056329) qz21 0 1 ep1395 ep81 ep1395 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz511 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67153847) qz594)

noncomputable def ep1397 := @Enclosure.Real.IsNear.cos_image qz211 qz511 Bool.false 67153847 131072 385 524288 Bool.true 1012358 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 230738861715482377543 450359962737049600 14653000014653 20000000000000000 67153847 131072 385 524288 (ep1394 rfl) rfl) (Enclosure.sfrac_false_div 67153847 131072) (BSN.cos_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4979084129700176461824) qz327) 226375608064910080 72057594037927936 Bool.false 1012358 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 67153847 131072 226375608064910080 72057594037927936 81 4979084129700176461824 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1012358 1048576 4979084129700176461824 18889465931478580854784 566056329 2147483648 400391 400000 (ep1396 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1398 := BSN.sin_dyadic_bound_f 566056329 2147483648 2 1 1048576 400391 ep1395 ep147 ep1395 ep1395 ep148 ep1395 273205 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 566056329) qz15 0 1 ep1395 ep147 ep1395 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 566056329) qz16 0 1 ep1395 ep148 ep1395 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1399 := @Enclosure.Real.IsNear.sin_image qz211 qz511 Bool.false 67153847 131072 385 524288 Bool.true 273205 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz211 Bool.false 230738861715482377543 450359962737049600 14653000014653 20000000000000000 67153847 131072 385 524288 (ep1394 rfl) rfl) (Enclosure.sfrac_false_div 67153847 131072) (BSN.sin_reduce2 qz511 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4979084129700176461824) qz327) 226375608064910080 72057594037927936 Bool.false 273205 1048576 81 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 67153847 131072 226375608064910080 72057594037927936 81 4979084129700176461824 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 273205 1048576 4979084129700176461824 18889465931478580854784 566056329 2147483648 400391 400000 (ep1398 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1400 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz433 (Real.cos qz211)) (@HMul.hMul Real Real Real qz0 qz433 (@Neg.neg Real Real.instNeg (Real.sin qz211))) Bool.true 92394371407 549755813888 222688346653 1717986918400000 Bool.false 49868928265 1099511627776 443066840181 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ft qz433 (Real.cos qz211) 182533 1048576 1 1048576 506179 524288 1211317 1638400000 92394371407 549755813888 222688346653 1717986918400000 qz437 (@Enclosure.Real.IsNear.recentre' (Real.cos qz211) Bool.true 1012358 1048576 77524288 104857600000 506179 524288 1211317 1638400000 (ep1397 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz433 (@Neg.neg Real Real.instNeg (Real.sin qz211)) 182533 1048576 1 1048576 273205 1048576 1211317 1638400000 49868928265 1099511627776 443066840181 3435973836800000 qz437 (@Enclosure.Real.IsNear.neg (Real.sin qz211) Bool.true 273205 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz211) Bool.true 273205 1048576 77524288 104857600000 273205 1048576 1211317 1638400000 (ep1399 rfl rfl) rfl)) rfl)

noncomputable def ep1401 := @ep1392 92394371407 549755813888 222688346653 1717986918400000 Bool.false 49868928265 1099511627776 443066840181 3435973836800000 Bool.false 646648850150570414047232 1176247406239 1099511627776 23212775781583 3435973836800000 Bool.false 51183273594398877679616 93101832307 1099511627776 23201031975333 3435973836800000 EMRow51.d16 (ep1393 ep1400) rfl rfl

noncomputable abbrev qz212 := (@HMul.hMul Real Real Real qz267 qz462 qz678)

noncomputable def ep1402 := @Enclosure.Complex.IsNear.of_eq qz729 (Complex.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz212)))) Bool.false 3513319173 274877906944 5448831059 42949672960000 Bool.true 188039812311 1099511627776 87785991319 687194767360000 (BSN.cpow_neg_s_mk qz144 146530 1000 34 qz145 rfl)

noncomputable def ep1403 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz678 146530 1000 0 1 15881309401485523 4503599627370496 1000000001 200000000000000 232708826659967368519 450359962737049600 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz679) Bool.false 66611039547888335060992 18889465931478580854784 1000000001000000 200000000000000000000 15881309401485523 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep727 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1404 := nat_lit 3819432493877595375209815111127615912525480076560904622574441281583940685893601

noncomputable def ep1405 := nat_lit 11359339440893584672741436006824468726397856071833554010402556645450313469921

noncomputable def ep1406 := nat_lit 11435578802750998956283962461369198800123644517539046759702518731460921430740961

noncomputable def ep1407 := BSN.cos_dyadic_bound_f 3213062213 2147483648 3 2 1048576 400391 ep1404 ep67 ep1405 ep1406 ep69 ep1405 78148 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3213062213) qz20 0 2 ep1404 ep67 ep1405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3213062213) qz21 0 2 ep1406 ep69 ep1405 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz512 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 270908729) qz25)

noncomputable def ep1408 := @Enclosure.Real.IsNear.cos_image qz212 qz512 Bool.false 270908729 524288 385 524288 Bool.false 78148 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 232708826659967368519 450359962737049600 14653000014653 20000000000000000 270908729 524288 385 524288 (ep1403 rfl) rfl) (Enclosure.sfrac_false_div 270908729 524288) (BSN.cos_reduce0 qz512 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113049576453600935149568) qz26) 226375608064910080 72057594037927936 Bool.false 78148 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 270908729 524288 226375608064910080 72057594037927936 82 113049576453600935149568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 78148 1048576 113049576453600935149568 75557863725914323419136 3213062213 2147483648 400391 400000 (ep1407 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1409 := nat_lit 6865891017426956807639474051224249067564745852952161477425672261534732983832545

noncomputable def ep1410 := nat_lit 17963704210356773454347517333004841275207785466948882877240870831355476354895841

noncomputable def ep1411 := BSN.sin_dyadic_bound_f 3213062213 2147483648 3 2 1048576 400391 ep1409 ep60 ep1405 ep1410 ep63 ep1405 1045659 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3213062213) qz15 0 2 ep1409 ep60 ep1405 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3213062213) qz16 0 2 ep1410 ep63 ep1405 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1412 := @Enclosure.Real.IsNear.sin_image qz212 qz512 Bool.false 270908729 524288 385 524288 Bool.false 1045659 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz212 Bool.false 232708826659967368519 450359962737049600 14653000014653 20000000000000000 270908729 524288 385 524288 (ep1403 rfl) rfl) (Enclosure.sfrac_false_div 270908729 524288) (BSN.sin_reduce0 qz512 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113049576453600935149568) qz26) 226375608064910080 72057594037927936 Bool.false 1045659 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 270908729 524288 226375608064910080 72057594037927936 82 113049576453600935149568 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045659 1048576 113049576453600935149568 75557863725914323419136 3213062213 2147483648 400391 400000 (ep1411 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1413 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz438 (Real.cos qz212)) (@HMul.hMul Real Real Real qz0 qz438 (@Neg.neg Real Real.instNeg (Real.sin qz212))) Bool.false 3513319173 274877906944 5448831059 42949672960000 Bool.true 188039812311 1099511627776 87785991319 687194767360000 (@Enclosure.Real.IsNear.mulLit_ff qz438 (Real.cos qz212) 179829 1048576 1 1048576 19537 262144 1211317 1638400000 3513319173 274877906944 5448831059 42949672960000 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz212) Bool.false 78148 1048576 77524288 104857600000 19537 262144 1211317 1638400000 (ep1408 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz438 (@Neg.neg Real Real.instNeg (Real.sin qz212)) 179829 1048576 1 1048576 1045659 1048576 1211317 1638400000 188039812311 1099511627776 87785991319 687194767360000 qz442 (@Enclosure.Real.IsNear.neg (Real.sin qz212) Bool.false 1045659 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz212) Bool.false 1045659 1048576 77524288 104857600000 1045659 1048576 1211317 1638400000 (ep1412 rfl rfl) rfl)) rfl)

noncomputable def ep1414 := @ep1390 3513319173 274877906944 5448831059 42949672960000 Bool.true 188039812311 1099511627776 87785991319 687194767360000 Bool.false 327187360358087067172864 1190300682931 1099511627776 23648682266303 3435973836800000 Bool.true 104385412931963378991104 23734495001 274877906944 2954995241491 429496729600000 (ep1391 (BSN.head_sum_c_succ qz141 33 34 rfl rfl) (ep1401 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1402 ep1413) rfl rfl

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz462 qz680)

noncomputable def ep1415 := @Enclosure.Complex.IsNear.of_eq qz728 (Complex.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.false 39865931925 274877906944 54025507241 429496729600000 Bool.false 95455444683 1099511627776 431075504803 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 35 qz145 rfl)

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz680 146530 1000 0 1 16011859227414739 4503599627370496 1000000001 200000000000000 234621773259308170567 450359962737049600 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 35 1 16011859227414739 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz681) Bool.false 67158605204982549446656 18889465931478580854784 1000000001000000 200000000000000000000 16011859227414739 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 35 1 5 70 64 46982 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep741 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1417 := nat_lit 1548457745648058565123607025101371942473903701962409462228724377005856130760960

noncomputable def ep1418 := nat_lit 579256920681083796922948929352609132854176691853687103568185978520881234176

noncomputable def ep1419 := nat_lit 4054546727397145915843000291284641339311793409543309288621834400573922725232896

noncomputable def ep1420 := BSN.sin_dyadic_bound_f 2214924382 2147483648 3 2 1048576 400391 ep1417 ep60 ep1418 ep1419 ep63 ep1418 899700 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2214924382) qz15 0 2 ep1417 ep60 ep1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2214924382) qz16 0 2 ep1419 ep63 ep1418 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz513 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68283923) qz594)

noncomputable def ep1421 := @Enclosure.Real.IsNear.cos_image qz213 qz513 Bool.false 68283923 131072 385 524288 Bool.false 899700 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 234621773259308170567 450359962737049600 14653000014653 20000000000000000 68283923 131072 385 524288 (ep1416 rfl) rfl) (Enclosure.sfrac_false_div 68283923 131072) (BSN.cos_reduce3 qz513 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19482680908291606839296) qz327) 226375608064910080 72057594037927936 Bool.false 899700 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 68283923 131072 226375608064910080 72057594037927936 82 19482680908291606839296 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 899700 1048576 19482680908291606839296 18889465931478580854784 2214924382 2147483648 400391 400000 (ep1420 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1422 := nat_lit 860511750658113017867302991247141127655659468508829117728654958771484908749056

noncomputable def ep1423 := nat_lit 2580376738132976886008063075882718164701270052142779978978828504357412963778816

noncomputable def ep1424 := BSN.cos_dyadic_bound_f 2214924382 2147483648 3 2 1048576 400391 ep1422 ep67 ep1418 ep1423 ep69 ep1418 538563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2214924382) qz20 0 2 ep1422 ep67 ep1418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2214924382) qz21 0 2 ep1423 ep69 ep1418 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1425 := @Enclosure.Real.IsNear.sin_image qz213 qz513 Bool.false 68283923 131072 385 524288 Bool.true 538563 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 234621773259308170567 450359962737049600 14653000014653 20000000000000000 68283923 131072 385 524288 (ep1416 rfl) rfl) (Enclosure.sfrac_false_div 68283923 131072) (BSN.sin_reduce3 qz513 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19482680908291606839296) qz327) 226375608064910080 72057594037927936 Bool.false 538563 1048576 82 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 68283923 131072 226375608064910080 72057594037927936 82 19482680908291606839296 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 538563 1048576 19482680908291606839296 18889465931478580854784 2214924382 2147483648 400391 400000 (ep1424 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1426 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz443 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz443 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.false 39865931925 274877906944 54025507241 429496729600000 Bool.false 95455444683 1099511627776 431075504803 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz443 (Real.cos qz213) 177241 1048576 1 1048576 224925 262144 1211317 1638400000 39865931925 274877906944 54025507241 429496729600000 qz447 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.false 899700 1048576 77524288 104857600000 224925 262144 1211317 1638400000 (ep1421 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz443 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 177241 1048576 1 1048576 538563 1048576 1211317 1638400000 95455444683 1099511627776 431075504803 3435973836800000 qz447 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 538563 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 538563 1048576 77524288 104857600000 538563 1048576 1211317 1638400000 (ep1425 rfl rfl) rfl)) rfl)

noncomputable def ep1427 := @ep1388 39865931925 274877906944 54025507241 429496729600000 Bool.false 95455444683 1099511627776 431075504803 3435973836800000 Bool.false 371020416061751022321664 1349764410631 1099511627776 24080886324231 3435973836800000 Bool.false 142239607880968830976 517464679 1099511627776 24071037436731 3435973836800000 (ep1389 (BSN.head_sum_c_succ qz141 34 35 rfl rfl) (ep1414 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1415 ep1426) rfl rfl

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz267 qz462 qz682)

noncomputable def ep1428 := @Enclosure.Complex.IsNear.of_eq qz727 (Complex.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.true 82623926851 549755813888 212898963563 1717986918400000 Bool.false 19802919819 274877906944 26516217711 214748364800000 (BSN.cpow_neg_s_mk qz144 146530 1000 36 qz145 rfl)

noncomputable def ep1429 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz682 146530 1000 0 1 16138732561338579 4503599627370496 1000000001 200000000000000 236480848221294198087 450359962737049600 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 36 1 16138732561338579 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz683) Bool.false 67690750536952647254016 18889465931478580854784 1000000001000000 200000000000000000000 16138732561338579 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 36 1 5 72 64 61752 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep752 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1430 := nat_lit 849020882434487111296777597954560000

noncomputable def ep1431 := BSN.cos_dyadic_bound_f 959907960 2147483648 2 1 1048576 400391 ep1430 ep80 ep1430 ep1430 ep81 ep1430 945554 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 959907960) qz20 0 1 ep1430 ep80 ep1430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 959907960) qz21 0 1 ep1430 ep81 ep1430 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz514 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 550599881) qz35)

noncomputable def ep1432 := @Enclosure.Real.IsNear.cos_image qz214 qz514 Bool.false 550599881 1048576 769 1048576 Bool.true 945554 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 236480848221294198087 450359962737049600 14653000014653 20000000000000000 550599881 1048576 769 1048576 (ep1429 rfl) rfl) (Enclosure.sfrac_false_div 550599881 1048576) (BSN.cos_reduce2 qz514 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67547517700297312960512) qz36) 226375608064910080 72057594037927936 Bool.false 945554 1048576 83 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 550599881 1048576 226375608064910080 72057594037927936 83 67547517700297312960512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 945554 1048576 67547517700297312960512 151115727451828646838272 959907960 2147483648 400391 400000 (ep1431 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1433 := BSN.sin_dyadic_bound_f 959907960 2147483648 2 1 1048576 400391 ep1430 ep147 ep1430 ep1430 ep148 ep1430 453252 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 959907960) qz15 0 1 ep1430 ep147 ep1430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 959907960) qz16 0 1 ep1430 ep148 ep1430 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1434 := @Enclosure.Real.IsNear.sin_image qz214 qz514 Bool.false 550599881 1048576 769 1048576 Bool.true 453252 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 236480848221294198087 450359962737049600 14653000014653 20000000000000000 550599881 1048576 769 1048576 (ep1429 rfl) rfl) (Enclosure.sfrac_false_div 550599881 1048576) (BSN.sin_reduce2 qz514 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67547517700297312960512) qz36) 226375608064910080 72057594037927936 Bool.false 453252 1048576 83 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q2 550599881 1048576 226375608064910080 72057594037927936 83 67547517700297312960512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 453252 1048576 67547517700297312960512 151115727451828646838272 959907960 2147483648 400391 400000 (ep1433 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1435 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz448 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz448 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.true 82623926851 549755813888 212898963563 1717986918400000 Bool.false 19802919819 274877906944 26516217711 214748364800000 (@Enclosure.Real.IsNear.mulLit_ft qz448 (Real.cos qz214) 174763 1048576 1 1048576 472777 524288 2419509 3276800000 82623926851 549755813888 212898963563 1717986918400000 qz452 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.true 945554 1048576 154848576 209715200000 472777 524288 2419509 3276800000 (ep1432 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz448 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 174763 1048576 1 1048576 113313 262144 2419509 3276800000 19802919819 274877906944 26516217711 214748364800000 qz452 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 113313 262144 2419509 3276800000 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 453252 1048576 154848576 209715200000 113313 262144 2419509 3276800000 (ep1434 rfl rfl) rfl)) rfl)

noncomputable def ep1436 := @ep1386 82623926851 549755813888 212898963563 1717986918400000 Bool.false 19802919819 274877906944 26516217711 214748364800000 Bool.false 651194863818313880829952 1184516556929 1099511627776 24506684251357 3435973836800000 Bool.false 21915780212787270123520 79729143955 1099511627776 24495296920107 3435973836800000 (ep1387 (BSN.head_sum_c_succ qz141 35 36 rfl rfl) (ep1427 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1428 ep1435) rfl rfl

noncomputable def ep1437 := @Enclosure.Complex.IsNear.mul qz209 (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 22879763883816416560517 698794846634166074736640 768858889817819234087041 ep1263 Bool.true

noncomputable abbrev qz215 := (Complex.re qz510)

noncomputable abbrev qz216 := (Complex.im qz510)

noncomputable def ep1438 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 1068949370368335763675 52409613497562455605248 498901576170435089489

noncomputable def ep1439 := nat_lit 8189002108994133688320000

noncomputable def ep1440 := nat_lit 2096384539902498224209920

noncomputable def ep1441 := nat_lit 32756008435976534753280000000

noncomputable def ep1442 := nat_lit 3597358746198920570050348122679839238964379648

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 11206921235 274877906944 26152551389 214748364800000 95382964505

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz267 qz462 qz684)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz267 qz462 qz684))

noncomputable abbrev qz731 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1444 := @Enclosure.Complex.IsNear.of_eq qz209 (Complex.mk (@HMul.hMul Real Real Real qz0 qz453 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz453 qz731)) Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (BSN.cpow_neg_s_mk qz144 146530 1000 37 qz145 rfl)

noncomputable def ep1445 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz132 146530 1000 0 1 16262126971752659 4503599627370496 1000000001 200000000000000 238288946517091712327 450359962737049600 14653000014653 20000000000000000 qz146 (BSN.isNear_log_sfrac 37 1 16262126971752659 4503599627370496 1000000001 200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz456 Bool.false 68208304206130064654336 18889465931478580854784 1000000001000000 200000000000000000000 16262126971752659 4503599627370496 1000000001 200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 76117 524288 24973259072661432 36028797018963968 200000 1000000000000000 rfl rfl rfl rfl (ep773 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1446 := nat_lit 2312435021858794592989764207235821926263673462935629744837469714015646048649216

noncomputable def ep1447 := nat_lit 4173616035444351139562000643661964372338013347714037636913412429317826215936

noncomputable def ep1448 := nat_lit 6928957833505495076690168620420141850046344362111461159238582317188302493515776

noncomputable def ep1449 := BSN.cos_dyadic_bound_f 2835071796 2147483648 3 2 1048576 400391 ep1446 ep67 ep1447 ep1448 ep69 ep1447 260044 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2835071796) qz20 0 2 ep1446 ep67 ep1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2835071796) qz21 0 2 ep1448 ep69 ep1447 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz515 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 554809687) qz35)

noncomputable def ep1450 := @Enclosure.Real.IsNear.cos_image qz217 qz515 Bool.false 554809687 1048576 385 524288 Bool.false 260044 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 238288946517091712327 450359962737049600 14653000014653 20000000000000000 554809687 1048576 385 524288 (ep1445 rfl) rfl) (Enclosure.sfrac_false_div 554809687 1048576) (BSN.cos_reduce0 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199500441948621513949184) qz36) 226375608064910080 72057594037927936 Bool.false 260044 1048576 84 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 554809687 1048576 226375608064910080 72057594037927936 84 199500441948621513949184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 260044 1048576 199500441948621513949184 151115727451828646838272 2835071796 2147483648 400391 400000 (ep1449 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1451 := nat_lit 4159044146517474786469925972509549895776741822605962310597914755284708626595840

noncomputable def ep1452 := nat_lit 10885977386345524062719086688863844641860062275690745228725250262764865160544256

noncomputable def ep1453 := BSN.sin_dyadic_bound_f 2835071796 2147483648 3 2 1048576 400391 ep1451 ep60 ep1447 ep1452 ep63 ep1447 1015819 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2835071796) qz15 0 2 ep1451 ep60 ep1447 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2835071796) qz16 0 2 ep1452 ep63 ep1447 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1454 := @Enclosure.Real.IsNear.sin_image qz217 qz515 Bool.false 554809687 1048576 385 524288 Bool.false 1015819 1048576 1 200000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 238288946517091712327 450359962737049600 14653000014653 20000000000000000 554809687 1048576 385 524288 (ep1445 rfl) rfl) (Enclosure.sfrac_false_div 554809687 1048576) (BSN.sin_reduce0 qz515 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 199500441948621513949184) qz36) 226375608064910080 72057594037927936 Bool.false 1015819 1048576 84 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q0 554809687 1048576 226375608064910080 72057594037927936 84 199500441948621513949184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1015819 1048576 199500441948621513949184 151115727451828646838272 2835071796 2147483648 400391 400000 (ep1453 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1455 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz453 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz453 qz731) Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (@Enclosure.Real.IsNear.mulLit_ff qz453 (Real.cos qz217) 172385 1048576 1 1048576 65011 262144 1211317 1638400000 11206921235 274877906944 26152551389 214748364800000 qz458 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.false 260044 1048576 77524288 104857600000 65011 262144 1211317 1638400000 (ep1450 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz453 qz731 172385 1048576 1 1048576 1015819 1048576 1211317 1638400000 175111958315 1099511627776 420802619099 3435973836800000 qz458 (@Enclosure.Real.IsNear.neg qz218 Bool.false 1015819 1048576 1211317 1638400000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 1015819 1048576 77524288 104857600000 1015819 1048576 1211317 1638400000 (ep1454 rfl rfl) rfl)) rfl)

noncomputable def ep1456 := @ep1443 190665063192 0 1 1068949370368335763675 52409613497562455605248 498901576170435089489 ep1439 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (ep1444 ep1455))

noncomputable def ep1457 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 95382964505 190665063192 0 1 Bool.false

noncomputable def ep1458 := @Enclosure.Complex.IsNear.addLitP qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) Bool.false 214342909 429425818 0 1 Bool.true 54216100

noncomputable def ep1459 := @ep1458 214712909 0 1 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1 Bool.false 190765929010 95382964505 190665063192 0 1 Bool.false 738993415577 738993415577 9533253159600 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz409 qz431 (@HSub.hSub Complex Complex Complex qz401 qz460 (1 : Complex)))

noncomputable def ep1460 := @Enclosure.Complex.IsNear.addLitP qz219 qz97 Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1

noncomputable def ep1461 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 74000000 85885163600) (Enclosure.sfrac Bool.true 21686440000 85885163600)) Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1

noncomputable def ep1462 := @ep1460 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 85737163600 214342909 429425818 0 1 Bool.true 21686440000 54216100 214712909 0 1 (ep1461 (BSN.N_div_s_sub_one_mk qz144 146530 1000 37 qz145 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 74000000 85885163600) (Enclosure.sfrac Bool.true 21686440000 85885163600) Bool.true 74000000 85885163600 0 1 Bool.true 21686440000 85885163600 0 1 (Enclosure.Real.IsNear.const Bool.true 74000000 85885163600) (Enclosure.Real.IsNear.const Bool.true 21686440000 85885163600))) qz98 rfl

noncomputable def ep1463 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135)) Bool.false 1 888 0 1

noncomputable def ep1464 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1465 := @ep1464 0 1 0 1 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1 Bool.false 1 1 888 0 1 Bool.false 14653 14653 44400 0

noncomputable def ep1466 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1467 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz135 Bool.false 1 888 0 1 Bool.false 14653 44400 0 1

noncomputable def ep1468 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) 1 888 0 1 0 1 0

noncomputable def ep1469 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 1 24 0 1 1 37 0 1 1

noncomputable def ep1470 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1471 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1472 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz141 Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 (BSN.ascPochhammer_one_eval qz141)

noncomputable def ep1473 := ep1472 (@Enclosure.Complex.IsNear.of_eq qz141 (Complex.mk qz92 qz144) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_crit_mk qz144 Bool.false 146530 1000 qz145) (@Enclosure.Complex.IsNear.mk qz92 qz144 Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 qz415 qz146))

noncomputable def ep1474 := @ep1471 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1475 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 146530 1000 0 1 0 1 0

noncomputable def ep1476 := @ep1475 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1477 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) 14653 1200 0 1 0 1 0 1 14653

noncomputable def ep1478 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 146530 1000 0 1 14653 1200 0

noncomputable def ep1479 := @ep1478 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1480 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1481 := @ep1480 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep797) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1482 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 (@ep1470 1 24 0 1 (ep1474 rfl) (ep1476 rfl) rfl rfl) (@ep1477 14653 1200 0 1 (ep1479 rfl) (ep1481 rfl) rfl rfl)

noncomputable def ep1483 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 ep1482

noncomputable def ep1484 := @ep1469 888 0 1 ep1483 qz138

noncomputable def ep1485 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 14653 1200 0 1 0 1 0 1 0

noncomputable def ep1486 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 14653 1200 0 1 ep1482

noncomputable def ep1487 := @ep1485 1 0 1 ep1486 qz139

noncomputable def ep1488 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136) 0 1 0 1 14653 44400 0

noncomputable def ep1489 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz137 1 24 0 1 0 1 0 1 0

noncomputable def ep1490 := @ep1489 1 0 1 ep1483 qz139

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz99)) ↑qz134) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)))) qz136 14653 1200 0 1 1 37 0 1 14653

noncomputable def ep1492 := @ep1491 44400 0 1 ep1486 qz138

noncomputable def ep1493 := @ep1465 1 (@ep1466 0 1 0 1 (BSN.bern_sum_base qz141 37) qz113) (ep1467 (@ep1468 1 1 1 888 0 1 (ep1484 rfl) (ep1487 rfl) rfl rfl) (@ep1488 1 14653 14653 44400 0 1 (ep1490 rfl) (ep1492 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1494 := ep1459 (ep1462 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1463 Bool.false 14653 44400 0 1 (BSN.bern_sum_succ qz141 37 0 1 1 rfl rfl) (ep1493 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1495 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 175111958315 1099511627776 420802619099 3435973836800000 738993415577

noncomputable def ep1496 := @ep1495 9533253159600 0 1 25881316836715819134551 ep1440 310970364771717344305123 ep1441 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (ep1444 ep1455))

noncomputable def ep1497 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))) Bool.false 95382964505 190665063192 0 1 Bool.false

noncomputable def ep1498 := @Enclosure.Real.IsNear.addLit_ft_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1))))))) 1656368200311012215519 524096134975624556052480 19326563277010125586453

noncomputable def ep1499 := nat_lit 2047250527248533422080000000

noncomputable def ep1500 := nat_lit 131024033743906139013120000

noncomputable def ep1501 := nat_lit 8406580841769858741957914872609830131730481152

noncomputable def ep1502 := @Enclosure.Real.IsNear.mulLit_ff qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 11206921235 274877906944 26152551389 214748364800000 738993415577

noncomputable def ep1503 := @ep1502 9533253159600 0 1 1656368200311012215519 524096134975624556052480 19326563277010125586453 ep1499 (@Enclosure.Complex.IsNear.re_isNear qz209 Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (ep1444 ep1455))

noncomputable def ep1504 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz210 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz80 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz80 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz122 qz123 (@HSub.hSub Nat Nat Nat qz121 (@HMul.hMul Nat Nat Nat qz80 2 k) 1)))))) 175111958315 1099511627776 420802619099 3435973836800000 95382964505

noncomputable def ep1505 := @ep1504 190665063192 0 1 16702697704360684609075 209638453990249822420992 8027480256226190416199 ep1500 (@Enclosure.Complex.IsNear.im_isNear qz209 Bool.false 11206921235 274877906944 26152551389 214748364800000 Bool.true 175111958315 1099511627776 420802619099 3435973836800000 (ep1444 ep1455))

noncomputable abbrev qz732 := (ep1494 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1506 := @ep1437 80200752121181398614337 1048192269951249112104960 386015846081451602238833 ep1378 (@ep1438 ep1439 25881316836715819134551 ep1440 310970364771717344305123 ep1441 ep1442 22879763883816416560517 698794846634166074736640 768858889817819234087041 ep1263 (ep1456 (@ep1457 738993415577 9533253159600 0 1 qz732) rfl) (ep1496 (@ep1497 738993415577 9533253159600 0 1 qz732) rfl) rfl rfl) (@ep1498 ep1499 16702697704360684609075 209638453990249822420992 8027480256226190416199 ep1500 ep1501 80200752121181398614337 1048192269951249112104960 386015846081451602238833 ep1378 (ep1503 (@ep1497 738993415577 9533253159600 0 1 qz732) rfl) (ep1505 (@ep1457 738993415577 9533253159600 0 1 qz732) rfl) rfl rfl)

noncomputable def ep1507 := @ep1383 ep1377 ep1378 (@ep1384 3435973836800000 (BSN.head_sum_c_eq qz141 37) (ep1385 (BSN.head_sum_c_succ qz141 36 37 rfl rfl) (ep1436 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1506 rfl rfl rfl

noncomputable def ep1508 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz141 1 37) Bool.false 775699511146609918085077 698794846634166074736640 ep1262 ep1263 Bool.true 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 (@ep1379 ep1263 Bool.true 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 (BSN.zetaApproximant_eq_folded' qz141 1 37 rfl) (ep1507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1509 := @Enclosure.Real.IsNear.mulLit_ft (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) (Complex.im (zetaApproximant qz141 1 37)) 93 524288 79149

noncomputable def ep1510 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182)) Bool.false 186 1048576 5065536

noncomputable def ep1511 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) qz724 Bool.false 82355059 524288 25

noncomputable def ep1512 := nat_lit 4645094859614919462794007685489829382512081992637093138356071969617102751011361

noncomputable def ep1513 := nat_lit 13901724859081344277397101074644083425477656868629332712659553201236160959615521

noncomputable def ep1514 := BSN.cos_dyadic_bound_t 3373638477 2147483648 3 2 1048576 400391 ep1512 ep67 ep1373 ep1513 ep69 ep1373 186 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3373638477) qz20 0 2 ep1512 ep67 ep1373 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3373638477) qz21 0 2 ep1513 ep69 ep1373 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1515 := @ep1511 65536 Bool.false 186 1048576 1 200000 (@ep1266 82355059 524288 25 65536 ep1371 rfl) (Enclosure.sfrac_false_div 82355059 524288) (BSN.sin_reduce3 qz724 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118699351470784787775488) qz26) 226375608064910080 72057594037927936 Bool.true 186 1048576 24 1000000000000000 400000 200000 (BSN.sin_reduce_arg_pos_rat_q3 82355059 524288 226375608064910080 72057594037927936 24 118699351470784787775488 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.true 186 1048576 118699351470784787775488 75557863725914323419136 3373638477 2147483648 400391 400000 (ep1514 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1516 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz141 1 37) Bool.false 775699511146609918085077 698794846634166074736640 ep1262 ep1263 Bool.true 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 (@ep1379 ep1263 Bool.true 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 (BSN.zetaApproximant_eq_folded' qz141 1 37 rfl) (ep1507 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow51.d17 : Enclosure.Real.IsNear (hardyZApproximantEM 1 37 qz144) Bool.false ep1247 ep1248 ep1249 ep1250 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 37 qz144) ep1251 Bool.false ep1247 ep1248 ep1249 ep1250 (@Eq.refl Real ep1251) (@ep1252 Bool.false ep1247 ep1248 ep1249 ep1250 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz404 (Complex.im (@HSub.hSub Complex Complex Complex qz73 qz180 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz181 (@Nat.cast Complex Complex.instNatCast j))))) qz182) (zetaApproximant qz141 1 37)) (@ep1254 ep1255 ep1256 ep1250 129981163840881687368647 ep1257 ep1258 ep1259 ep1260 ep1247 ep1248 ep1249 ep1250 (@ep1261 204800000 775699511146609918085077 698794846634166074736640 ep1262 ep1263 ep1253 ep1255 ep1256 ep1250 (@ep1264 13107200000 1048575 1048576 79149 204800000 (ep1376 rfl rfl) rfl) ep1508 rfl) (@ep1509 204800000 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 129981163840881687368647 ep1257 ep1258 ep1259 (@ep1510 13107200000 93 524288 79149 204800000 (ep1515 rfl rfl) rfl) ep1516 rfl) rfl rfl))

theorem EMRow51.d18 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow51.d19 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow51.d20 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow51.d21 : @Eq Nat (Nat.pow 37 (Nat.succ (Nat.mul 2 3))) 94931877133 := @Eq.refl Nat 94931877133

noncomputable abbrev qz733 := (@HAdd.hAdd Complex Complex Complex qz739 qz738 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz516 := qz733

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz516) (@HAdd.hAdd Real Real Real qz424 (Complex.re qz271) qz287))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz517 := (@HPow.hPow Complex Complex Complex qz547 qz671 (@HSub.hSub Complex Complex Complex qz658 qz548 qz554))

noncomputable abbrev qz223 := qz517

noncomputable def ep1517 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 19413142729 309237645312 33880265 309237645312 567219936172448967 1008806316530991104 42612027401

noncomputable def ep1518 := nat_lit 194989858444723934977348075520

noncomputable def ep1519 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37)) 26561 1769472 1 1769472 2192667 524288 117 16384 19413142729 309237645312

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz734 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz518 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz734 qz224 2))

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz518 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1521 := nat_lit 781950621441006189802102638025

noncomputable def ep1522 := nat_lit 19807040628566084398385987584

noncomputable def ep1523 := nat_lit 26986075409044041160201671

noncomputable def ep1524 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz519 := qz734

noncomputable def ep1525 := @Enclosure.Real.IsNear.mulLit_ff (@HPow.hPow Real Nat Real qz519 qz224 1) qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1521 ep1522 ep1523 ep1524

noncomputable def ep1526 := ep1525 (@Enclosure.Real.IsNear.of_eq (@HPow.hPow Real Nat Real qz519 qz224 1) qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz520 := (@HPow.hPow Real Nat Real qz734 qz224 2)

noncomputable def ep1527 := @Enclosure.Real.IsNear.inv_image qz520 ep1521 ep1522 ep1523 ep1524 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz520 (@HMul.hMul Real Real Real qz0 (@HPow.hPow Real Nat Real qz519 qz224 1) qz224) Bool.false ep1521 ep1522 ep1523 ep1524 (BSN.pow_succ_r qz224 1 2 rfl) ep1526) rfl rfl rfl

noncomputable def ep1528 := ep1520 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz518 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1527 rfl rfl rfl) rfl)

noncomputable def ep1529 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))))) Bool.false 2192667 524288 117 16384

noncomputable def ep1530 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))))) Bool.false 4385334 1048576 7488 1048576

noncomputable def ep1531 := nat_lit 348300125303149832450986001128228127651621

noncomputable def ep1532 := nat_lit 19913462825645753837971841404244695449600

noncomputable def ep1533 := nat_lit 6739751707536716150001252276051182135478142305156118287

noncomputable def ep1534 := nat_lit 112840638068498007481750408116580791196057600000000000000

noncomputable def ep1535 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37)))) ep1531 ep1532 ep1533 ep1534 2188923 2196411

noncomputable def ep1536 := nat_lit 2775420959611921906952174718543233320760209

noncomputable def ep1537 := nat_lit 158682147283825323021211511413941737619456

noncomputable def ep1538 := nat_lit 407982774469395082572202779089390195749191481126374173

noncomputable def ep1539 := nat_lit 6861930693354608563079416709792075140300800000000000000

noncomputable def ep1540 := nat_lit 112579537593994015892840996862907031204944521

noncomputable def ep1541 := nat_lit 462195253528567838645249671645514920739051929600

noncomputable def ep1542 := nat_lit 276314746359973129325259179230890248422941539701686979

noncomputable def ep1543 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37))) ep1536 ep1537 ep1538 ep1539 ep1540 ep1541 ep1542

noncomputable def ep1544 := nat_lit 1015565742616482067335753673049227120764518400000000000000

noncomputable def ep1545 := nat_lit 1282804258439098920661171419295393545774136214405986349746947926695693916656061663439486976

noncomputable def ep1546 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 37)) (Complex.re (zetaApproximant qz5 1 37)) 1665959471179272688297 398349278000883695616 ep562 ep563 1665959471179272688297 398349278000883695616 ep562 ep563 ep1536

noncomputable def ep1547 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz5 1 37)) (Complex.im (zetaApproximant qz5 1 37)) 10610350493456567049789 679849434454841507184640 ep690 ep691 10610350493456567049789 679849434454841507184640 ep690 ep691 ep1540

noncomputable def ep1548 := @ep1517 504403158265495552 ep1518 5674951780957750015 9079256848778919936 497747966783569 4539628424389459968 (@ep1519 33880265 309237645312 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz518) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow51.d18 EMRow51.d19 rfl) (ep1528 rfl)) (ep1529 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 37)) (@ep1530 2192667 524288 117 16384 (@ep1535 524288 (@ep1543 ep1544 ep1545 ep1531 ep1532 ep1533 ep1534 (@ep1546 ep1537 ep1538 ep1539 ep835 ep835 rfl) (@ep1547 ep1541 ep1542 ep1544 ep843 ep843 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz516)

noncomputable abbrev qz735 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1549 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz735) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 567219936172448967 1008806316530991104 42612027401 504403158265495552 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz12 3)

noncomputable def ep1550 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz735) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 151595121 3670016 1 3670016 3741676727 274877906944 1075 549755813888

noncomputable def ep1551 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz735 151595121 1048576 1 1048576 2 7 0 1 151595121 3670016

noncomputable abbrev qz521 := (Complex.re qz733)

noncomputable abbrev qz522 := (Complex.im qz733)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz267 qz521 qz521) (@HMul.hMul Real Real Real qz267 qz522 qz522))

noncomputable abbrev qz227 := qz516

noncomputable def ep1552 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 151595121 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1553 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 151595121 1048576 1 1048576 151595121

noncomputable def ep1554 := @Enclosure.Real.IsNear.sqrt_image qz226 209011709 10000 0 1 75797560 75797561 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz521 qz521)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz522 qz522)

noncomputable def ep1555 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 208889209 10000 0 1

noncomputable abbrev qz230 := qz521

noncomputable def ep1556 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1557 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz12) Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 144530 1000 3 qz13)

noncomputable abbrev qz523 := (ep1557 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1558 := @ep1556 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz523)

noncomputable def ep1559 := ep1558 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz523)

noncomputable abbrev qz231 := qz522

noncomputable def ep1560 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 144530 1000 0 1 144530 1000 0 1 208889209 10000

noncomputable def ep1561 := @ep1560 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz523)

noncomputable def ep1562 := ep1561 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 144530 1000 0 1 qz523)

noncomputable def ep1563 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 3741676727 274877906944

noncomputable def ep1564 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 29933413816 2199023255552

noncomputable def ep1565 := nat_lit 1123070813559258995277954308920502554619135673472391029637964077

noncomputable def ep1566 := nat_lit 6061139590338720582374321738240968939117083442230067200000000000000

noncomputable def ep1567 := nat_lit 3688375234795898924840556818316960619510236527561984955222996747502121880617

noncomputable def ep1568 := nat_lit 69302175385455413146484247124835280216080390446114770146820096000000000000000000000000

noncomputable def ep1569 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1565 ep1566 ep1567 ep1568

noncomputable def ep1570 := nat_lit 178451464179074521909148868893544117526985074096664628278961

noncomputable def ep1571 := nat_lit 5986310706507378352962293074805895248510699696029696000000000000

noncomputable def ep1572 := nat_lit 388700527367855698288605569975616003403280296594220630339221350676404406039

noncomputable def ep1573 := nat_lit 46201450256970275430989498083223520144053593630743180097880064000000000000000000000000

noncomputable def ep1574 := nat_lit 1884777412155892083689882158331578271246126571899036187011032129

noncomputable def ep1575 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1570 ep1571 ep1572 ep1573 ep1574

noncomputable def ep1576 := nat_lit 12122279180677441164748643476481937878234166884460134400000000000000

noncomputable def ep1577 := nat_lit 6210648887488230754815296926707073228810632165341308019428329442975030543117

noncomputable def ep1578 := nat_lit 138604350770910826292968494249670560432160780892229540293640192000000000000000000000000

noncomputable def ep1579 := nat_lit 13446101670751487817005881350079275273849783939823384922387139954970791826302802961656080648475354928397899146461184000000000000

noncomputable def ep1580 := nat_lit 422435159733508122096336569031

noncomputable def ep1581 := nat_lit 77371252455336267181195264000000

noncomputable def ep1582 := nat_lit 5236931203745017232597814502744483

noncomputable def ep1583 := nat_lit 6797164869044319086089504555008000000000000

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1580 ep1581 ep1582 ep1583 ep1580 ep1581 ep1582

noncomputable def ep1585 := nat_lit 43414023220105874952469688995873

noncomputable def ep1586 := nat_lit 3481706360490132023153786880000000

noncomputable def ep1587 := nat_lit 36638801014971874581921780717689699

noncomputable def ep1588 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1580 ep1581 ep1582 ep1583 Bool.false ep1585 ep1586 ep1587

noncomputable def ep1589 := nat_lit 20391494607132957258268513665024000000000000

noncomputable def ep1590 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1580 ep1581 ep1582 ep1583 Bool.false ep1585 ep1586 ep1587 ep1589

noncomputable def ep1591 := nat_lit 9127786485890957384357765173

noncomputable def ep1592 := nat_lit 23211375736600880154358579200000

noncomputable def ep1593 := nat_lit 7512734607563152679271292735499

noncomputable def ep1594 := nat_lit 135943297380886381721790091100160000000000

noncomputable def ep1595 := nat_lit 1176027614341614792445432055363

noncomputable def ep1596 := nat_lit 232113757366008801543585792000000

noncomputable def ep1597 := nat_lit 1620431491122286532878083288656511

noncomputable abbrev qz232 := (Complex.re qz517)

noncomputable abbrev qz233 := (Complex.im qz517)

noncomputable def ep1598 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1591 ep1592 ep1593 ep1594 ep1595 ep1596 ep1597

noncomputable def ep1599 := nat_lit 2265721623014773028696501518336000000000000

noncomputable def ep1600 := nat_lit 29415903650776402666118980541670760523597956801883642265600000

noncomputable def ep1601 := nat_lit 4835703278458516698824704

noncomputable def ep1602 := nat_lit 28321520287684662858706268979200000

noncomputable def ep1603 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 626655127 4800000 0 1 14565884954278778899 ep1601 11988627051579445035437 ep1602 ep1591

noncomputable def ep1604 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 626655127 4800000 0 1 0 1 0 1 626655127

noncomputable def ep1605 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1879965381 20000 0 1 626655127 4800000 0

noncomputable def ep1606 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow51.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz524 := (@HAdd.hAdd Complex Complex Complex qz546 qz545 qz555)

noncomputable abbrev qz234 := qz524

noncomputable def ep1607 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1

noncomputable abbrev qz235 := (Complex.re qz524)

noncomputable abbrev qz236 := (Complex.im qz524)

noncomputable def ep1608 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 208881709 4000 0 1 208889209 5000 0 1

noncomputable def ep1609 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 208881709 10000 0 1 5 2 0 1 208881709 4000

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz546 qz545 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz525

noncomputable def ep1610 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1

noncomputable abbrev qz238 := (Complex.re qz525)

noncomputable abbrev qz239 := (Complex.im qz525)

noncomputable def ep1611 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 208889209 10000 0 1

noncomputable def ep1612 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1613 := @ep1612 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep1614 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz12) Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 144530 1000 1 qz13)

noncomputable abbrev qz526 := (ep1614 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1615 := ep1613 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz526)

noncomputable def ep1616 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 144530 1000 0 1 144530 1000 0 1 208889209 10000

noncomputable def ep1617 := @ep1616 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep1618 := ep1617 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz526)

noncomputable def ep1619 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 (@ep1611 835526836 208881709 10000 0 1 (ep1615 rfl) (ep1618 rfl) rfl rfl)

noncomputable def ep1620 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 14453 200 0 1 43359 200 0 1

noncomputable def ep1621 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 144530 1000 0 1 14453 200

noncomputable def ep1622 := @ep1621 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep1623 := ep1622 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz526)

noncomputable def ep1624 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 144530 1000 0 1 3 2 0 1 43359 200

noncomputable def ep1625 := @ep1624 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 144530 1000 0 1 ep799)

noncomputable def ep1626 := ep1625 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 144530 1000 0 1 qz526)

noncomputable abbrev qz240 := (ep1610 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1619 (@ep1620 11562400 14453 50 0 1 (ep1623 rfl) (ep1626 rfl) rfl rfl)))

noncomputable def ep1627 := @ep1609 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz240)

noncomputable def ep1628 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz12) Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 144530 1000 2 qz13)

noncomputable abbrev qz527 := (ep1628 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1629 := ep1627 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1630 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 14453 50 0 1 144530 1000 0 1 208889209 5000

noncomputable def ep1631 := @ep1630 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz240)

noncomputable def ep1632 := ep1631 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1633 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 (@ep1608 1879965381000 1879965381 20000 0 1 (ep1629 rfl) (ep1632 rfl) rfl rfl)

noncomputable def ep1634 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 3018967340177 1000000 0 1 14453 20 0 1

noncomputable def ep1635 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 208881709 10000 0 1 144530 1000 0 1 3018967340177 1000000

noncomputable def ep1636 := @ep1635 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz240)

noncomputable def ep1637 := ep1636 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable def ep1638 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 14453 50 0 1 5 2 0 1 14453 20

noncomputable def ep1639 := @ep1638 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 208881709 10000 0 1 Bool.false 14453 50 0 1 qz240)

noncomputable def ep1640 := ep1639 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 144530 1000 0 1 qz527)

noncomputable abbrev qz241 := (ep1607 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1633 (@ep1634 60364893803540 3018244690177 1000000 0 1 (ep1637 rfl) (ep1640 rfl) rfl rfl)))

noncomputable def ep1641 := @ep1605 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz241)

noncomputable def ep1642 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3018244690177 1000000 0 1 0 1 0

noncomputable def ep1643 := @ep1642 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz241)

noncomputable def ep1644 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 3018244690177 720000000 0 1 0 1 0 1 3018244690177

noncomputable def ep1645 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3018244690177 1000000 0 1 3018244690177 720000000 0

noncomputable def ep1646 := @ep1645 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz241)

noncomputable def ep1647 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1879965381 20000 0 1 0 1 0

noncomputable def ep1648 := @ep1647 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1879965381 20000 0 1 Bool.true 3018244690177 1000000 0 1 qz241)

noncomputable def ep1649 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 (@ep1604 626655127 4800000 0 1 (ep1641 rfl) (ep1643 rfl) rfl rfl) (@ep1644 3018244690177 720000000 0 1 (ep1646 rfl) (ep1648 rfl) rfl rfl)

noncomputable def ep1650 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 ep1649

noncomputable def ep1651 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.false 14565884954278778899 ep1601 11988627051579445035437 ep1602 Bool.true 5844593803986690285 ep1601 4831908913006430541687 ep1602

noncomputable abbrev qz736 := (@Nat.cast Real Real.instNatCast 94931877133)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz736))

noncomputable def ep1652 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz242 qz686)) Bool.false 14565884954278778899 ep1601 11988627051579445035437 ep1602 Bool.true 5844593803986690285 ep1601 4831908913006430541687

noncomputable def ep1653 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz736) 677541430085473957 2199023255552 1 2199023255552 3568566 3568567 1099511627776 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz736) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz736 qz14)) Bool.false 677541430085473957 2199023255552 1 2199023255552 (BSN.sqrt_natCast_div_one 94931877133) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz736 qz14)) Bool.false 677541430085473957 2199023255552 1 2199023255552 677541430085473957 2199023255552 1 2199023255552 (BSN.sqrt_enclosure 94931877133 1 338770715042736978 338770715042736979 1099511627776 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1654 := nat_lit 143043195604289387581424009216

noncomputable def ep1655 := nat_lit 39614081257132168796771975168

noncomputable def ep1656 := nat_lit 374832200000000000000000000

noncomputable def ep1657 := BSN.log_dyadic_bound 5 69 5 4 485539463835065745 1099511627776 374832200000 852543171681000 41015625 159629307967 74 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 69) 0 4 852543171681000 485539463835065745 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz132 144530 1000 0 1 16262128565846227 4503599627370496 1001874161 374832200000000000000 235036544162175518831 450359962737049600 14480087248933 37483220000000000000000 qz18 (BSN.isNear_log_sfrac 37 1 16262128565846227 4503599627370496 1001874161 374832200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz456 Bool.false ep1654 ep1655 1001874161000000 ep1656 16262128565846227 4503599627370496 1001874161 374832200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 159629307967 1099511627776 24973259072661432 36028797018963968 374832200000 1000000000000000 rfl rfl rfl rfl (ep1657 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1659 := nat_lit 472379867898568725227372544

noncomputable def ep1660 := nat_lit 1237940039285380274899124224

noncomputable def ep1661 := nat_lit 6027816752419108559737546475189691918491003299406953268122166743142273471680676158444430668832231826025716559427254764391366656

noncomputable def ep1662 := nat_lit 6823366825375442818493753656289620051425606865182673602958602092918794624677906806699937015021905992974048683225329102547866091520

noncomputable def ep1663 := nat_lit 76069815190264354728718122191176085105730756614790952849235958100908097861353007047332634673582560866291704100101162008576

noncomputable def ep1664 := nat_lit 18083298117626945150503181989324693403302798436707630222460801757510618598846305769319197341227348312955417094873564090850082816

noncomputable def ep1665 := nat_lit 307051507141894926832218914533032902314152308933220312133137094181345758110505806301497165675985769683832190745139809614653974118400

noncomputable def ep1666 := BSN.cos_dyadic_bound_f 1718507948311776 4503599627370496 3 2 2199023255552 750396494141 ep1661 ep1662 ep1663 ep1664 ep1665 ep1663 2040859397503 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1718507948311776) (BSN.cosEvenQ 4503599627370496) 0 2 ep1661 ep1662 ep1663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1718507948311776) (BSN.cosOddQ 4503599627370496) 0 2 ep1664 ep1665 ep1663 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz528 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4482966311687) (@Nat.cast Real Real.instNatCast 8589934592))

noncomputable def ep1667 := @Enclosure.Real.IsNear.cos_image qz130 qz528 Bool.false 4482966311687 8589934592 851 2199023255552 Bool.false 2040859397503 2199023255552 1 374832200000 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 235036544162175518831 450359962737049600 14480087248933 37483220000000000000000 4482966311687 8589934592 851 2199023255552 (ep1658 rfl) rfl) (Enclosure.sfrac_false_div 4482966311687 8589934592) (BSN.cos_reduce0 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1659) (@Nat.cast Real Real.instNatCast ep1660)) 226375608064910080 72057594037927936 Bool.false 2040859397503 2199023255552 83 1000000000000000 749664400000 374832200000 (BSN.sin_reduce_arg_pos_rat_q0 4482966311687 8589934592 226375608064910080 72057594037927936 83 ep1659 ep1660 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 2040859397503 2199023255552 ep1659 ep1660 1718507948311776 4503599627370496 750396494141 749664400000 (ep1666 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1668 := nat_lit 10850009298502243196043800680843692512415721354327224049857620748889611522546928002794337337790278420797596773605778494974853120

noncomputable def ep1669 := nat_lit 61410301428378985366443782906606580462830461786644062426627418836269151622101161260299433135197153936766438149027961922930794823680

noncomputable def ep1670 := nat_lit 28416567859233662228302298144297551818855765697251067611893917484112057279273988292926140203280305301752303268113257799243268096

noncomputable def ep1671 := nat_lit 1125855526186948065051469353287787308485225132755141144488169345331601113071854623105489607478614488840718032732179301920397905100800

noncomputable def ep1672 := BSN.sin_dyadic_bound_f 1718507948311776 4503599627370496 3 2 2199023255552 750396494141 ep1668 ep1669 ep1663 ep1670 ep1671 ep1663 818899382145 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1718507948311776) (BSN.sinEvenQ 4503599627370496) 0 2 ep1668 ep1669 ep1663 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1718507948311776) (BSN.sinOddQ 4503599627370496) 0 2 ep1670 ep1671 ep1663 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1673 := @Enclosure.Real.IsNear.sin_image qz130 qz528 Bool.false 4482966311687 8589934592 851 2199023255552 Bool.false 818899382145 2199023255552 1 374832200000 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 235036544162175518831 450359962737049600 14480087248933 37483220000000000000000 4482966311687 8589934592 851 2199023255552 (ep1658 rfl) rfl) (Enclosure.sfrac_false_div 4482966311687 8589934592) (BSN.sin_reduce0 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1659) (@Nat.cast Real Real.instNatCast ep1660)) 226375608064910080 72057594037927936 Bool.false 818899382145 2199023255552 83 1000000000000000 749664400000 374832200000 (BSN.sin_reduce_arg_pos_rat_q0 4482966311687 8589934592 226375608064910080 72057594037927936 83 ep1659 ep1660 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 818899382145 2199023255552 ep1659 ep1660 1718507948311776 4503599627370496 750396494141 749664400000 (ep1672 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz529 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 7137133 2199023255552 1 2199023255552 7137133 2199023255552 1 2199023255552 (ep1653 rfl rfl) rfl)

noncomputable def ep1674 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz242 qz686) Bool.false 14565884954278778899 ep1601 11988627051579445035437 ep1602 Bool.true 5844593803986690285 ep1601 4831908913006430541687 ep1602 (@Enclosure.Real.IsNear.mulLit_ff qz242 (Real.cos qz130) 7137133 2199023255552 1 2199023255552 2040859397503 2199023255552 5018456647743 12879136323901849600000 14565884954278778899 ep1601 11988627051579445035437 ep1602 qz529 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.false 2040859397503 2199023255552 321181225455552 824264724729718374400000 2040859397503 2199023255552 5018456647743 12879136323901849600000 (ep1667 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz686 7137133 2199023255552 1 2199023255552 818899382145 2199023255552 5018456647743 12879136323901849600000 5844593803986690285 ep1601 4831908913006430541687 ep1602 qz529 (@Enclosure.Real.IsNear.neg qz131 Bool.false 818899382145 2199023255552 5018456647743 12879136323901849600000 (@Enclosure.Real.IsNear.recentre' qz131 Bool.false 818899382145 2199023255552 321181225455552 824264724729718374400000 818899382145 2199023255552 5018456647743 12879136323901849600000 (ep1673 rfl rfl) rfl)) rfl)

noncomputable def ep1675 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 3018244690177 720000000 0 1 5844593803986690285 ep1601 4831908913006430541687 ep1602 ep1595

noncomputable def ep1676 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 626655127 4800000 0 1 Bool.false 3018244690177 720000000 0 1 ep1649

noncomputable def ep1677 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.false 14565884954278778899 ep1601 11988627051579445035437 ep1602 Bool.true 5844593803986690285 ep1601 4831908913006430541687 ep1602

noncomputable def ep1678 := nat_lit 244169644833379500457089413

noncomputable def ep1679 := nat_lit 1547425049106725343623905280000

noncomputable def ep1680 := nat_lit 1009313497844158894305848593083

noncomputable def ep1681 := nat_lit 45314432460295460573930030366720000000000

noncomputable def ep1682 := nat_lit 43963404920980978828498140175123

noncomputable def ep1683 := nat_lit 36184609940942003079484148850802349

noncomputable def ep1684 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1678 ep1679 ep1680 ep1681 ep1682 ep1586 ep1683

noncomputable def ep1685 := nat_lit 67179947013292847879775283479137631619830459513922062909440000

noncomputable def ep1686 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 626655127 4800000 0 1 5844593803986690285 ep1601 4831908913006430541687 ep1602 ep1678

noncomputable def ep1687 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 3018244690177 720000000 0 1 14565884954278778899 ep1601 11988627051579445035437 ep1602 ep1682

noncomputable abbrev qz530 := (@ep1652 ep1602 (BSN.cpow_neg_s_sub_mk qz12 144530 1000 37 3 94931877133 qz13 rfl EMRow51.d21) ep1674)

noncomputable def ep1688 := ep1590 (@ep1598 ep1599 ep1600 ep1580 ep1581 ep1582 ep1583 (@ep1603 ep1592 ep1593 ep1594 ep1650 (ep1651 qz530) rfl) (@ep1675 ep1596 ep1597 ep1599 ep1676 (ep1677 qz530) rfl) rfl rfl) (@ep1684 ep1589 ep1685 ep1585 ep1586 ep1587 ep1589 (@ep1686 ep1679 ep1680 ep1681 ep1650 (ep1677 qz530) rfl) (@ep1687 ep1586 ep1683 ep1589 ep1676 (ep1651 qz530) rfl) rfl rfl)

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1585 ep1586 ep1587 ep1589 ep1585 ep1586 ep1587

noncomputable def ep1690 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1580 ep1581 ep1582 ep1583 Bool.false ep1585 ep1586 ep1587

noncomputable def ep1691 := @ep1550 567219936172448967 1008806316530991104 42612027401 504403158265495552 (@ep1551 1 3670016 (ep1552 (@ep1553 1048576 1 1048576 (ep1554 (@ep1555 836046836 209011709 10000 0 1 (ep1559 rfl) (ep1562 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1563 1075 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1564 4300 2199023255552 3741676727 274877906944 1075 549755813888 (@ep1569 14966704758 14966709058 1099511627776 (@ep1575 ep1576 ep1577 ep1578 ep1579 ep1565 ep1566 ep1567 ep1568 (@ep1584 ep1583 ep1570 ep1571 ep1572 ep1573 (@ep1588 ep1589 ep1688) (@ep1588 ep1589 ep1688) rfl) (@ep1689 ep1589 ep1574 ep1576 ep1577 ep1578 (@ep1690 ep1589 ep1688) (@ep1690 ep1589 ep1688) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow51.d22 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 5674951780957750015 9079256848778919936 497747966783569 4539628424389459968 := ep1548 (ep1549 ep1691) rfl rfl

noncomputable abbrev qz737 := (@HAdd.hAdd Complex Complex Complex qz739 qz745 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz531 := qz737

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz531) (@HAdd.hAdd Real Real Real qz424 (Complex.re qz460) qz287))

noncomputable abbrev qz532 := (@HPow.hPow Complex Complex Complex qz547 qz671 (@HSub.hSub Complex Complex Complex qz658 qz689 qz554))

noncomputable abbrev qz244 := qz532

noncomputable def ep1692 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 5152648073 309237645312 3774667 34359738368 1198532317954556775 2017612633061982208 178549731861

noncomputable def ep1693 := nat_lit 381027359680407716035228073984

noncomputable def ep1694 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37)) 26561 1769472 1 1769472 581979 524288 3815 524288 5152648073 309237645312

noncomputable def ep1695 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 37)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 37)) (Complex.im (zetaApproximant qz141 1 37))))) Bool.false 581979 524288 3815 524288

noncomputable def ep1696 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 37)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 37)) (Complex.im (zetaApproximant qz141 1 37))))) Bool.false 1163958 1048576 7630 1048576

noncomputable def ep1697 := nat_lit 25221855232500146725278921368541248968793

noncomputable def ep1698 := nat_lit 20468392699864213423850387130453432729600

noncomputable def ep1699 := nat_lit 5776903902133533928441683785398175266841909730256744261

noncomputable def ep1700 := nat_lit 357652029552588636818991422652654543490252800000000000000

noncomputable def ep1701 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 37)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 37)) (Complex.im (zetaApproximant qz141 1 37)))) ep1697 ep1698 ep1699 ep1700 578164 585794

noncomputable def ep1702 := nat_lit 601709731593089604554183038675606987994610095929

noncomputable def ep1703 := nat_lit 488314237682467685470196289061757670045358489600

noncomputable def ep1704 := nat_lit 1912587801867372415987489641509608167268543343864428731

noncomputable def ep1705 := nat_lit 119217343184196212272997140884218181163417600000000000000

noncomputable def ep1706 := nat_lit 17580752292851330953423835322440157826096369

noncomputable def ep1707 := nat_lit 1098707034785552292307941650388954757602056601600

noncomputable def ep1708 := nat_lit 9785124132854170119803715217337691259069924665864517

noncomputable def ep1709 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz141 1 37)) (Complex.re (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz141 1 37)) (Complex.im (zetaApproximant qz141 1 37))) ep1702 ep1703 ep1704 ep1705 ep1706 ep1707 ep1708

noncomputable def ep1710 := nat_lit 89413007388147159204747855663163635872563200000000000000

noncomputable def ep1711 := nat_lit 661111299931907801266462259474221626076936324499569970590741999708418149663548115305825619148800

noncomputable def ep1712 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz141 1 37)) (Complex.re (zetaApproximant qz141 1 37)) 775699511146609918085077 698794846634166074736640 ep1262 ep1263 775699511146609918085077 698794846634166074736640 ep1262 ep1263 ep1702

noncomputable def ep1713 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (zetaApproximant qz141 1 37)) (Complex.im (zetaApproximant qz141 1 37)) 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 4192940769060699592537 1048192269951249112104960 ep1377 ep1378 ep1706

noncomputable def ep1714 := @ep1692 2017612633061982208 ep1693 11089355675515477663 18158513697557839872 221827962286613 2017612633061982208 (@ep1694 3774667 34359738368 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz518) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow51.d18 EMRow51.d19 rfl) (ep1528 rfl)) (ep1695 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz141 1 37)) (@ep1696 581979 524288 3815 524288 (@ep1701 524288 (@ep1709 ep1710 ep1711 ep1697 ep1698 ep1699 ep1700 (@ep1712 ep1703 ep1704 ep1705 ep1508 ep1508 rfl) (@ep1713 ep1707 ep1708 ep1710 ep1516 ep1516 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz531)

noncomputable def ep1715 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz735) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 1198532317954556775 2017612633061982208 178549731861 2017612633061982208 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz144 3)

noncomputable def ep1716 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz735) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 153691665 3670016 1 3670016 7798290935 549755813888 1111 549755813888

noncomputable def ep1717 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz735 153691665 1048576 1 1048576 2 7 0 1 153691665 3670016

noncomputable abbrev qz533 := (Complex.re qz737)

noncomputable abbrev qz534 := (Complex.im qz737)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz267 qz533 qz533) (@HMul.hMul Real Real Real qz267 qz534 qz534))

noncomputable abbrev qz247 := qz531

noncomputable def ep1718 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 153691665 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1719 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 153691665 1048576 1 1048576 153691665

noncomputable def ep1720 := @Enclosure.Real.IsNear.sqrt_image qz246 214832909 10000 0 1 76845832 76845833 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz533 qz533)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz534 qz534)

noncomputable def ep1721 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 214710409 10000 0 1

noncomputable abbrev qz250 := qz533

noncomputable def ep1722 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1723 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk (Enclosure.sfrac Bool.false 7 2) qz144) Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz144 Bool.false 146530 1000 3 qz145)

noncomputable abbrev qz535 := (ep1723 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz144 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz146))

noncomputable def ep1724 := @ep1722 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz535)

noncomputable def ep1725 := ep1724 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz535)

noncomputable abbrev qz251 := qz534

noncomputable def ep1726 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 146530 1000 0 1 146530 1000 0 1 214710409 10000

noncomputable def ep1727 := @ep1726 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz535)

noncomputable def ep1728 := ep1727 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 146530 1000 0 1 qz535)

noncomputable def ep1729 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 7798290935 549755813888

noncomputable def ep1730 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 31193163740 2199023255552

noncomputable def ep1731 := nat_lit 243917796018237683148756586980413930810730577638736988392998113

noncomputable def ep1732 := nat_lit 1212227918067744116474864347648193787823416688446013440000000000000

noncomputable def ep1733 := nat_lit 3971871734520861765160951261534790879835349881149452282561297647141403342417

noncomputable def ep1734 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1731 ep1732 ep1733 ep1568

noncomputable def ep1735 := nat_lit 2323167872585496354966765655804967263793228833172690142312759841

noncomputable def ep1736 := nat_lit 7465696654316726210043717037124370833090097583516479713162016456814300829917

noncomputable def ep1737 := nat_lit 116010087596880476520800213999172044314076943214679741617221289

noncomputable def ep1738 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1735 ep1576 ep1736 ep1578 ep1737

noncomputable def ep1739 := nat_lit 478046814724997320278185485945210926580602178782424851960578837468505854917

noncomputable def ep1740 := nat_lit 29568396204686095225631257853283933522688142054189065732016508188662304386821773970984130748082104104511090429263872000000000000000

noncomputable def ep1741 := nat_lit 48199251784498650606921597720721

noncomputable def ep1742 := nat_lit 39670196687947394620738000166126999

noncomputable def ep1743 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1741 ep1586 ep1742 ep1589 ep1741 ep1586 ep1742

noncomputable def ep1744 := nat_lit 10770797909016790967709908225267

noncomputable def ep1745 := nat_lit 11367287739586857408055102772945749

noncomputable def ep1746 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1741 ep1586 ep1742 ep1589 Bool.false ep1744 ep1586 ep1745

noncomputable def ep1747 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1741 ep1586 ep1742 ep1589 Bool.false ep1744 ep1586 ep1745 ep1589

noncomputable def ep1748 := nat_lit 2506560562847007931006834567

noncomputable def ep1749 := nat_lit 2080284998650341712837089934949

noncomputable def ep1750 := nat_lit 47823267700071599417270572535671

noncomputable def ep1751 := nat_lit 39358153938149843363812436675884649

noncomputable abbrev qz252 := (Complex.re qz532)

noncomputable abbrev qz253 := (Complex.im qz532)

noncomputable def ep1752 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1748 ep1592 ep1749 ep1594 ep1750 ep1586 ep1751

noncomputable def ep1753 := nat_lit 1118770943393028653474479220124059665465718344444451959603200000

noncomputable def ep1754 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 644118727 4800000 0 1 3891457363025881921 ep1601 3229660793033178979187 ep1602 ep1748

noncomputable def ep1755 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 644118727 4800000 0 1 0 1 0 1 644118727

noncomputable def ep1756 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 1932356181 20000 0 1 644118727 4800000 0

noncomputable abbrev qz536 := (@HAdd.hAdd Complex Complex Complex qz546 qz688 qz555)

noncomputable abbrev qz254 := qz536

noncomputable def ep1757 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1

noncomputable abbrev qz255 := (Complex.re qz536)

noncomputable abbrev qz256 := (Complex.im qz536)

noncomputable def ep1758 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 214702909 4000 0 1 214710409 5000 0 1

noncomputable def ep1759 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 214702909 10000 0 1 5 2 0 1 214702909 4000

noncomputable abbrev qz537 := (@HAdd.hAdd Complex Complex Complex qz546 qz688 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz537

noncomputable def ep1760 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz72 (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1

noncomputable abbrev qz258 := (Complex.re qz537)

noncomputable abbrev qz259 := (Complex.im qz537)

noncomputable def ep1761 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 214710409 10000 0 1

noncomputable def ep1762 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1763 := @ep1762 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1764 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk (Enclosure.sfrac Bool.false 3 2) qz144) Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz144 Bool.false 146530 1000 1 qz145)

noncomputable abbrev qz538 := (ep1764 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz144 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz146))

noncomputable def ep1765 := ep1763 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz538)

noncomputable def ep1766 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 146530 1000 0 1 146530 1000 0 1 214710409 10000

noncomputable def ep1767 := @ep1766 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1768 := ep1767 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz538)

noncomputable def ep1769 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 (@ep1761 858811636 214702909 10000 0 1 (ep1765 rfl) (ep1768 rfl) rfl rfl)

noncomputable def ep1770 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 14653 200 0 1 43959 200 0 1

noncomputable def ep1771 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 146530 1000 0 1 14653 200

noncomputable def ep1772 := @ep1771 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1773 := ep1772 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz538)

noncomputable def ep1774 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 146530 1000 0 1 3 2 0 1 43959 200

noncomputable def ep1775 := @ep1774 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 146530 1000 0 1 ep1473)

noncomputable def ep1776 := ep1775 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 146530 1000 0 1 qz538)

noncomputable abbrev qz260 := (ep1760 (BSN.ascPochhammer_succ_eval_c 1 2 qz460 rfl) (ep1769 (@ep1770 11722400 14653 50 0 1 (ep1773 rfl) (ep1776 rfl) rfl rfl)))

noncomputable def ep1777 := @ep1759 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz260)

noncomputable def ep1778 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk (Enclosure.sfrac Bool.false 5 2) qz144) Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 (BSN.s_add_nat_mk qz144 Bool.false 146530 1000 2 qz145)

noncomputable abbrev qz539 := (ep1778 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz144 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz146))

noncomputable def ep1779 := ep1777 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz539)

noncomputable def ep1780 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 14653 50 0 1 146530 1000 0 1 214710409 5000

noncomputable def ep1781 := @ep1780 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz260)

noncomputable def ep1782 := ep1781 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz539)

noncomputable def ep1783 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 (@ep1758 1932356181000 1932356181 20000 0 1 (ep1779 rfl) (ep1782 rfl) rfl rfl)

noncomputable def ep1784 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 3146041725577 1000000 0 1 14653 20 0 1

noncomputable def ep1785 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 214702909 10000 0 1 146530 1000 0 1 3146041725577 1000000

noncomputable def ep1786 := @ep1785 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz260)

noncomputable def ep1787 := ep1786 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz539)

noncomputable def ep1788 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 14653 50 0 1 5 2 0 1 14653 20

noncomputable def ep1789 := @ep1788 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 214702909 10000 0 1 Bool.false 14653 50 0 1 qz260)

noncomputable def ep1790 := ep1789 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 146530 1000 0 1 qz539)

noncomputable abbrev qz261 := (ep1757 (BSN.ascPochhammer_succ_eval_c 2 3 qz460 rfl) (ep1783 (@ep1784 62906181511540 3145309075577 1000000 0 1 (ep1787 rfl) (ep1790 rfl) rfl rfl)))

noncomputable def ep1791 := @ep1756 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz261)

noncomputable def ep1792 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 3145309075577 1000000 0 1 0 1 0

noncomputable def ep1793 := @ep1792 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz261)

noncomputable def ep1794 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) 3145309075577 720000000 0 1 0 1 0 1 3145309075577

noncomputable def ep1795 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 3145309075577 1000000 0 1 3145309075577 720000000 0

noncomputable def ep1796 := @ep1795 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz261)

noncomputable def ep1797 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 1932356181 20000 0 1 0 1 0

noncomputable def ep1798 := @ep1797 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1606) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 1932356181 20000 0 1 Bool.true 3145309075577 1000000 0 1 qz261)

noncomputable def ep1799 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 (@ep1755 644118727 4800000 0 1 (ep1791 rfl) (ep1793 rfl) rfl rfl) (@ep1794 3145309075577 720000000 0 1 (ep1796 rfl) (ep1798 rfl) rfl rfl)

noncomputable def ep1800 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 ep1799

noncomputable def ep1801 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.false 3891457363025881921 ep1601 3229660793033178979187 ep1602 Bool.true 15204632216087866223 ep1601 12513286609497884397937 ep1602

noncomputable def ep1802 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz731)) Bool.false 3891457363025881921 ep1601 3229660793033178979187 ep1602 Bool.true 15204632216087866223 ep1601 12513286609497884397937

noncomputable def ep1803 := @Enclosure.Real.IsNear.mulLit_ff qz144 qz132 146530 1000 0 1 16262128565846227 4503599627370496 1001874161 374832200000000000000 238288969875344764231 450359962737049600 14680462081133 37483220000000000000000 qz146 (BSN.isNear_log_sfrac 37 1 16262128565846227 4503599627370496 1001874161 374832200000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz456 Bool.false ep1654 ep1655 1001874161000000 ep1656 16262128565846227 4503599627370496 1001874161 374832200000000000000 (BSN.log_rat_reduce_isNear 37 1 5 74 64 159629307967 1099511627776 24973259072661432 36028797018963968 374832200000 1000000000000000 rfl rfl rfl rfl (ep1657 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1804 := nat_lit 13074983417274546722749546496

noncomputable def ep1805 := nat_lit 9903520314283042199192993792

noncomputable def ep1806 := nat_lit 75989890405053452823187494706919790316820510111541159662016680614296795544180456132539287722392635749826833430166470240197284047259279660254292556347894153852684229442747053629386004159533574710475130773232697255028219168050698245869760652935995094224471081353216

noncomputable def ep1807 := nat_lit 599205769308871494669005633404748773453705986173265619753359186119574540201718521016582654337481038554791270797803930120647421245947038870502085995962344054183037643944802456687515051311778021064186337694386596224481457310393291043136983312363285164951074766848000

noncomputable def ep1808 := nat_lit 2439951491001793962520946763958614168776664871540358260622396292511440484019442282428452580872827311737272296330374288042981992442822648642916868709732522910604082861374721585496044790407011309830495212980616447249538980627727505688694014784401504731136

noncomputable def ep1809 := nat_lit 774163808537946698102025004422919796013783879702612343768063397689358483108794689502990285206873369366889737781223638823574820867762114235594472394240007467078132509556932919666970947181664507079841871858839467026465978480034742108704408344065768395775404656295936

noncomputable def ep1810 := nat_lit 91678482704257338684357861910926562338417015884509639822263955476294904650862933715537146113634598898883064432064001308459055450629896947186819157382238640290004759523554775873189802850702037222820509667241149222345662968490173529599958446791582630237514439327744000

noncomputable def ep1811 := BSN.cos_dyadic_bound_f 5945814071890048 4503599627370496 5 4 2199023255552 750396494141 ep1806 ep1807 ep1808 ep1809 ep1810 ep1808 545240976037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 5945814071890048) (BSN.cosEvenQ 4503599627370496) 0 4 ep1806 ep1807 ep1808 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 5945814071890048) (BSN.cosOddQ 4503599627370496) 0 4 ep1809 ep1810 ep1808 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz540 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36360011272483) (@Nat.cast Real Real.instNatCast 68719476736))

noncomputable def ep1812 := @Enclosure.Real.IsNear.cos_image qz217 qz540 Bool.false 36360011272483 68719476736 863 2199023255552 Bool.false 545240976037 2199023255552 1 374832200000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 238288969875344764231 450359962737049600 14680462081133 37483220000000000000000 36360011272483 68719476736 863 2199023255552 (ep1803 rfl) rfl) (Enclosure.sfrac_false_div 36360011272483 68719476736) (BSN.cos_reduce0 qz540 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1804) (@Nat.cast Real Real.instNatCast ep1805)) 226375608064910080 72057594037927936 Bool.false 545240976037 2199023255552 84 1000000000000000 749664400000 374832200000 (BSN.sin_reduce_arg_pos_rat_q0 36360011272483 68719476736 226375608064910080 72057594037927936 84 ep1804 ep1805 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 545240976037 2199023255552 ep1804 ep1805 5945814071890048 4503599627370496 750396494141 749664400000 (ep1811 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1813 := nat_lit 10986484475174838424430408912619986187134465237768626971456496837544342795734448276688748564990981378427139414254438973457042499767052381441225439946678134536158685300844331012293595942904079056896

noncomputable def ep1814 := nat_lit 433508493418857668581224415970842172945704524136195884060107236574755230272398559971038183579402879451701676292035087663075723672867783462894129725544215056950382789287271065333206471540875250892800

noncomputable def ep1815 := nat_lit 1952252079571464114815841464646947247459006380781935612524707335170150345903729711351632461791977115693303396972638749468720800233302397216724725813743460921082784185259965358279263095095296

noncomputable def ep1816 := nat_lit 54898331928257910871168104534569748982667322231290206527982420214678140039649444553909806066967714643650459739751299149041666811887720452271620198809546756956543589385329710422225852467161759481856

noncomputable def ep1817 := nat_lit 15172797269660018400342854558979476053099658344766855942103753280116433059533949598986336425279100780809558670221228068207650328550372421201294540394047526993263397625054487286662226503930633781248000

noncomputable def ep1818 := BSN.sin_dyadic_bound_f 5945814071890048 4503599627370496 4 3 2199023255552 750396494141 ep1813 ep1814 ep1815 ep1816 ep1817 ep1815 2130355734731 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 5945814071890048) (BSN.sinEvenQ 4503599627370496) 0 3 ep1813 ep1814 ep1815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 5945814071890048) (BSN.sinOddQ 4503599627370496) 0 3 ep1816 ep1817 ep1815 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1819 := @Enclosure.Real.IsNear.sin_image qz217 qz540 Bool.false 36360011272483 68719476736 863 2199023255552 Bool.false 2130355734731 2199023255552 1 374832200000 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 238288969875344764231 450359962737049600 14680462081133 37483220000000000000000 36360011272483 68719476736 863 2199023255552 (ep1803 rfl) rfl) (Enclosure.sfrac_false_div 36360011272483 68719476736) (BSN.sin_reduce0 qz540 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1804) (@Nat.cast Real Real.instNatCast ep1805)) 226375608064910080 72057594037927936 Bool.false 2130355734731 2199023255552 84 1000000000000000 749664400000 374832200000 (BSN.sin_reduce_arg_pos_rat_q0 36360011272483 68719476736 226375608064910080 72057594037927936 84 ep1804 ep1805 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2130355734731 2199023255552 ep1804 ep1805 5945814071890048 4503599627370496 750396494141 749664400000 (ep1818 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1820 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz731) Bool.false 3891457363025881921 ep1601 3229660793033178979187 ep1602 Bool.true 15204632216087866223 ep1601 12513286609497884397937 ep1602 (@Enclosure.Real.IsNear.mulLit_ff qz242 (Real.cos qz217) 7137133 2199023255552 1 2199023255552 545240976037 2199023255552 5088737685243 12879136323901849600000 3891457363025881921 ep1601 3229660793033178979187 ep1602 qz529 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.false 545240976037 2199023255552 325679211855552 824264724729718374400000 545240976037 2199023255552 5088737685243 12879136323901849600000 (ep1812 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz731 7137133 2199023255552 1 2199023255552 2130355734731 2199023255552 5088737685243 12879136323901849600000 15204632216087866223 ep1601 12513286609497884397937 ep1602 qz529 (@Enclosure.Real.IsNear.neg qz218 Bool.false 2130355734731 2199023255552 5088737685243 12879136323901849600000 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 2130355734731 2199023255552 325679211855552 824264724729718374400000 2130355734731 2199023255552 5088737685243 12879136323901849600000 (ep1819 rfl rfl) rfl)) rfl)

noncomputable def ep1821 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 3145309075577 720000000 0 1 15204632216087866223 ep1601 12513286609497884397937 ep1602 ep1750

noncomputable def ep1822 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 644118727 4800000 0 1 Bool.false 3145309075577 720000000 0 1 ep1799

noncomputable def ep1823 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.false 3891457363025881921 ep1601 3229660793033178979187 ep1602 Bool.true 15204632216087866223 ep1601 12513286609497884397937 ep1602

noncomputable def ep1824 := nat_lit 9793588347529705311705058121

noncomputable def ep1825 := nat_lit 8060042241495923407592341866199

noncomputable def ep1826 := nat_lit 12239836161146246764465666943417

noncomputable def ep1827 := nat_lit 10158281403362468896916251493015899

noncomputable def ep1828 := @Enclosure.Real.IsNear.addLit_tf_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1824 ep1592 ep1825 ep1594 ep1826 ep1586 ep1827

noncomputable def ep1829 := nat_lit 250005037249183836194620794709589518295004946374607660646400000

noncomputable def ep1830 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 644118727 4800000 0 1 15204632216087866223 ep1601 12513286609497884397937 ep1602 ep1824

noncomputable def ep1831 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 3145309075577 720000000 0 1 3891457363025881921 ep1601 3229660793033178979187 ep1602 ep1826

noncomputable abbrev qz541 := (@ep1802 ep1602 (BSN.cpow_neg_s_sub_mk qz144 146530 1000 37 3 94931877133 qz145 rfl EMRow51.d21) ep1820)

noncomputable def ep1832 := ep1747 (@ep1752 ep1589 ep1753 ep1741 ep1586 ep1742 ep1589 (@ep1754 ep1592 ep1749 ep1594 ep1800 (ep1801 qz541) rfl) (@ep1821 ep1586 ep1751 ep1589 ep1822 (ep1823 qz541) rfl) rfl rfl) (@ep1828 ep1589 ep1829 ep1744 ep1586 ep1745 ep1589 (@ep1830 ep1592 ep1825 ep1594 ep1800 (ep1823 qz541) rfl) (@ep1831 ep1586 ep1827 ep1589 ep1822 (ep1801 qz541) rfl) rfl rfl)

noncomputable def ep1833 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1744 ep1586 ep1745 ep1589 ep1744 ep1586 ep1745

noncomputable def ep1834 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1741 ep1586 ep1742 ep1589 Bool.false ep1744 ep1586 ep1745

noncomputable def ep1835 := @ep1716 1198532317954556775 2017612633061982208 178549731861 2017612633061982208 (@ep1717 1 3670016 (ep1718 (@ep1719 1048576 1 1048576 (ep1720 (@ep1721 859331636 214832909 10000 0 1 (ep1725 rfl) (ep1728 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1729 1111 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1730 4444 2199023255552 7798290935 549755813888 1111 549755813888 (@ep1734 15596579648 15596584092 1099511627776 (@ep1738 ep1576 ep1739 ep1578 ep1740 ep1731 ep1732 ep1733 ep1568 (@ep1743 ep1589 ep1735 ep1576 ep1736 ep1578 (@ep1746 ep1589 ep1832) (@ep1746 ep1589 ep1832) rfl) (@ep1833 ep1589 ep1737 ep1576 ep1739 ep1578 (@ep1834 ep1589 ep1832) (@ep1834 ep1589 ep1832) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow51.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 11089355675515477663 18158513697557839872 221827962286613 2017612633061982208 := ep1714 (ep1715 ep1835) rfl rfl

noncomputable def EMRow51.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz542 := (EMRow51.d3 qz557 qz695 (@Enclosure.dec_le_dec qz557 qz695 144530 1000 146530 1000 (@Eq.refl Real qz557) (@Eq.refl Real qz695) rfl rfl rfl) 37 37 1 1)

noncomputable abbrev qz262 := qz542

noncomputable def ep1836 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz12 144530 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 37 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz542)

noncomputable def ep1837 := @Enclosure.Real.IsNear.neg_val qz263 ep547 ep548

noncomputable def ep1838 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 37 qz12) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz542)

noncomputable def ep1839 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1837 ep549 ep550 (@ep1838 ep547 ep548 ep549 ep550 (@Eq.refl Real (hardyZApproximantEM 1 37 qz12)) EMRow51.d12) rfl rfl rfl)

noncomputable def ep1840 := @Enclosure.Real.IsNear.pos_val qz264 ep1247 ep1248

noncomputable def ep1841 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 37 qz144) Bool.false

noncomputable def ep1842 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 37 qz12)

noncomputable def ep1843 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 37 qz12) Bool.true

noncomputable def ep1844 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 37 qz12) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 5674951780957750015 9079256848778919936 497747966783569 4539628424389459968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 37))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1845 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 37 qz144)

noncomputable def ep1846 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 37 qz144) Bool.false

noncomputable def ep1847 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 37 qz144) (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 11089355675515477663 18158513697557839872 221827962286613 2017612633061982208 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz424 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz141 1 37))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz72 (@HMul.hMul Complex Complex Complex qz72 (@HDiv.hDiv Complex Complex Complex qz79 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz141 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1848 := @List.cons EMRow51.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1836 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 37 rfl) (ep1839 (@ep1840 ep1249 ep1250 (@ep1841 ep1247 ep1248 ep1249 ep1250 (@Eq.refl Real (hardyZApproximantEM 1 37 qz144)) EMRow51.d17) rfl rfl rfl)) (ep1842 (hardyZErrorBoundEM 1 37 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 37 qz12 rfl) (@ep1843 Bool.false ep547 ep548 ep549 ep550 5674951780957750015 9079256848778919936 497747966783569 4539628424389459968 (@ep1838 ep547 ep548 ep549 ep550 (@Eq.refl Real (hardyZApproximantEM 1 37 qz12)) EMRow51.d12) (ep1844 EMRow51.d22) rfl rfl rfl rfl rfl)) (ep1845 (hardyZErrorBoundEM 1 37 qz144) (BSN.hardyZErrorBoundEM_le_strong 1 37 qz144 rfl) (@ep1846 Bool.false ep1247 ep1248 ep1249 ep1250 11089355675515477663 18158513697557839872 221827962286613 2017612633061982208 (@ep1841 ep1247 ep1248 ep1249 ep1250 (@Eq.refl Real (hardyZApproximantEM 1 37 qz144)) EMRow51.d17) (ep1847 EMRow51.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow51.d0)

noncomputable abbrev qz543 := (@Enclosure.dec_le_dec qz557 qz695 144530 1000 146530 1000 (@Eq.refl Real qz557) (@Eq.refl Real qz695) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1848 (@List.IsChain.singleton EMRow51.d1 EMRow51.d24 (EMRow51.d2 qz277 qz462 qz543))))

noncomputable abbrev qz544 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1849 := And (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz544 qz265)) (@Option.some Real qz12))

noncomputable def ep1850 := ep1849 (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz544 qz265)) (@Option.some Real qz144))

noncomputable def ep1851 := @And.intro (@Eq Nat (@List.length qz544 qz265) 1) ep1850

noncomputable def ep1852 := @And.intro (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz544 qz265)) (@Option.some Real qz12))

noncomputable def ep1853 := @ep1852 (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz544 qz265)) (@Option.some Real qz144))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1848 (@List.IsChain.singleton EMRow51.d1 EMRow51.d24 (EMRow51.d2 qz277 qz462 qz543)))

theorem EMRow51.d25 : Zeta.Certificates.BatchSpec 1 144530 1000 146530 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz544 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz544 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz544 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz544 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz144)))) qz266 (ep1851 (@Eq.refl Nat 1) (ep1853 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz144))))

theorem solution : Zeta.Certificates.BatchSpec 1 144530 1000 146530 1000 := EMRow51.d25
#print axioms solution
#check solution
