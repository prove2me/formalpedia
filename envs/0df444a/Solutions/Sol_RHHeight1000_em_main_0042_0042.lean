-- Prove2me | solution 1 for RHHeight1000.em_main_0042_0042
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:47:45.479493+00:00
-- url     : https://prove2.me/submissions/d8cd46bd-8d73-4de9-8543-817639388b51

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow42.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow42.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow42.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow42.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow42.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 250000000191479 95739500000000000000 4138529546116343 2251799813685248 250000000191479 95739500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 382958 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 250000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000765916 382958000000000000000 4138529546116343 2251799813685248 250000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 382958 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 250000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000765916 382958000000000000000 4138529546116343 2251799813685248 250000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow42.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 382958 1200336 1048576 1 382958 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 382958 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 382958 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 382958 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 382958 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 382958 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 382958 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow42.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz591 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 126105 1000)))

noncomputable abbrev qz537 := qz591

noncomputable abbrev qz271 := qz537

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz592 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz538 := qz592

noncomputable abbrev qz272 := qz538

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz539 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz539

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz540 := (@Neg.neg Complex Complex.instNeg qz591)

noncomputable abbrev qz274 := qz540

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz275 := (@Nat.cast Complex Complex.instNatCast 8)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz7)) Bool.false 3241342526577 1099511627776 473052693901763 210533386974920704 Bool.false 299101308825 549755813888 236494263974255 105266693487460352

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) (@HPow.hPow Complex Complex Complex qz6 qz275 qz7) Bool.false 3278220965629 1099511627776 423522164168727 210533386974920704 Bool.false 26402590201 137438953472 105819292798061 52633346743730176 Bool.true

noncomputable abbrev qz276 := (@Nat.cast Complex Complex.instNatCast 7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7)) Bool.false 3278220965629 1099511627776 423522164168727 210533386974920704 Bool.false 26402590201 137438953472 105819292798061 52633346743730176

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) Bool.false 721767893451 274877906944 92600759575661 52633346743730176 Bool.false 351598640283 1099511627776 370279202131579 210533386974920704 Bool.false

noncomputable abbrev qz277 := (@Nat.cast Complex Complex.instNatCast 6)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7)) Bool.false 721767893451 274877906944 92600759575661 52633346743730176 Bool.false 351598640283 1099511627776 370279202131579 210533386974920704

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) Bool.false 612899698329 274877906944 78259323270459 52633346743730176 Bool.false 242738150583 1099511627776 313059550026359 210533386974920704 Bool.false

noncomputable abbrev qz278 := (@Nat.cast Complex Complex.instNatCast 5)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7)) Bool.false 612899698329 274877906944 78259323270459 52633346743730176 Bool.false 242738150583 1099511627776 313059550026359 210533386974920704

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) Bool.false 1304351502465 549755813888 125172757497513 105266693487460352 Bool.false 354340493919 549755813888 125120832605251 105266693487460352 Bool.true

noncomputable abbrev qz279 := (@Nat.cast Complex Complex.instNatCast 4)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7)) Bool.false 1304351502465 549755813888 125172757497513 105266693487460352 Bool.false 354340493919 549755813888 125120832605251 105266693487460352

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) Bool.false 591143239419 274877906944 45059155071459 52633346743730176 Bool.false 27013251415 137438953472 11252627122789 13158336685932544 Bool.false

noncomputable abbrev qz541 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz280 := qz541

noncomputable abbrev qz8 := qz280

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 591143239419 274877906944 45059155071459 52633346743730176 Bool.false 27013251415 137438953472 11252627122789 13158336685932544

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 220012572457 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 274877906944 24782210183581 52633346743730176 Bool.false

noncomputable abbrev qz542 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz281 := qz542

noncomputable abbrev qz9 := qz281

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 220012572457 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 274877906944 24782210183581 52633346743730176

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz282 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz282

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz543 := (@Nat.cast Real Real.instNatCast 2)

noncomputable abbrev qz11 := (@Inv.inv Real Real.instInv (Real.sqrt qz543))

noncomputable abbrev qz593 := (Enclosure.sfrac Bool.false 126105 1000)

noncomputable abbrev qz544 := qz593

noncomputable abbrev qz283 := qz544

noncomputable abbrev qz284 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz12 := (@HMul.hMul Real Real Real qz267 qz283 (Real.log qz284))

noncomputable abbrev qz13 := qz283

noncomputable abbrev qz285 := (@Eq.refl Real qz544)

noncomputable abbrev qz14 := qz285

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)))) Bool.false 82573618985 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 274877906944 24782210183581 52633346743730176 (BSN.cpow_neg_s_mk qz13 126105 1000 2 qz14 rfl)

noncomputable abbrev qz15 := (@Nat.cast Real Real.instNatCast 1)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz543) 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz543) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz543 qz15)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 191479 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 1454220631524441439005750057963046453620031420371757686697716071582476900000000

noncomputable def ep57 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep58 := nat_lit 510919978468558600972428221803233440067911155408771682411006289062500000000

noncomputable def ep59 := nat_lit 3807845878789349912042056696591725952959019959102989263389162367771814500000000

noncomputable def ep60 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable abbrev qz286 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz287 := (BSN.sinOddQ 2147483648)

noncomputable def ep61 := BSN.sin_dyadic_bound_f 2180439850 2147483648 3 2 1048576 383332 ep56 ep57 ep58 ep59 ep60 ep58 890936 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2180439850) qz286 0 2 ep56 ep57 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2180439850) qz287 0 2 ep59 ep60 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz16 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz17 := (Real.log qz284)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 126105 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz288 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 91655131) qz16)

noncomputable abbrev qz289 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 191479 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 191479 rfl rfl rfl (ep55 rfl)))

noncomputable def ep62 := @Enclosure.Real.IsNear.cos_image qz12 qz288 Bool.false 91655131 1048576 173 262144 Bool.false 890936 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 572844573 6553600 25221 38295800 91655131 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 126105 1000 0 1 363408 524288 1 191479 572844573 6553600 25221 38295800 qz18 qz289 rfl) rfl) (Enclosure.sfrac_false_div 91655131 1048576) (BSN.cos_reduce3 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153434814057294522744832) qz19) 226375608064910080 72057594037927936 Bool.false 890936 1048576 13 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 91655131 1048576 226375608064910080 72057594037927936 13 153434814057294522744832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 890936 1048576 153434814057294522744832 151115727451828646838272 2180439850 2147483648 383332 382958 (ep61 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep63 := nat_lit 808127426392897936603626666966938355762269860720047057802024931452070500000000

noncomputable def ep64 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep65 := nat_lit 2423360439221756692608935144457208600406673759849323630041252781778086500000000

noncomputable def ep66 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable abbrev qz290 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz291 := (BSN.cosOddQ 2147483648)

noncomputable def ep67 := BSN.cos_dyadic_bound_f 2180439850 2147483648 3 2 1048576 383332 ep63 ep64 ep58 ep65 ep66 ep58 552940 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2180439850) qz290 0 2 ep63 ep64 ep58 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2180439850) qz291 0 2 ep65 ep66 ep58 rfl rfl rfl rfl) rfl rfl

noncomputable def ep68 := @Enclosure.Real.IsNear.sin_image qz12 qz288 Bool.false 91655131 1048576 173 262144 Bool.true 552940 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz12 Bool.false 572844573 6553600 25221 38295800 91655131 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz17 126105 1000 0 1 363408 524288 1 191479 572844573 6553600 25221 38295800 qz18 qz289 rfl) rfl) (Enclosure.sfrac_false_div 91655131 1048576) (BSN.sin_reduce3 qz288 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 153434814057294522744832) qz19) 226375608064910080 72057594037927936 Bool.false 552940 1048576 13 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 91655131 1048576 226375608064910080 72057594037927936 13 153434814057294522744832 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 552940 1048576 153434814057294522744832 151115727451828646838272 2180439850 2147483648 383332 382958 (ep67 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep69 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz12)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12))) Bool.false 82573618985 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 274877906944 24782210183581 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz12) 741455 1048576 1 1048576 111367 131072 33388011 50195070976 82573618985 137438953472 12399194983801 26316673371865088 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz12) Bool.false 890936 1048576 33388011 50195070976 111367 131072 33388011 50195070976 (ep62 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz11 (@Neg.neg Real Real.instNeg (Real.sin qz12)) 741455 1048576 1 1048576 138235 262144 33388011 50195070976 102495031925 274877906944 24782210183581 52633346743730176 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz12) Bool.true 138235 262144 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz12) Bool.true 552940 1048576 33388011 50195070976 138235 262144 33388011 50195070976 (ep68 rfl rfl) rfl)) rfl)

noncomputable abbrev qz293 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz20 := qz293

noncomputable def ep70 := @ep51 82573618985 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 274877906944 24782210183581 52633346743730176 Bool.false 220012572457 220012572457 137438953472 12399194983801 26316673371865088 Bool.false 102495031925 102495031925 274877906944 24782210183581 52633346743730176 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep53 ep69) rfl rfl

noncomputable abbrev qz294 := (@Nat.cast Real Real.instNatCast 3)

noncomputable abbrev qz21 := (@Inv.inv Real Real.instInv (Real.sqrt qz294))

noncomputable abbrev qz22 := (@HMul.hMul Real Real Real qz267 qz283 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep71 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)))) Bool.false 151118094505 274877906944 20260765103857 52633346743730176 Bool.true 48468529095 274877906944 20228298307575 52633346743730176 (BSN.cpow_neg_s_mk qz13 126105 1000 3 qz14 rfl)

noncomputable def ep72 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz294) 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz294) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz15)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz294 qz15)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep73 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 191479 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep74 := nat_lit 197344516330915999038070806643360000

noncomputable def ep75 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep76 := nat_lit 7656353255721115427925928667214784757760

noncomputable def ep77 := BSN.cos_dyadic_bound_f 666509380 2147483648 2 1 1048576 383332 ep74 ep75 ep74 ep74 ep76 ep74 998476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 666509380) qz290 0 1 ep74 ep75 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 666509380) qz291 0 1 ep74 ep76 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz23 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz295 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 145270185) qz16)

noncomputable abbrev qz296 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 191479 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 191479 rfl rfl rfl (ep73 rfl)))

noncomputable def ep78 := @Enclosure.Real.IsNear.cos_image qz22 qz295 Bool.false 145270185 1048576 173 262144 Bool.false 998476 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 14527018569 104857600 25221 38295800 145270185 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 126105 1000 0 1 575989 524288 1 191479 14527018569 104857600 25221 38295800 qz18 qz296 rfl) rfl) (Enclosure.sfrac_false_div 145270185 1048576) (BSN.cos_reduce0 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46901428089515178721280) qz19) 226375608064910080 72057594037927936 Bool.false 998476 1048576 22 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 145270185 1048576 226375608064910080 72057594037927936 22 46901428089515178721280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 998476 1048576 46901428089515178721280 151115727451828646838272 666509380 2147483648 383332 382958 (ep77 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep79 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep80 := nat_lit 17864824263349269331827166890167831101440

noncomputable def ep81 := BSN.sin_dyadic_bound_f 666509380 2147483648 2 1 1048576 383332 ep74 ep79 ep74 ep74 ep80 ep74 320244 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 666509380) qz286 0 1 ep74 ep79 ep74 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 666509380) qz287 0 1 ep74 ep80 ep74 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz22 qz295 Bool.false 145270185 1048576 173 262144 Bool.false 320244 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz22 Bool.false 14527018569 104857600 25221 38295800 145270185 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz23 126105 1000 0 1 575989 524288 1 191479 14527018569 104857600 25221 38295800 qz18 qz296 rfl) rfl) (Enclosure.sfrac_false_div 145270185 1048576) (BSN.sin_reduce0 qz295 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46901428089515178721280) qz19) 226375608064910080 72057594037927936 Bool.false 320244 1048576 22 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 145270185 1048576 226375608064910080 72057594037927936 22 46901428089515178721280 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 320244 1048576 46901428089515178721280 151115727451828646838272 666509380 2147483648 383332 382958 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz297 := (@Enclosure.Real.IsNear.recentre' qz21 Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep72 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz22)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22))) Bool.false 151118094505 274877906944 20260765103857 52633346743730176 Bool.true 48468529095 274877906944 20228298307575 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz21 (Real.cos qz22) 605395 1048576 1 1048576 249619 262144 33388011 50195070976 151118094505 274877906944 20260765103857 52633346743730176 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz22) Bool.false 998476 1048576 33388011 50195070976 249619 262144 33388011 50195070976 (ep78 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz22)) 605395 1048576 1 1048576 80061 262144 33388011 50195070976 48468529095 274877906944 20228298307575 52633346743730176 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz22) Bool.false 80061 262144 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz22) Bool.false 320244 1048576 33388011 50195070976 80061 262144 33388011 50195070976 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 151118094505 274877906944 20260765103857 52633346743730176 Bool.true 48468529095 274877906944 20228298307575 52633346743730176 Bool.false 81246108177795297312768 591143239419 274877906944 45059155071459 52633346743730176 Bool.false 14850692017414492651520 27013251415 137438953472 11252627122789 13158336685932544 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep70 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep71 ep83) rfl rfl

noncomputable abbrev qz545 := (@Nat.cast Real Real.instNatCast 4)

noncomputable abbrev qz24 := (@Inv.inv Real Real.instInv (Real.sqrt qz545))

noncomputable abbrev qz25 := (@HMul.hMul Real Real Real qz267 qz283 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)))) Bool.false 122065023627 549755813888 35054447354595 105266693487460352 Bool.false 246287488259 549755813888 35099815622939 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 4 qz14 rfl)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz545) 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz545) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz545 qz15)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 318077276165597140789031982421875

noncomputable def ep88 := nat_lit 49379992292270016474244603430625

noncomputable def ep89 := nat_lit 20095619060363156210525625

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 14 13 ep87 524288 191479 ep88 ep89 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 953391202858218704683582771246232721

noncomputable def ep92 := BSN.sin_dyadic_bound_f 988138419 2147483648 2 1 1048576 383332 ep91 ep79 ep91 ep91 ep80 ep91 465642 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 988138419) qz286 0 1 ep91 ep79 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 988138419) qz287 0 1 ep91 ep80 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz26 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz298 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183310515) qz16)

noncomputable abbrev qz299 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 191479 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 191479 rfl rfl rfl (ep90 rfl)))

noncomputable def ep93 := @Enclosure.Real.IsNear.cos_image qz25 qz298 Bool.false 183310515 1048576 173 262144 Bool.false 465642 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 18331051557 104857600 25221 38295800 183310515 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz26 126105 1000 0 1 726817 524288 1 191479 18331051557 104857600 25221 38295800 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 183310515 1048576) (BSN.cos_reduce3 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69534059654901084979200) qz19) 226375608064910080 72057594037927936 Bool.false 465642 1048576 27 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 183310515 1048576 226375608064910080 72057594037927936 27 69534059654901084979200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 465642 1048576 69534059654901084979200 151115727451828646838272 988138419 2147483648 383332 382958 (ep92 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep94 := BSN.cos_dyadic_bound_f 988138419 2147483648 2 1 1048576 383332 ep91 ep75 ep91 ep91 ep76 ep91 939514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 988138419) qz290 0 1 ep91 ep75 ep91 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 988138419) qz291 0 1 ep91 ep76 ep91 rfl rfl rfl rfl) rfl rfl

noncomputable def ep95 := @Enclosure.Real.IsNear.sin_image qz25 qz298 Bool.false 183310515 1048576 173 262144 Bool.true 939514 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz25 Bool.false 18331051557 104857600 25221 38295800 183310515 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz26 126105 1000 0 1 726817 524288 1 191479 18331051557 104857600 25221 38295800 qz18 qz299 rfl) rfl) (Enclosure.sfrac_false_div 183310515 1048576) (BSN.sin_reduce3 qz298 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69534059654901084979200) qz19) 226375608064910080 72057594037927936 Bool.false 939514 1048576 27 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 183310515 1048576 226375608064910080 72057594037927936 27 69534059654901084979200 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 939514 1048576 69534059654901084979200 151115727451828646838272 988138419 2147483648 383332 382958 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz300 := (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep86 rfl rfl) rfl)

noncomputable def ep96 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz25)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25))) Bool.false 122065023627 549755813888 35054447354595 105266693487460352 Bool.false 246287488259 549755813888 35099815622939 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz24 (Real.cos qz25) 524287 1048576 1 1048576 232821 524288 33388011 50195070976 122065023627 549755813888 35054447354595 105266693487460352 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz25) Bool.false 465642 1048576 33388011 50195070976 232821 524288 33388011 50195070976 (ep93 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz24 (@Neg.neg Real Real.instNeg (Real.sin qz25)) 524287 1048576 1 1048576 469757 524288 33388011 50195070976 246287488259 549755813888 35099815622939 105266693487460352 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz25) Bool.true 469757 524288 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz25) Bool.true 939514 1048576 33388011 50195070976 469757 524288 33388011 50195070976 (ep95 rfl rfl) rfl)) rfl)

noncomputable def ep97 := @ep47 122065023627 549755813888 35054447354595 105266693487460352 Bool.false 246287488259 549755813888 35099815622939 105266693487460352 Bool.false 358537410916840856616960 1304351502465 549755813888 125172757497513 105266693487460352 Bool.false 48700186656978939936768 354340493919 549755813888 125120832605251 105266693487460352 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep96) rfl rfl

noncomputable abbrev qz546 := (@Nat.cast Real Real.instNatCast 5)

noncomputable abbrev qz27 := (@Inv.inv Real Real.instInv (Real.sqrt qz546))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz283 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep98 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 78552105807 549755813888 31345889043405 105266693487460352 Bool.true 465942837255 1099511627776 62817884815857 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 5 qz14 rfl)

noncomputable def ep99 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz546) 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz546) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz546 qz15)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz546 qz15)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep100 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep101 := nat_lit 765440954430599474856563326857688500

noncomputable def ep102 := nat_lit 108794268166472120024432640000

noncomputable def ep103 := BSN.log_dyadic_bound 2 3 18 17 ep100 524288 191479 ep101 ep102 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep101 ep100 ep102 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep104 := nat_lit 237873004611978689568010362143200401

noncomputable def ep105 := BSN.sin_dyadic_bound_f 698371149 2147483648 2 1 1048576 383332 ep104 ep79 ep104 ep104 ep80 ep104 335022 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 698371149) qz286 0 1 ep104 ep79 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 698371149) qz287 0 1 ep104 ep80 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz29 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz301 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212816815) qz16)

noncomputable abbrev qz302 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 191479 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 191479 rfl rfl rfl (ep103 rfl rfl)))

noncomputable def ep106 := @Enclosure.Real.IsNear.cos_image qz28 qz301 Bool.false 212816815 1048576 173 262144 Bool.true 335022 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 665052549 3276800 25221 38295800 212816815 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 126105 1000 0 1 843808 524288 1 191479 665052549 3276800 25221 38295800 qz18 qz302 rfl) rfl) (Enclosure.sfrac_false_div 212816815 1048576) (BSN.cos_reduce1 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49143500736646464143360) qz19) 226375608064910080 72057594037927936 Bool.false 335022 1048576 32 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 212816815 1048576 226375608064910080 72057594037927936 32 49143500736646464143360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 335022 1048576 49143500736646464143360 151115727451828646838272 698371149 2147483648 383332 382958 (ep105 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep107 := BSN.cos_dyadic_bound_f 698371149 2147483648 2 1 1048576 383332 ep104 ep75 ep104 ep104 ep76 ep104 993615 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 698371149) qz290 0 1 ep104 ep75 ep104 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 698371149) qz291 0 1 ep104 ep76 ep104 rfl rfl rfl rfl) rfl rfl

noncomputable def ep108 := @Enclosure.Real.IsNear.sin_image qz28 qz301 Bool.false 212816815 1048576 173 262144 Bool.false 993615 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 665052549 3276800 25221 38295800 212816815 1048576 173 262144 (@Enclosure.Real.IsNear.mulLit_ff qz13 qz29 126105 1000 0 1 843808 524288 1 191479 665052549 3276800 25221 38295800 qz18 qz302 rfl) rfl) (Enclosure.sfrac_false_div 212816815 1048576) (BSN.sin_reduce1 qz301 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49143500736646464143360) qz19) 226375608064910080 72057594037927936 Bool.false 993615 1048576 32 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 212816815 1048576 226375608064910080 72057594037927936 32 49143500736646464143360 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 993615 1048576 49143500736646464143360 151115727451828646838272 698371149 2147483648 383332 382958 (ep107 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz303 := (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep99 rfl rfl) rfl)

noncomputable def ep109 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 78552105807 549755813888 31345889043405 105266693487460352 Bool.true 465942837255 1099511627776 62817884815857 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz27 (Real.cos qz28) 468937 1048576 1 1048576 167511 524288 33388011 50195070976 78552105807 549755813888 31345889043405 105266693487460352 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 335022 1048576 33388011 50195070976 167511 524288 33388011 50195070976 (ep106 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz27 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 468937 1048576 1 1048576 993615 1048576 33388011 50195070976 465942837255 1099511627776 62817884815857 210533386974920704 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.false 993615 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.false 993615 1048576 33388011 50195070976 993615 1048576 33388011 50195070976 (ep108 rfl rfl) rfl)) rfl)

noncomputable def ep110 := @ep45 78552105807 549755813888 31345889043405 105266693487460352 Bool.true 465942837255 1099511627776 62817884815857 210533386974920704 Bool.false 673890344973138137186304 612899698329 274877906944 78259323270459 52633346743730176 Bool.false 133446709535425066696704 242738150583 1099511627776 313059550026359 210533386974920704 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep97 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep98 ep109) rfl rfl

noncomputable abbrev qz304 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz30 := (@Inv.inv Real Real.instInv (Real.sqrt qz304))

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz31 := (@HMul.hMul Real Real Real qz267 qz283 qz547)

noncomputable def ep111 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)))) Bool.false 54434097561 137438953472 7170718152601 26316673371865088 Bool.false 27215122425 274877906944 14304913026305 52633346743730176 (BSN.cpow_neg_s_mk qz13 126105 1000 6 qz14 rfl)

noncomputable abbrev qz305 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 6) qz15)

noncomputable def ep112 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz304) 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz304) (Real.sqrt qz305) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz305) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep113 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 191479 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep114 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz547 126105 1000 0 1 4034681531866359 2251799813685248 500000000191479 95739500000000000000 101758702915201440339 450359962737049600 12610500004829291859 19147900000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 33845361775666394038272 18889465931478580854784 1000000000382958 191479000000000000000 4034681531866359 2251799813685248 500000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep115 := nat_lit 4230786746899766757701209955865600189031979957383255094680741764853663689793665

noncomputable def ep116 := nat_lit 4318696476088847683770573856300229326928210292754193504960393325240644984961

noncomputable def ep117 := nat_lit 11073639780919054802491349907690181076173492309815494648965340175899681952817281

noncomputable def ep118 := BSN.sin_dyadic_bound_f 2847207279 2147483648 3 2 1048576 383332 ep115 ep57 ep116 ep117 ep60 ep116 1017272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2847207279) qz286 0 2 ep115 ep57 ep116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2847207279) qz287 0 2 ep117 ep60 ep116 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz32 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz33 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz306 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118462721) qz32)

noncomputable def ep119 := @Enclosure.Real.IsNear.cos_image qz31 qz306 Bool.false 118462721 524288 173 262144 Bool.false 1017272 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 101758702915201440339 450359962737049600 12610500004829291859 19147900000000000000000 118462721 524288 173 262144 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 118462721 524288) (BSN.cos_reduce3 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100177200330253629652992) qz33) 226375608064910080 72057594037927936 Bool.false 1017272 1048576 35 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 118462721 524288 226375608064910080 72057594037927936 35 100177200330253629652992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1017272 1048576 100177200330253629652992 75557863725914323419136 2847207279 2147483648 383332 382958 (ep118 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep120 := nat_lit 2352356502267021019915681341639244651385290292009699138602616710841031225434241

noncomputable def ep121 := nat_lit 7048432113848885364379502877205133495502014455443589028797929345872612386332801

noncomputable def ep122 := BSN.cos_dyadic_bound_f 2847207279 2147483648 3 2 1048576 383332 ep120 ep64 ep116 ep121 ep66 ep116 254300 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2847207279) qz290 0 2 ep120 ep64 ep116 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2847207279) qz291 0 2 ep121 ep66 ep116 rfl rfl rfl rfl) rfl rfl

noncomputable def ep123 := @Enclosure.Real.IsNear.sin_image qz31 qz306 Bool.false 118462721 524288 173 262144 Bool.true 254300 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz31 Bool.false 101758702915201440339 450359962737049600 12610500004829291859 19147900000000000000000 118462721 524288 173 262144 (ep114 rfl) rfl) (Enclosure.sfrac_false_div 118462721 524288) (BSN.sin_reduce3 qz306 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 100177200330253629652992) qz33) 226375608064910080 72057594037927936 Bool.false 254300 1048576 35 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 118462721 524288 226375608064910080 72057594037927936 35 100177200330253629652992 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 254300 1048576 100177200330253629652992 75557863725914323419136 2847207279 2147483648 383332 382958 (ep122 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz307 := (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep112 rfl rfl) rfl)

noncomputable def ep124 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz31)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31))) Bool.false 54434097561 137438953472 7170718152601 26316673371865088 Bool.false 27215122425 274877906944 14304913026305 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz30 (Real.cos qz31) 428079 1048576 1 1048576 127159 131072 33388011 50195070976 54434097561 137438953472 7170718152601 26316673371865088 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz31) Bool.false 1017272 1048576 33388011 50195070976 127159 131072 33388011 50195070976 (ep119 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz31)) 428079 1048576 1 1048576 63575 262144 33388011 50195070976 27215122425 274877906944 14304913026305 52633346743730176 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz31) Bool.true 63575 262144 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz31) Bool.true 254300 1048576 33388011 50195070976 63575 262144 33388011 50195070976 (ep123 rfl rfl) rfl)) rfl)

noncomputable def ep125 := @ep43 54434097561 137438953472 7170718152601 26316673371865088 Bool.false 27215122425 274877906944 14304913026305 52633346743730176 Bool.false 99199023925595442511872 721767893451 274877906944 92600759575661 52633346743730176 Bool.false 96646698325347403825152 351598640283 1099511627776 370279202131579 210533386974920704 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep110 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep111 ep124) rfl rfl

noncomputable abbrev qz308 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz34 := (@Inv.inv Real Real.instInv (Real.sqrt qz308))

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz35 := (@HMul.hMul Real Real Real qz267 qz283 qz548)

noncomputable def ep126 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)))) Bool.false 391149391825 1099511627776 53119125866083 210533386974920704 Bool.true 140377918675 1099511627776 52997969060665 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 7 qz14 rfl)

noncomputable abbrev qz309 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7) qz15)

noncomputable def ep127 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz308) 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz308) (Real.sqrt qz309) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz309) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep128 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 191479 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep129 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz548 126105 1000 0 1 4381796493761783 2251799813685248 500000000191479 95739500000000000000 110513289369165929043 450359962737049600 12610500004829291859 19147900000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 36757173121942042968064 18889465931478580854784 1000000000382958 191479000000000000000 4381796493761783 2251799813685248 500000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep130 := nat_lit 299794477728201448504116590808946321

noncomputable def ep131 := BSN.cos_dyadic_bound_f 739956019 2147483648 2 1 1048576 383332 ep130 ep75 ep130 ep130 ep76 ep130 986941 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 739956019) qz290 0 1 ep130 ep75 ep130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 739956019) qz291 0 1 ep130 ep76 ep130 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz310 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 128654401) qz32)

noncomputable def ep132 := @Enclosure.Real.IsNear.cos_image qz35 qz310 Bool.false 128654401 524288 173 262144 Bool.false 986941 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 110513289369165929043 450359962737049600 12610500004829291859 19147900000000000000000 128654401 524288 173 262144 (ep129 rfl) rfl) (Enclosure.sfrac_false_div 128654401 524288) (BSN.cos_reduce0 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26034887924429914898432) qz33) 226375608064910080 72057594037927936 Bool.false 986941 1048576 39 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 128654401 524288 226375608064910080 72057594037927936 39 26034887924429914898432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986941 1048576 26034887924429914898432 75557863725914323419136 739956019 2147483648 383332 382958 (ep131 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep133 := BSN.sin_dyadic_bound_f 739956019 2147483648 2 1 1048576 383332 ep130 ep79 ep130 ep130 ep80 ep130 354199 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 739956019) qz286 0 1 ep130 ep79 ep130 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 739956019) qz287 0 1 ep130 ep80 ep130 rfl rfl rfl rfl) rfl rfl

noncomputable def ep134 := @Enclosure.Real.IsNear.sin_image qz35 qz310 Bool.false 128654401 524288 173 262144 Bool.false 354199 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 110513289369165929043 450359962737049600 12610500004829291859 19147900000000000000000 128654401 524288 173 262144 (ep129 rfl) rfl) (Enclosure.sfrac_false_div 128654401 524288) (BSN.sin_reduce0 qz310 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26034887924429914898432) qz33) 226375608064910080 72057594037927936 Bool.false 354199 1048576 39 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 128654401 524288 226375608064910080 72057594037927936 39 26034887924429914898432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 354199 1048576 26034887924429914898432 75557863725914323419136 739956019 2147483648 383332 382958 (ep133 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz311 := (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep127 rfl rfl) rfl)

noncomputable def ep135 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz35)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35))) Bool.false 391149391825 1099511627776 53119125866083 210533386974920704 Bool.true 140377918675 1099511627776 52997969060665 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz34 (Real.cos qz35) 396325 1048576 1 1048576 986941 1048576 33388011 50195070976 391149391825 1099511627776 53119125866083 210533386974920704 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz35) Bool.false 986941 1048576 33388011 50195070976 986941 1048576 33388011 50195070976 (ep132 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz34 (@Neg.neg Real Real.instNeg (Real.sin qz35)) 396325 1048576 1 1048576 354199 1048576 33388011 50195070976 140377918675 1099511627776 52997969060665 210533386974920704 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz35) Bool.false 354199 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz35) Bool.false 354199 1048576 33388011 50195070976 354199 1048576 33388011 50195070976 (ep134 rfl rfl) rfl)) rfl)

noncomputable def ep136 := @ep41 391149391825 1099511627776 53119125866083 210533386974920704 Bool.true 140377918675 1099511627776 52997969060665 210533386974920704 Bool.false 901110517532038084427776 3278220965629 1099511627776 423522164168727 210533386974920704 Bool.false 232239639435233416183808 26402590201 137438953472 105819292798061 52633346743730176 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep125 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep126 ep135) rfl rfl

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz36 := (@Inv.inv Real Real.instInv (Real.sqrt qz312))

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz37 := (@HMul.hMul Real Real Real qz267 qz283 qz549)

noncomputable def ep137 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz275 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)))) Bool.true 9219609763 274877906944 12382632433259 52633346743730176 Bool.false 193490948021 549755813888 24855678378133 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 8 qz14 rfl)

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8) qz15)

noncomputable def ep138 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz312) 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz312) (Real.sqrt qz313) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz313) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep139 := BSN.log_dyadic_bound 0 16 1 0 1 524288 191479 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep140 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz549 126105 1000 0 1 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 236193962651847741177 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 39279540158062550581248 18889465931478580854784 1000000000574437 191479000000000000000 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep139 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep141 := nat_lit 3614636604562466648095731567201159377722001558056326646949358220426347440800000

noncomputable def ep142 := nat_lit 10177071369042294369000015993864368797211624692580371973574718491408100000000

noncomputable def ep143 := nat_lit 10823555670949315355549194669615749395571581424783819196900925224296226122400000

noncomputable def ep144 := BSN.cos_dyadic_bound_f 3169223390 2147483648 3 2 1048576 383332 ep141 ep64 ep142 ep143 ep66 ep142 99476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3169223390) qz290 0 2 ep141 ep64 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3169223390) qz291 0 2 ep143 ep66 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz314 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 274965961) qz16)

noncomputable def ep145 := @Enclosure.Real.IsNear.cos_image qz37 qz314 Bool.false 274965961 1048576 173 262144 Bool.true 99476 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 236193962651847741177 900719925474099200 25221000014487875577 38295800000000000000000 274965961 1048576 173 262144 (ep140 rfl) rfl) (Enclosure.sfrac_false_div 274965961 1048576) (BSN.cos_reduce2 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223014269996439502323712) qz19) 226375608064910080 72057594037927936 Bool.false 99476 1048576 41 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 274965961 1048576 226375608064910080 72057594037927936 41 223014269996439502323712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 99476 1048576 223014269996439502323712 151115727451828646838272 3169223390 2147483648 383332 382958 (ep144 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep146 := nat_lit 6498204231117206131077116808166995384861833504747323666929985021974298913440000

noncomputable def ep147 := nat_lit 17002629156423757104795020185971112268014078453407384239716554084756122135200000

noncomputable def ep148 := BSN.sin_dyadic_bound_f 3169223390 2147483648 3 2 1048576 383332 ep146 ep57 ep142 ep147 ep60 ep142 1043846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3169223390) qz286 0 2 ep146 ep57 ep142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3169223390) qz287 0 2 ep147 ep60 ep142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep149 := @Enclosure.Real.IsNear.sin_image qz37 qz314 Bool.false 274965961 1048576 173 262144 Bool.true 1043846 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 236193962651847741177 900719925474099200 25221000014487875577 38295800000000000000000 274965961 1048576 173 262144 (ep140 rfl) rfl) (Enclosure.sfrac_false_div 274965961 1048576) (BSN.sin_reduce2 qz314 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223014269996439502323712) qz19) 226375608064910080 72057594037927936 Bool.false 1043846 1048576 41 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 274965961 1048576 226375608064910080 72057594037927936 41 223014269996439502323712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1043846 1048576 223014269996439502323712 151115727451828646838272 3169223390 2147483648 383332 382958 (ep148 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz315 := (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep138 rfl rfl) rfl)

noncomputable def ep150 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz37)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37))) Bool.true 9219609763 274877906944 12382632433259 52633346743730176 Bool.false 193490948021 549755813888 24855678378133 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz37) 370727 1048576 1 1048576 24869 262144 33388011 50195070976 9219609763 274877906944 12382632433259 52633346743730176 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz37) Bool.true 99476 1048576 33388011 50195070976 24869 262144 33388011 50195070976 (ep145 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz36 (@Neg.neg Real Real.instNeg (Real.sin qz37)) 370727 1048576 1 1048576 521923 524288 33388011 50195070976 193490948021 549755813888 24855678378133 105266693487460352 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz37) Bool.true 521923 524288 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz37) Bool.true 1043846 1048576 33388011 50195070976 521923 524288 33388011 50195070976 (ep149 rfl rfl) rfl)) rfl)

noncomputable def ep151 := @ep39 9219609763 274877906944 12382632433259 52633346743730176 Bool.false 193490948021 549755813888 24855678378133 105266693487460352 Bool.false 890973449394062452850688 3241342526577 1099511627776 473052693901763 210533386974920704 Bool.false 41108170867013477990400 299101308825 549755813888 236494263974255 105266693487460352 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep136 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep137 ep150) rfl rfl

theorem EMRow42.d6 : Enclosure.Complex.IsNear qz3 Bool.false 3241342526577 1099511627776 473052693901763 210533386974920704 Bool.false 299101308825 549755813888 236494263974255 105266693487460352 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep151 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz38 := (BSN.headSumC qz271 17)

noncomputable abbrev qz39 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 16) qz274)

noncomputable def ep152 := @Enclosure.Complex.IsNear.of_eq qz38 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz39) Bool.false 3722361836107 1099511627776 795121928098095 210533386974920704 Bool.false 12435306791 274877906944 99365126219729 26316673371865088

noncomputable def ep153 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz39 Bool.false 1944387334469 549755813888 95005087752799 26316673371865088 Bool.true 42259257301 274877906944 94975191753571 26316673371865088 Bool.true

noncomputable def ep154 := nat_lit 2046390060794633850454016

noncomputable abbrev qz40 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 15) qz274)

noncomputable def ep155 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz40) Bool.false 1944387334469 549755813888 95005087752799 26316673371865088 Bool.true 42259257301 274877906944 94975191753571 26316673371865088

noncomputable def ep156 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz40 Bool.false 4057317709963 1099511627776 723763354061269 210533386974920704 Bool.false 59410165481 1099511627776 723481819423905 210533386974920704 Bool.true

noncomputable def ep157 := nat_lit 4275752966298095885221888

noncomputable abbrev qz41 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 14) qz274)

noncomputable def ep158 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz41) Bool.false 4057317709963 1099511627776 723763354061269 210533386974920704 Bool.false 59410165481 1099511627776 723481819423905 210533386974920704

noncomputable def ep159 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz41 Bool.false 3769960461165 1099511627776 686139855156639 210533386974920704 Bool.true 511991287 274877906944 42875791780377 13158336685932544 Bool.false

noncomputable def ep160 := nat_lit 2230533999842905391366144

noncomputable abbrev qz42 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 13) qz274)

noncomputable def ep161 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz42) Bool.false 3769960461165 1099511627776 686139855156639 210533386974920704 Bool.true 511991287 274877906944 42875791780377 13158336685932544

noncomputable def ep162 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz42 Bool.false 4072284347523 1099511627776 647156350972545 210533386974920704 Bool.false 18942470491 549755813888 323600961774491 105266693487460352 Bool.true

noncomputable def ep163 := nat_lit 2072557681653344391659520

noncomputable abbrev qz43 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 12) qz274)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz43) Bool.false 4072284347523 1099511627776 647156350972545 210533386974920704 Bool.false 18942470491 549755813888 323600961774491 105266693487460352

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz43 Bool.false 3851201723451 1099511627776 606590562691729 210533386974920704 Bool.true 47463800227 274877906944 4739311905305 1644792085741568 Bool.false

noncomputable abbrev qz44 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 11) qz274)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz44) Bool.false 3851201723451 1099511627776 606590562691729 210533386974920704 Bool.true 47463800227 274877906944 4739311905305 1644792085741568

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz44 Bool.false 226169393677 68719476736 70528276028373 26316673371865088 Bool.false 5808703417 137438953472 141066311932855 52633346743730176 Bool.false

noncomputable abbrev qz45 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 10) qz274)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz45) Bool.false 226169393677 68719476736 70528276028373 26316673371865088 Bool.false 5808703417 137438953472 141066311932855 52633346743730176

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz45 Bool.false 3539462185777 1099511627776 519895923433419 210533386974920704 Bool.false 48126754775 137438953472 129946307499489 52633346743730176 Bool.false

noncomputable def ep170 := nat_lit 3978814051118547711557632

noncomputable abbrev qz316 := (@Nat.cast Complex Complex.instNatCast 9)

noncomputable def ep171 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 (@HPow.hPow Complex Complex Complex qz6 qz316 qz7)) Bool.false 3539462185777 1099511627776 519895923433419 210533386974920704 Bool.false 48126754775 137438953472 129946307499489 52633346743730176

noncomputable def ep172 := @Enclosure.Complex.IsNear.addLitP qz3 (@HPow.hPow Complex Complex Complex qz6 qz316 qz7) Bool.false 3241342526577 1099511627776 473052693901763 210533386974920704 Bool.false 299101308825 549755813888 236494263974255 105266693487460352 Bool.false

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt qz317))

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz283 qz550)

noncomputable def ep173 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz316 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.false 4658119675 17179869184 5855403691457 26316673371865088 Bool.true 106594289725 549755813888 23398351024723 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 9 qz14 rfl)

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9) qz15)

noncomputable def ep174 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz317) 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz317) (Real.sqrt qz318) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz318) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep175 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 191479 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep176 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz550 126105 1000 0 1 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 249572332161621806841 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 41504390431577613533184 18889465931478580854784 1000000000574437 191479000000000000000 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep177 := nat_lit 3158734921273968130809377457518750625

noncomputable def ep178 := BSN.cos_dyadic_bound_f 1333147785 2147483648 2 1 1048576 383332 ep177 ep75 ep177 ep177 ep76 ep177 852928 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1333147785) qz290 0 1 ep177 ep75 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1333147785) qz291 0 1 ep177 ep76 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz319 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 290540433) qz16)

noncomputable def ep179 := @Enclosure.Real.IsNear.cos_image qz47 qz319 Bool.false 290540433 1048576 173 262144 Bool.false 852928 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 249572332161621806841 900719925474099200 25221000014487875577 38295800000000000000000 290540433 1048576 173 262144 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 290540433 1048576) (BSN.cos_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93811935435879136362496) qz19) 226375608064910080 72057594037927936 Bool.false 852928 1048576 44 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 290540433 1048576 226375608064910080 72057594037927936 44 93811935435879136362496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 852928 1048576 93811935435879136362496 151115727451828646838272 1333147785 2147483648 383332 382958 (ep178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep180 := BSN.sin_dyadic_bound_f 1333147785 2147483648 2 1 1048576 383332 ep177 ep79 ep177 ep177 ep80 ep177 609938 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1333147785) qz286 0 1 ep177 ep79 ep177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1333147785) qz287 0 1 ep177 ep80 ep177 rfl rfl rfl rfl) rfl rfl

noncomputable def ep181 := @Enclosure.Real.IsNear.sin_image qz47 qz319 Bool.false 290540433 1048576 173 262144 Bool.false 609938 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 249572332161621806841 900719925474099200 25221000014487875577 38295800000000000000000 290540433 1048576 173 262144 (ep176 rfl) rfl) (Enclosure.sfrac_false_div 290540433 1048576) (BSN.sin_reduce0 qz319 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93811935435879136362496) qz19) 226375608064910080 72057594037927936 Bool.false 609938 1048576 44 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 290540433 1048576 226375608064910080 72057594037927936 44 93811935435879136362496 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 609938 1048576 93811935435879136362496 151115727451828646838272 1333147785 2147483648 383332 382958 (ep180 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz320 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep174 rfl rfl) rfl)

noncomputable def ep182 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.false 4658119675 17179869184 5855403691457 26316673371865088 Bool.true 106594289725 549755813888 23398351024723 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz47) 349525 1048576 1 1048576 13327 16384 33388011 50195070976 4658119675 17179869184 5855403691457 26316673371865088 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.false 852928 1048576 33388011 50195070976 13327 16384 33388011 50195070976 (ep179 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 349525 1048576 1 1048576 304969 524288 33388011 50195070976 106594289725 549755813888 23398351024723 105266693487460352 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 304969 524288 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 609938 1048576 33388011 50195070976 304969 524288 33388011 50195070976 (ep181 rfl rfl) rfl)) rfl)

noncomputable def ep183 := @ep172 4658119675 17179869184 5855403691457 26316673371865088 Bool.true 106594289725 549755813888 23398351024723 105266693487460352 Bool.false 60807497333363565395968 3539462185777 1099511627776 519895923433419 210533386974920704 Bool.false 105831852964473261260800 48126754775 137438953472 129946307499489 52633346743730176 EMRow42.d6 (ep173 ep182) rfl rfl

noncomputable abbrev qz321 := (@Nat.cast Real Real.instNatCast 10)

noncomputable abbrev qz48 := (@Inv.inv Real Real.instInv (Real.sqrt qz321))

noncomputable abbrev qz551 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz49 := (@HMul.hMul Real Real Real qz267 qz283 qz551)

noncomputable def ep184 := @Enclosure.Complex.IsNear.of_eq qz45 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)))) Bool.false 79248113055 1099511627776 44330284793565 210533386974920704 Bool.true 21159025679 68719476736 5560002216683 26316673371865088 (BSN.cpow_neg_s_mk qz13 126105 1000 10 qz14 rfl)

noncomputable abbrev qz322 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz15)

noncomputable def ep185 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz321) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz321) (Real.sqrt qz322) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz322) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep186 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 191479 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep187 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz551 126105 1000 0 1 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 261539681451529981689 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 43494585150108164161536 18889465931478580854784 1000000000574437 191479000000000000000 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep188 := nat_lit 2460964775248608499201890163838960411617272709838787582037417208063962983078721

noncomputable def ep189 := nat_lit 4725891171912053091240043381005909581807815853117331505629896277516713106241

noncomputable def ep190 := nat_lit 7373442543402001391423190404754869415688202497810128083100991831636855523023681

noncomputable def ep191 := BSN.cos_dyadic_bound_f 2879456119 2147483648 3 2 1048576 383332 ep188 ep64 ep189 ep190 ep66 ep189 238995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2879456119) qz290 0 2 ep188 ep64 ep189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2879456119) qz291 0 2 ep190 ep66 ep189 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 304472261) qz16)

noncomputable def ep192 := @Enclosure.Real.IsNear.cos_image qz49 qz323 Bool.false 304472261 1048576 173 262144 Bool.false 238995 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 261539681451529981689 900719925474099200 25221000014487875577 38295800000000000000000 304472261 1048576 173 262144 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 304472261 1048576) (BSN.cos_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202623711078184881487872) qz19) 226375608064910080 72057594037927936 Bool.false 238995 1048576 46 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 304472261 1048576 226375608064910080 72057594037927936 46 202623711078184881487872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 238995 1048576 202623711078184881487872 151115727451828646838272 2879456119 2147483648 383332 382958 (ep191 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep193 := nat_lit 4425955882509965656090410260205324013245644625027323782462847057493119999056705

noncomputable def ep194 := nat_lit 11584137773247766727612876325539934276320428030356991369726912937556477700119361

noncomputable def ep195 := BSN.sin_dyadic_bound_f 2879456119 2147483648 3 2 1048576 383332 ep193 ep57 ep189 ep194 ep60 ep189 1020976 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2879456119) qz286 0 2 ep193 ep57 ep189 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2879456119) qz287 0 2 ep194 ep60 ep189 rfl rfl rfl rfl) rfl rfl

noncomputable def ep196 := @Enclosure.Real.IsNear.sin_image qz49 qz323 Bool.false 304472261 1048576 173 262144 Bool.false 1020976 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 261539681451529981689 900719925474099200 25221000014487875577 38295800000000000000000 304472261 1048576 173 262144 (ep187 rfl) rfl) (Enclosure.sfrac_false_div 304472261 1048576) (BSN.sin_reduce0 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 202623711078184881487872) qz19) 226375608064910080 72057594037927936 Bool.false 1020976 1048576 46 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 304472261 1048576 226375608064910080 72057594037927936 46 202623711078184881487872 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1020976 1048576 202623711078184881487872 151115727451828646838272 2879456119 2147483648 383332 382958 (ep195 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' qz48 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep185 rfl rfl) rfl)

noncomputable def ep197 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz49)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49))) Bool.false 79248113055 1099511627776 44330284793565 210533386974920704 Bool.true 21159025679 68719476736 5560002216683 26316673371865088 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz49) 331589 1048576 1 1048576 238995 1048576 33388011 50195070976 79248113055 1099511627776 44330284793565 210533386974920704 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz49) Bool.false 238995 1048576 33388011 50195070976 238995 1048576 33388011 50195070976 (ep192 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz48 (@Neg.neg Real Real.instNeg (Real.sin qz49)) 331589 1048576 1 1048576 63811 65536 33388011 50195070976 21159025679 68719476736 5560002216683 26316673371865088 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz49) Bool.false 63811 65536 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz49) Bool.false 1020976 1048576 33388011 50195070976 63811 65536 33388011 50195070976 (ep196 rfl rfl) rfl)) rfl)

noncomputable def ep198 := @ep169 79248113055 1099511627776 44330284793565 210533386974920704 Bool.true 21159025679 68719476736 5560002216683 26316673371865088 Bool.false ep170 226169393677 68719476736 70528276028373 26316673371865088 Bool.false 399171059330855206912 5808703417 137438953472 141066311932855 52633346743730176 (ep171 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep183 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep184 ep197) rfl rfl

noncomputable abbrev qz325 := (@Nat.cast Real Real.instNatCast 11)

noncomputable abbrev qz50 := (@Inv.inv Real Real.instInv (Real.sqrt qz325))

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz51 := (@HMul.hMul Real Real Real qz267 qz283 qz552)

noncomputable def ep199 := @Enclosure.Complex.IsNear.of_eq qz44 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)))) Bool.false 232491424619 1099511627776 42364354464745 210533386974920704 Bool.true 59081207061 274877906944 10591669036905 52633346743730176 (BSN.cpow_neg_s_mk qz13 126105 1000 11 qz14 rfl)

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz15)

noncomputable def ep200 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz325) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz325) (Real.sqrt qz326) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz326) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep201 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 191479 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep202 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz552 126105 1000 0 1 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 272365519066561236729 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 45294944137145793642496 18889465931478580854784 1000000000574437 191479000000000000000 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep203 := nat_lit 301441359521495382177585668173647087963919050073089392806094038193410560368896

noncomputable def ep204 := nat_lit 71144800674469709112912754953768940762633861065748116044705288175919964416

noncomputable def ep205 := nat_lit 904181788963137207114531179011033726010231882497136682186192704003879841177856

noncomputable def ep206 := BSN.cos_dyadic_bound_f 1704189542 2147483648 3 2 1048576 383332 ep203 ep64 ep204 ep205 ep66 ep204 735367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1704189542) qz290 0 2 ep203 ep64 ep204 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1704189542) qz291 0 2 ep205 ep66 ep204 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz327 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 317075195) qz16)

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz51 qz327 Bool.false 317075195 1048576 173 262144 Bool.false 735367 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 272365519066561236729 900719925474099200 25221000014487875577 38295800000000000000000 317075195 1048576 173 262144 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 317075195 1048576) (BSN.cos_reduce0 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119921677977614213447680) qz19) 226375608064910080 72057594037927936 Bool.false 735367 1048576 48 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 317075195 1048576 226375608064910080 72057594037927936 48 119921677977614213447680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 735367 1048576 119921677977614213447680 151115727451828646838272 1704189542 2147483648 383332 382958 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := nat_lit 8434737735962494590650503439555815696

noncomputable def ep209 := BSN.sin_dyadic_bound_f 1704189542 2147483648 2 1 1048576 383332 ep208 ep79 ep208 ep208 ep80 ep208 747492 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1704189542) qz286 0 1 ep208 ep79 ep208 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1704189542) qz287 0 1 ep208 ep80 ep208 rfl rfl rfl rfl) rfl rfl

noncomputable def ep210 := @Enclosure.Real.IsNear.sin_image qz51 qz327 Bool.false 317075195 1048576 173 262144 Bool.false 747492 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 272365519066561236729 900719925474099200 25221000014487875577 38295800000000000000000 317075195 1048576 173 262144 (ep202 rfl) rfl) (Enclosure.sfrac_false_div 317075195 1048576) (BSN.sin_reduce0 qz327 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119921677977614213447680) qz19) 226375608064910080 72057594037927936 Bool.false 747492 1048576 48 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 317075195 1048576 226375608064910080 72057594037927936 48 119921677977614213447680 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 747492 1048576 119921677977614213447680 151115727451828646838272 1704189542 2147483648 383332 382958 (ep209 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz328 := (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep200 rfl rfl) rfl)

noncomputable def ep211 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz51)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51))) Bool.false 232491424619 1099511627776 42364354464745 210533386974920704 Bool.true 59081207061 274877906944 10591669036905 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz51) 316157 1048576 1 1048576 735367 1048576 33388011 50195070976 232491424619 1099511627776 42364354464745 210533386974920704 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz51) Bool.false 735367 1048576 33388011 50195070976 735367 1048576 33388011 50195070976 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz50 (@Neg.neg Real Real.instNeg (Real.sin qz51)) 316157 1048576 1 1048576 186873 262144 33388011 50195070976 59081207061 274877906944 10591669036905 52633346743730176 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz51) Bool.false 186873 262144 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz51) Bool.false 747492 1048576 33388011 50195070976 186873 262144 33388011 50195070976 (ep210 rfl rfl) rfl)) rfl)

noncomputable def ep212 := @ep167 232491424619 1099511627776 42364354464745 210533386974920704 Bool.true 59081207061 274877906944 10591669036905 52633346743730176 Bool.false 264652567240334100135936 3851201723451 1099511627776 606590562691729 210533386974920704 Bool.true 6523375031002956038144 47463800227 274877906944 4739311905305 1644792085741568 (ep168 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep198 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep199 ep211) rfl rfl

noncomputable abbrev qz329 := (@Nat.cast Real Real.instNatCast 12)

noncomputable abbrev qz52 := (@Inv.inv Real Real.instInv (Real.sqrt qz329))

noncomputable abbrev qz553 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz53 := (@HMul.hMul Real Real Real qz267 qz283 qz553)

noncomputable def ep213 := @Enclosure.Complex.IsNear.of_eq qz43 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)))) Bool.false 27635328009 137438953472 2535361767551 13158336685932544 Bool.false 113870070945 549755813888 20284999834971 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 12 qz14 rfl)

noncomputable abbrev qz330 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz15)

noncomputable def ep214 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz329) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz329) (Real.sqrt qz330) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz330) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep215 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 191479 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep216 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz553 126105 1000 0 1 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 282248726714352127737 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 46938541828353910898688 18889465931478580854784 1000000000574437 191479000000000000000 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep217 := nat_lit 7498212064756477041900723427847704576

noncomputable def ep218 := BSN.sin_dyadic_bound_f 1654776824 2147483648 2 1 1048576 383332 ep217 ep79 ep217 ep217 ep80 ep217 730376 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1654776824) qz286 0 1 ep217 ep79 ep217 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1654776824) qz287 0 1 ep217 ep80 ep217 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 328580763) qz16)

noncomputable def ep219 := @Enclosure.Real.IsNear.cos_image qz53 qz331 Bool.false 328580763 1048576 173 262144 Bool.false 730376 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 282248726714352127737 900719925474099200 25221000014487875577 38295800000000000000000 328580763 1048576 173 262144 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 328580763 1048576) (BSN.cos_reduce3 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116444567001265042620416) qz19) 226375608064910080 72057594037927936 Bool.false 730376 1048576 49 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 328580763 1048576 226375608064910080 72057594037927936 49 116444567001265042620416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 730376 1048576 116444567001265042620416 151115727451828646838272 1654776824 2147483648 383332 382958 (ep218 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep220 := nat_lit 267964704836567527115272825734971461312892707467582773573897637742083787718656

noncomputable def ep221 := nat_lit 56223184168059590660010333308953052881668929534062998303275206952171339776

noncomputable def ep222 := nat_lit 803781668141366462164498456538296477832914784543680194725086362812347020476416

noncomputable def ep223 := BSN.cos_dyadic_bound_f 1654776824 2147483648 3 2 1048576 383332 ep220 ep64 ep221 ep222 ep66 ep221 752370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1654776824) qz290 0 2 ep220 ep64 ep221 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1654776824) qz291 0 2 ep222 ep66 ep221 rfl rfl rfl rfl) rfl rfl

noncomputable def ep224 := @Enclosure.Real.IsNear.sin_image qz53 qz331 Bool.false 328580763 1048576 173 262144 Bool.true 752370 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 282248726714352127737 900719925474099200 25221000014487875577 38295800000000000000000 328580763 1048576 173 262144 (ep216 rfl) rfl) (Enclosure.sfrac_false_div 328580763 1048576) (BSN.sin_reduce3 qz331 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 116444567001265042620416) qz19) 226375608064910080 72057594037927936 Bool.false 752370 1048576 49 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 328580763 1048576 226375608064910080 72057594037927936 49 116444567001265042620416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 752370 1048576 116444567001265042620416 151115727451828646838272 1654776824 2147483648 383332 382958 (ep223 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz332 := (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep214 rfl rfl) rfl)

noncomputable def ep225 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz53)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53))) Bool.false 27635328009 137438953472 2535361767551 13158336685932544 Bool.false 113870070945 549755813888 20284999834971 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz52 (Real.cos qz53) 302697 1048576 1 1048576 91297 131072 33388011 50195070976 27635328009 137438953472 2535361767551 13158336685932544 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz53) Bool.false 730376 1048576 33388011 50195070976 91297 131072 33388011 50195070976 (ep219 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz53)) 302697 1048576 1 1048576 376185 524288 33388011 50195070976 113870070945 549755813888 20284999834971 105266693487460352 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz53) Bool.true 376185 524288 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz53) Bool.true 752370 1048576 33388011 50195070976 376185 524288 33388011 50195070976 (ep224 rfl rfl) rfl)) rfl)

noncomputable def ep226 := @ep165 27635328009 137438953472 2535361767551 13158336685932544 Bool.false 113870070945 549755813888 20284999834971 105266693487460352 Bool.false 559690498963967475449856 4072284347523 1099511627776 647156350972545 210533386974920704 Bool.false 5206866640914563989504 18942470491 549755813888 323600961774491 105266693487460352 (ep166 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep212 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep213 ep225) rfl rfl

noncomputable abbrev qz333 := (@Nat.cast Real Real.instNatCast 13)

noncomputable abbrev qz54 := (@Inv.inv Real Real.instInv (Real.sqrt qz333))

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz55 := (@HMul.hMul Real Real Real qz267 qz283 qz554)

noncomputable def ep227 := @Enclosure.Complex.IsNear.of_eq qz42 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)))) Bool.true 151161943179 549755813888 19491752092047 105266693487460352 Bool.true 19966453065 549755813888 19405372468525 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 13 qz14 rfl)

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz15)

noncomputable def ep228 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz333) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz333) (Real.sqrt qz334) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep229 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 191479 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep230 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz554 126105 1000 0 1 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 291340307172923002617 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 48450490295254733815808 18889465931478580854784 1000000000574437 191479000000000000000 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep231 := nat_lit 5880945572960703645150861672942410328751171193459785235269393430745496865975905

noncomputable def ep232 := nat_lit 8337953527113809309886947946005404741767696793179454628244333951589244972641

noncomputable def ep233 := nat_lit 15388976956805563379369582656269923062861633997586670784878872920792775871409761

noncomputable def ep234 := BSN.sin_dyadic_bound_f 3091237931 2147483648 3 2 1048576 383332 ep231 ep57 ep232 ep233 ep60 ep232 1039546 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3091237931) qz286 0 2 ep231 ep57 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3091237931) qz287 0 2 ep233 ep60 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz555 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 84791189) qz555)

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep235 := @Enclosure.Real.IsNear.cos_image qz55 qz335 Bool.false 84791189 262144 691 1048576 Bool.true 1039546 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 291340307172923002617 900719925474099200 25221000014487875577 38295800000000000000000 84791189 262144 691 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 84791189 262144) (BSN.cos_reduce1 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54381632794045037150208) qz336) 226375608064910080 72057594037927936 Bool.false 1039546 1048576 51 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 84791189 262144 226375608064910080 72057594037927936 51 54381632794045037150208 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039546 1048576 54381632794045037150208 37778931862957161709568 3091237931 2147483648 383332 382958 (ep234 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep236 := nat_lit 3270897742101330384777095128499563695858102972719071554984438276614871256641121

noncomputable def ep237 := nat_lit 9796017319249763535711511489606680278090773524570855755696826161941435279978081

noncomputable def ep238 := BSN.cos_dyadic_bound_f 3091237931 2147483648 3 2 1048576 383332 ep236 ep64 ep232 ep237 ep66 ep232 137310 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3091237931) qz290 0 2 ep236 ep64 ep232 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3091237931) qz291 0 2 ep237 ep66 ep232 rfl rfl rfl rfl) rfl rfl

noncomputable def ep239 := @Enclosure.Real.IsNear.sin_image qz55 qz335 Bool.false 84791189 262144 691 1048576 Bool.false 137310 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 291340307172923002617 900719925474099200 25221000014487875577 38295800000000000000000 84791189 262144 691 1048576 (ep230 rfl) rfl) (Enclosure.sfrac_false_div 84791189 262144) (BSN.sin_reduce1 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54381632794045037150208) qz336) 226375608064910080 72057594037927936 Bool.false 137310 1048576 51 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 84791189 262144 226375608064910080 72057594037927936 51 54381632794045037150208 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 137310 1048576 54381632794045037150208 37778931862957161709568 3091237931 2147483648 383332 382958 (ep238 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep228 rfl rfl) rfl)

noncomputable def ep240 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz55)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55))) Bool.true 151161943179 549755813888 19491752092047 105266693487460352 Bool.true 19966453065 549755813888 19405372468525 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz55) 290823 1048576 1 1048576 519773 524288 133360565 200780283904 151161943179 549755813888 19491752092047 105266693487460352 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz55) Bool.true 1039546 1048576 133360565 200780283904 519773 524288 133360565 200780283904 (ep235 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz55)) 290823 1048576 1 1048576 68655 524288 133360565 200780283904 19966453065 549755813888 19405372468525 105266693487460352 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz55) Bool.false 68655 524288 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz55) Bool.false 137310 1048576 133360565 200780283904 68655 524288 133360565 200780283904 (ep239 rfl rfl) rfl)) rfl)

noncomputable def ep241 := @ep162 151161943179 549755813888 19491752092047 105266693487460352 Bool.true 19966453065 549755813888 19405372468525 105266693487460352 Bool.false ep163 3769960461165 1099511627776 686139855156639 210533386974920704 Bool.true 562940373376499187712 511991287 274877906944 42875791780377 13158336685932544 (ep164 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep226 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep227 ep240) rfl rfl

noncomputable abbrev qz338 := (@Nat.cast Real Real.instNatCast 14)

noncomputable abbrev qz56 := (@Inv.inv Real Real.instInv (Real.sqrt qz338))

noncomputable abbrev qz556 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz57 := (@HMul.hMul Real Real Real qz267 qz283 qz556)

noncomputable def ep242 := @Enclosure.Complex.IsNear.of_eq qz41 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)))) Bool.false 143678624399 549755813888 18811749452315 105266693487460352 Bool.false 61458130629 1099511627776 37469150937873 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 14 qz14 rfl)

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz15)

noncomputable def ep243 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz338) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz338) (Real.sqrt qz339) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz339) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep244 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 191479 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep245 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz556 126105 1000 0 1 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 59951579924456221029 180143985094819840 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 49850353174629559828480 18889465931478580854784 1000000000574437 191479000000000000000 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep246 := nat_lit 4685875828884074865837356331724457786736353542611735806501318929065561991840000

noncomputable def ep247 := nat_lit 5296594250509652758099395115207522695570579174156073975492620637200100000000

noncomputable def ep248 := nat_lit 12263956494481275687013296133853720118992859292939245849638371047473386007200000

noncomputable def ep249 := BSN.sin_dyadic_bound_f 2920784990 2147483648 3 2 1048576 383332 ep246 ep57 ep247 ep248 ep60 ep247 1025386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2920784990) qz286 0 2 ep246 ep57 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2920784990) qz287 0 2 ep248 ep60 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz340 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 348964123) qz16)

noncomputable def ep250 := @Enclosure.Real.IsNear.cos_image qz57 qz340 Bool.false 348964123 1048576 173 262144 Bool.false 1025386 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 59951579924456221029 180143985094819840 25221000014487875577 38295800000000000000000 348964123 1048576 173 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 348964123 1048576) (BSN.cos_reduce3 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205531971791888765157376) qz19) 226375608064910080 72057594037927936 Bool.false 1025386 1048576 52 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 348964123 1048576 226375608064910080 72057594037927936 52 205531971791888765157376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1025386 1048576 205531971791888765157376 151115727451828646838272 2920784990 2147483648 383332 382958 (ep249 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep251 := nat_lit 2605618391269156993357686582120346558273783336639478147600951680875178928800000

noncomputable def ep252 := nat_lit 7806261985306451674556860956130624629430208851570122294851869801351136586400000

noncomputable def ep253 := BSN.cos_dyadic_bound_f 2920784990 2147483648 3 2 1048576 383332 ep251 ep64 ep247 ep252 ep66 ep247 219303 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2920784990) qz290 0 2 ep251 ep64 ep247 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2920784990) qz291 0 2 ep252 ep66 ep247 rfl rfl rfl rfl) rfl rfl

noncomputable def ep254 := @Enclosure.Real.IsNear.sin_image qz57 qz340 Bool.false 348964123 1048576 173 262144 Bool.true 219303 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 59951579924456221029 180143985094819840 25221000014487875577 38295800000000000000000 348964123 1048576 173 262144 (ep245 rfl) rfl) (Enclosure.sfrac_false_div 348964123 1048576) (BSN.sin_reduce3 qz340 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 205531971791888765157376) qz19) 226375608064910080 72057594037927936 Bool.false 219303 1048576 52 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 348964123 1048576 226375608064910080 72057594037927936 52 205531971791888765157376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 219303 1048576 205531971791888765157376 151115727451828646838272 2920784990 2147483648 383332 382958 (ep253 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz341 := (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep243 rfl rfl) rfl)

noncomputable def ep255 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz57)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57))) Bool.false 143678624399 549755813888 18811749452315 105266693487460352 Bool.false 61458130629 1099511627776 37469150937873 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz57) 280243 1048576 1 1048576 512693 524288 33388011 50195070976 143678624399 549755813888 18811749452315 105266693487460352 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz57) Bool.false 1025386 1048576 33388011 50195070976 512693 524288 33388011 50195070976 (ep250 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz57)) 280243 1048576 1 1048576 219303 1048576 33388011 50195070976 61458130629 1099511627776 37469150937873 210533386974920704 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz57) Bool.true 219303 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz57) Bool.true 219303 1048576 33388011 50195070976 219303 1048576 33388011 50195070976 (ep254 rfl rfl) rfl)) rfl)

noncomputable def ep256 := @ep159 143678624399 549755813888 18811749452315 105266693487460352 Bool.false 61458130629 1099511627776 37469150937873 210533386974920704 Bool.false ep160 4057317709963 1099511627776 723763354061269 210533386974920704 Bool.false 16330541938613959000064 59410165481 1099511627776 723481819423905 210533386974920704 (ep161 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep241 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep242 ep255) rfl rfl

noncomputable abbrev qz342 := (@Nat.cast Real Real.instNatCast 15)

noncomputable abbrev qz58 := (@Inv.inv Real Real.instInv (Real.sqrt qz342))

noncomputable abbrev qz557 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz59 := (@HMul.hMul Real Real Real qz267 qz283 qz557)

noncomputable def ep257 := @Enclosure.Complex.IsNear.of_eq qz40 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)))) Bool.true 168543041025 1099511627776 36277347961123 210533386974920704 Bool.true 228447194685 1099511627776 36319714604663 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 15 qz14 rfl)

noncomputable abbrev qz343 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz15)

noncomputable def ep258 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz342) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz342) (Real.sqrt qz343) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz343) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep259 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 191479 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep260 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz557 126105 1000 0 1 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 307594445514034368249 900719925474099200 25221000014487875577 38295800000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 51153586820399524478976 18889465931478580854784 1000000000574437 191479000000000000000 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep261 := nat_lit 3471704586306030605807534711158716481

noncomputable def ep262 := BSN.sin_dyadic_bound_f 1365009553 2147483648 2 1 1048576 383332 ep261 ep79 ep261 ep261 ep80 ep261 622525 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1365009553) qz286 0 1 ep261 ep79 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1365009553) qz287 0 1 ep261 ep80 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 358087063) qz16)

noncomputable def ep263 := @Enclosure.Real.IsNear.cos_image qz59 qz344 Bool.false 358087063 1048576 173 262144 Bool.true 622525 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 307594445514034368249 900719925474099200 25221000014487875577 38295800000000000000000 358087063 1048576 173 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 358087063 1048576) (BSN.cos_reduce1 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96054008083010421784576) qz19) 226375608064910080 72057594037927936 Bool.false 622525 1048576 54 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 358087063 1048576 226375608064910080 72057594037927936 54 96054008083010421784576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 622525 1048576 96054008083010421784576 151115727451828646838272 1365009553 2147483648 383332 382958 (ep262 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep264 := nat_lit 124054837389976404429134276354341885381614277332994688054076883206229162688641

noncomputable def ep265 := nat_lit 12052732734578327111370407711858729460003880553133993666255734903341023361

noncomputable def ep266 := nat_lit 372140406704460056633180088247601938685922824237877796174898138148880806019201

noncomputable def ep267 := BSN.cos_dyadic_bound_f 1365009553 2147483648 3 2 1048576 383332 ep264 ep64 ep265 ep266 ep66 ep265 843785 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1365009553) qz290 0 2 ep264 ep64 ep265 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1365009553) qz291 0 2 ep266 ep66 ep265 rfl rfl rfl rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz59 qz344 Bool.false 358087063 1048576 173 262144 Bool.false 843785 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 307594445514034368249 900719925474099200 25221000014487875577 38295800000000000000000 358087063 1048576 173 262144 (ep260 rfl) rfl) (Enclosure.sfrac_false_div 358087063 1048576) (BSN.sin_reduce1 qz344 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96054008083010421784576) qz19) 226375608064910080 72057594037927936 Bool.false 843785 1048576 54 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 358087063 1048576 226375608064910080 72057594037927936 54 96054008083010421784576 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 843785 1048576 96054008083010421784576 151115727451828646838272 1365009553 2147483648 383332 382958 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz345 := (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep258 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz59)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59))) Bool.true 168543041025 1099511627776 36277347961123 210533386974920704 Bool.true 228447194685 1099511627776 36319714604663 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz58 (Real.cos qz59) 270741 1048576 1 1048576 622525 1048576 33388011 50195070976 168543041025 1099511627776 36277347961123 210533386974920704 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz59) Bool.true 622525 1048576 33388011 50195070976 622525 1048576 33388011 50195070976 (ep263 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz59)) 270741 1048576 1 1048576 843785 1048576 33388011 50195070976 228447194685 1099511627776 36319714604663 210533386974920704 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz59) Bool.false 843785 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz59) Bool.false 843785 1048576 33388011 50195070976 843785 1048576 33388011 50195070976 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep156 168543041025 1099511627776 36277347961123 210533386974920704 Bool.true 228447194685 1099511627776 36319714604663 210533386974920704 Bool.false ep157 1944387334469 549755813888 95005087752799 26316673371865088 Bool.true 185858179134509289570304 42259257301 274877906944 94975191753571 26316673371865088 (ep158 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep256 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep257 ep269) rfl rfl

noncomputable abbrev qz346 := (@Nat.cast Real Real.instNatCast 16)

noncomputable abbrev qz60 := (@Inv.inv Real Real.instInv (Real.sqrt qz346))

noncomputable abbrev qz558 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz61 := (@HMul.hMul Real Real Real qz267 qz283 qz558)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz39 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)))) Bool.true 166412832831 1099511627776 35081226075703 210533386974920704 Bool.false 13673641023 68719476736 2194967233079 13158336685932544 (BSN.cpow_neg_s_mk qz13 126105 1000 16 qz14 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz15)

noncomputable def ep272 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz346) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz346) (Real.sqrt qz347) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep273 := BSN.log_dyadic_bound 0 32 1 0 1 524288 191479 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep274 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz558 126105 1000 0 1 3121657384082679 1125899906842624 250000000191479 47869750000000000000 78731320883949247059 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 52372720210750067441664 18889465931478580854784 1000000000765916 191479000000000000000 3121657384082679 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep275 := nat_lit 545832052583610012655187045713109713249516189920150325308538771513568232690625

noncomputable def ep276 := nat_lit 233179003465094466852194071996735434711034899619785303829251782844187890625

noncomputable def ep277 := nat_lit 1637029799743899849031856748995335668879126499961211405317957810975016322290625

noncomputable def ep278 := BSN.cos_dyadic_bound_f 1976792935 2147483648 3 2 1048576 383332 ep275 ep64 ep276 ep277 ep66 ep276 634817 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1976792935) qz290 0 2 ep275 ep64 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1976792935) qz291 0 2 ep277 ep66 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 183310641) qz32)

noncomputable def ep279 := @Enclosure.Real.IsNear.cos_image qz61 qz348 Bool.false 183310641 524288 691 1048576 Bool.true 634817 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 78731320883949247059 225179981368524800 6305250004829291859 9573950000000000000000 183310641 524288 691 1048576 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 183310641 524288) (BSN.cos_reduce2 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69552218168598642819072) qz33) 226375608064910080 72057594037927936 Bool.false 634817 1048576 55 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 183310641 524288 226375608064910080 72057594037927936 55 69552218168598642819072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 634817 1048576 69552218168598642819072 75557863725914323419136 1976792935 2147483648 383332 382958 (ep278 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep280 := nat_lit 982311151447725947205854927026000095501360313936574757312306387298147468530625

noncomputable def ep281 := nat_lit 2572342154452719708783287923237243630847363908567835188183174130513400399090625

noncomputable def ep282 := BSN.sin_dyadic_bound_f 1976792935 2147483648 3 2 1048576 383332 ep280 ep57 ep276 ep281 ep60 ep276 834576 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1976792935) qz286 0 2 ep280 ep57 ep276 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1976792935) qz287 0 2 ep281 ep60 ep276 rfl rfl rfl rfl) rfl rfl

noncomputable def ep283 := @Enclosure.Real.IsNear.sin_image qz61 qz348 Bool.false 183310641 524288 691 1048576 Bool.true 834576 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 78731320883949247059 225179981368524800 6305250004829291859 9573950000000000000000 183310641 524288 691 1048576 (ep274 rfl) rfl) (Enclosure.sfrac_false_div 183310641 524288) (BSN.sin_reduce2 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 69552218168598642819072) qz33) 226375608064910080 72057594037927936 Bool.false 834576 1048576 55 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 183310641 524288 226375608064910080 72057594037927936 55 69552218168598642819072 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 834576 1048576 69552218168598642819072 75557863725914323419136 1976792935 2147483648 383332 382958 (ep282 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep272 rfl rfl) rfl)

noncomputable def ep284 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz61)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61))) Bool.true 166412832831 1099511627776 35081226075703 210533386974920704 Bool.false 13673641023 68719476736 2194967233079 13158336685932544 (@Enclosure.Real.IsNear.mulLit_ft qz60 (Real.cos qz61) 262143 1048576 1 1048576 634817 1048576 133360565 200780283904 166412832831 1099511627776 35081226075703 210533386974920704 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz61) Bool.true 634817 1048576 133360565 200780283904 634817 1048576 133360565 200780283904 (ep279 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz61)) 262143 1048576 1 1048576 52161 65536 133360565 200780283904 13673641023 68719476736 2194967233079 13158336685932544 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz61) Bool.true 52161 65536 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz61) Bool.true 834576 1048576 133360565 200780283904 52161 65536 133360565 200780283904 (ep283 rfl rfl) rfl)) rfl)

noncomputable def ep285 := @ep153 166412832831 1099511627776 35081226075703 210533386974920704 Bool.false 13673641023 68719476736 2194967233079 13158336685932544 Bool.false ep154 3722361836107 1099511627776 795121928098095 210533386974920704 Bool.false 854547775729147314176 12435306791 274877906944 99365126219729 26316673371865088 (ep155 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep271 ep284) rfl rfl

theorem EMRow42.d7 : Enclosure.Complex.IsNear qz38 Bool.false 3722361836107 1099511627776 795121928098095 210533386974920704 Bool.false 12435306791 274877906944 99365126219729 26316673371865088 := ep152 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep285 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz62 := (BSN.headSumC qz271 25)

noncomputable abbrev qz63 := (@HPow.hPow Complex Complex Complex qz273 (@Nat.cast Complex Complex.instNatCast 24) qz274)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq qz62 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz63) Bool.false 2605246211759 549755813888 261212916732499 52633346743730176 Bool.false 16809981067 549755813888 130533478921845 26316673371865088

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz63 Bool.false 5162544476933 1099511627776 1016264277429211 210533386974920704 Bool.true 185634526179 1099511627776 1015527191273367 210533386974920704 Bool.false

noncomputable def ep288 := nat_lit 5728997006096791364435968

noncomputable abbrev qz350 := (@Nat.cast Complex Complex.instNatCast 23)

noncomputable def ep289 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7)) Bool.false 5162544476933 1099511627776 1016264277429211 210533386974920704 Bool.true 185634526179 1099511627776 1015527191273367 210533386974920704

noncomputable def ep290 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) Bool.false 2477530398505 549755813888 30841377623501 6579168342966272 Bool.true 70791425601 274877906944 493141644952291 105266693487460352 Bool.false

noncomputable def ep291 := nat_lit 2838138840649300657045504

noncomputable abbrev qz351 := (@Nat.cast Complex Complex.instNatCast 22)

noncomputable def ep292 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz351 qz7)) Bool.false 2477530398505 549755813888 30841377623501 6579168342966272 Bool.true 70791425601 274877906944 493141644952291 105266693487460352

noncomputable def ep293 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) Bool.false 1181817295079 274877906944 59807197297909 13158336685932544 Bool.true 227830203093 1099511627776 956422073257795 210533386974920704 Bool.false

noncomputable abbrev qz352 := (@Nat.cast Complex Complex.instNatCast 21)

noncomputable def ep294 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz352 qz7)) Bool.false 1181817295079 274877906944 59807197297909 13158336685932544 Bool.true 227830203093 1099511627776 956422073257795 210533386974920704

noncomputable def ep295 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) (@HPow.hPow Complex Complex Complex qz6 qz352 qz7) Bool.false 141781226047 34359738368 115760143710709 26316673371865088 Bool.true 81661951147 1099511627776 925661876352969 210533386974920704 Bool.false

noncomputable abbrev qz353 := (@Nat.cast Complex Complex.instNatCast 20)

noncomputable def ep296 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz353 qz7)) Bool.false 141781226047 34359738368 115760143710709 26316673371865088 Bool.true 81661951147 1099511627776 925661876352969 210533386974920704

noncomputable def ep297 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) (@HPow.hPow Complex Complex Complex qz6 qz353 qz7) Bool.false 2181591571681 549755813888 10402619245345 2448062639243264 Bool.false 11527268629 137438953472 1299717920775 306007829905408 Bool.false

noncomputable def ep298 := nat_lit 1247120853112111839051776

noncomputable abbrev qz354 := (@Nat.cast Complex Complex.instNatCast 19)

noncomputable def ep299 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7)) Bool.false 2181591571681 549755813888 10402619245345 2448062639243264 Bool.false 11527268629 137438953472 1299717920775 306007829905408

noncomputable def ep300 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) Bool.false 2077536813995 549755813888 431189193784269 105266693487460352 Bool.false 234757776097 1099511627776 862011253967535 210533386974920704 Bool.false

noncomputable abbrev qz355 := (@Nat.cast Complex Complex.instNatCast 18)

noncomputable def ep301 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7)) Bool.false 2077536813995 549755813888 431189193784269 105266693487460352 Bool.false 234757776097 1099511627776 862011253967535 210533386974920704

noncomputable def ep302 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) Bool.false 3896473357915 1099511627776 829217707942983 210533386974920704 Bool.false 251727163757 1099511627776 829037776658515 210533386974920704 Bool.false

noncomputable def ep303 := nat_lit 4568551768240414775050240

noncomputable abbrev qz356 := (@Nat.cast Complex Complex.instNatCast 17)

noncomputable def ep304 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz38 (@HPow.hPow Complex Complex Complex qz6 qz356 qz7)) Bool.false 3896473357915 1099511627776 829217707942983 210533386974920704 Bool.false 251727163757 1099511627776 829037776658515 210533386974920704

noncomputable def ep305 := @Enclosure.Complex.IsNear.addLitP qz38 (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) Bool.false 3722361836107 1099511627776 795121928098095 210533386974920704 Bool.false 12435306791 274877906944 99365126219729 26316673371865088 Bool.false

noncomputable abbrev qz357 := (@Nat.cast Real Real.instNatCast 17)

noncomputable abbrev qz64 := (@Inv.inv Real Real.instInv (Real.sqrt qz357))

noncomputable abbrev qz559 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz65 := (@HMul.hMul Real Real Real qz267 qz283 qz559)

noncomputable def ep306 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz356 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)))) Bool.false 10881970113 68719476736 4261972480611 26316673371865088 Bool.false 201985936593 1099511627776 34116766900683 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 17 qz14 rfl)

noncomputable abbrev qz358 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz15)

noncomputable def ep307 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz357) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz357) (Real.sqrt qz358) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz358) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep308 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 191479 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep309 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz559 126105 1000 0 1 3189913004350711 1125899906842624 250000000191479 47869750000000000000 80452795882729282131 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 53517859495200818200576 18889465931478580854784 1000000000765916 191479000000000000000 3189913004350711 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep308 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep310 := nat_lit 5447784012707174492917906716684960000

noncomputable def ep311 := BSN.sin_dyadic_bound_f 1527759420 2147483648 2 1 1048576 383332 ep310 ep79 ep310 ep310 ep80 ep310 684624 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1527759420) qz286 0 1 ep310 ep79 ep310 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1527759420) qz287 0 1 ep310 ep80 ep310 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 93659381) qz555)

noncomputable def ep312 := @Enclosure.Real.IsNear.cos_image qz65 qz359 Bool.false 93659381 262144 173 262144 Bool.false 684624 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 80452795882729282131 225179981368524800 6305250004829291859 9573950000000000000000 93659381 262144 173 262144 (ep309 rfl) rfl) (Enclosure.sfrac_false_div 93659381 262144) (BSN.cos_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26876627954354138120192) qz336) 226375608064910080 72057594037927936 Bool.false 684624 1048576 56 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 93659381 262144 226375608064910080 72057594037927936 56 26876627954354138120192 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 684624 1048576 26876627954354138120192 37778931862957161709568 1527759420 2147483648 383332 382958 (ep311 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep313 := nat_lit 194677086374043858038559921801728488074545796726662326476894473614766284800000

noncomputable def ep314 := nat_lit 29678350649107883936924854642761175954711741764616003424851890201600000000

noncomputable def ep315 := nat_lit 583971902420833358347805915695899941871727966696457747423833717063895654400000

noncomputable def ep316 := BSN.cos_dyadic_bound_f 1527759420 2147483648 3 2 1048576 383332 ep313 ep64 ep314 ep315 ep66 ep314 794229 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1527759420) qz290 0 2 ep313 ep64 ep314 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1527759420) qz291 0 2 ep315 ep66 ep314 rfl rfl rfl rfl) rfl rfl

noncomputable def ep317 := @Enclosure.Real.IsNear.sin_image qz65 qz359 Bool.false 93659381 262144 173 262144 Bool.true 794229 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz65 Bool.false 80452795882729282131 225179981368524800 6305250004829291859 9573950000000000000000 93659381 262144 173 262144 (ep309 rfl) rfl) (Enclosure.sfrac_false_div 93659381 262144) (BSN.sin_reduce3 qz359 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26876627954354138120192) qz336) 226375608064910080 72057594037927936 Bool.false 794229 1048576 56 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 93659381 262144 226375608064910080 72057594037927936 56 26876627954354138120192 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794229 1048576 26876627954354138120192 37778931862957161709568 1527759420 2147483648 383332 382958 (ep316 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz360 := (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep307 rfl rfl) rfl)

noncomputable def ep318 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz65)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65))) Bool.false 10881970113 68719476736 4261972480611 26316673371865088 Bool.false 201985936593 1099511627776 34116766900683 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz65) 254317 1048576 1 1048576 42789 65536 33388011 50195070976 10881970113 68719476736 4261972480611 26316673371865088 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz65) Bool.false 684624 1048576 33388011 50195070976 42789 65536 33388011 50195070976 (ep312 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz65)) 254317 1048576 1 1048576 794229 1048576 33388011 50195070976 201985936593 1099511627776 34116766900683 210533386974920704 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz65) Bool.true 794229 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz65) Bool.true 794229 1048576 33388011 50195070976 794229 1048576 33388011 50195070976 (ep317 rfl rfl) rfl)) rfl)

noncomputable def ep319 := @ep305 10881970113 68719476736 4261972480611 26316673371865088 Bool.false 201985936593 1099511627776 34116766900683 210533386974920704 Bool.false 267763610271683643965440 3896473357915 1099511627776 829217707942983 210533386974920704 Bool.false 69194235894473695428608 251727163757 1099511627776 829037776658515 210533386974920704 EMRow42.d7 (ep306 ep318) rfl rfl

noncomputable abbrev qz361 := (@Nat.cast Real Real.instNatCast 18)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz361))

noncomputable abbrev qz560 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz283 qz560)

noncomputable def ep320 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz355 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 258600270075 1099511627776 33160679625555 210533386974920704 Bool.true 4242346915 274877906944 8243369327255 52633346743730176 (BSN.cpow_neg_s_mk qz13 126105 1000 18 qz14 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz15)

noncomputable def ep321 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz361) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz361) (Real.sqrt qz362) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep322 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 191479 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep323 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz560 126105 1000 0 1 3254268794313975 1125899906842624 250000000191479 47869750000000000000 3283036530455710539 9007199254740992 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 54597570484265130393600 18889465931478580854784 1000000000765916 191479000000000000000 3254268794313975 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep324 := nat_lit 392094122431228610283379426966081

noncomputable def ep325 := BSN.cos_dyadic_bound_f 140717329 2147483648 2 1 1048576 383332 ep324 ep75 ep324 ep324 ep76 ep324 1046325 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 140717329) qz290 0 1 ep324 ep75 ep324 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 140717329) qz291 0 1 ep324 ep76 ep324 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191097877) qz32)

noncomputable def ep326 := @Enclosure.Real.IsNear.cos_image qz67 qz363 Bool.false 191097877 524288 691 1048576 Bool.false 1046325 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 3283036530455710539 9007199254740992 6305250004829291859 9573950000000000000000 191097877 524288 691 1048576 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 191097877 524288) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4951050888318459838464) qz33) 226375608064910080 72057594037927936 Bool.false 1046325 1048576 58 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 191097877 524288 226375608064910080 72057594037927936 58 4951050888318459838464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1046325 1048576 4951050888318459838464 75557863725914323419136 140717329 2147483648 383332 382958 (ep325 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep327 := BSN.sin_dyadic_bound_f 140717329 2147483648 1 0 1048576 383332 0 1 1 0 1 1 68660 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 140717329) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 140717329) qz287 0 0 rfl) rfl rfl

noncomputable def ep328 := @Enclosure.Real.IsNear.sin_image qz67 qz363 Bool.false 191097877 524288 691 1048576 Bool.false 68660 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 3283036530455710539 9007199254740992 6305250004829291859 9573950000000000000000 191097877 524288 691 1048576 (ep323 rfl) rfl) (Enclosure.sfrac_false_div 191097877 524288) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4951050888318459838464) qz33) 226375608064910080 72057594037927936 Bool.false 68660 1048576 58 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 191097877 524288 226375608064910080 72057594037927936 58 4951050888318459838464 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 68660 1048576 4951050888318459838464 75557863725914323419136 140717329 2147483648 383332 382958 (ep327 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep321 rfl rfl) rfl)

noncomputable def ep329 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 258600270075 1099511627776 33160679625555 210533386974920704 Bool.true 4242346915 274877906944 8243369327255 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 247151 1048576 1 1048576 1046325 1048576 133360565 200780283904 258600270075 1099511627776 33160679625555 210533386974920704 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 1046325 1048576 133360565 200780283904 1046325 1048576 133360565 200780283904 (ep326 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 247151 1048576 1 1048576 17165 262144 133360565 200780283904 4242346915 274877906944 8243369327255 52633346743730176 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.false 17165 262144 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.false 68660 1048576 133360565 200780283904 17165 262144 133360565 200780283904 (ep328 rfl rfl) rfl)) rfl)

noncomputable def ep330 := @ep302 258600270075 1099511627776 33160679625555 210533386974920704 Bool.true 4242346915 274877906944 8243369327255 52633346743730176 Bool.false ep303 2077536813995 549755813888 431189193784269 105266693487460352 Bool.false 64529726132371553517568 234757776097 1099511627776 862011253967535 210533386974920704 (ep304 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep319 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep320 ep329) rfl rfl

noncomputable abbrev qz365 := (@Nat.cast Real Real.instNatCast 19)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz365))

noncomputable abbrev qz561 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz283 qz561)

noncomputable def ep331 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz354 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.false 52027378843 274877906944 8061716882783 52633346743730176 Bool.true 142539627065 1099511627776 32194675525665 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 19 qz14 rfl)

noncomputable abbrev qz366 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz15)

noncomputable def ep332 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz365) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz365) (Real.sqrt qz366) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz366) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep333 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 191479 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep334 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz561 126105 1000 0 1 3315143513283831 1125899906842624 250000000191479 47869750000000000000 83611234548531501651 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 55618878793361701994496 18889465931478580854784 1000000000765916 191479000000000000000 3315143513283831 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep335 := nat_lit 2766179032785019555387120109763081121

noncomputable def ep336 := BSN.cos_dyadic_bound_f 1289644681 2147483648 2 1 1048576 383332 ep335 ep75 ep335 ep335 ep76 ep335 865108 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1289644681) qz290 0 1 ep335 ep75 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1289644681) qz291 0 1 ep335 ep76 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 389345151) qz16)

noncomputable def ep337 := @Enclosure.Real.IsNear.cos_image qz69 qz367 Bool.false 389345151 1048576 691 1048576 Bool.false 865108 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 83611234548531501651 225179981368524800 6305250004829291859 9573950000000000000000 389345151 1048576 691 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 389345151 1048576) (BSN.cos_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90750676651512055201792) qz19) 226375608064910080 72057594037927936 Bool.false 865108 1048576 59 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 389345151 1048576 226375608064910080 72057594037927936 59 90750676651512055201792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 865108 1048576 90750676651512055201792 151115727451828646838272 1289644681 2147483648 383332 382958 (ep336 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep338 := BSN.sin_dyadic_bound_f 1289644681 2147483648 2 1 1048576 383332 ep335 ep79 ep335 ep335 ep80 ep335 592535 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1289644681) qz286 0 1 ep335 ep79 ep335 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1289644681) qz287 0 1 ep335 ep80 ep335 rfl rfl rfl rfl) rfl rfl

noncomputable def ep339 := @Enclosure.Real.IsNear.sin_image qz69 qz367 Bool.false 389345151 1048576 691 1048576 Bool.false 592535 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 83611234548531501651 225179981368524800 6305250004829291859 9573950000000000000000 389345151 1048576 691 1048576 (ep334 rfl) rfl) (Enclosure.sfrac_false_div 389345151 1048576) (BSN.sin_reduce0 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 90750676651512055201792) qz19) 226375608064910080 72057594037927936 Bool.false 592535 1048576 59 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 389345151 1048576 226375608064910080 72057594037927936 59 90750676651512055201792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 592535 1048576 90750676651512055201792 151115727451828646838272 1289644681 2147483648 383332 382958 (ep338 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep332 rfl rfl) rfl)

noncomputable def ep340 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.false 52027378843 274877906944 8061716882783 52633346743730176 Bool.true 142539627065 1099511627776 32194675525665 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz69) 240559 1048576 1 1048576 216277 262144 133360565 200780283904 52027378843 274877906944 8061716882783 52633346743730176 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.false 865108 1048576 133360565 200780283904 216277 262144 133360565 200780283904 (ep337 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 240559 1048576 1 1048576 592535 1048576 133360565 200780283904 142539627065 1099511627776 32194675525665 210533386974920704 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.false 592535 1048576 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.false 592535 1048576 133360565 200780283904 592535 1048576 133360565 200780283904 (ep339 rfl rfl) rfl)) rfl)

noncomputable def ep341 := @ep300 52027378843 274877906944 8061716882783 52633346743730176 Bool.true 142539627065 1099511627776 32194675525665 210533386974920704 Bool.false 599671325030344623652864 2181591571681 549755813888 10402619245345 2448062639243264 Bool.false 101394927152664078712832 11527268629 137438953472 1299717920775 306007829905408 (ep301 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep330 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep331 ep340) rfl rfl

noncomputable abbrev qz369 := (@Nat.cast Real Real.instNatCast 20)

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt qz369))

noncomputable abbrev qz562 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz283 qz562)

noncomputable def ep342 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz353 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.false 86908045071 549755813888 15727947293001 105266693487460352 Bool.true 173880100179 1099511627776 31455946859769 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 20 qz14 rfl)

noncomputable abbrev qz370 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz15)

noncomputable def ep343 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz369) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz369) (Real.sqrt qz370) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz370) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep344 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 191479 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep345 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz562 126105 1000 0 1 3372893643545847 1125899906842624 250000000191479 47869750000000000000 85067750583869807187 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz370) Bool.false 56587765202795681021952 18889465931478580854784 1000000000765916 191479000000000000000 3372893643545847 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep346 := nat_lit 289476922198028061978477733260823497878103571767701933985686054668650399399936

noncomputable def ep347 := nat_lit 65610525318967557971080741579696641102474239289892975104468863182077689856

noncomputable def ep348 := nat_lit 868299545543446250819491038299311100352105766824526016006849226279587042820096

noncomputable def ep349 := BSN.cos_dyadic_bound_f 1687025664 2147483648 3 2 1048576 383332 ep346 ep64 ep347 ep348 ep66 ep347 741318 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1687025664) qz290 0 2 ep346 ep64 ep347 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1687025664) qz291 0 2 ep348 ep66 ep347 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 198063791) qz32)

noncomputable def ep350 := @Enclosure.Real.IsNear.cos_image qz71 qz371 Bool.false 198063791 524288 173 262144 Bool.false 741318 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 85067750583869807187 225179981368524800 6305250004829291859 9573950000000000000000 198063791 524288 173 262144 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 198063791 524288) (BSN.cos_reduce0 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59356938709471332401152) qz33) 226375608064910080 72057594037927936 Bool.false 741318 1048576 60 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 198063791 524288 226375608064910080 72057594037927936 60 59356938709471332401152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741318 1048576 59356938709471332401152 75557863725914323419136 1687025664 2147483648 383332 382958 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep351 := nat_lit 8100032427031854665196127791995682816

noncomputable def ep352 := BSN.sin_dyadic_bound_f 1687025664 2147483648 2 1 1048576 383332 ep351 ep79 ep351 ep351 ep80 ep351 741591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1687025664) qz286 0 1 ep351 ep79 ep351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1687025664) qz287 0 1 ep351 ep80 ep351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep353 := @Enclosure.Real.IsNear.sin_image qz71 qz371 Bool.false 198063791 524288 173 262144 Bool.false 741591 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 85067750583869807187 225179981368524800 6305250004829291859 9573950000000000000000 198063791 524288 173 262144 (ep345 rfl) rfl) (Enclosure.sfrac_false_div 198063791 524288) (BSN.sin_reduce0 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59356938709471332401152) qz33) 226375608064910080 72057594037927936 Bool.false 741591 1048576 60 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 198063791 524288 226375608064910080 72057594037927936 60 59356938709471332401152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741591 1048576 59356938709471332401152 75557863725914323419136 1687025664 2147483648 383332 382958 (ep352 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep343 rfl rfl) rfl)

noncomputable def ep354 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.false 86908045071 549755813888 15727947293001 105266693487460352 Bool.true 173880100179 1099511627776 31455946859769 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz71) 234469 1048576 1 1048576 370659 524288 33388011 50195070976 86908045071 549755813888 15727947293001 105266693487460352 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.false 741318 1048576 33388011 50195070976 370659 524288 33388011 50195070976 (ep350 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 234469 1048576 1 1048576 741591 1048576 33388011 50195070976 173880100179 1099511627776 31455946859769 210533386974920704 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 741591 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 741591 1048576 33388011 50195070976 741591 1048576 33388011 50195070976 (ep353 rfl rfl) rfl)) rfl)

noncomputable def ep355 := @ep297 86908045071 549755813888 15727947293001 105266693487460352 Bool.true 173880100179 1099511627776 31455946859769 210533386974920704 Bool.false ep298 141781226047 34359738368 115760143710709 26316673371865088 Bool.true 11223533104125270032384 81661951147 1099511627776 925661876352969 210533386974920704 (ep299 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep341 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep342 ep354) rfl rfl

noncomputable abbrev qz373 := (@Nat.cast Real Real.instNatCast 21)

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt qz373))

noncomputable abbrev qz563 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz267 qz283 qz563)

noncomputable def ep356 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz352 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.false 47567486703 274877906944 3854250885109 26316673371865088 Bool.true 73084125973 549755813888 15380098452413 105266693487460352 (BSN.cpow_neg_s_mk qz13 126105 1000 21 qz14 rfl)

noncomputable abbrev qz374 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz15)

noncomputable def ep357 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz373) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz373) (Real.sqrt qz374) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz374) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep358 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 191479 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep359 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz563 126105 1000 0 1 3427826275261687 1125899906842624 250000000191479 47869750000000000000 86453206488375007827 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz374) Bool.false 57509381830540779323392 18889465931478580854784 1000000000765916 191479000000000000000 3427826275261687 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep360 := nat_lit 139930947643370753793669986308603997708922531014025445153031412774369614626816

noncomputable def ep361 := nat_lit 15334685403920025094927037905098155012895720652584986556026350635147329536

noncomputable def ep362 := nat_lit 419762173559304421330820104850001796816741801600771165485982185621838549221376

noncomputable def ep363 := BSN.cos_dyadic_bound_f 1406725496 2147483648 3 2 1048576 383332 ep360 ep64 ep361 ep362 ep66 ep361 831534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1406725496) qz290 0 2 ep360 ep64 ep361 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1406725496) qz291 0 2 ep362 ep66 ep361 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 201289557) qz32)

noncomputable def ep364 := @Enclosure.Real.IsNear.cos_image qz73 qz375 Bool.false 201289557 524288 691 1048576 Bool.false 831534 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 86453206488375007827 225179981368524800 6305250004829291859 9573950000000000000000 201289557 524288 691 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 201289557 524288) (BSN.cos_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49494753283630321106944) qz33) 226375608064910080 72057594037927936 Bool.false 831534 1048576 61 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 201289557 524288 226375608064910080 72057594037927936 61 49494753283630321106944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 831534 1048576 49494753283630321106944 75557863725914323419136 1406725496 2147483648 383332 382958 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep365 := nat_lit 3915952681522087173511285706002272256

noncomputable def ep366 := BSN.sin_dyadic_bound_f 1406725496 2147483648 2 1 1048576 383332 ep365 ep79 ep365 ep365 ep80 ep365 638797 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1406725496) qz286 0 1 ep365 ep79 ep365 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1406725496) qz287 0 1 ep365 ep80 ep365 rfl rfl rfl rfl) rfl rfl

noncomputable def ep367 := @Enclosure.Real.IsNear.sin_image qz73 qz375 Bool.false 201289557 524288 691 1048576 Bool.false 638797 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 86453206488375007827 225179981368524800 6305250004829291859 9573950000000000000000 201289557 524288 691 1048576 (ep359 rfl) rfl) (Enclosure.sfrac_false_div 201289557 524288) (BSN.sin_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49494753283630321106944) qz33) 226375608064910080 72057594037927936 Bool.false 638797 1048576 61 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 201289557 524288 226375608064910080 72057594037927936 61 49494753283630321106944 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 638797 1048576 49494753283630321106944 75557863725914323419136 1406725496 2147483648 383332 382958 (ep366 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep357 rfl rfl) rfl)

noncomputable def ep368 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.false 47567486703 274877906944 3854250885109 26316673371865088 Bool.true 73084125973 549755813888 15380098452413 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz73) 114409 524288 1 524288 415767 524288 133360565 200780283904 47567486703 274877906944 3854250885109 26316673371865088 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.false 831534 1048576 133360565 200780283904 415767 524288 133360565 200780283904 (ep364 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 114409 524288 1 524288 638797 1048576 133360565 200780283904 73084125973 549755813888 15380098452413 105266693487460352 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.false 638797 1048576 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.false 638797 1048576 133360565 200780283904 638797 1048576 133360565 200780283904 (ep367 rfl rfl) rfl)) rfl)

noncomputable def ep369 := @ep295 47567486703 274877906944 3854250885109 26316673371865088 Bool.true 73084125973 549755813888 15380098452413 105266693487460352 Bool.false 40606933057691893891072 1181817295079 274877906944 59807197297909 13158336685932544 Bool.true 125250978729660549955584 227830203093 1099511627776 956422073257795 210533386974920704 (ep296 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep355 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep356 ep368) rfl rfl

noncomputable abbrev qz377 := (@Nat.cast Real Real.instNatCast 22)

noncomputable abbrev qz74 := (@Inv.inv Real Real.instInv (Real.sqrt qz377))

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz267 qz283 qz564)

noncomputable def ep370 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz351 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.false 113895808347 549755813888 1875557949093 13158336685932544 Bool.true 55335499311 1099511627776 29861216646787 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 22 qz14 rfl)

noncomputable abbrev qz378 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz15)

noncomputable def ep371 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz377) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz377) (Real.sqrt qz378) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz378) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep372 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 191479 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep373 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz564 126105 1000 0 1 3480203401436407 1125899906842624 250000000191479 47869750000000000000 87774209987627620947 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz378) Bool.false 58388124189833310502912 18889465931478580854784 1000000000765916 191479000000000000000 3480203401436407 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep374 := nat_lit 68590228812914234272344785938397761

noncomputable def ep375 := BSN.cos_dyadic_bound_f 511759087 2147483648 2 1 1048576 383332 ep374 ep75 ep374 ep374 ep76 ep374 1018942 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 511759087) qz290 0 1 ep374 ep75 ep374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 511759087) qz291 0 1 ep374 ep76 ep374 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz379 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 102182629) qz555)

noncomputable def ep376 := @Enclosure.Real.IsNear.cos_image qz75 qz379 Bool.false 102182629 262144 691 1048576 Bool.false 1018942 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 87774209987627620947 225179981368524800 6305250004829291859 9573950000000000000000 102182629 262144 691 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 102182629 262144) (BSN.cos_reduce0 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9002961079592999190528) qz336) 226375608064910080 72057594037927936 Bool.false 1018942 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 102182629 262144 226375608064910080 72057594037927936 62 9002961079592999190528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1018942 1048576 9002961079592999190528 37778931862957161709568 511759087 2147483648 383332 382958 (ep375 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep377 := BSN.sin_dyadic_bound_f 511759087 2147483648 2 1 1048576 383332 ep374 ep79 ep374 ep374 ep80 ep374 247523 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 511759087) qz286 0 1 ep374 ep79 ep374 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 511759087) qz287 0 1 ep374 ep80 ep374 rfl rfl rfl rfl) rfl rfl

noncomputable def ep378 := @Enclosure.Real.IsNear.sin_image qz75 qz379 Bool.false 102182629 262144 691 1048576 Bool.false 247523 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 87774209987627620947 225179981368524800 6305250004829291859 9573950000000000000000 102182629 262144 691 1048576 (ep373 rfl) rfl) (Enclosure.sfrac_false_div 102182629 262144) (BSN.sin_reduce0 qz379 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9002961079592999190528) qz336) 226375608064910080 72057594037927936 Bool.false 247523 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 102182629 262144 226375608064910080 72057594037927936 62 9002961079592999190528 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 247523 1048576 9002961079592999190528 37778931862957161709568 511759087 2147483648 383332 382958 (ep377 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz380 := (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep371 rfl rfl) rfl)

noncomputable def ep379 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.false 113895808347 549755813888 1875557949093 13158336685932544 Bool.true 55335499311 1099511627776 29861216646787 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz74 (Real.cos qz75) 223557 1048576 1 1048576 509471 524288 133360565 200780283904 113895808347 549755813888 1875557949093 13158336685932544 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.false 1018942 1048576 133360565 200780283904 509471 524288 133360565 200780283904 (ep376 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 223557 1048576 1 1048576 247523 1048576 133360565 200780283904 55335499311 1099511627776 29861216646787 210533386974920704 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.false 247523 1048576 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.false 247523 1048576 133360565 200780283904 247523 1048576 133360565 200780283904 (ep378 rfl rfl) rfl)) rfl)

noncomputable def ep380 := @ep293 113895808347 549755813888 1875557949093 13158336685932544 Bool.true 55335499311 1099511627776 29861216646787 210533386974920704 Bool.false 681018370331188626718720 2477530398505 549755813888 30841377623501 6579168342966272 Bool.true 311343982380556436373504 70791425601 274877906944 493141644952291 105266693487460352 (ep294 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep369 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep370 ep379) rfl rfl

noncomputable abbrev qz381 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz76 := (@Inv.inv Real Real.instInv (Real.sqrt qz381))

noncomputable abbrev qz565 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz267 qz283 qz565)

noncomputable def ep381 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz350 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 207483679923 1099511627776 29340193477179 210533386974920704 Bool.false 97531176225 1099511627776 29243901368785 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 23 qz14 rfl)

noncomputable abbrev qz382 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz15)

noncomputable def ep382 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz381) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz381) (Real.sqrt qz382) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz382) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep383 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 191479 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep384 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz565 126105 1000 0 1 3530250507853047 1125899906842624 250000000191479 47869750000000000000 89036448058561698387 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 59227775304360265777152 18889465931478580854784 1000000000765916 191479000000000000000 3530250507853047 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep385 := nat_lit 2242284036809976768294291563015925996900097477105270114783348344987416501989185

noncomputable def ep386 := nat_lit 1214250421281616827059202154204501108181565524768607418831076503137384968001

noncomputable def ep387 := nat_lit 5870682738582149870669810623458713180563199429187986840992566779676249358118721

noncomputable def ep388 := BSN.sin_dyadic_bound_f 2429621001 2147483648 3 2 1048576 383332 ep385 ep57 ep386 ep387 ep60 ep386 948961 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2429621001) qz286 0 2 ep385 ep57 ep386 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2429621001) qz287 0 2 ep387 ep60 ep386 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz383 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207304135) qz32)

noncomputable def ep389 := @Enclosure.Real.IsNear.cos_image qz77 qz383 Bool.false 207304135 524288 691 1048576 Bool.false 948961 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 89036448058561698387 225179981368524800 6305250004829291859 9573950000000000000000 207304135 524288 691 1048576 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 207304135 524288) (BSN.cos_reduce3 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85484689342586347847680) qz33) 226375608064910080 72057594037927936 Bool.false 948961 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 207304135 524288 226375608064910080 72057594037927936 62 85484689342586347847680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 948961 1048576 85484689342586347847680 75557863725914323419136 2429621001 2147483648 383332 382958 (ep388 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep390 := nat_lit 1246253020637223367642188291521827554325912627513936111510229558994403561090881

noncomputable def ep391 := nat_lit 3736330561069106869272446470257073660761374751492271119693026523976935913336641

noncomputable def ep392 := BSN.cos_dyadic_bound_f 2429621001 2147483648 3 2 1048576 383332 ep390 ep64 ep386 ep391 ep66 ep386 446075 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2429621001) qz290 0 2 ep390 ep64 ep386 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2429621001) qz291 0 2 ep391 ep66 ep386 rfl rfl rfl rfl) rfl rfl

noncomputable def ep393 := @Enclosure.Real.IsNear.sin_image qz77 qz383 Bool.false 207304135 524288 691 1048576 Bool.true 446075 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 89036448058561698387 225179981368524800 6305250004829291859 9573950000000000000000 207304135 524288 691 1048576 (ep384 rfl) rfl) (Enclosure.sfrac_false_div 207304135 524288) (BSN.sin_reduce3 qz383 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 85484689342586347847680) qz33) 226375608064910080 72057594037927936 Bool.false 446075 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 207304135 524288 226375608064910080 72057594037927936 62 85484689342586347847680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 446075 1048576 85484689342586347847680 75557863725914323419136 2429621001 2147483648 383332 382958 (ep392 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz384 := (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep382 rfl rfl) rfl)

noncomputable def ep394 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 207483679923 1099511627776 29340193477179 210533386974920704 Bool.false 97531176225 1099511627776 29243901368785 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz77) 218643 1048576 1 1048576 948961 1048576 133360565 200780283904 207483679923 1099511627776 29340193477179 210533386974920704 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 948961 1048576 133360565 200780283904 948961 1048576 133360565 200780283904 (ep389 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz76 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 218643 1048576 1 1048576 446075 1048576 133360565 200780283904 97531176225 1099511627776 29243901368785 210533386974920704 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.true 446075 1048576 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.true 446075 1048576 133360565 200780283904 446075 1048576 133360565 200780283904 (ep393 rfl rfl) rfl)) rfl)

noncomputable def ep395 := @ep290 207483679923 1099511627776 29340193477179 210533386974920704 Bool.false 97531176225 1099511627776 29243901368785 210533386974920704 Bool.false ep291 5162544476933 1099511627776 1016264277429211 210533386974920704 Bool.true 51026830012624693886976 185634526179 1099511627776 1015527191273367 210533386974920704 (ep292 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep380 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep381 ep394) rfl rfl

noncomputable abbrev qz385 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz78 := (@Inv.inv Real Real.instInv (Real.sqrt qz385))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz79 := (@HMul.hMul Real Real Real qz267 qz283 qz566)

noncomputable def ep396 := @Enclosure.Complex.IsNear.of_eq qz63 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)))) Bool.false 47947946585 1099511627776 28587389500785 210533386974920704 Bool.false 219254488313 1099511627776 28740640101393 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 24 qz14 rfl)

noncomputable abbrev qz386 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz15)

noncomputable def ep397 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz385) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz385) (Real.sqrt qz386) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz386) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep398 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 191479 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep399 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz566 126105 1000 0 1 3578169457974519 1125899906842624 250000000191479 47869750000000000000 90245011899575343699 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz386) Bool.false 60031721881041427759104 18889465931478580854784 1000000000765916 191479000000000000000 3578169457974519 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep400 := nat_lit 45695117811812308835466864047947776

noncomputable def ep401 := BSN.sin_dyadic_bound_f 462346368 2147483648 2 1 1048576 383332 ep400 ep79 ep400 ep400 ep80 ep400 224015 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 462346368) qz286 0 1 ep400 ep79 ep400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 462346368) qz287 0 1 ep400 ep80 ep400 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz387 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 105059021) qz555)

noncomputable def ep402 := @Enclosure.Real.IsNear.cos_image qz79 qz387 Bool.false 105059021 262144 691 1048576 Bool.false 224015 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 90245011899575343699 225179981368524800 6305250004829291859 9573950000000000000000 105059021 262144 691 1048576 (ep399 rfl) rfl) (Enclosure.sfrac_false_div 105059021 262144) (BSN.cos_reduce3 qz387 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8133683335505706483712) qz336) 226375608064910080 72057594037927936 Bool.false 224015 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 105059021 262144 226375608064910080 72057594037927936 63 8133683335505706483712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 224015 1048576 8133683335505706483712 37778931862957161709568 462346368 2147483648 383332 382958 (ep401 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep403 := BSN.cos_dyadic_bound_f 462346368 2147483648 2 1 1048576 383332 ep400 ep75 ep400 ep400 ep76 ep400 1024367 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 462346368) qz290 0 1 ep400 ep75 ep400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 462346368) qz291 0 1 ep400 ep76 ep400 rfl rfl rfl rfl) rfl rfl

noncomputable def ep404 := @Enclosure.Real.IsNear.sin_image qz79 qz387 Bool.false 105059021 262144 691 1048576 Bool.true 1024367 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz79 Bool.false 90245011899575343699 225179981368524800 6305250004829291859 9573950000000000000000 105059021 262144 691 1048576 (ep399 rfl) rfl) (Enclosure.sfrac_false_div 105059021 262144) (BSN.sin_reduce3 qz387 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8133683335505706483712) qz336) 226375608064910080 72057594037927936 Bool.false 1024367 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 105059021 262144 226375608064910080 72057594037927936 63 8133683335505706483712 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1024367 1048576 8133683335505706483712 37778931862957161709568 462346368 2147483648 383332 382958 (ep403 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz388 := (@Enclosure.Real.IsNear.recentre' qz78 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep397 rfl rfl) rfl)

noncomputable def ep405 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz79)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79))) Bool.false 47947946585 1099511627776 28587389500785 210533386974920704 Bool.false 219254488313 1099511627776 28740640101393 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz78 (Real.cos qz79) 214039 1048576 1 1048576 224015 1048576 133360565 200780283904 47947946585 1099511627776 28587389500785 210533386974920704 qz388 (@Enclosure.Real.IsNear.recentre' (Real.cos qz79) Bool.false 224015 1048576 133360565 200780283904 224015 1048576 133360565 200780283904 (ep402 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz79)) 214039 1048576 1 1048576 1024367 1048576 133360565 200780283904 219254488313 1099511627776 28740640101393 210533386974920704 qz388 (@Enclosure.Real.IsNear.neg (Real.sin qz79) Bool.true 1024367 1048576 133360565 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz79) Bool.true 1024367 1048576 133360565 200780283904 1024367 1048576 133360565 200780283904 (ep404 rfl rfl) rfl)) rfl)

noncomputable def ep406 := @ep287 47947946585 1099511627776 28587389500785 210533386974920704 Bool.false 219254488313 1099511627776 28740640101393 210533386974920704 Bool.false ep288 2605246211759 549755813888 261212916732499 52633346743730176 Bool.false 36965539291721822633984 16809981067 549755813888 130533478921845 26316673371865088 (ep289 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep395 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep396 ep405) rfl rfl

theorem EMRow42.d8 : Enclosure.Complex.IsNear qz62 Bool.false 2605246211759 549755813888 261212916732499 52633346743730176 Bool.false 16809981067 549755813888 130533478921845 26316673371865088 := ep286 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep406 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow42.d9 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow42.d10 : @Eq Nat (Nat.pow 26 1) 26 := @Eq.refl Nat 26

noncomputable def ep407 := nat_lit 34538876814077682559846983250741

noncomputable def ep408 := nat_lit 7627189045418150941904234086400

noncomputable def ep409 := nat_lit 1887845411879303704902303927006702628853

noncomputable def ep410 := nat_lit 279644841352933856720626378099992716902400

noncomputable abbrev qz594 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz567 := qz594

noncomputable abbrev qz389 := qz567

noncomputable abbrev qz80 := qz389

noncomputable abbrev qz568 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz390 := qz568

noncomputable abbrev qz81 := qz390

noncomputable abbrev qz595 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz596 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz569 := (@HAdd.hAdd Complex Complex Complex qz592 (@HAdd.hAdd Complex Complex Complex qz592 qz595 (@HMul.hMul Complex Complex Complex qz594 Complex.I (@HDiv.hDiv Complex Complex Complex qz596 (↑qz593) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz391 := qz569

noncomputable abbrev qz82 := (Complex.Stirling.logGammaStirling 1 qz391)

noncomputable abbrev qz570 := (@HAdd.hAdd Complex Complex Complex qz592 qz595 (@HMul.hMul Complex Complex Complex qz594 Complex.I (@HDiv.hDiv Complex Complex Complex qz596 (↑qz593) (2 : Complex))))

noncomputable abbrev qz392 := qz570

noncomputable abbrev qz83 := qz392

noncomputable abbrev qz84 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz283 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz393 := (@instHSub Real Real.instSub)

noncomputable def ep411 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84))) (zetaApproximant qz5 1 26))

noncomputable def ep412 := @Enclosure.Real.IsNear.of_eq ep411 (@HSub.hSub Real Real Real qz393 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 26))))

noncomputable def ep413 := nat_lit 2763136115279149762794763273163

noncomputable def ep414 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 26))) ep413

noncomputable def ep415 := nat_lit 610175123633452075352338726912

noncomputable def ep416 := nat_lit 3761363092719669837134668876341221576969

noncomputable def ep417 := nat_lit 559289682705867713441252756199985433804800

noncomputable def ep418 := nat_lit 649253823378950175115327593

noncomputable def ep419 := nat_lit 15254378090836301883808468172800

noncomputable def ep420 := nat_lit 14327731038937572669938977672183680737

noncomputable def ep421 := nat_lit 42149526860380842571451737961137475862845766131329742441283584

noncomputable def ep422 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.re (zetaApproximant qz5 1 26)) 1048575 1048576 34033113

noncomputable def ep423 := nat_lit 197635084420223858293023623

noncomputable def ep424 := nat_lit 43643125793942361499238400

noncomputable def ep425 := nat_lit 8671487258641538317099238383

noncomputable def ep426 := nat_lit 1671348416779657887502533918720

noncomputable def ep427 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.false 1048575 1048576 34033113

noncomputable abbrev qz394 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65884349) qz32)

noncomputable def ep428 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz394 Bool.false 65884349 524288 175

noncomputable def ep429 := nat_lit 13357615770098159828734781

noncomputable def ep430 := nat_lit 40156056780800000000000000000

noncomputable def ep431 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) Bool.false 452753799525858895569 3602879701896396800 ep429 ep430

noncomputable def ep432 := nat_lit 3699032052098159828734781

noncomputable def ep433 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84 712802681244413159121 3602879701896396800 ep432 ep430 1892104641 26214400

noncomputable def ep434 := nat_lit 11868669202290675432003993600

noncomputable def ep435 := nat_lit 1721183794784197773813049

noncomputable def ep436 := nat_lit 10039014195200000000000000000

noncomputable def ep437 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 89315111090765786129 900719925474099200 ep435 ep436 Bool.false 712802681244413159121 3602879701896396800

noncomputable def ep438 := nat_lit 1694969394673768617665849

noncomputable def ep439 := nat_lit 3489316852058003771953981

noncomputable def ep440 := @Enclosure.Complex.IsNear.subLitP qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 81849818858055303529 900719925474099200 ep438 ep436 Bool.false 724035761588221197521 3602879701896396800 ep439

noncomputable def ep441 := nat_lit 402239501026927248953610534580649984

noncomputable def ep442 := nat_lit 200636118102564346340097334104293376

noncomputable abbrev qz597 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz571 := qz597

noncomputable abbrev qz395 := (@HSub.hSub Complex Complex Complex qz568 qz569 qz571)

noncomputable abbrev qz396 := (Complex.log qz569)

noncomputable abbrev qz85 := (@HSub.hSub Complex Complex Complex qz390 (@HMul.hMul Complex Complex Complex qz389 qz395 qz396) qz391)

noncomputable abbrev qz397 := qz571

noncomputable abbrev qz86 := (@HMul.hMul Complex Complex Complex qz389 qz397 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz572 := qz596

noncomputable abbrev qz398 := qz572

noncomputable abbrev qz87 := qz398

noncomputable abbrev qz88 := (@instHMul Nat instMulNat)

noncomputable abbrev qz573 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz399 := qz573

noncomputable abbrev qz89 := qz399

noncomputable abbrev qz90 := qz391

noncomputable abbrev qz400 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz91 := qz400

noncomputable abbrev qz401 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz92 := qz401

noncomputable abbrev qz402 := (@instHSub Int Int.instSub)

noncomputable abbrev qz403 := (@instHMul Int Int.instMul)

noncomputable def ep443 := @Enclosure.Complex.IsNear.of_eq qz82 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 81849818858055303529

noncomputable def ep444 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz85 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 81849861284213588329 900719925474099200

noncomputable def ep445 := nat_lit 5624676722861945517062534201344

noncomputable def ep446 := nat_lit 4975535867449380899466642037145600

noncomputable def ep447 := @ep444 25863173773393523909 153183200000000000000000 Bool.false 724040517277723868369 3602879701896396800 13310500053256245749 153183200000000000000000 Bool.false 3236859 68719476736 3 68719476736 Bool.true 9070757871 6871947673600 8407 6871947673600 Bool.true ep445 81849818858055303529 900719925474099200 ep438 ep436 Bool.false ep446

noncomputable def ep448 := @Enclosure.Complex.IsNear.addLitP qz85 qz86 Bool.true 82677566765655687529 900719925474099200 25571000006303680159 153183200000000000000000

noncomputable def ep449 := nat_lit 10728225018244443449458688

noncomputable def ep450 := @ep448 Bool.false 724040517277723868369 3602879701896396800 13310500053256245749 153183200000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep449 81849861284213588329 900719925474099200 25863173773393523909 153183200000000000000000 Bool.false 724040517277723868369 724040517277723868369 3602879701896396800

noncomputable abbrev qz93 := (@HMul.hMul Complex Complex Complex qz389 qz395 qz396)

noncomputable def ep451 := @Enclosure.Complex.IsNear.subLitP qz93 qz90 Bool.true 80650946933338964329 900719925474099200 25571000006303680159 153183200000000000000000 Bool.false 951211089681546427601

noncomputable def ep452 := nat_lit 2896162069110895473476000

noncomputable def ep453 := @ep451 3602879701896396800 13310500053256245749 153183200000000000000000 Bool.false 9000 4000 0 1 Bool.false 252210 4000 0 1 Bool.true 330710267062622750116000 82677566765655687529 900719925474099200 25571000006303680159 153183200000000000000000 Bool.false ep452 724040517277723868369 3602879701896396800 13310500053256245749 153183200000000000000000

noncomputable abbrev qz94 := qz395

noncomputable abbrev qz95 := qz396

noncomputable def ep454 := @Enclosure.Complex.IsNear.mul qz94 qz95 Bool.true 80650946933338964329 900719925474099200 25571000006303680159 153183200000000000000000 Bool.false 951211089681546427601 3602879701896396800 13310500053256245749

noncomputable abbrev qz96 := (Complex.re qz395)

noncomputable abbrev qz97 := (Complex.re qz396)

noncomputable abbrev qz98 := (Complex.im qz395)

noncomputable abbrev qz99 := (Complex.im qz396)

noncomputable def ep455 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz96 qz97) (@HMul.hMul Real Real Real qz0 qz98 qz99) 261318915720853067 36028797018963968 3500000014743883 1531832000000000000000 21795979956590072751 225179981368524800

noncomputable def ep456 := nat_lit 726439149112126013703330116422074368

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 7000 4000 0 1 37331273674407581 9007199254740992 500000002106269 382958000000000000000

noncomputable def ep458 := @Enclosure.Complex.IsNear.re_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable abbrev qz100 := (Enclosure.sfrac Bool.false 252210 4000)

noncomputable def ep459 := @Enclosure.Complex.IsNear.of_eq qz94 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz100) Bool.false 7000 4000 0 1 Bool.false 252210 4000 0

noncomputable abbrev qz404 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz101 := qz404

noncomputable abbrev qz405 := (Complex.log (Complex.mk qz101 qz100))

noncomputable def ep460 := @Enclosure.Complex.IsNear.of_eq qz95 qz405 Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep461 := nat_lit 87674772349118177994076332398344099090596295246919851298228248114731071284953159096127010762181326551669900951935000000000000000000000000

noncomputable def ep462 := nat_lit 3203496921167671947147720799502670000732509004207276125957695424258757835618647133900309938235774774236108778032000000000000000000000000

noncomputable def ep463 := nat_lit 7946655864602808443717027304479830310368778752064250608146774235554482664885869143011920858382961926903995000000000000000000000000

noncomputable def ep464 := BSN.log_dyadic_bound 30922884100 96458884100 7 6 ep461 1048576 382958 ep462 ep463 696872 127381768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30922884100) (BSN.artanhQ 96458884100) 0 6 ep462 ep461 ep463 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz102 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz406 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz407 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable abbrev qz574 := (Real.log (Enclosure.sfrac Bool.false 63690884100 16000000))

noncomputable def ep465 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz574 1 2 0 1 37331273674407581 4503599627370496 500000002106269 191479000000000000000 37331273674407581 9007199254740992 500000002106269 382958000000000000000 qz406 (BSN.isNear_log_sfrac 63690884100 16000000 37331273674407581 4503599627370496 500000002106269 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63690884100) qz407)) Bool.false 313157420995324829237248 37778931862957161709568 1000000004212538 382958000000000000000 37331273674407581 4503599627370496 500000002106269 191479000000000000000 (BSN.log_rat_reduce_isNear 63690884100 16000000 11 127381768200 65536000000 696872 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep464 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep466 := BSN.arctan_dyadic_bound_f 9000 252210 1 0 1048576 382958 0 1 1 0 1 1 37402 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz103 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz104 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz406 BSN.pi_near_15 rfl)

noncomputable abbrev qz408 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 252210)))

noncomputable def ep467 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz408 884279719003555 562949953421312 1 2000000000000000 37402 1048576 1 382958 906179036476007776256 864199673152931 562949953421312 1000000000191479 382958000000000000000 qz104 (ep466 rfl) rfl rfl

noncomputable abbrev qz409 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252210) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep468 := @Enclosure.Complex.IsNear.re_isNear qz95 Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (ep460 (@congrArg Complex Complex qz90 (Complex.mk qz101 qz100) Complex.log (BSN.w_shift_mk qz13 Bool.false 126105 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz405 Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz405) (@HMul.hMul Real Real Real qz0 qz102 qz574) Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 (Enclosure.clog_re_eq 9000 252210 4000 63690884100 16000000 rfl rfl rfl) (ep465 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz405) qz409 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 9000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz409 (@HSub.hSub Real Real Real qz393 qz103 qz408) Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 252210 9000 rfl rfl) ep467))))

noncomputable def ep469 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz99 252210 4000 0 1 864199673152931 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep470 := @Enclosure.Complex.IsNear.im_isNear qz94 Bool.false 7000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable def ep471 := @Enclosure.Complex.IsNear.im_isNear qz95 Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (ep460 (@congrArg Complex Complex qz90 (Complex.mk qz101 qz100) Complex.log (BSN.w_shift_mk qz13 Bool.false 126105 1000 2 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz405 Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz405) (@HMul.hMul Real Real Real qz0 qz102 qz574) Bool.false 37331273674407581 9007199254740992 500000002106269 382958000000000000000 (Enclosure.clog_re_eq 9000 252210 4000 63690884100 16000000 rfl rfl rfl) (ep465 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz405) qz409 Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 9000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz409 (@HSub.hSub Real Real Real qz393 qz103 qz408) Bool.false 864199673152931 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 252210 9000 rfl rfl) ep467))))

noncomputable abbrev qz105 := (@ep459 1 (BSN.w_sub_half_mk qz283 Bool.false 126105 1000 2 qz285 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 252210 4000) Bool.false 7000 4000 0 1 Bool.false 252210 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 252210 4000)))

noncomputable def ep472 := @ep455 25221000004829291859 153183200000000000000000 ep456 80650946933338964329 900719925474099200 25571000006303680159 153183200000000000000000 (@ep457 261318915720853067 36028797018963968 3500000014743883 1531832000000000000000 (ep458 qz105) ep468 rfl) (@ep469 21795979956590072751 225179981368524800 25221000004829291859 153183200000000000000000 (ep470 qz105) ep471 rfl) rfl

noncomputable def ep473 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz96 qz99) (@HMul.hMul Real Real Real qz0 qz98 qz97) 6049397712070517 2251799813685248 7000000001340353 1531832000000000000000 941532053342233600401 3602879701896396800

noncomputable def ep474 := nat_lit 2141936954520247972004850165033730048

noncomputable def ep475 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz99 7000 4000 0 1 864199673152931 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep476 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz97 252210 4000 0 1 37331273674407581 9007199254740992 500000002106269 382958000000000000000

noncomputable def ep477 := @ep473 12610500053122210449 153183200000000000000000 ep474 951211089681546427601 3602879701896396800 13310500053256245749 153183200000000000000000 (@ep475 6049397712070517 2251799813685248 7000000001340353 1531832000000000000000 (ep458 qz105) ep471 rfl) (@ep476 941532053342233600401 3602879701896396800 12610500053122210449 153183200000000000000000 (ep470 qz105) ep468 rfl) rfl

noncomputable def ep478 := @Enclosure.Complex.IsNear.of_eq qz90 (Complex.mk qz101 qz100) Bool.false 9000 4000 0 1 Bool.false 252210 4000 0 1 (BSN.w_shift_mk qz13 Bool.false 126105 1000 2 qz14 rfl)

noncomputable abbrev qz410 := (ep478 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 252210 4000) Bool.false 9000 4000 0 1 Bool.false 252210 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 252210 4000)))

noncomputable abbrev qz106 := qz410

noncomputable def ep479 := ep453 (@ep454 153183200000000000000000 (ep472 rfl) (ep477 rfl)) qz106 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz107 := qz397

noncomputable def ep480 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz107) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz107) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep481 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz107) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz108 := (@Enclosure.Complex.IsNear.of_eq qz397 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz282) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz282 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz406 qz293))

noncomputable def ep482 := ep481 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz108) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow42.d4)

noncomputable def ep483 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz107) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep484 := ep483 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz108) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep485 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz107) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz107) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep486 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz107) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep487 := ep486 (@Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz108) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz20)

noncomputable def ep488 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz107) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep489 := ep488 (@Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz108) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow42.d4)

noncomputable def ep490 := @ep450 13310500053256245749 153183200000000000000000 (ep479 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz107 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep480 131072 1 524288 (ep482 rfl) (ep484 rfl) rfl rfl) (@ep485 1 0 1 (ep487 rfl) (ep489 rfl) rfl rfl))

noncomputable abbrev qz109 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz411 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz110 := (@HMul.hMul Complex Complex Complex qz389 (@HMul.hMul Complex Complex Complex qz389 (2 : Complex) qz411) (@HSub.hSub Complex Complex Complex qz390 (@HMul.hMul Complex Complex Complex qz389 (2 : Complex) qz411) (1 : Complex)))

noncomputable abbrev qz412 := (@HPow.hPow Complex Int Complex qz573 qz569 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz111 := qz412

noncomputable def ep491 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz111)) Bool.false 3236859 68719476736 3 68719476736

noncomputable def ep492 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz111) Bool.false 0 1 0 1 Bool.false

noncomputable def ep493 := @ep492 0 1 0 1 Bool.false 3236859 68719476736 3 68719476736 Bool.true 9070757871 6871947673600 8407 6871947673600 Bool.false 3236859 3236859 68719476736 3 68719476736 Bool.true 9070757871 9070757871 6871947673600 8407

noncomputable def ep494 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz90 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep495 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz111 Bool.false 3236859 68719476736 3 68719476736 Bool.true 9070757871 6871947673600 8407 6871947673600

noncomputable abbrev qz112 := (Complex.re qz412)

noncomputable abbrev qz113 := (Complex.im qz412)

noncomputable def ep496 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz112) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz113) 3236859 68719476736 3 68719476736 0 1 0

noncomputable def ep497 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz112 1 12 0 1 9710577 17179869184 9 17179869184 3236859

noncomputable def ep498 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz413 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz20)

noncomputable def ep499 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep498 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz413)

noncomputable def ep500 := @Enclosure.Complex.IsNear.re_isNear qz111 Bool.false 9710577 17179869184 9 17179869184 Bool.true 27212273613 1717986918400 25221 1717986918400

noncomputable abbrev qz575 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz414 := (@HPow.hPow Complex Nat Complex qz575 qz569 1)

noncomputable abbrev qz114 := (@Inv.inv Complex Complex.instInv qz414)

noncomputable def ep501 := @Enclosure.Complex.IsNear.of_eq qz111 qz114 Bool.false 9710577 17179869184 9 17179869184 Bool.true 27212273613 1717986918400 25221

noncomputable def ep502 := @Enclosure.Complex.IsNear.of_parts qz114 Bool.false 9710577 17179869184 9 17179869184 Bool.true 27212273613 1717986918400 25221

noncomputable abbrev qz115 := (Complex.re qz414)

noncomputable abbrev qz116 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz117 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz118 := qz414

noncomputable def ep503 := @Enclosure.Real.IsNear.mulLit_ff qz115 (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118)) 9000 4000 0 1 1078953 4294967296 1 4294967296

noncomputable def ep504 := @Enclosure.Complex.IsNear.re_isNear qz118 Bool.false 9000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable def ep505 := @Enclosure.Complex.IsNear.of_eq qz118 qz90 Bool.false 9000 4000 0 1 Bool.false 252210 4000 0

noncomputable def ep506 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118)) Bool.false 1078953 4294967296 1 4294967296 1078953 4294967296 1

noncomputable abbrev qz119 := (Complex.im qz414)

noncomputable abbrev qz415 := (@instHAdd Real Real.instAdd)

noncomputable def ep507 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118) (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 qz115 qz115) (@HMul.hMul Real Real Real qz0 qz119 qz119)) Bool.false 636908841 160000 0 1

noncomputable def ep508 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz115 qz115) (@HMul.hMul Real Real Real qz0 qz119 qz119) 81 16 0 1 636098841 160000

noncomputable def ep509 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 9000 4000 0 1 9000 4000 0 1

noncomputable def ep510 := @Enclosure.Real.IsNear.mulLit_ff qz119 qz119 252210 4000 0 1 252210 4000 0 1

noncomputable def ep511 := @Enclosure.Complex.IsNear.im_isNear qz118 Bool.false 9000 4000 0 1 Bool.false 252210 4000 0 1

noncomputable abbrev qz120 := (ep504 (@ep505 1 (BSN.pow_one_c qz391) qz410))

noncomputable abbrev qz121 := (ep511 (@ep505 1 (BSN.pow_one_c qz391) qz410))

noncomputable def ep512 := @ep508 0 1 10190541456 636908841 160000 0 1 (@ep509 81 16 0 1 qz120 qz120 rfl) (@ep510 636098841 160000 0 1 qz121 qz121 rfl)

noncomputable def ep513 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118) 636908841 160000 0 1 539476 539477 2147483648 (ep507 (Enclosure.Complex.normSq_eq_mul_add_mul qz118) (ep512 rfl rfl)) rfl

noncomputable def ep514 := @Enclosure.Real.IsNear.of_eq (Complex.re qz114) (@HMul.hMul Real Real Real qz0 qz115 (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118))) Bool.false 9710577 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz118) (@ep503 9710577 17179869184 9 17179869184 qz120 (@ep506 4294967296 (ep513 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep515 := @Enclosure.Real.IsNear.of_eq (Complex.im qz114) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz119) (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118))) Bool.true 27212273613 1717986918400 25221 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz118)

noncomputable def ep516 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz119) (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz118)) 252210 4000 0 1 1078953 4294967296 1

noncomputable def ep517 := @ep516 4294967296 27212273613 1717986918400 25221 1717986918400 (@Enclosure.Real.IsNear.neg qz119 Bool.false 252210 4000 0 1 qz121) (@ep506 4294967296 (ep513 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep518 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz113 0 1 0 1 27212273613 1717986918400 25221 1717986918400 0

noncomputable def ep519 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep498 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz413)

noncomputable def ep520 := @Enclosure.Complex.IsNear.im_isNear qz111 Bool.false 9710577 17179869184 9 17179869184 Bool.true 27212273613 1717986918400 25221 1717986918400

noncomputable abbrev qz122 := (@ep501 1717986918400 (BSN.zpow_one_sub_two_mul qz391 1 1 rfl rfl) (@ep502 1717986918400 ep514 (ep515 ep517)))

noncomputable def ep521 := @ep496 1 3236859 3236859 68719476736 3 68719476736 (@ep497 68719476736 3 68719476736 ep499 (ep500 qz122) rfl) (@ep518 1 0 1 ep519 (ep520 qz122) rfl) rfl

noncomputable def ep522 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz113) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz112) 9070757871 6871947673600 8407 6871947673600 0 1 0

noncomputable def ep523 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz113 1 12 0 1 27212273613 1717986918400 25221 1717986918400 9070757871

noncomputable def ep524 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz112 0 1 0 1 9710577 17179869184 9 17179869184 0

noncomputable def ep525 := @ep522 1 9070757871 9070757871 6871947673600 8407 6871947673600 (@ep523 6871947673600 8407 6871947673600 ep499 (ep520 qz122) rfl) (@ep524 1 0 1 ep519 (ep500 qz122) rfl) rfl

noncomputable abbrev qz123 := (@Enclosure.Complex.IsNear.mk qz282 qz282 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz293 qz293)

noncomputable def ep526 := @ep493 6871947673600 (@ep494 0 1 0 1 (BSN.stirling_sum_base qz90) qz123) (ep495 (ep521 rfl) (ep525 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep527 := @ep447 724035761588221197521 3602879701896396800 ep439 ep430 (ep490 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep491 Bool.true 9070757871 6871947673600 8407 6871947673600 (BSN.stirling_sum_succ qz90 0 1 rfl) (ep526 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep528 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz13 2) Bool.false 37326461163552413 4503599627370496 500000002106269 191479000000000000000 Bool.false 877584401860003 281474976710656

noncomputable abbrev qz124 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz392 qz411))

noncomputable def ep529 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 1) qz124) Bool.false 37326461163552413 4503599627370496 500000002106269 191479000000000000000 Bool.false 877584401860003 281474976710656 1000000000191479 191479000000000000000

noncomputable def ep530 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 1) qz124 Bool.false 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000 Bool.false

noncomputable def ep531 := nat_lit 672413746348935750948005863227392

noncomputable def ep532 := nat_lit 988072196300717281892601167872

noncomputable abbrev qz125 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz392 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep533 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz13 0) qz125) Bool.false 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep534 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz13 0) qz125 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz416 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz100))

noncomputable def ep535 := @Enclosure.Complex.IsNear.of_eq qz125 qz416 Bool.false 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep536 := nat_lit 86806164880873954488569946036875020913097829914134132804302732210538205940935177274184739223059746871901564951935000000000000000000000000

noncomputable def ep537 := nat_lit 3159860731180558998594250880393764200109442808239747303714160701475522720406929467615978909242884080735129578032000000000000000000000000

noncomputable def ep538 := nat_lit 7703432410921730887628644086776547617171058961004132829452507833404614019275656496093505252794992054903995000000000000000000000000

noncomputable def ep539 := BSN.log_dyadic_bound 30842884100 96378884100 7 6 ep536 1048576 382958 ep537 ep538 695554 127221768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30842884100) (BSN.artanhQ 96378884100) 0 6 ep537 ep536 ep538 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep540 := @Enclosure.Real.IsNear.mulLit_ff qz102 (Real.log (Enclosure.sfrac Bool.false 63610884100 16000000)) 1 2 0 1 37325612907511453 4503599627370496 500000002106269 191479000000000000000 37325612907511453 9007199254740992 500000002106269 382958000000000000000 qz406 (BSN.isNear_log_sfrac 63610884100 16000000 37325612907511453 4503599627370496 500000002106269 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63610884100) qz407)) Bool.false 313109935040853834727424 37778931862957161709568 1000000004212538 382958000000000000000 37325612907511453 4503599627370496 500000002106269 191479000000000000000 (BSN.log_rat_reduce_isNear 63610884100 16000000 11 127221768200 65536000000 695554 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep539 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep541 := BSN.arctan_dyadic_bound_f 1000 252210 1 0 1048576 382958 0 1 1 0 1 1 4157 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz417 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz418 := (@Nat.cast Real Real.instNatCast 252210)

noncomputable def ep542 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz418)) 884279719003555 562949953421312 1 2000000000000000 4157 1048576 1 382958 924894307677499293696 882047946622371 562949953421312 1000000000191479 382958000000000000000 qz104 (ep541 rfl) rfl rfl

noncomputable abbrev qz126 := (@HAdd.hAdd Complex Complex Complex qz272 qz392 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz419 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz100)

noncomputable def ep543 := @ep534 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000 Bool.false 37325612907511453 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 882047946622371 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz13 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz13) qz123) (ep535 (@congrArg Complex Complex qz126 qz419 Complex.log (BSN.w_shift_mk qz13 Bool.false 126105 1000 0 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz416 Bool.false 37325612907511453 9007199254740992 500000002106269 382958000000000000000 Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz416) (@HMul.hMul Real Real Real qz0 qz102 (Real.log (Enclosure.sfrac Bool.false 63610884100 16000000))) Bool.false 37325612907511453 9007199254740992 500000002106269 382958000000000000000 (Enclosure.clog_re_eq 1000 252210 4000 63610884100 16000000 rfl rfl rfl) (ep540 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz416) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz417)) Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 1000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz417)) (@HSub.hSub Real Real Real qz393 qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz418))) Bool.false 882047946622371 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 252210 1000 rfl rfl) ep542)))) rfl rfl

noncomputable abbrev qz420 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz100))

noncomputable def ep544 := @Enclosure.Complex.IsNear.of_eq qz124 qz420 Bool.false 37327309419593373 9007199254740992 500000002106269 382958000000000000000 Bool.false 873120857097635 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep545 := nat_lit 87065915180560400899433459180947997032327860604791834849982515870973302491362213870478701755403200992728065751935000000000000000000000000

noncomputable def ep546 := nat_lit 3172895538474371735115915320549211646155698345553405038152146309491441636343634971911976039885730164996623338032000000000000000000000000

noncomputable def ep547 := nat_lit 7775673003424676706858484593598113244170145323728169042796521782238442286764061208765357218980375016503995000000000000000000000000

noncomputable def ep548 := BSN.log_dyadic_bound 30866884100 96402884100 7 6 ep545 1048576 382958 ep546 ep547 695949 127269768200 65536000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base6 (BSN.artanhP 30866884100) (BSN.artanhQ 96402884100) 0 6 ep546 ep545 ep547 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep549 := @Enclosure.Real.IsNear.mulLit_ff qz102 (Real.log (Enclosure.sfrac Bool.false 63634884100 16000000)) 1 2 0 1 37327309419593373 4503599627370496 500000002106269 191479000000000000000 37327309419593373 9007199254740992 500000002106269 382958000000000000000 qz406 (BSN.isNear_log_sfrac 63634884100 16000000 37327309419593373 4503599627370496 500000002106269 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 63634884100) qz407)) Bool.false 313124166415676325494784 37778931862957161709568 1000000004212538 382958000000000000000 37327309419593373 4503599627370496 500000002106269 191479000000000000000 (BSN.log_rat_reduce_isNear 63634884100 16000000 11 127269768200 65536000000 695949 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep548 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep550 := BSN.arctan_dyadic_bound_f 5000 252210 1 0 1048576 382958 0 1 1 0 1 1 20785 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 252210) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 252210) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz421 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep551 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz418)) 884279719003555 562949953421312 1 2000000000000000 20785 1048576 1 382958 915533575852009717760 873120857097635 562949953421312 1000000000191479 382958000000000000000 qz104 (ep550 rfl) rfl rfl

noncomputable abbrev qz127 := (@HAdd.hAdd Complex Complex Complex qz272 qz392 qz411)

noncomputable abbrev qz422 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz100)

noncomputable def ep552 := @ep530 37327309419593373 9007199254740992 500000002106269 382958000000000000000 Bool.false 873120857097635 562949953421312 1000000000191479 382958000000000000000 Bool.false ep531 37326461163552413 4503599627370496 500000002106269 191479000000000000000 Bool.false ep532 877584401860003 281474976710656 1000000000191479 191479000000000000000 (ep533 (BSN.log_sum_c_succ qz13 0 1 rfl) (ep543 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep544 (@congrArg Complex Complex qz127 qz422 Complex.log (BSN.w_shift_mk qz13 Bool.false 126105 1000 1 qz14 rfl)) (@Enclosure.Complex.IsNear.of_parts qz420 Bool.false 37327309419593373 9007199254740992 500000002106269 382958000000000000000 Bool.false 873120857097635 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz420) (@HMul.hMul Real Real Real qz0 qz102 (Real.log (Enclosure.sfrac Bool.false 63634884100 16000000))) Bool.false 37327309419593373 9007199254740992 500000002106269 382958000000000000000 (Enclosure.clog_re_eq 5000 252210 4000 63634884100 16000000 rfl rfl rfl) (ep549 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz420) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz421)) Bool.false 873120857097635 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 5000 252210 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz418 qz421)) (@HSub.hSub Real Real Real qz393 qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz418))) Bool.false 873120857097635 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 252210 5000 rfl rfl) ep551)))) rfl rfl

noncomputable def ep553 := @ep440 ep430 Bool.false 37326461163552413 4503599627370496 500000002106269 191479000000000000000 Bool.false 877584401860003 281474976710656 1000000000191479 191479000000000000000 Bool.true ep441 89315111090765786129 900719925474099200 ep435 ep436 Bool.false ep442 712802681244413159121 3602879701896396800 ep432 ep430 (@ep443 900719925474099200 ep438 ep436 Bool.false 724035761588221197521 3602879701896396800 ep439 ep430 (BSN.logGammaStirling_unfold 1 qz90) (ep527 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep528 1000000000191479 191479000000000000000 (BSN.log_sum_c_eq qz13 2) (ep529 (BSN.log_sum_c_succ qz13 1 2 rfl) (ep552 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz128 := (@HDiv.hDiv Real Real Real qz270 qz283 (2 : Real))

noncomputable def ep554 := @Enclosure.Real.IsNear.mulLit_ff qz128 (Real.log Real.pi) 126105 2000 0 1 75021 65536 1 262144 1892104641 26214400 25221 104857600 (@Enclosure.Real.IsNear.of_eq qz128 (Enclosure.sfrac Bool.false 126105 2000) Bool.false 126105 2000 0 1 (BSN.t_half_eq qz13 Bool.false 126105 1000 qz14) (Enclosure.Real.IsNear.const Bool.false 126105 2000)) EMRow42.d5 rfl

noncomputable def ep555 := @ep433 25221 104857600 ep434 452753799525858895569 3602879701896396800 ep429 ep430 (@ep437 ep432 ep430 (ep553 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep554 rfl rfl

noncomputable def ep556 := BSN.cos_dyadic_bound_f 1539413 2147483648 1 0 1048576 383332 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 1539413) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 1539413) qz291 0 0 rfl) rfl rfl

noncomputable def ep557 := @ep428 524288 Bool.false 1048575 1048576 1 191479 (@ep431 65884349 524288 175 524288 ep555 rfl) (Enclosure.sfrac_false_div 65884349 524288) (BSN.cos_reduce0 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54163299480662704128) qz33) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 20 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 65884349 524288 226375608064910080 72057594037927936 20 54163299480662704128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 54163299480662704128 75557863725914323419136 1539413 2147483648 383332 382958 (ep556 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep558 := nat_lit 14547708597980787166412800

noncomputable def ep559 := nat_lit 14444137083651995264289958253

noncomputable def ep560 := nat_lit 2785580694632763145837556531200

noncomputable abbrev qz576 := (@Nat.cast Complex Complex.instNatCast 26)

noncomputable abbrev qz423 := (@HPow.hPow Complex Complex Complex qz539 qz576 qz540)

noncomputable abbrev qz129 := qz423

noncomputable abbrev qz424 := qz576

noncomputable abbrev qz130 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz398 qz424 (@HSub.hSub Complex Complex Complex qz390 qz271 (1 : Complex))) qz397)

noncomputable abbrev qz131 := (@instHSub Nat instSubNat)

noncomputable abbrev qz425 := qz575

noncomputable abbrev qz132 := qz425

noncomputable abbrev qz133 := qz424

noncomputable def ep561 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 26) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz129 (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep423 ep424 ep425

noncomputable def ep562 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz80 qz129 (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 1258879597747 274877906944 536509713180659 105266693487460352

noncomputable def ep563 := nat_lit 2240712273371180861235577

noncomputable def ep564 := nat_lit 153174105600216471248012143

noncomputable def ep565 := nat_lit 1342623517047164036664857

noncomputable def ep566 := nat_lit 255177971252932467333659053

noncomputable def ep567 := nat_lit 54325518344131877911518390127387738112

noncomputable def ep568 := nat_lit 950548772547511466757728482432647168

noncomputable def ep569 := @ep562 Bool.false 166815201509 1099511627776 1072397444934139 210533386974920704 Bool.true ep563 ep424 ep564 ep426 Bool.true ep565 ep558 ep566 ep560 Bool.false ep567 ep423 ep424 ep425 ep426 Bool.false ep568 864519072408721937570343 ep558

noncomputable def ep570 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 26) Bool.false 1258879597747 274877906944 536509713180659 105266693487460352 Bool.false 166815201509 1099511627776 1072397444934139

noncomputable abbrev qz426 := (@Nat.cast Complex Complex.instNatCast 25)

noncomputable def ep571 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz62 (@HPow.hPow Complex Complex Complex qz6 qz426 qz7)) Bool.false 1258879597747 274877906944 536509713180659 105266693487460352 Bool.false 166815201509 1099511627776 1072397444934139 210533386974920704

noncomputable def ep572 := @Enclosure.Complex.IsNear.addLitP qz62 (@HPow.hPow Complex Complex Complex qz6 qz426 qz7) Bool.false 2605246211759 549755813888 261212916732499 52633346743730176 Bool.false 16809981067 549755813888 130533478921845 26316673371865088 Bool.true

noncomputable def ep573 := nat_lit 1384152755692800072220672

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz134 := (@Inv.inv Real Real.instInv (Real.sqrt qz427))

noncomputable abbrev qz577 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz135 := (@HMul.hMul Real Real Real qz267 qz283 qz577)

noncomputable def ep574 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz426 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135)))) Bool.true 87487016265 549755813888 14083879715661 105266693487460352 Bool.false 133195239375 1099511627776 28129613559379 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 25 qz14 rfl)

noncomputable abbrev qz428 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz15)

noncomputable def ep575 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz427) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz427) (Real.sqrt qz428) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz428) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep576 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 191479 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep577 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz577 126105 1000 0 1 3624129903009015 1125899906842624 250000000191479 47869750000000000000 18280836056758073463 45035996273704960 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz428) Bool.false 60802810194841294602240 18889465931478580854784 1000000000765916 191479000000000000000 3624129903009015 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep578 := nat_lit 136201528325902623962249428998671118658646834294802701327138975172338241904896

noncomputable def ep579 := nat_lit 14528267193532052579716796838958540632357826889133078072359449151284060416

noncomputable def ep580 := nat_lit 408575528443320807781588853402335438894675787230629837825272206618712157593856

noncomputable def ep581 := BSN.cos_dyadic_bound_f 1397258394 2147483648 3 2 1048576 383332 ep578 ep64 ep579 ep580 ep66 ep579 834342 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1397258394) qz290 0 2 ep578 ep64 ep579 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1397258394) qz291 0 2 ep580 ep66 ep579 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz429 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 212816941) qz32)

noncomputable def ep582 := @Enclosure.Real.IsNear.cos_image qz135 qz429 Bool.false 212816941 524288 173 262144 Bool.true 834342 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 18280836056758073463 45035996273704960 6305250004829291859 9573950000000000000000 212816941 524288 173 262144 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 212816941 524288) (BSN.cos_reduce2 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49161659250344021983232) qz33) 226375608064910080 72057594037927936 Bool.false 834342 1048576 64 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 212816941 524288 226375608064910080 72057594037927936 64 49161659250344021983232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 834342 1048576 49161659250344021983232 75557863725914323419136 1397258394 2147483648 383332 382958 (ep581 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep583 := nat_lit 3811596410105882731653846017513703696

noncomputable def ep584 := BSN.sin_dyadic_bound_f 1397258394 2147483648 2 1 1048576 383332 ep583 ep79 ep583 ep583 ep80 ep583 635125 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1397258394) qz286 0 1 ep583 ep79 ep583 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1397258394) qz287 0 1 ep583 ep80 ep583 rfl rfl rfl rfl) rfl rfl

noncomputable def ep585 := @Enclosure.Real.IsNear.sin_image qz135 qz429 Bool.false 212816941 524288 173 262144 Bool.true 635125 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz135 Bool.false 18280836056758073463 45035996273704960 6305250004829291859 9573950000000000000000 212816941 524288 173 262144 (ep577 rfl) rfl) (Enclosure.sfrac_false_div 212816941 524288) (BSN.sin_reduce2 qz429 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 49161659250344021983232) qz33) 226375608064910080 72057594037927936 Bool.false 635125 1048576 64 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 212816941 524288 226375608064910080 72057594037927936 64 49161659250344021983232 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 635125 1048576 49161659250344021983232 75557863725914323419136 1397258394 2147483648 383332 382958 (ep584 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz430 := (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep575 rfl rfl) rfl)

noncomputable def ep586 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz135)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135))) Bool.true 87487016265 549755813888 14083879715661 105266693487460352 Bool.false 133195239375 1099511627776 28129613559379 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz135) 209715 1048576 1 1048576 417171 524288 33388011 50195070976 87487016265 549755813888 14083879715661 105266693487460352 qz430 (@Enclosure.Real.IsNear.recentre' (Real.cos qz135) Bool.true 834342 1048576 33388011 50195070976 417171 524288 33388011 50195070976 (ep582 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz134 (@Neg.neg Real Real.instNeg (Real.sin qz135)) 209715 1048576 1 1048576 635125 1048576 33388011 50195070976 133195239375 1099511627776 28129613559379 210533386974920704 qz430 (@Enclosure.Real.IsNear.neg (Real.sin qz135) Bool.true 635125 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' (Real.sin qz135) Bool.true 635125 1048576 33388011 50195070976 635125 1048576 33388011 50195070976 (ep585 rfl rfl) rfl)) rfl)

noncomputable def ep587 := @ep572 87487016265 549755813888 14083879715661 105266693487460352 Bool.false 133195239375 1099511627776 28129613559379 210533386974920704 Bool.false ep573 1258879597747 274877906944 536509713180659 105266693487460352 Bool.false 91707626874471020756992 166815201509 1099511627776 1072397444934139 210533386974920704 EMRow42.d8 (ep574 ep586) rfl rfl

noncomputable def ep588 := @Enclosure.Complex.IsNear.mul qz129 (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true ep563 ep424 ep564 ep426 Bool.true

noncomputable def ep589 := nat_lit 5490129937784681390360327

noncomputable abbrev qz136 := (Complex.re qz423)

noncomputable abbrev qz137 := (Complex.im qz423)

noncomputable def ep590 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 33150484734124028025163 436431257939423614992384 ep589

noncomputable def ep591 := nat_lit 83567420838982894375126695936

noncomputable def ep592 := nat_lit 14457168948174281146935201

noncomputable def ep593 := nat_lit 557116138926552629167511306240

noncomputable def ep594 := nat_lit 325972292049230038283847713345677732837228281856

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_tf qz136 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 166771743211 1099511627776 27619461601319 210533386974920704 198777587233

noncomputable abbrev qz431 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz138 := (@Inv.inv Real Real.instInv (Real.sqrt qz431))

noncomputable abbrev qz432 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz544 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable abbrev qz139 := (Real.cos qz432)

noncomputable abbrev qz140 := (Real.sin qz432)

noncomputable abbrev qz578 := (@Neg.neg Real Real.instNeg qz140)

noncomputable def ep596 := @Enclosure.Complex.IsNear.of_eq qz129 (Complex.mk (@HMul.hMul Real Real Real qz0 qz138 qz139) (@HMul.hMul Real Real Real qz0 qz138 qz578)) Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (BSN.cpow_neg_s_mk qz13 126105 1000 26 qz14 rfl)

noncomputable abbrev qz433 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15)

noncomputable def ep597 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz431) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz431) (Real.sqrt qz433) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz433) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep598 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 191479 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz434 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz141 := qz434

noncomputable abbrev qz435 := (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz15))

noncomputable def ep599 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz141 126105 1000 0 1 3668288609262839 1125899906842624 250000000191479 47869750000000000000 92517907014218062419 225179981368524800 6305250004829291859 9573950000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz435 Bool.false 61543670347942250676224 18889465931478580854784 1000000000765916 191479000000000000000 3668288609262839 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep598 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep600 := nat_lit 836201379006121383515171730616073363165133780910990459452379020481497072251425

noncomputable def ep601 := nat_lit 168983271783598853661797381220293225161178011964040493313864928560565826081

noncomputable def ep602 := nat_lit 2189777638766477796776664003472502143067946566557033233005151177091013320749601

noncomputable def ep603 := BSN.sin_dyadic_bound_f 1898805427 2147483648 3 2 1048576 383332 ep600 ep57 ep601 ep602 ep60 ep601 810977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1898805427) qz286 0 2 ep600 ep57 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1898805427) qz287 0 2 ep602 ep60 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz142 := qz432

noncomputable abbrev qz436 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107705019) qz555)

noncomputable def ep604 := @Enclosure.Real.IsNear.cos_image qz142 qz436 Bool.false 107705019 262144 173 262144 Bool.true 810977 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 92517907014218062419 225179981368524800 6305250004829291859 9573950000000000000000 107705019 262144 173 262144 (ep599 rfl) rfl) (Enclosure.sfrac_false_div 107705019 262144) (BSN.cos_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33404138350437464014848) qz336) 226375608064910080 72057594037927936 Bool.false 810977 1048576 65 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 107705019 262144 226375608064910080 72057594037927936 65 33404138350437464014848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 810977 1048576 33404138350437464014848 37778931862957161709568 1898805427 2147483648 383332 382958 (ep603 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep605 := nat_lit 464631425346415701443389538067249776525145957400312051026127840235747513840161

noncomputable def ep606 := nat_lit 1393556309495679906622845019439308743125115516177008072091755790850121409868321

noncomputable def ep607 := BSN.cos_dyadic_bound_f 1898805427 2147483648 3 2 1048576 383332 ep605 ep64 ep601 ep606 ep66 ep601 664701 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1898805427) qz290 0 2 ep605 ep64 ep601 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1898805427) qz291 0 2 ep606 ep66 ep601 rfl rfl rfl rfl) rfl rfl

noncomputable def ep608 := @Enclosure.Real.IsNear.sin_image qz142 qz436 Bool.false 107705019 262144 173 262144 Bool.false 664701 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 92517907014218062419 225179981368524800 6305250004829291859 9573950000000000000000 107705019 262144 173 262144 (ep599 rfl) rfl) (Enclosure.sfrac_false_div 107705019 262144) (BSN.sin_reduce1 qz436 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 33404138350437464014848) qz336) 226375608064910080 72057594037927936 Bool.false 664701 1048576 65 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 107705019 262144 226375608064910080 72057594037927936 65 33404138350437464014848 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 664701 1048576 33404138350437464014848 37778931862957161709568 1898805427 2147483648 383332 382958 (ep607 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz437 := (@Enclosure.Real.IsNear.recentre' qz138 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep597 rfl rfl) rfl)

noncomputable def ep609 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz138 qz139) (@HMul.hMul Real Real Real qz0 qz138 qz578) Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz138 qz139 205643 1048576 1 1048576 810977 1048576 33388011 50195070976 166771743211 1099511627776 27619461601319 210533386974920704 qz437 (@Enclosure.Real.IsNear.recentre' qz139 Bool.true 810977 1048576 33388011 50195070976 810977 1048576 33388011 50195070976 (ep604 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz138 qz578 205643 1048576 1 1048576 664701 1048576 33388011 50195070976 136691107743 1099511627776 27591452819115 210533386974920704 qz437 (@Enclosure.Real.IsNear.neg qz140 Bool.false 664701 1048576 33388011 50195070976 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 664701 1048576 33388011 50195070976 664701 1048576 33388011 50195070976 (ep608 rfl rfl) rfl)) rfl)

noncomputable def ep610 := @ep595 396931916784 0 1 33150484734124028025163 436431257939423614992384 ep589 ep591 (@Enclosure.Complex.IsNear.re_isNear qz129 Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (ep596 ep609))

noncomputable def ep611 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 198777587233 396931916784 0 1 Bool.false

noncomputable def ep612 := @Enclosure.Complex.IsNear.addLitP qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 635068841 1272217682 0 1 Bool.true 131149200

noncomputable def ep613 := @ep612 636108841 0 1 Bool.false 1 624 0 1 Bool.false 8407 20800 0 1 Bool.false 397555174466 198777587233 396931916784 0 1 Bool.false 2619863666287 2619863666287 13231063892800 0 1

noncomputable abbrev qz143 := (@HDiv.hDiv Complex Complex Complex qz398 qz424 (@HSub.hSub Complex Complex Complex qz390 qz271 (1 : Complex)))

noncomputable def ep614 := @Enclosure.Complex.IsNear.addLitP qz143 qz107 Bool.true 52000000 63610884100 0 1 Bool.true 13114920000 63610884100 0 1

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq qz143 (Complex.mk (Enclosure.sfrac Bool.true 52000000 63610884100) (Enclosure.sfrac Bool.true 13114920000 63610884100)) Bool.true 52000000 63610884100 0 1 Bool.true 13114920000 63610884100 0 1

noncomputable def ep616 := @ep614 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 63506884100 635068841 1272217682 0 1 Bool.true 13114920000 131149200 636108841 0 1 (ep615 (BSN.N_div_s_sub_one_mk qz13 126105 1000 26 qz14 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 52000000 63610884100) (Enclosure.sfrac Bool.true 13114920000 63610884100) Bool.true 52000000 63610884100 0 1 Bool.true 13114920000 63610884100 0 1 (Enclosure.Real.IsNear.const Bool.true 52000000 63610884100) (Enclosure.Real.IsNear.const Bool.true 13114920000 63610884100))) qz108 rfl

noncomputable abbrev qz144 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz438 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz575 qz576 1))

noncomputable abbrev qz145 := qz438

noncomputable def ep617 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145)) Bool.false 1 624 0 1

noncomputable def ep618 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145) Bool.false 0 1 0 1 Bool.false

noncomputable def ep619 := @ep618 0 1 0 1 Bool.false 1 624 0 1 Bool.false 8407 20800 0 1 Bool.false 1 1 624 0 1 Bool.false 8407 8407 20800 0

noncomputable def ep620 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep621 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz145 Bool.false 1 624 0 1 Bool.false 8407 20800 0 1

noncomputable abbrev qz146 := (Complex.re qz438)

noncomputable abbrev qz147 := (Complex.im qz438)

noncomputable def ep622 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 1 624 0 1 0 1 0

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 1 24 0 1 1 26 0 1 1

noncomputable def ep624 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep625 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep626 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow42.d9 rfl) qz413

noncomputable def ep627 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep628 := ep627 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz102 qz13) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_crit_mk qz13 Bool.false 126105 1000 qz14) (@Enclosure.Complex.IsNear.mk qz102 qz13 Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 qz406 qz18))

noncomputable def ep629 := @ep625 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 126105 1000 0 1 0 1 0

noncomputable def ep631 := @ep630 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep632 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 8407 800 0 1 0 1 0 1 8407

noncomputable def ep633 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 126105 1000 0 1 8407 800 0

noncomputable def ep634 := @ep633 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep635 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep636 := @ep635 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep637 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 (@ep624 1 24 0 1 (ep629 rfl) (ep631 rfl) rfl rfl) (@ep632 8407 800 0 1 (ep634 rfl) (ep636 rfl) rfl rfl)

noncomputable def ep638 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 ep637

noncomputable abbrev qz148 := (@Enclosure.Complex.IsNear.re_isNear qz438 Bool.false 1 26 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz438 (Complex.mk (Enclosure.sfrac Bool.false 1 26) qz282) Bool.false 1 26 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 26 1 26 EMRow42.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 26) qz282 Bool.false 1 26 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 26) qz293)))

noncomputable def ep639 := @ep623 624 0 1 ep638 qz148

noncomputable def ep640 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 8407 800 0 1 0 1 0 1 0

noncomputable def ep641 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 8407 800 0 1 ep637

noncomputable abbrev qz149 := (@Enclosure.Complex.IsNear.im_isNear qz438 Bool.false 1 26 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz438 (Complex.mk (Enclosure.sfrac Bool.false 1 26) qz282) Bool.false 1 26 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 26 1 26 EMRow42.d10 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 26) qz282 Bool.false 1 26 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 26) qz293)))

noncomputable def ep642 := @ep640 1 0 1 ep641 qz149

noncomputable def ep643 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) 0 1 0 1 8407 20800 0

noncomputable def ep644 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 0 1 0 1 0

noncomputable def ep645 := @ep644 1 0 1 ep638 qz149

noncomputable def ep646 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 8407 800 0 1 1 26 0 1 8407

noncomputable def ep647 := @ep646 20800 0 1 ep641 qz148

noncomputable def ep648 := @ep619 1 (@ep620 0 1 0 1 (BSN.bern_sum_base qz5 26) qz123) (ep621 (@ep622 1 1 1 624 0 1 (ep639 rfl) (ep642 rfl) rfl rfl) (@ep643 1 8407 8407 20800 0 1 (ep645 rfl) (ep647 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep649 := ep613 (ep616 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep617 Bool.false 8407 20800 0 1 (BSN.bern_sum_succ qz5 26 0 1 1 rfl rfl) (ep648 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep650 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 136691107743 1099511627776 27591452819115 210533386974920704 2619863666287

noncomputable def ep651 := @ep650 13231063892800 0 1 358112066680407313760241 ep558 ep592 ep593 (@Enclosure.Complex.IsNear.im_isNear qz129 Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (ep596 ep609))

noncomputable def ep652 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 198777587233 396931916784 0 1 Bool.false

noncomputable def ep653 := nat_lit 72359223931704611255032553

noncomputable def ep654 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 436919230601844561827557 ep558 ep653

noncomputable def ep655 := nat_lit 1828187473212278560786265

noncomputable def ep656 := nat_lit 27855806946327631458375565312

noncomputable def ep657 := nat_lit 195320956827982322255024390783703435031605149696

noncomputable def ep658 := @Enclosure.Real.IsNear.mulLit_tf qz136 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 166771743211 1099511627776 27619461601319 210533386974920704 2619863666287

noncomputable def ep659 := @ep658 13231063892800 0 1 436919230601844561827557 ep558 ep653 ep560 (@Enclosure.Complex.IsNear.re_isNear qz129 Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (ep596 ep609))

noncomputable def ep660 := @Enclosure.Real.IsNear.mulLit_tf qz137 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz130 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 136691107743 1099511627776 27591452819115 210533386974920704 198777587233

noncomputable def ep661 := @ep660 396931916784 0 1 9057042864453194748373 145477085979807871664128 ep655 ep656 (@Enclosure.Complex.IsNear.im_isNear qz129 Bool.true 166771743211 1099511627776 27619461601319 210533386974920704 Bool.true 136691107743 1099511627776 27591452819115 210533386974920704 (ep596 ep609))

noncomputable abbrev qz439 := (ep649 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep662 := @ep588 ep565 ep558 ep566 ep560 (@ep590 ep591 358112066680407313760241 ep558 ep592 ep593 ep594 ep563 ep424 ep564 ep426 (ep610 (@ep611 2619863666287 13231063892800 0 1 qz439) rfl) (ep651 (@ep652 2619863666287 13231063892800 0 1 qz439) rfl) rfl rfl) (@ep654 ep560 9057042864453194748373 145477085979807871664128 ep655 ep656 ep657 ep565 ep558 ep566 ep560 (ep659 (@ep652 2619863666287 13231063892800 0 1 qz439) rfl) (ep661 (@ep611 2619863666287 13231063892800 0 1 qz439) rfl) rfl rfl)

noncomputable def ep663 := @ep569 ep559 ep560 (@ep570 210533386974920704 (BSN.head_sum_c_eq qz5 26) (ep571 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep587 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep662 rfl rfl rfl

noncomputable def ep664 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 26) Bool.false ep423 ep424 ep425 ep426 Bool.false 864519072408721937570343 ep558 ep559 ep560 (@ep561 ep426 Bool.false 864519072408721937570343 ep558 ep559 ep560 (BSN.zetaApproximant_eq_folded' qz5 1 26 rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep665 := @Enclosure.Real.IsNear.mulLit_ff (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) (Complex.im (zetaApproximant qz5 1 26)) 751 1048576 34033113

noncomputable def ep666 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84)) Bool.false 751 1048576 34033113

noncomputable def ep667 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) qz394 Bool.false 65884349 524288 175

noncomputable def ep668 := BSN.sin_dyadic_bound_f 1539413 2147483648 1 0 1048576 383332 0 1 1 0 1 1 751 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 1539413) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 1539413) qz287 0 0 rfl) rfl rfl

noncomputable def ep669 := @ep667 524288 Bool.false 751 1048576 1 191479 (@ep431 65884349 524288 175 524288 ep555 rfl) (Enclosure.sfrac_false_div 65884349 524288) (BSN.sin_reduce0 qz394 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54163299480662704128) qz33) 226375608064910080 72057594037927936 Bool.false 751 1048576 20 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 65884349 524288 226375608064910080 72057594037927936 20 54163299480662704128 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 751 1048576 54163299480662704128 75557863725914323419136 1539413 2147483648 383332 382958 (ep668 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep670 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 26) Bool.false ep423 ep424 ep425 ep426 Bool.false 864519072408721937570343 ep558 ep559 ep560 (@ep561 ep426 Bool.false 864519072408721937570343 ep558 ep559 ep560 (BSN.zetaApproximant_eq_folded' qz5 1 26 rfl) (ep663 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow42.d11 : Enclosure.Real.IsNear (hardyZApproximantEM 1 26 qz13) Bool.false ep407 ep408 ep409 ep410 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 26 qz13) ep411 Bool.false ep407 ep408 ep409 ep410 (@Eq.refl Real ep411) (@ep412 Bool.false ep407 ep408 ep409 ep410 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz82 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz83 (@Nat.cast Complex Complex.instNatCast j))))) qz84) (zetaApproximant qz5 1 26)) (@ep414 ep415 ep416 ep417 ep418 ep419 ep420 ep417 ep421 ep407 ep408 ep409 ep410 (@ep422 100390141952 ep423 ep424 ep425 ep426 ep413 ep415 ep416 ep417 (@ep427 100390141952 1048575 1048576 34033113 100390141952 (ep557 rfl rfl) rfl) ep664 rfl) (@ep665 100390141952 864519072408721937570343 ep558 ep559 ep560 ep418 ep419 ep420 ep417 (@ep666 100390141952 751 1048576 34033113 100390141952 (ep669 rfl rfl) rfl) ep670 rfl) rfl rfl))

noncomputable abbrev qz598 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 128194 1000)))

noncomputable abbrev qz579 := qz598

noncomputable abbrev qz440 := qz579

noncomputable abbrev qz150 := (BSN.headSumC qz440 9)

noncomputable abbrev qz151 := qz440

noncomputable abbrev qz580 := (@Neg.neg Complex Complex.instNeg qz598)

noncomputable abbrev qz441 := qz580

noncomputable abbrev qz152 := qz441

noncomputable abbrev qz442 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz152)

noncomputable def ep671 := @Enclosure.Complex.IsNear.of_eq qz150 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 8) qz442) Bool.false 71874769533 274877906944 60069306576359 26316673371865088 Bool.true 83381101039 137438953472 240329728889841 105266693487460352

noncomputable def ep672 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 8) qz442 Bool.false 635229511595 1099511627776 430082516182857 210533386974920704 Bool.true 123317817129 274877906944 215138683659763 105266693487460352 Bool.true

noncomputable def ep673 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz152)) Bool.false 635229511595 1099511627776 430082516182857 210533386974920704 Bool.true 123317817129 274877906944 215138683659763 105266693487460352

noncomputable def ep674 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 7) (@HPow.hPow Complex Complex Complex qz6 qz276 qz152) Bool.false 379579178735 549755813888 188128862549457 105266693487460352 Bool.true 444969742983 549755813888 188160402970337 105266693487460352 Bool.true

noncomputable def ep675 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz152)) Bool.false 379579178735 549755813888 188128862549457 105266693487460352 Bool.true 444969742983 549755813888 188160402970337 105266693487460352

noncomputable def ep676 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 6) (@HPow.hPow Complex Complex Complex qz6 qz277 qz152) Bool.false 1179819176479 1099511627776 317996953609465 210533386974920704 Bool.true 1046564602407 1099511627776 318178137166593 210533386974920704 Bool.true

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz152)) Bool.false 1179819176479 1099511627776 317996953609465 210533386974920704 Bool.true 1046564602407 1099511627776 318178137166593 210533386974920704

noncomputable def ep678 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 5) (@HPow.hPow Complex Complex Complex qz6 qz278 qz152) Bool.false 462300341583 549755813888 7946168855425 6579168342966272 Bool.true 1466859705271 1099511627776 254391181918711 210533386974920704 Bool.false

noncomputable def ep679 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz152)) Bool.false 462300341583 549755813888 7946168855425 6579168342966272 Bool.true 1466859705271 1099511627776 254391181918711 210533386974920704

noncomputable def ep680 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 4) (@HPow.hPow Complex Complex Complex qz6 qz279 qz152) Bool.false 260406696109 274877906944 91505123798957 105266693487460352 Bool.true 464852564715 549755813888 91485293850759 105266693487460352 Bool.true

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz152)) Bool.false 260406696109 274877906944 91505123798957 105266693487460352 Bool.true 464852564715 549755813888 91485293850759 105266693487460352

noncomputable def ep682 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz152) Bool.false 1587330442831 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 1099511627776 100741010238001 210533386974920704 Bool.true

noncomputable def ep683 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz152)) Bool.false 1587330442831 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 1099511627776 100741010238001 210533386974920704

noncomputable def ep684 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz152) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep685 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz151)

noncomputable abbrev qz599 := (Enclosure.sfrac Bool.false 128194 1000)

noncomputable abbrev qz581 := qz599

noncomputable abbrev qz443 := qz581

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz267 qz443 (Real.log qz284))

noncomputable abbrev qz154 := qz443

noncomputable abbrev qz444 := (@Eq.refl Real qz581)

noncomputable abbrev qz155 := qz444

noncomputable def ep686 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.false 487818815055 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 1099511627776 100741010238001 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 2 qz155 rfl)

noncomputable def ep687 := nat_lit 482399978991659211785040281693601139610630501379006914074197693788887906779136

noncomputable def ep688 := nat_lit 182149942680904595086931320042174755992541871846653020492764745046012461056

noncomputable def ep689 := nat_lit 1446835637089615826164946982440719069319906420393327436181607551876571695415296

noncomputable def ep690 := BSN.cos_dyadic_bound_f 1916697736 2147483648 3 2 1048576 383332 ep687 ep64 ep688 ep689 ep66 ep688 657921 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1916697736) qz290 0 2 ep687 ep64 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1916697736) qz291 0 2 ep689 ep66 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz156 := (Enclosure.Real.IsNear.const Bool.false 128194 1000)

noncomputable abbrev qz445 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46586725) qz32)

noncomputable def ep691 := @Enclosure.Real.IsNear.cos_image qz153 qz445 Bool.false 46586725 524288 703 1048576 Bool.false 657921 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1455835161 16384000 64097 95739500 46586725 524288 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz17 128194 1000 0 1 363408 524288 1 191479 1455835161 16384000 64097 95739500 qz156 qz289 rfl) rfl) (Enclosure.sfrac_false_div 46586725 524288) (BSN.cos_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67437806349584391208960) qz33) 226375608064910080 72057594037927936 Bool.false 657921 1048576 14 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 46586725 524288 226375608064910080 72057594037927936 14 67437806349584391208960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 657921 1048576 67437806349584391208960 75557863725914323419136 1916697736 2147483648 383332 382958 (ep690 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep692 := nat_lit 868174242230841857537002961992448311494340868984735122917161637023961422233600

noncomputable def ep693 := nat_lit 2273494772602150067062009868795391580499285779548459312273673144523157799960576

noncomputable def ep694 := BSN.sin_dyadic_bound_f 1916697736 2147483648 3 2 1048576 383332 ep692 ep57 ep688 ep693 ep60 ep688 816487 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1916697736) qz286 0 2 ep692 ep57 ep688 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1916697736) qz287 0 2 ep693 ep60 ep688 rfl rfl rfl rfl) rfl rfl

noncomputable def ep695 := @Enclosure.Real.IsNear.sin_image qz153 qz445 Bool.false 46586725 524288 703 1048576 Bool.false 816487 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 1455835161 16384000 64097 95739500 46586725 524288 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz17 128194 1000 0 1 363408 524288 1 191479 1455835161 16384000 64097 95739500 qz156 qz289 rfl) rfl) (Enclosure.sfrac_false_div 46586725 524288) (BSN.sin_reduce0 qz445 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67437806349584391208960) qz33) 226375608064910080 72057594037927936 Bool.false 816487 1048576 14 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 46586725 524288 226375608064910080 72057594037927936 14 67437806349584391208960 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 816487 1048576 67437806349584391208960 75557863725914323419136 1916697736 2147483648 383332 382958 (ep694 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep696 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz11 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz11 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.false 487818815055 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 1099511627776 100741010238001 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz11 (Real.cos qz153) 741455 1048576 1 1048576 657921 1048576 135658313 200780283904 487818815055 1099511627776 100710648178887 210533386974920704 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.false 657921 1048576 135658313 200780283904 657921 1048576 135658313 200780283904 (ep691 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz11 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 741455 1048576 1 1048576 816487 1048576 135658313 200780283904 605388368585 1099511627776 100741010238001 210533386974920704 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 816487 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 816487 1048576 135658313 200780283904 816487 1048576 135658313 200780283904 (ep695 rfl rfl) rfl)) rfl)

noncomputable def ep697 := @ep684 487818815055 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 1099511627776 100741010238001 210533386974920704 Bool.false 1587330442831 1587330442831 1099511627776 100710648178887 210533386974920704 Bool.true 605388368585 605388368585 1099511627776 100741010238001 210533386974920704 (ep685 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz20)) (ep686 ep696) rfl rfl

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz443 (Real.log (Enclosure.sfrac Bool.false 3 1)))

noncomputable def ep698 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.true 545703658395 1099511627776 82299599419027 210533386974920704 Bool.true 324316760845 1099511627776 82229577463517 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 3 qz155 rfl)

noncomputable def ep699 := nat_lit 1567570297906400496407423662424762759756383072339497423473097921665226222240000

noncomputable def ep700 := nat_lit 593639179887460618999924396376214999889270425183869355257865926672100000000

noncomputable def ep701 := nat_lit 4104580126320754935302966857327864784600230180200766987282934202384790039200000

noncomputable def ep702 := BSN.sin_dyadic_bound_f 2221725090 2147483648 3 2 1048576 383332 ep699 ep57 ep700 ep701 ep60 ep700 901401 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2221725090) qz286 0 2 ep699 ep57 ep700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2221725090) qz287 0 2 ep701 ep60 ep700 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz446 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147676667) qz16)

noncomputable def ep703 := @Enclosure.Real.IsNear.cos_image qz157 qz446 Bool.false 147676667 1048576 703 1048576 Bool.true 901401 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 36919166933 262144000 64097 95739500 147676667 1048576 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz23 128194 1000 0 1 575989 524288 1 191479 36919166933 262144000 64097 95739500 qz156 qz296 rfl) rfl) (Enclosure.sfrac_false_div 147676667 1048576) (BSN.cos_reduce1 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156340004518405817237504) qz19) 226375608064910080 72057594037927936 Bool.false 901401 1048576 22 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 147676667 1048576 226375608064910080 72057594037927936 22 156340004518405817237504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 901401 1048576 156340004518405817237504 151115727451828646838272 2221725090 2147483648 383332 382958 (ep702 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep704 := nat_lit 871136227361283591612568667745479850975719160377580288309613452448091056800000

noncomputable def ep705 := nat_lit 2612221403724075853599706154443687122927378940282373126218324625490928970400000

noncomputable def ep706 := BSN.cos_dyadic_bound_f 2221725090 2147483648 3 2 1048576 383332 ep704 ep64 ep700 ep705 ep66 ep700 535711 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2221725090) qz290 0 2 ep704 ep64 ep700 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2221725090) qz291 0 2 ep705 ep66 ep700 rfl rfl rfl rfl) rfl rfl

noncomputable def ep707 := @Enclosure.Real.IsNear.sin_image qz157 qz446 Bool.false 147676667 1048576 703 1048576 Bool.false 535711 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 36919166933 262144000 64097 95739500 147676667 1048576 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz23 128194 1000 0 1 575989 524288 1 191479 36919166933 262144000 64097 95739500 qz156 qz296 rfl) rfl) (Enclosure.sfrac_false_div 147676667 1048576) (BSN.sin_reduce1 qz446 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 156340004518405817237504) qz19) 226375608064910080 72057594037927936 Bool.false 535711 1048576 22 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 147676667 1048576 226375608064910080 72057594037927936 22 156340004518405817237504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 535711 1048576 156340004518405817237504 151115727451828646838272 2221725090 2147483648 383332 382958 (ep706 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep708 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz21 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz21 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.true 545703658395 1099511627776 82299599419027 210533386974920704 Bool.true 324316760845 1099511627776 82229577463517 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz21 (Real.cos qz157) 605395 1048576 1 1048576 901401 1048576 135658313 200780283904 545703658395 1099511627776 82299599419027 210533386974920704 qz297 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.true 901401 1048576 135658313 200780283904 901401 1048576 135658313 200780283904 (ep703 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz21 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 605395 1048576 1 1048576 535711 1048576 135658313 200780283904 324316760845 1099511627776 82229577463517 210533386974920704 qz297 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.false 535711 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.false 535711 1048576 135658313 200780283904 535711 1048576 135658313 200780283904 (ep707 rfl rfl) rfl)) rfl)

noncomputable def ep709 := @ep682 545703658395 1099511627776 82299599419027 210533386974920704 Bool.true 324316760845 1099511627776 82229577463517 210533386974920704 Bool.false 1145280761290307022094336 260406696109 274877906944 91505123798957 105266693487460352 Bool.true 1022221600211276063047680 464852564715 549755813888 91485293850759 105266693487460352 (ep683 (BSN.head_sum_c_succ qz151 2 3 rfl rfl) (ep697 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep698 ep708) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz443 (Real.log (Enclosure.sfrac Bool.false 4 1)))

noncomputable def ep710 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz279 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 58513050635 549755813888 35633577887843 105266693487460352 Bool.true 537154575841 1099511627776 71420594217193 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 4 qz155 rfl)

noncomputable def ep711 := nat_lit 45032211599548294205346014384450625

noncomputable def ep712 := BSN.sin_dyadic_bound_f 460660335 2147483648 2 1 1048576 383332 ep711 ep79 ep711 ep711 ep80 ep711 223210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 460660335) qz286 0 1 ep711 ep79 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 460660335) qz287 0 1 ep711 ep80 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz447 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 46586789) qz555)

noncomputable def ep713 := @Enclosure.Real.IsNear.cos_image qz158 qz447 Bool.false 46586789 262144 11 16384 Bool.true 223210 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 46586789249 262144000 64097 95739500 46586789 262144 11 16384 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz26 128194 1000 0 1 726817 524288 1 191479 46586789249 262144000 64097 95739500 qz156 qz299 rfl) rfl) (Enclosure.sfrac_false_div 46586789 262144) (BSN.cos_reduce1 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8104022321053457973248) qz336) 226375608064910080 72057594037927936 Bool.false 223210 1048576 28 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 46586789 262144 226375608064910080 72057594037927936 28 8104022321053457973248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 223210 1048576 8104022321053457973248 37778931862957161709568 460660335 2147483648 383332 382958 (ep712 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep714 := BSN.cos_dyadic_bound_f 460660335 2147483648 2 1 1048576 383332 ep711 ep75 ep711 ep711 ep76 ep711 1024543 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 460660335) qz290 0 1 ep711 ep75 ep711 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 460660335) qz291 0 1 ep711 ep76 ep711 rfl rfl rfl rfl) rfl rfl

noncomputable def ep715 := @Enclosure.Real.IsNear.sin_image qz158 qz447 Bool.false 46586789 262144 11 16384 Bool.false 1024543 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 46586789249 262144000 64097 95739500 46586789 262144 11 16384 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz26 128194 1000 0 1 726817 524288 1 191479 46586789249 262144000 64097 95739500 qz156 qz299 rfl) rfl) (Enclosure.sfrac_false_div 46586789 262144) (BSN.sin_reduce1 qz447 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8104022321053457973248) qz336) 226375608064910080 72057594037927936 Bool.false 1024543 1048576 28 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 46586789 262144 226375608064910080 72057594037927936 28 8104022321053457973248 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1024543 1048576 8104022321053457973248 37778931862957161709568 460660335 2147483648 383332 382958 (ep714 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep716 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz24 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 58513050635 549755813888 35633577887843 105266693487460352 Bool.true 537154575841 1099511627776 71420594217193 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz24 (Real.cos qz158) 524287 1048576 1 1048576 111605 524288 2122653 3137191936 58513050635 549755813888 35633577887843 105266693487460352 qz300 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 223210 1048576 2122653 3137191936 111605 524288 2122653 3137191936 (ep713 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz24 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 524287 1048576 1 1048576 1024543 1048576 2122653 3137191936 537154575841 1099511627776 71420594217193 210533386974920704 qz300 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 1024543 1048576 2122653 3137191936 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 1024543 1048576 2122653 3137191936 1024543 1048576 2122653 3137191936 (ep715 rfl rfl) rfl)) rfl)

noncomputable def ep717 := @ep680 58513050635 549755813888 35633577887843 105266693487460352 Bool.true 537154575841 1099511627776 71420594217193 210533386974920704 Bool.false 127076150273831287652352 462300341583 549755813888 7946168855425 6579168342966272 Bool.true 806414651130770408603648 1466859705271 1099511627776 254391181918711 210533386974920704 (ep681 (BSN.head_sum_c_succ qz151 3 4 rfl rfl) (ep709 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep710 ep716) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz443 (Real.log (Enclosure.sfrac Bool.false 5 1)))

noncomputable def ep718 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz278 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.false 255218493313 1099511627776 63719550235865 210533386974920704 Bool.false 26268443929 68719476736 31893477623941 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 5 qz155 rfl)

noncomputable def ep719 := nat_lit 1886301192762191662396826140863369216

noncomputable def ep720 := BSN.sin_dyadic_bound_f 1171932936 2147483648 2 1 1048576 383332 ep719 ep79 ep719 ep719 ep80 ep719 544249 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1171932936) qz286 0 1 ep719 ep79 ep719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1171932936) qz287 0 1 ep719 ep80 ep719 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216342245) qz16)

noncomputable def ep721 := @Enclosure.Real.IsNear.cos_image qz159 qz448 Bool.false 216342245 1048576 703 1048576 Bool.false 544249 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1690173793 8192000 64097 95739500 216342245 1048576 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz29 128194 1000 0 1 843808 524288 1 191479 1690173793 8192000 64097 95739500 qz156 qz302 rfl) rfl) (Enclosure.sfrac_false_div 216342245 1048576) (BSN.cos_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82467449030368726876160) qz19) 226375608064910080 72057594037927936 Bool.false 544249 1048576 32 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 216342245 1048576 226375608064910080 72057594037927936 32 82467449030368726876160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 544249 1048576 82467449030368726876160 151115727451828646838272 1171932936 2147483648 383332 382958 (ep720 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep722 := BSN.cos_dyadic_bound_f 1171932936 2147483648 2 1 1048576 383332 ep719 ep75 ep719 ep719 ep76 ep719 896272 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1171932936) qz290 0 1 ep719 ep75 ep719 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1171932936) qz291 0 1 ep719 ep76 ep719 rfl rfl rfl rfl) rfl rfl

noncomputable def ep723 := @Enclosure.Real.IsNear.sin_image qz159 qz448 Bool.false 216342245 1048576 703 1048576 Bool.true 896272 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 1690173793 8192000 64097 95739500 216342245 1048576 703 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz154 qz29 128194 1000 0 1 843808 524288 1 191479 1690173793 8192000 64097 95739500 qz156 qz302 rfl) rfl) (Enclosure.sfrac_false_div 216342245 1048576) (BSN.sin_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82467449030368726876160) qz19) 226375608064910080 72057594037927936 Bool.false 896272 1048576 32 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 216342245 1048576 226375608064910080 72057594037927936 32 82467449030368726876160 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 896272 1048576 82467449030368726876160 151115727451828646838272 1171932936 2147483648 383332 382958 (ep722 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep724 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz27 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz27 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.false 255218493313 1099511627776 63719550235865 210533386974920704 Bool.false 26268443929 68719476736 31893477623941 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz27 (Real.cos qz159) 468937 1048576 1 1048576 544249 1048576 135658313 200780283904 255218493313 1099511627776 63719550235865 210533386974920704 qz303 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.false 544249 1048576 135658313 200780283904 544249 1048576 135658313 200780283904 (ep721 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz27 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 468937 1048576 1 1048576 56017 65536 135658313 200780283904 26268443929 68719476736 31893477623941 105266693487460352 qz303 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.true 56017 65536 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.true 896272 1048576 135658313 200780283904 56017 65536 135658313 200780283904 (ep723 rfl rfl) rfl)) rfl)

noncomputable def ep725 := @ep678 255218493313 1099511627776 63719550235865 210533386974920704 Bool.false 26268443929 68719476736 31893477623941 105266693487460352 Bool.false 648612451605882551140352 1179819176479 1099511627776 317996953609465 210533386974920704 Bool.true 71919371847828926103552 1046564602407 1099511627776 318178137166593 210533386974920704 (ep679 (BSN.head_sum_c_succ qz151 4 5 rfl rfl) (ep717 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep718 ep724) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz443 qz547)

noncomputable def ep726 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz277 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.true 420660819009 1099511627776 58260771489449 210533386974920704 Bool.false 156625116441 1099511627776 58142668774081 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 6 qz155 rfl)

noncomputable def ep727 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz547 128194 1000 0 1 4034681531866359 2251799813685248 500000000191479 95739500000000000000 258610982148038012823 1125899906842624000 32048500012273229463 47869750000000000000000 qz156 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 500000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz305) Bool.false 33845361775666394038272 18889465931478580854784 1000000000382958 191479000000000000000 4034681531866359 2251799813685248 500000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep113 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep728 := nat_lit 343250996024563912014150312230916096

noncomputable def ep729 := BSN.cos_dyadic_bound_f 765425544 2147483648 2 1 1048576 383332 ep728 ep75 ep728 ep728 ep76 ep728 982671 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 765425544) qz290 0 1 ep728 ep75 ep728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 765425544) qz291 0 1 ep728 ep76 ep728 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 240850245) qz16)

noncomputable def ep730 := @Enclosure.Real.IsNear.cos_image qz160 qz449 Bool.false 240850245 1048576 703 1048576 Bool.true 982671 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 258610982148038012823 1125899906842624000 32048500012273229463 47869750000000000000000 240850245 1048576 703 1048576 (ep727 rfl) rfl) (Enclosure.sfrac_false_div 240850245 1048576) (BSN.cos_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53862034359377157160960) qz19) 226375608064910080 72057594037927936 Bool.false 982671 1048576 36 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 240850245 1048576 226375608064910080 72057594037927936 36 53862034359377157160960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 982671 1048576 53862034359377157160960 151115727451828646838272 765425544 2147483648 383332 382958 (ep729 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep731 := BSN.sin_dyadic_bound_f 765425544 2147483648 2 1 1048576 383332 ep728 ep79 ep728 ep728 ep80 ep728 365879 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 765425544) qz286 0 1 ep728 ep79 ep728 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 765425544) qz287 0 1 ep728 ep80 ep728 rfl rfl rfl rfl) rfl rfl

noncomputable def ep732 := @Enclosure.Real.IsNear.sin_image qz160 qz449 Bool.false 240850245 1048576 703 1048576 Bool.true 365879 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 258610982148038012823 1125899906842624000 32048500012273229463 47869750000000000000000 240850245 1048576 703 1048576 (ep727 rfl) rfl) (Enclosure.sfrac_false_div 240850245 1048576) (BSN.sin_reduce2 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53862034359377157160960) qz19) 226375608064910080 72057594037927936 Bool.false 365879 1048576 36 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 240850245 1048576 226375608064910080 72057594037927936 36 53862034359377157160960 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365879 1048576 53862034359377157160960 151115727451828646838272 765425544 2147483648 383332 382958 (ep731 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep733 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz30 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz30 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.true 420660819009 1099511627776 58260771489449 210533386974920704 Bool.false 156625116441 1099511627776 58142668774081 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz30 (Real.cos qz160) 428079 1048576 1 1048576 982671 1048576 135658313 200780283904 420660819009 1099511627776 58260771489449 210533386974920704 qz307 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.true 982671 1048576 135658313 200780283904 982671 1048576 135658313 200780283904 (ep730 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz30 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 428079 1048576 1 1048576 365879 1048576 135658313 200780283904 156625116441 1099511627776 58142668774081 210533386974920704 qz307 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.true 365879 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.true 365879 1048576 135658313 200780283904 365879 1048576 135658313 200780283904 (ep732 rfl rfl) rfl)) rfl)

noncomputable def ep734 := @ep676 420660819009 1099511627776 58260771489449 210533386974920704 Bool.false 156625116441 1099511627776 58142668774081 210533386974920704 Bool.false 834703441361594189086720 379579178735 549755813888 188128862549457 105266693487460352 Bool.true 978498812836613367791616 444969742983 549755813888 188160402970337 105266693487460352 (ep677 (BSN.head_sum_c_succ qz151 5 6 rfl rfl) (ep725 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep726 ep733) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz443 qz548)

noncomputable def ep735 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz276 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.true 123928845875 1099511627776 53824791083943 210533386974920704 Bool.false 198334108725 549755813888 13489140344713 52633346743730176 (BSN.cpow_neg_s_mk qz154 128194 1000 7 qz155 rfl)

noncomputable def ep736 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz548 128194 1000 0 1 4381796493761783 2251799813685248 500000000191479 95739500000000000000 280860009860649004951 1125899906842624000 32048500012273229463 47869750000000000000000 qz156 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 500000000191479 95739500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz309) Bool.false 36757173121942042968064 18889465931478580854784 1000000000382958 191479000000000000000 4381796493761783 2251799813685248 500000000191479 95739500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep128 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep737 := nat_lit 1967274691020606395038468206532658002452367442491625726731485950521034933558401

noncomputable def ep738 := nat_lit 3022296681489025207728883677046835515683487088205848546258140103698621422721

noncomputable def ep739 := nat_lit 5895779479698841134699946852243880336325735353298465483101941571355707557829761

noncomputable def ep740 := BSN.cos_dyadic_bound_f 2722965487 2147483648 3 2 1048576 383332 ep737 ep64 ep738 ep739 ep66 ep738 312695 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2722965487) qz290 0 2 ep737 ep64 ep738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2722965487) qz291 0 2 ep739 ep66 ep738 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 261571267) qz16)

noncomputable def ep741 := @Enclosure.Real.IsNear.cos_image qz161 qz450 Bool.false 261571267 1048576 703 1048576 Bool.true 312695 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 280860009860649004951 1125899906842624000 32048500012273229463 47869750000000000000000 261571267 1048576 703 1048576 (ep736 rfl) rfl) (Enclosure.sfrac_false_div 261571267 1048576) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191611661786070525149184) qz19) 226375608064910080 72057594037927936 Bool.false 312695 1048576 39 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 261571267 1048576 226375608064910080 72057594037927936 39 191611661786070525149184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 312695 1048576 191611661786070525149184 151115727451828646838272 2722965487 2147483648 383332 382958 (ep740 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep742 := nat_lit 3538676606491900290903059664817146936001714606814361629279668198854903983266945

noncomputable def ep743 := nat_lit 9263069298565899482981214262853499479645764991132899559990903532071141235776641

noncomputable def ep744 := BSN.sin_dyadic_bound_f 2722965487 2147483648 3 2 1048576 383332 ep742 ep57 ep738 ep743 ep60 ep738 1000866 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2722965487) qz286 0 2 ep742 ep57 ep738 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2722965487) qz287 0 2 ep743 ep60 ep738 rfl rfl rfl rfl) rfl rfl

noncomputable def ep745 := @Enclosure.Real.IsNear.sin_image qz161 qz450 Bool.false 261571267 1048576 703 1048576 Bool.true 1000866 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 280860009860649004951 1125899906842624000 32048500012273229463 47869750000000000000000 261571267 1048576 703 1048576 (ep736 rfl) rfl) (Enclosure.sfrac_false_div 261571267 1048576) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191611661786070525149184) qz19) 226375608064910080 72057594037927936 Bool.false 1000866 1048576 39 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 261571267 1048576 226375608064910080 72057594037927936 39 191611661786070525149184 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000866 1048576 191611661786070525149184 151115727451828646838272 2722965487 2147483648 383332 382958 (ep744 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep746 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz34 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz34 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.true 123928845875 1099511627776 53824791083943 210533386974920704 Bool.false 198334108725 549755813888 13489140344713 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ft qz34 (Real.cos qz161) 396325 1048576 1 1048576 312695 1048576 135658313 200780283904 123928845875 1099511627776 53824791083943 210533386974920704 qz311 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.true 312695 1048576 135658313 200780283904 312695 1048576 135658313 200780283904 (ep741 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz34 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 396325 1048576 1 1048576 500433 524288 135658313 200780283904 198334108725 549755813888 13489140344713 52633346743730176 qz311 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 500433 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 1000866 1048576 135658313 200780283904 500433 524288 135658313 200780283904 (ep745 rfl rfl) rfl)) rfl)

noncomputable def ep747 := @ep674 123928845875 1099511627776 53824791083943 210533386974920704 Bool.false 198334108725 549755813888 13489140344713 52633346743730176 Bool.false 349221117152585958031360 635229511595 1099511627776 430082516182857 210533386974920704 Bool.true 135589373845289884975104 123317817129 274877906944 215138683659763 105266693487460352 (ep675 (BSN.head_sum_c_succ qz151 6 7 rfl rfl) (ep734 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep735 ep746) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz443 qz549)

noncomputable def ep748 := @Enclosure.Complex.IsNear.of_eq qz442 (Complex.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 347730433463 1099511627776 50471936428015 210533386974920704 Bool.true 43444384949 274877906944 12595522615039 52633346743730176 (BSN.cpow_neg_s_mk qz154 128194 1000 8 qz155 rfl)

noncomputable def ep749 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz549 128194 1000 0 1 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 600266620042642427589 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz313) Bool.false 39279540158062550581248 18889465931478580854784 1000000000574437 191479000000000000000 9364972152248037 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep139 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep750 := nat_lit 2057670582024070178752450196795007599391614319141208065097871777020121416236865

noncomputable def ep751 := nat_lit 1022627382879734148820245940544334171720612053929466593356706127716826775361

noncomputable def ep752 := nat_lit 5387481556205045184301184402940329076414299368711087700771848558464966942031681

noncomputable def ep753 := BSN.sin_dyadic_bound_f 2378015479 2147483648 3 2 1048576 383332 ep750 ep57 ep751 ep752 ep60 ep751 937969 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2378015479) qz286 0 2 ep750 ep57 ep751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2378015479) qz287 0 2 ep752 ep60 ep751 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 279520927) qz16)

noncomputable def ep754 := @Enclosure.Real.IsNear.cos_image qz162 qz451 Bool.false 279520927 1048576 703 1048576 Bool.true 937969 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 600266620042642427589 2251799813685248000 64097000036819688389 95739500000000000000000 279520927 1048576 703 1048576 (ep749 rfl) rfl) (Enclosure.sfrac_false_div 279520927 1048576) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167337962958754964045824) qz19) 226375608064910080 72057594037927936 Bool.false 937969 1048576 42 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 279520927 1048576 226375608064910080 72057594037927936 42 167337962958754964045824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 937969 1048576 167337962958754964045824 151115727451828646838272 2378015479 2147483648 383332 382958 (ep753 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep755 := nat_lit 1143604824405763314484170218637468370404994893769084243540309523290163820920641

noncomputable def ep756 := nat_lit 3428769218451530475154870164031316442871543457199393797434215157615057809211201

noncomputable def ep757 := BSN.cos_dyadic_bound_f 2378015479 2147483648 3 2 1048576 383332 ep755 ep64 ep751 ep756 ep66 ep751 468748 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2378015479) qz290 0 2 ep755 ep64 ep751 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2378015479) qz291 0 2 ep756 ep66 ep751 rfl rfl rfl rfl) rfl rfl

noncomputable def ep758 := @Enclosure.Real.IsNear.sin_image qz162 qz451 Bool.false 279520927 1048576 703 1048576 Bool.false 468748 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 600266620042642427589 2251799813685248000 64097000036819688389 95739500000000000000000 279520927 1048576 703 1048576 (ep749 rfl) rfl) (Enclosure.sfrac_false_div 279520927 1048576) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 167337962958754964045824) qz19) 226375608064910080 72057594037927936 Bool.false 468748 1048576 42 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 279520927 1048576 226375608064910080 72057594037927936 42 167337962958754964045824 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 468748 1048576 167337962958754964045824 151115727451828646838272 2378015479 2147483648 383332 382958 (ep757 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep759 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz36 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz36 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 347730433463 1099511627776 50471936428015 210533386974920704 Bool.true 43444384949 274877906944 12595522615039 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ft qz36 (Real.cos qz162) 370727 1048576 1 1048576 937969 1048576 135658313 200780283904 347730433463 1099511627776 50471936428015 210533386974920704 qz315 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 937969 1048576 135658313 200780283904 937969 1048576 135658313 200780283904 (ep754 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz36 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 370727 1048576 1 1048576 117187 262144 135658313 200780283904 43444384949 274877906944 12595522615039 52633346743730176 qz315 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 117187 262144 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 468748 1048576 135658313 200780283904 117187 262144 135658313 200780283904 (ep758 rfl rfl) rfl)) rfl)

noncomputable def ep760 := @ep672 347730433463 1099511627776 50471936428015 210533386974920704 Bool.true 43444384949 274877906944 12595522615039 52633346743730176 Bool.false 316108579381014725394432 71874769533 274877906944 60069306576359 26316673371865088 Bool.true 45839245064573007429632 83381101039 137438953472 240329728889841 105266693487460352 (ep673 (BSN.head_sum_c_succ qz151 7 8 rfl rfl) (ep747 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep748 ep759) rfl rfl

theorem EMRow42.d12 : Enclosure.Complex.IsNear qz150 Bool.false 71874769533 274877906944 60069306576359 26316673371865088 Bool.true 83381101039 137438953472 240329728889841 105266693487460352 := ep671 (BSN.head_sum_c_succ qz151 8 9 rfl rfl) (ep760 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz163 := (BSN.headSumC qz440 17)

noncomputable abbrev qz452 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz152)

noncomputable def ep761 := @Enclosure.Complex.IsNear.of_eq qz163 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 16) qz452) Bool.false 761764839889 1099511627776 807598499451061 210533386974920704 Bool.true 35716939049 1099511627776 807884078124905 210533386974920704

noncomputable def ep762 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 16) qz452 Bool.false 505851099833 549755813888 192963480775427 52633346743730176 Bool.true 75061086769 549755813888 96529812435277 26316673371865088 Bool.true

noncomputable abbrev qz453 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz152)

noncomputable def ep763 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 15) qz453) Bool.false 505851099833 549755813888 192963480775427 52633346743730176 Bool.true 75061086769 549755813888 96529812435277 26316673371865088

noncomputable def ep764 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 15) qz453 Bool.false 507208053725 549755813888 367561800368983 105266693487460352 Bool.false 66878672855 549755813888 367654662705529 105266693487460352 Bool.true

noncomputable abbrev qz454 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz152)

noncomputable def ep765 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 14) qz454) Bool.false 507208053725 549755813888 367561800368983 105266693487460352 Bool.false 66878672855 549755813888 367654662705529 105266693487460352

noncomputable def ep766 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 14) qz454 Bool.false 212737731509 274877906944 174248620787963 52633346743730176 Bool.true 110436035499 1099511627776 697125049426809 210533386974920704 Bool.false

noncomputable abbrev qz455 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz152)

noncomputable def ep767 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 13) qz455) Bool.false 212737731509 274877906944 174248620787963 52633346743730176 Bool.true 110436035499 1099511627776 697125049426809 210533386974920704

noncomputable def ep768 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 13) qz455 Bool.false 1001005996877 1099511627776 657442993086747 210533386974920704 Bool.false 155040576759 1099511627776 657497565367663 210533386974920704 Bool.true

noncomputable abbrev qz456 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz152)

noncomputable def ep769 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 12) qz456) Bool.false 1001005996877 1099511627776 657442993086747 210533386974920704 Bool.false 155040576759 1099511627776 657497565367663 210533386974920704

noncomputable def ep770 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 12) qz456 Bool.false 1101347025407 1099511627776 616316019684563 210533386974920704 Bool.true 9130131009 68719476736 154060895555367 52633346743730176 Bool.true

noncomputable abbrev qz457 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz152)

noncomputable def ep771 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 11) qz457) Bool.false 1101347025407 1099511627776 616316019684563 210533386974920704 Bool.true 9130131009 68719476736 154060895555367 52633346743730176

noncomputable def ep772 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 11) qz457 Bool.false 50459875361 68719476736 71656063212019 26316673371865088 Bool.true 299288932931 1099511627776 573261332299925 210533386974920704 Bool.false

noncomputable abbrev qz458 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz152)

noncomputable def ep773 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 10) qz458) Bool.false 50459875361 68719476736 71656063212019 26316673371865088 Bool.true 299288932931 1099511627776 573261332299925 210533386974920704

noncomputable def ep774 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 10) qz458 Bool.false 462697435807 1099511627776 528066538394823 210533386974920704 Bool.true 345132438537 1099511627776 528251919554589 210533386974920704 Bool.false

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 10) (@HAdd.hAdd Complex Complex Complex qz4 qz150 (@HPow.hPow Complex Complex Complex qz6 qz316 qz152)) Bool.false 462697435807 1099511627776 528066538394823 210533386974920704 Bool.true 345132438537 1099511627776 528251919554589 210533386974920704

noncomputable def ep776 := @Enclosure.Complex.IsNear.addLitP qz150 (@HPow.hPow Complex Complex Complex qz6 qz316 qz152) Bool.false 71874769533 274877906944 60069306576359 26316673371865088 Bool.true 83381101039 137438953472 240329728889841 105266693487460352 Bool.false

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz443 qz550)

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz316 qz152) (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.false 175198357675 1099511627776 47512085783951 210533386974920704 Bool.false 321916369775 1099511627776 47592461774907 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 9 qz155 rfl)

noncomputable def ep778 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz550 128194 1000 0 1 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 634266594289023946437 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz318) Bool.false 41504390431577613533184 18889465931478580854784 1000000000574437 191479000000000000000 9895417793173221 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep175 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep779 := nat_lit 1312373724374064438655784765685724176

noncomputable def ep780 := BSN.sin_dyadic_bound_f 1070321826 2147483648 2 1 1048576 383332 ep779 ep79 ep779 ep779 ep80 ep779 501247 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1070321826) qz286 0 1 ep779 ep79 ep779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1070321826) qz287 0 1 ep779 ep80 ep779 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 147676699) qz32)

noncomputable def ep781 := @Enclosure.Real.IsNear.cos_image qz164 qz459 Bool.false 147676699 524288 703 1048576 Bool.false 501247 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 634266594289023946437 2251799813685248000 64097000036819688389 95739500000000000000000 147676699 524288 703 1048576 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 147676699 524288) (BSN.cos_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37658601403288668602368) qz33) 226375608064910080 72057594037927936 Bool.false 501247 1048576 44 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 147676699 524288 226375608064910080 72057594037927936 44 37658601403288668602368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 501247 1048576 37658601403288668602368 75557863725914323419136 1070321826 2147483648 383332 382958 (ep780 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep782 := BSN.cos_dyadic_bound_f 1070321826 2147483648 2 1 1048576 383332 ep779 ep75 ep779 ep779 ep76 ep779 921011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1070321826) qz290 0 1 ep779 ep75 ep779 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1070321826) qz291 0 1 ep779 ep76 ep779 rfl rfl rfl rfl) rfl rfl

noncomputable def ep783 := @Enclosure.Real.IsNear.sin_image qz164 qz459 Bool.false 147676699 524288 703 1048576 Bool.true 921011 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 634266594289023946437 2251799813685248000 64097000036819688389 95739500000000000000000 147676699 524288 703 1048576 (ep778 rfl) rfl) (Enclosure.sfrac_false_div 147676699 524288) (BSN.sin_reduce3 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37658601403288668602368) qz33) 226375608064910080 72057594037927936 Bool.false 921011 1048576 44 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 147676699 524288 226375608064910080 72057594037927936 44 37658601403288668602368 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 921011 1048576 37658601403288668602368 75557863725914323419136 1070321826 2147483648 383332 382958 (ep782 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep784 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.false 175198357675 1099511627776 47512085783951 210533386974920704 Bool.false 321916369775 1099511627776 47592461774907 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz46 (Real.cos qz164) 349525 1048576 1 1048576 501247 1048576 135658313 200780283904 175198357675 1099511627776 47512085783951 210533386974920704 qz320 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.false 501247 1048576 135658313 200780283904 501247 1048576 135658313 200780283904 (ep781 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 349525 1048576 1 1048576 921011 1048576 135658313 200780283904 321916369775 1099511627776 47592461774907 210533386974920704 qz320 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.true 921011 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.true 921011 1048576 135658313 200780283904 921011 1048576 135658313 200780283904 (ep783 rfl rfl) rfl)) rfl)

noncomputable def ep785 := @ep776 175198357675 1099511627776 47512085783951 210533386974920704 Bool.false 321916369775 1099511627776 47592461774907 210533386974920704 Bool.false 127185302702983959543808 462697435807 1099511627776 528066538394823 210533386974920704 Bool.true 47434641161764642750464 345132438537 1099511627776 528251919554589 210533386974920704 EMRow42.d12 (ep777 ep784) rfl rfl

noncomputable abbrev qz165 := (@HMul.hMul Real Real Real qz267 qz443 qz551)

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq qz458 (Complex.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)))) Bool.false 344660569969 1099511627776 45181967301329 210533386974920704 Bool.false 22921752803 549755813888 5626176593167 26316673371865088 (BSN.cpow_neg_s_mk qz154 128194 1000 10 qz155 rfl)

noncomputable def ep787 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz551 128194 1000 0 1 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 664680582133885144773 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz322) Bool.false 43494585150108164161536 18889465931478580854784 1000000000574437 191479000000000000000 10369917190100709 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep186 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep788 := nat_lit 5866085045413739785267045810465656222686967361591391530984517536560664317720705

noncomputable def ep789 := nat_lit 8295927871012611745394937344009554726564552471223937232359770112140635994241

noncomputable def ep790 := nat_lit 15350124569054345685254480557424512732718095719214520016107058682239226469087361

noncomputable def ep791 := BSN.sin_dyadic_bound_f 3089286033 2147483648 3 2 1048576 383332 ep788 ep57 ep789 ep790 ep60 ep789 1039421 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3089286033) qz286 0 2 ep788 ep57 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3089286033) qz287 0 2 ep790 ep60 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309516015) qz16)

noncomputable def ep792 := @Enclosure.Real.IsNear.cos_image qz165 qz460 Bool.false 309516015 1048576 703 1048576 Bool.false 1039421 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 664680582133885144773 2251799813685248000 64097000036819688389 95739500000000000000000 309516015 1048576 703 1048576 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 309516015 1048576) (BSN.cos_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217389178589721783173120) qz19) 226375608064910080 72057594037927936 Bool.false 1039421 1048576 46 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 309516015 1048576 226375608064910080 72057594037927936 46 217389178589721783173120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039421 1048576 217389178589721783173120 151115727451828646838272 3089286033 2147483648 383332 382958 (ep791 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep793 := nat_lit 3262623215394749930368534311300479925815677224204650378205780751472431570286721

noncomputable def ep794 := nat_lit 9771277790442224567614813059213420667993902567671503260152622714193013438871681

noncomputable def ep795 := BSN.cos_dyadic_bound_f 3089286033 2147483648 3 2 1048576 383332 ep793 ep64 ep789 ep794 ep66 ep789 138254 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3089286033) qz290 0 2 ep793 ep64 ep789 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3089286033) qz291 0 2 ep794 ep66 ep789 rfl rfl rfl rfl) rfl rfl

noncomputable def ep796 := @Enclosure.Real.IsNear.sin_image qz165 qz460 Bool.false 309516015 1048576 703 1048576 Bool.true 138254 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz165 Bool.false 664680582133885144773 2251799813685248000 64097000036819688389 95739500000000000000000 309516015 1048576 703 1048576 (ep787 rfl) rfl) (Enclosure.sfrac_false_div 309516015 1048576) (BSN.sin_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 217389178589721783173120) qz19) 226375608064910080 72057594037927936 Bool.false 138254 1048576 46 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 309516015 1048576 226375608064910080 72057594037927936 46 217389178589721783173120 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 138254 1048576 217389178589721783173120 151115727451828646838272 3089286033 2147483648 383332 382958 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz48 (Real.cos qz165)) (@HMul.hMul Real Real Real qz0 qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165))) Bool.false 344660569969 1099511627776 45181967301329 210533386974920704 Bool.false 22921752803 549755813888 5626176593167 26316673371865088 (@Enclosure.Real.IsNear.mulLit_ff qz48 (Real.cos qz165) 331589 1048576 1 1048576 1039421 1048576 135658313 200780283904 344660569969 1099511627776 45181967301329 210533386974920704 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz165) Bool.false 1039421 1048576 135658313 200780283904 1039421 1048576 135658313 200780283904 (ep792 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz48 (@Neg.neg Real Real.instNeg (Real.sin qz165)) 331589 1048576 1 1048576 69127 524288 135658313 200780283904 22921752803 549755813888 5626176593167 26316673371865088 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz165) Bool.true 69127 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz165) Bool.true 138254 1048576 135658313 200780283904 69127 524288 135658313 200780283904 (ep796 rfl rfl) rfl)) rfl)

noncomputable def ep798 := @ep774 344660569969 1099511627776 45181967301329 210533386974920704 Bool.false 22921752803 549755813888 5626176593167 26316673371865088 Bool.false 887699515128754970034176 50459875361 68719476736 71656063212019 26316673371865088 Bool.true 164535830911152950345728 299288932931 1099511627776 573261332299925 210533386974920704 (ep775 (BSN.head_sum_c_succ qz151 9 10 rfl rfl) (ep785 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep786 ep797) rfl rfl

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz443 qz552)

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq qz457 (Complex.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.false 293989019631 1099511627776 43067513988411 210533386974920704 Bool.false 153206836787 1099511627776 42982249921543 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 11 qz155 rfl)

noncomputable def ep800 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz552 128194 1000 0 1 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 692193516339930042053 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz326) Bool.false 45294944137145793642496 18889465931478580854784 1000000000574437 191479000000000000000 10799156221662949 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep201 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep801 := nat_lit 1934401417231446988248367346544290399235539097741211093620607038769067647303680

noncomputable def ep802 := nat_lit 903825879505089439625365962633170265521520915360612177160103821980588834816

noncomputable def ep803 := nat_lit 5064826088944114824414901981771735436615567555459254730243330647731018122919936

noncomputable def ep804 := BSN.sin_dyadic_bound_f 2341588608 2147483648 3 2 1048576 383332 ep801 ep57 ep802 ep803 ep60 ep802 929883 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2341588608) qz286 0 2 ep801 ep57 ep802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2341588608) qz287 0 2 ep803 ep60 ep802 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 322327723) qz16)

noncomputable def ep805 := @Enclosure.Real.IsNear.cos_image qz166 qz461 Bool.false 322327723 1048576 703 1048576 Bool.false 929883 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 692193516339930042053 2251799813685248000 64097000036819688389 95739500000000000000000 322327723 1048576 703 1048576 (ep800 rfl) rfl) (Enclosure.sfrac_false_div 322327723 1048576) (BSN.cos_reduce3 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164774649764499848953856) qz19) 226375608064910080 72057594037927936 Bool.false 929883 1048576 48 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 322327723 1048576 226375608064910080 72057594037927936 48 164774649764499848953856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 929883 1048576 164774649764499848953856 151115727451828646838272 2341588608 2147483648 383332 382958 (ep804 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep806 := nat_lit 1075069154408361699888926466285776075248864619151944212979075067681473399095296

noncomputable def ep807 := nat_lit 3223399811466074920787528666932061885215550815625111414582904995400459019616256

noncomputable def ep808 := BSN.cos_dyadic_bound_f 2341588608 2147483648 3 2 1048576 383332 ep806 ep64 ep802 ep807 ep66 ep802 484591 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2341588608) qz290 0 2 ep806 ep64 ep802 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2341588608) qz291 0 2 ep807 ep66 ep802 rfl rfl rfl rfl) rfl rfl

noncomputable def ep809 := @Enclosure.Real.IsNear.sin_image qz166 qz461 Bool.false 322327723 1048576 703 1048576 Bool.true 484591 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 692193516339930042053 2251799813685248000 64097000036819688389 95739500000000000000000 322327723 1048576 703 1048576 (ep800 rfl) rfl) (Enclosure.sfrac_false_div 322327723 1048576) (BSN.sin_reduce3 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164774649764499848953856) qz19) 226375608064910080 72057594037927936 Bool.false 484591 1048576 48 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 322327723 1048576 226375608064910080 72057594037927936 48 164774649764499848953856 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 484591 1048576 164774649764499848953856 151115727451828646838272 2341588608 2147483648 383332 382958 (ep808 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep810 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz50 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.false 293989019631 1099511627776 43067513988411 210533386974920704 Bool.false 153206836787 1099511627776 42982249921543 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz50 (Real.cos qz166) 316157 1048576 1 1048576 929883 1048576 135658313 200780283904 293989019631 1099511627776 43067513988411 210533386974920704 qz328 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.false 929883 1048576 135658313 200780283904 929883 1048576 135658313 200780283904 (ep805 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz50 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 316157 1048576 1 1048576 484591 1048576 135658313 200780283904 153206836787 1099511627776 42982249921543 210533386974920704 qz328 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 484591 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 484591 1048576 135658313 200780283904 484591 1048576 135658313 200780283904 (ep809 rfl rfl) rfl)) rfl)

noncomputable def ep811 := @ep772 293989019631 1099511627776 43067513988411 210533386974920704 Bool.false 153206836787 1099511627776 42982249921543 210533386974920704 Bool.false 75683991290719137431552 1101347025407 1099511627776 616316019684563 210533386974920704 Bool.true 160618963320219572895744 9130131009 68719476736 154060895555367 52633346743730176 (ep773 (BSN.head_sum_c_succ qz151 10 11 rfl rfl) (ep798 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep799 ep810) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz443 qz553)

noncomputable def ep812 := @Enclosure.Complex.IsNear.of_eq qz456 (Complex.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.true 50170514265 549755813888 5140871675273 26316673371865088 Bool.false 301122672903 1099511627776 41253983146195 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 12 qz155 rfl)

noncomputable def ep813 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz553 128194 1000 0 1 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 717310837643623501509 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz330) Bool.false 46938541828353910898688 18889465931478580854784 1000000000574437 191479000000000000000 11191020447815397 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep215 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep814 := nat_lit 1852800333695761860930388897598376405296582647453115525408978667930944307690625

noncomputable def ep815 := nat_lit 2681278120912970921771409328279809981533400482857738171468086782441062890625

noncomputable def ep816 := nat_lit 5553038444845459640947623874138569595926681141393631099883999830227950797290625

noncomputable def ep817 := BSN.cos_dyadic_bound_f 2682518545 2147483648 3 2 1048576 383332 ep814 ep64 ep815 ep816 ep66 ep815 331490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2682518545) qz290 0 2 ep814 ep64 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2682518545) qz291 0 2 ep816 ep66 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20876493) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep818 := @Enclosure.Real.IsNear.cos_image qz167 qz462 Bool.false 20876493 65536 703 1048576 Bool.true 331490 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 717310837643623501509 2251799813685248000 64097000036819688389 95739500000000000000000 20876493 65536 703 1048576 (ep813 rfl) rfl) (Enclosure.sfrac_false_div 20876493 65536) (BSN.cos_reduce2 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11797841330615286235136) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 331490 1048576 50 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 20876493 65536 226375608064910080 72057594037927936 50 11797841330615286235136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 331490 1048576 11797841330615286235136 9444732965739290427392 2682518545 2147483648 383332 382958 (ep817 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep819 := nat_lit 3332895578155640972937282888214453681548622045029321755198987132849746903530625

noncomputable def ep820 := nat_lit 8724671111545200595248110996887306616466765564771215878005446540768242074090625

noncomputable def ep821 := BSN.sin_dyadic_bound_f 2682518545 2147483648 3 2 1048576 383332 ep819 ep57 ep815 ep820 ep60 ep815 994799 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2682518545) qz286 0 2 ep819 ep57 ep815 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2682518545) qz287 0 2 ep820 ep60 ep815 rfl rfl rfl rfl) rfl rfl

noncomputable def ep822 := @Enclosure.Real.IsNear.sin_image qz167 qz462 Bool.false 20876493 65536 703 1048576 Bool.true 994799 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 717310837643623501509 2251799813685248000 64097000036819688389 95739500000000000000000 20876493 65536 703 1048576 (ep813 rfl) rfl) (Enclosure.sfrac_false_div 20876493 65536) (BSN.sin_reduce2 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11797841330615286235136) (@Nat.cast Real Real.instNatCast 9444732965739290427392)) 226375608064910080 72057594037927936 Bool.false 994799 1048576 50 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 20876493 65536 226375608064910080 72057594037927936 50 11797841330615286235136 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994799 1048576 11797841330615286235136 9444732965739290427392 2682518545 2147483648 383332 382958 (ep821 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep823 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz52 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.true 50170514265 549755813888 5140871675273 26316673371865088 Bool.false 301122672903 1099511627776 41253983146195 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz52 (Real.cos qz167) 302697 1048576 1 1048576 165745 524288 135658313 200780283904 50170514265 549755813888 5140871675273 26316673371865088 qz332 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.true 331490 1048576 135658313 200780283904 165745 524288 135658313 200780283904 (ep818 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz52 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 302697 1048576 1 1048576 994799 1048576 135658313 200780283904 301122672903 1099511627776 41253983146195 210533386974920704 qz332 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 994799 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 994799 1048576 135658313 200780283904 994799 1048576 135658313 200780283904 (ep822 rfl rfl) rfl)) rfl)

noncomputable def ep824 := @ep770 50170514265 549755813888 5140871675273 26316673371865088 Bool.false 301122672903 1099511627776 41253983146195 210533386974920704 Bool.false 550308866519883921227776 1001005996877 1099511627776 657442993086747 210533386974920704 Bool.false 10654307307726122778624 155040576759 1099511627776 657497565367663 210533386974920704 (ep771 (BSN.head_sum_c_succ qz151 11 12 rfl rfl) (ep811 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep812 ep823) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz443 qz554)

noncomputable def ep825 := @Enclosure.Complex.IsNear.of_eq qz455 (Complex.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.true 150055070841 1099511627776 39551490065105 210533386974920704 Bool.true 132738306129 549755813888 19813742029573 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 13 qz155 rfl)

noncomputable def ep826 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz554 128194 1000 0 1 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 740416306604133289669 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 48450490295254733815808 18889465931478580854784 1000000000574437 191479000000000000000 11551497052968677 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep229 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep827 := nat_lit 1489790690886295146476848076218536976

noncomputable def ep828 := BSN.sin_dyadic_bound_f 1104794018 2147483648 2 1 1048576 383332 ep827 ep79 ep827 ep827 ep80 ep827 515967 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1104794018) qz286 0 1 ep827 ep79 ep827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1104794018) qz287 0 1 ep827 ep80 ep827 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 172391605) qz32)

noncomputable def ep829 := @Enclosure.Real.IsNear.cos_image qz168 qz463 Bool.false 172391605 524288 703 1048576 Bool.true 515967 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 740416306604133289669 2251799813685248000 64097000036819688389 95739500000000000000000 172391605 524288 703 1048576 (ep826 rfl) rfl) (Enclosure.sfrac_false_div 172391605 524288) (BSN.cos_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38871483836320133939200) qz33) 226375608064910080 72057594037927936 Bool.false 515967 1048576 52 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 172391605 524288 226375608064910080 72057594037927936 52 38871483836320133939200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 515967 1048576 38871483836320133939200 75557863725914323419136 1104794018 2147483648 383332 382958 (ep828 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep830 := BSN.cos_dyadic_bound_f 1104794018 2147483648 2 1 1048576 383332 ep827 ep75 ep827 ep827 ep76 ep827 912846 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1104794018) qz290 0 1 ep827 ep75 ep827 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1104794018) qz291 0 1 ep827 ep76 ep827 rfl rfl rfl rfl) rfl rfl

noncomputable def ep831 := @Enclosure.Real.IsNear.sin_image qz168 qz463 Bool.false 172391605 524288 703 1048576 Bool.false 912846 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 740416306604133289669 2251799813685248000 64097000036819688389 95739500000000000000000 172391605 524288 703 1048576 (ep826 rfl) rfl) (Enclosure.sfrac_false_div 172391605 524288) (BSN.sin_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38871483836320133939200) qz33) 226375608064910080 72057594037927936 Bool.false 912846 1048576 52 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 172391605 524288 226375608064910080 72057594037927936 52 38871483836320133939200 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 912846 1048576 38871483836320133939200 75557863725914323419136 1104794018 2147483648 383332 382958 (ep830 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep832 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz54 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.true 150055070841 1099511627776 39551490065105 210533386974920704 Bool.true 132738306129 549755813888 19813742029573 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ft qz54 (Real.cos qz168) 290823 1048576 1 1048576 515967 1048576 135658313 200780283904 150055070841 1099511627776 39551490065105 210533386974920704 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.true 515967 1048576 135658313 200780283904 515967 1048576 135658313 200780283904 (ep829 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz54 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 290823 1048576 1 1048576 456423 524288 135658313 200780283904 132738306129 549755813888 19813742029573 105266693487460352 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.false 456423 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.false 912846 1048576 135658313 200780283904 456423 524288 135658313 200780283904 (ep831 rfl rfl) rfl)) rfl)

noncomputable def ep833 := @ep768 150055070841 1099511627776 39551490065105 210533386974920704 Bool.true 132738306129 549755813888 19813742029573 105266693487460352 Bool.false 935630437843336939175936 212737731509 274877906944 174248620787963 52633346743730176 Bool.true 60712852578316805210112 110436035499 1099511627776 697125049426809 210533386974920704 (ep769 (BSN.head_sum_c_succ qz151 12 13 rfl rfl) (ep824 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep825 ep832) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz443 qz556)

noncomputable def ep834 := @Enclosure.Complex.IsNear.of_eq qz454 (Complex.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 81732590707 549755813888 19064558793057 105266693487460352 Bool.false 244193381209 1099511627776 38184275984249 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 14 qz155 rfl)

noncomputable def ep835 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz556 128194 1000 0 1 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 152361778613769097153 450359962737049600 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz339) Bool.false 49850353174629559828480 18889465931478580854784 1000000000574437 191479000000000000000 11885250371606245 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep244 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep836 := nat_lit 2575301748360410075941442086538064561

noncomputable def ep837 := BSN.sin_dyadic_bound_f 1266797013 2147483648 2 1 1048576 383332 ep836 ep79 ep836 ep836 ep80 ep836 583298 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1266797013) qz286 0 1 ep836 ep79 ep836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1266797013) qz287 0 1 ep836 ep80 ep836 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 354744909) qz16)

noncomputable def ep838 := @Enclosure.Real.IsNear.cos_image qz169 qz464 Bool.false 354744909 1048576 703 1048576 Bool.false 583298 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 152361778613769097153 450359962737049600 64097000036819688389 95739500000000000000000 354744909 1048576 703 1048576 (ep835 rfl) rfl) (Enclosure.sfrac_false_div 354744909 1048576) (BSN.cos_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89142914999078719848448) qz19) 226375608064910080 72057594037927936 Bool.false 583298 1048576 53 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 354744909 1048576 226375608064910080 72057594037927936 53 89142914999078719848448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 583298 1048576 89142914999078719848448 151115727451828646838272 1266797013 2147483648 383332 382958 (ep837 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep839 := BSN.cos_dyadic_bound_f 1266797013 2147483648 2 1 1048576 383332 ep836 ep75 ep836 ep836 ep76 ep836 871363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1266797013) qz290 0 1 ep836 ep75 ep836 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1266797013) qz291 0 1 ep836 ep76 ep836 rfl rfl rfl rfl) rfl rfl

noncomputable def ep840 := @Enclosure.Real.IsNear.sin_image qz169 qz464 Bool.false 354744909 1048576 703 1048576 Bool.true 871363 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 152361778613769097153 450359962737049600 64097000036819688389 95739500000000000000000 354744909 1048576 703 1048576 (ep835 rfl) rfl) (Enclosure.sfrac_false_div 354744909 1048576) (BSN.sin_reduce3 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 89142914999078719848448) qz19) 226375608064910080 72057594037927936 Bool.false 871363 1048576 53 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 354744909 1048576 226375608064910080 72057594037927936 53 89142914999078719848448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 871363 1048576 89142914999078719848448 151115727451828646838272 1266797013 2147483648 383332 382958 (ep839 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep841 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz56 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 81732590707 549755813888 19064558793057 105266693487460352 Bool.false 244193381209 1099511627776 38184275984249 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz56 (Real.cos qz169) 280243 1048576 1 1048576 291649 524288 135658313 200780283904 81732590707 549755813888 19064558793057 105266693487460352 qz341 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 583298 1048576 135658313 200780283904 291649 524288 135658313 200780283904 (ep838 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz56 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 280243 1048576 1 1048576 871363 1048576 135658313 200780283904 244193381209 1099511627776 38184275984249 210533386974920704 qz341 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.true 871363 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.true 871363 1048576 135658313 200780283904 871363 1048576 135658313 200780283904 (ep840 rfl rfl) rfl)) rfl)

noncomputable def ep842 := @ep766 81732590707 549755813888 19064558793057 105266693487460352 Bool.false 244193381209 1099511627776 38184275984249 210533386974920704 Bool.false 139420288193067902566400 507208053725 549755813888 367561800368983 105266693487460352 Bool.false 147067756908599270440960 66878672855 549755813888 367654662705529 105266693487460352 (ep767 (BSN.head_sum_c_succ qz151 13 14 rfl rfl) (ep833 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep834 ep841) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz443 qz557)

noncomputable def ep843 := @Enclosure.Complex.IsNear.of_eq qz453 (Complex.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.true 339238473 137438953472 18365161181871 105266693487460352 Bool.true 17742469953 68719476736 18464587035579 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 15 qz155 rfl)

noncomputable def ep844 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz557 128194 1000 0 1 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 781724799734866218693 2251799813685248000 64097000036819688389 95739500000000000000000 qz156 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz343) Bool.false 51153586820399524478976 18889465931478580854784 1000000000574437 191479000000000000000 12195965485668069 4503599627370496 1000000000574437 191479000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep259 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep845 := BSN.sin_dyadic_bound_f 20529673 2147483648 1 0 1048576 383332 0 1 1 0 1 1 10024 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 20529673) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 20529673) qz287 0 0 rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11375593) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep846 := @Enclosure.Real.IsNear.cos_image qz170 qz465 Bool.false 11375593 32768 703 1048576 Bool.true 10024 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 781724799734866218693 2251799813685248000 64097000036819688389 95739500000000000000000 11375593 32768 703 1048576 (ep844 rfl) rfl) (Enclosure.sfrac_false_div 11375593 32768) (BSN.cos_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45145228704382713856) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 10024 1048576 55 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 11375593 32768 226375608064910080 72057594037927936 55 45145228704382713856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 10024 1048576 45145228704382713856 4722366482869645213696 20529673 2147483648 383332 382958 (ep845 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep847 := BSN.cos_dyadic_bound_f 20529673 2147483648 1 0 1048576 383332 0 1 1 0 1 1 1048528 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 20529673) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 20529673) qz291 0 0 rfl) rfl rfl

noncomputable def ep848 := @Enclosure.Real.IsNear.sin_image qz170 qz465 Bool.false 11375593 32768 703 1048576 Bool.false 1048528 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 781724799734866218693 2251799813685248000 64097000036819688389 95739500000000000000000 11375593 32768 703 1048576 (ep844 rfl) rfl) (Enclosure.sfrac_false_div 11375593 32768) (BSN.sin_reduce1 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 45145228704382713856) (@Nat.cast Real Real.instNatCast 4722366482869645213696)) 226375608064910080 72057594037927936 Bool.false 1048528 1048576 55 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 11375593 32768 226375608064910080 72057594037927936 55 45145228704382713856 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048528 1048576 45145228704382713856 4722366482869645213696 20529673 2147483648 383332 382958 (ep847 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep849 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz58 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.true 339238473 137438953472 18365161181871 105266693487460352 Bool.true 17742469953 68719476736 18464587035579 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ft qz58 (Real.cos qz170) 270741 1048576 1 1048576 1253 131072 135658313 200780283904 339238473 137438953472 18365161181871 105266693487460352 qz345 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.true 10024 1048576 135658313 200780283904 1253 131072 135658313 200780283904 (ep846 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz58 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 270741 1048576 1 1048576 65533 65536 135658313 200780283904 17742469953 68719476736 18464587035579 105266693487460352 qz345 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 65533 65536 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 1048528 1048576 135658313 200780283904 65533 65536 135658313 200780283904 (ep848 rfl rfl) rfl)) rfl)

noncomputable def ep850 := @ep764 339238473 137438953472 18365161181871 105266693487460352 Bool.true 17742469953 68719476736 18464587035579 105266693487460352 Bool.false 69523645773707713970176 505851099833 549755813888 192963480775427 52633346743730176 Bool.true 5158158606001172905984 75061086769 549755813888 96529812435277 26316673371865088 (ep765 (BSN.head_sum_c_succ qz151 14 15 rfl rfl) (ep842 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep843 ep849) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz443 qz558)

noncomputable def ep851 := @Enclosure.Complex.IsNear.of_eq qz452 (Complex.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.true 249937359777 1099511627776 35744576349353 210533386974920704 Bool.false 114405234489 1099511627776 35645578642689 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 16 qz155 rfl)

noncomputable def ep852 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz558 128194 1000 0 1 3121657384082679 1125899906842624 250000000191479 47869750000000000000 200088873347547475863 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 52372720210750067441664 18889465931478580854784 1000000000765916 191479000000000000000 3121657384082679 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep273 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep853 := nat_lit 722163273443609792115588492819809296

noncomputable def ep854 := BSN.cos_dyadic_bound_f 921847006 2147483648 2 1 1048576 383332 ep853 ep75 ep853 ep853 ep76 ep853 953439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 921847006) qz290 0 1 ep853 ep75 ep853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 921847006) qz291 0 1 ep853 ep76 ep853 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 372694569) qz16)

noncomputable def ep855 := @Enclosure.Real.IsNear.cos_image qz171 qz466 Bool.false 372694569 1048576 703 1048576 Bool.true 953439 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 200088873347547475863 562949953421312000 16024250012273229463 23934875000000000000000 372694569 1048576 703 1048576 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 372694569 1048576) (BSN.cos_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64869216171763158745088) qz19) 226375608064910080 72057594037927936 Bool.false 953439 1048576 56 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 372694569 1048576 226375608064910080 72057594037927936 56 64869216171763158745088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 953439 1048576 64869216171763158745088 151115727451828646838272 921847006 2147483648 383332 382958 (ep854 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep856 := BSN.sin_dyadic_bound_f 921847006 2147483648 2 1 1048576 383332 ep853 ep79 ep853 ep853 ep80 ep853 436423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 921847006) qz286 0 1 ep853 ep79 ep853 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 921847006) qz287 0 1 ep853 ep80 ep853 rfl rfl rfl rfl) rfl rfl

noncomputable def ep857 := @Enclosure.Real.IsNear.sin_image qz171 qz466 Bool.false 372694569 1048576 703 1048576 Bool.true 436423 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 200088873347547475863 562949953421312000 16024250012273229463 23934875000000000000000 372694569 1048576 703 1048576 (ep852 rfl) rfl) (Enclosure.sfrac_false_div 372694569 1048576) (BSN.sin_reduce2 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 64869216171763158745088) qz19) 226375608064910080 72057594037927936 Bool.false 436423 1048576 56 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 372694569 1048576 226375608064910080 72057594037927936 56 64869216171763158745088 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 436423 1048576 64869216171763158745088 151115727451828646838272 921847006 2147483648 383332 382958 (ep856 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep858 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz60 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.true 249937359777 1099511627776 35744576349353 210533386974920704 Bool.false 114405234489 1099511627776 35645578642689 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ft qz60 (Real.cos qz171) 262143 1048576 1 1048576 953439 1048576 135658313 200780283904 249937359777 1099511627776 35744576349353 210533386974920704 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.true 953439 1048576 135658313 200780283904 953439 1048576 135658313 200780283904 (ep855 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz60 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 262143 1048576 1 1048576 436423 1048576 135658313 200780283904 114405234489 1099511627776 35645578642689 210533386974920704 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.true 436423 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.true 436423 1048576 135658313 200780283904 436423 1048576 135658313 200780283904 (ep857 rfl rfl) rfl)) rfl)

noncomputable def ep859 := @ep762 249937359777 1099511627776 35744576349353 210533386974920704 Bool.false 114405234489 1099511627776 35645578642689 210533386974920704 Bool.false 418784649544439202578432 761764839889 1099511627776 807598499451061 210533386974920704 Bool.true 19635594896471083712512 35716939049 1099511627776 807884078124905 210533386974920704 (ep763 (BSN.head_sum_c_succ qz151 15 16 rfl rfl) (ep850 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep851 ep858) rfl rfl

theorem EMRow42.d13 : Enclosure.Complex.IsNear qz163 Bool.false 761764839889 1099511627776 807598499451061 210533386974920704 Bool.true 35716939049 1099511627776 807884078124905 210533386974920704 := ep761 (BSN.head_sum_c_succ qz151 16 17 rfl rfl) (ep859 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz172 := (BSN.headSumC qz440 25)

noncomputable abbrev qz467 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz152)

noncomputable def ep860 := @Enclosure.Complex.IsNear.of_eq qz172 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 24) qz467) Bool.false 2251041895485 1099511627776 1061514294545783 210533386974920704 Bool.true 12002851551 274877906944 530713181492483 105266693487460352

noncomputable def ep861 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 24) qz467 Bool.false 532432057237 274877906944 516184731094603 105266693487460352 Bool.true 118417663885 549755813888 64513821002845 13158336685932544 Bool.false

noncomputable abbrev qz468 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz152)

noncomputable def ep862 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 23) qz468) Bool.false 532432057237 274877906944 516184731094603 105266693487460352 Bool.true 118417663885 549755813888 64513821002845 13158336685932544

noncomputable def ep863 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 23) qz468 Bool.false 1903869354019 1099511627776 1002510787620197 210533386974920704 Bool.true 276200469419 1099511627776 1002525785404351 210533386974920704 Bool.false

noncomputable def ep864 := nat_lit 2341660951731113084059648

noncomputable abbrev qz469 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz152)

noncomputable def ep865 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 22) qz469) Bool.false 1903869354019 1099511627776 1002510787620197 210533386974920704 Bool.true 276200469419 1099511627776 1002525785404351 210533386974920704

noncomputable def ep866 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 22) qz469 Bool.false 1689097249891 1099511627776 971999331841327 210533386974920704 Bool.true 91132138573 549755813888 486058913448583 105266693487460352 Bool.false

noncomputable abbrev qz470 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz152)

noncomputable def ep867 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 21) qz470) Bool.false 1689097249891 1099511627776 971999331841327 210533386974920704 Bool.true 91132138573 549755813888 486058913448583 105266693487460352

noncomputable def ep868 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 21) qz470 Bool.false 1510605938447 1099511627776 940659267209103 210533386974920704 Bool.true 10962548821 549755813888 470404071161541 105266693487460352 Bool.false

noncomputable abbrev qz471 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz152)

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 20) qz471) Bool.false 1510605938447 1099511627776 940659267209103 210533386974920704 Bool.true 10962548821 549755813888 470404071161541 105266693487460352

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 20) qz471 Bool.false 83280004601 68719476736 5283174396251 1224031319621632 Bool.false 36884343027 274877906944 10568162165427 2448062639243264 Bool.false

noncomputable abbrev qz472 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz152)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 19) qz472) Bool.false 83280004601 68719476736 5283174396251 1224031319621632 Bool.false 36884343027 274877906944 10568162165427 2448062639243264

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 19) qz472 Bool.false 553695711453 549755813888 437946433697191 105266693487460352 Bool.false 261389376187 1099511627776 876137359078843 210533386974920704 Bool.false

noncomputable abbrev qz473 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz152)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz151 18) qz473) Bool.false 553695711453 549755813888 437946433697191 105266693487460352 Bool.false 261389376187 1099511627776 876137359078843 210533386974920704

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz151 18) qz473 Bool.false 426203362405 549755813888 421083547950711 105266693487460352 Bool.false 215076244599 1099511627776 842573254837415 210533386974920704 Bool.false

noncomputable abbrev qz474 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz152)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 18) (@HAdd.hAdd Complex Complex Complex qz4 qz163 qz474) Bool.false 426203362405 549755813888 421083547950711 105266693487460352 Bool.false 215076244599 1099511627776 842573254837415 210533386974920704

noncomputable def ep876 := @Enclosure.Complex.IsNear.addLitP qz163 qz474 Bool.false 761764839889 1099511627776 807598499451061 210533386974920704 Bool.true 35716939049 1099511627776 807884078124905 210533386974920704 Bool.false

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz443 qz559)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq qz474 (Complex.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 90641884921 1099511627776 34568596450361 210533386974920704 Bool.false 7837286989 34359738368 17344588356255 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 17 qz155 rfl)

noncomputable def ep878 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz559 128194 1000 0 1 3189913004350711 1125899906842624 250000000191479 47869750000000000000 204463853839867522967 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz358) Bool.false 53517859495200818200576 18889465931478580854784 1000000000765916 191479000000000000000 3189913004350711 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep308 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep879 := nat_lit 307681771361872572554416591817204881

noncomputable def ep880 := BSN.sin_dyadic_bound_f 744775603 2147483648 2 1 1048576 383332 ep879 ep79 ep879 ep879 ep80 ep879 356413 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 744775603) qz286 0 1 ep879 ep79 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 744775603) qz287 0 1 ep879 ep80 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 380843605) qz16)

noncomputable def ep881 := @Enclosure.Real.IsNear.cos_image qz173 qz475 Bool.false 380843605 1048576 703 1048576 Bool.false 356413 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 204463853839867522967 562949953421312000 16024250012273229463 23934875000000000000000 380843605 1048576 703 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 380843605 1048576) (BSN.cos_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52408923937327630254080) qz19) 226375608064910080 72057594037927936 Bool.false 356413 1048576 57 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 380843605 1048576 226375608064910080 72057594037927936 57 52408923937327630254080 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 356413 1048576 52408923937327630254080 151115727451828646838272 744775603 2147483648 383332 382958 (ep880 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep882 := BSN.cos_dyadic_bound_f 744775603 2147483648 2 1 1048576 383332 ep879 ep75 ep879 ep879 ep76 ep879 986144 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 744775603) qz290 0 1 ep879 ep75 ep879 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 744775603) qz291 0 1 ep879 ep76 ep879 rfl rfl rfl rfl) rfl rfl

noncomputable def ep883 := @Enclosure.Real.IsNear.sin_image qz173 qz475 Bool.false 380843605 1048576 703 1048576 Bool.true 986144 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 204463853839867522967 562949953421312000 16024250012273229463 23934875000000000000000 380843605 1048576 703 1048576 (ep878 rfl) rfl) (Enclosure.sfrac_false_div 380843605 1048576) (BSN.sin_reduce3 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52408923937327630254080) qz19) 226375608064910080 72057594037927936 Bool.false 986144 1048576 57 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 380843605 1048576 226375608064910080 72057594037927936 57 52408923937327630254080 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 986144 1048576 52408923937327630254080 151115727451828646838272 744775603 2147483648 383332 382958 (ep882 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep884 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz64 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz64 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 90641884921 1099511627776 34568596450361 210533386974920704 Bool.false 7837286989 34359738368 17344588356255 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz64 (Real.cos qz173) 254317 1048576 1 1048576 356413 1048576 135658313 200780283904 90641884921 1099511627776 34568596450361 210533386974920704 qz360 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 356413 1048576 135658313 200780283904 356413 1048576 135658313 200780283904 (ep881 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz64 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 254317 1048576 1 1048576 30817 32768 135658313 200780283904 7837286989 34359738368 17344588356255 105266693487460352 qz360 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 30817 32768 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 986144 1048576 135658313 200780283904 30817 32768 135658313 200780283904 (ep883 rfl rfl) rfl)) rfl)

noncomputable def ep885 := @ep876 90641884921 1099511627776 34568596450361 210533386974920704 Bool.false 7837286989 34359738368 17344588356255 105266693487460352 Bool.false 937231105523051984322560 426203362405 549755813888 421083547950711 105266693487460352 Bool.false 7389963493593613074432 215076244599 1099511627776 842573254837415 210533386974920704 EMRow42.d13 (ep877 ep884) rfl rfl

noncomputable abbrev qz174 := (@HMul.hMul Real Real Real qz267 qz443 qz560)

noncomputable def ep886 := @Enclosure.Complex.IsNear.of_eq qz473 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)))) Bool.false 15936543631 68719476736 1053930359155 6579168342966272 Bool.false 11578282897 274877906944 8391026060357 52633346743730176 (BSN.cpow_neg_s_mk qz154 128194 1000 18 qz155 rfl)

noncomputable def ep887 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz560 128194 1000 0 1 3254268794313975 1125899906842624 250000000191479 47869750000000000000 8343554676365714223 22517998136852480 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 54597570484265130393600 18889465931478580854784 1000000000765916 191479000000000000000 3254268794313975 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep322 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep888 := nat_lit 5128860654202629248042945751339963713238798670160419934174425256626889114224225

noncomputable def ep889 := nat_lit 6344015816681912895740226027718775333644588395840833264245105357881826051681

noncomputable def ep890 := nat_lit 13422459021113210647805088030416931707942381469207833716600431215824329485551201

noncomputable def ep891 := BSN.sin_dyadic_bound_f 2987414827 2147483648 3 2 1048576 383332 ep888 ep57 ep889 ep890 ep60 ep889 1031696 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2987414827) qz286 0 2 ep888 ep57 ep889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2987414827) qz287 0 2 ep890 ep60 ep889 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 388527041) qz16)

noncomputable def ep892 := @Enclosure.Real.IsNear.cos_image qz174 qz476 Bool.false 388527041 1048576 703 1048576 Bool.false 1031696 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 8343554676365714223 22517998136852480 16024250012273229463 23934875000000000000000 388527041 1048576 703 1048576 (ep887 rfl) rfl) (Enclosure.sfrac_false_div 388527041 1048576) (BSN.cos_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210220629737044759805952) qz19) 226375608064910080 72057594037927936 Bool.false 1031696 1048576 58 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 388527041 1048576 226375608064910080 72057594037927936 58 210220629737044759805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1031696 1048576 210220629737044759805952 151115727451828646838272 2987414827 2147483648 383332 382958 (ep891 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep893 := nat_lit 2852186592697763765755298851201188185280952411598384778214345189396219208369761

noncomputable def ep894 := nat_lit 8543871746459927471474416101548127005175568058003472668114545357472893973005921

noncomputable def ep895 := BSN.cos_dyadic_bound_f 2987414827 2147483648 3 2 1048576 383332 ep893 ep64 ep889 ep894 ep66 ep889 187388 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2987414827) qz290 0 2 ep893 ep64 ep889 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2987414827) qz291 0 2 ep894 ep66 ep889 rfl rfl rfl rfl) rfl rfl

noncomputable def ep896 := @Enclosure.Real.IsNear.sin_image qz174 qz476 Bool.false 388527041 1048576 703 1048576 Bool.true 187388 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz174 Bool.false 8343554676365714223 22517998136852480 16024250012273229463 23934875000000000000000 388527041 1048576 703 1048576 (ep887 rfl) rfl) (Enclosure.sfrac_false_div 388527041 1048576) (BSN.sin_reduce3 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 210220629737044759805952) qz19) 226375608064910080 72057594037927936 Bool.false 187388 1048576 58 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 388527041 1048576 226375608064910080 72057594037927936 58 210220629737044759805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 187388 1048576 210220629737044759805952 151115727451828646838272 2987414827 2147483648 383332 382958 (ep895 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep897 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz174)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174))) Bool.false 15936543631 68719476736 1053930359155 6579168342966272 Bool.false 11578282897 274877906944 8391026060357 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz174) 247151 1048576 1 1048576 64481 65536 135658313 200780283904 15936543631 68719476736 1053930359155 6579168342966272 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz174) Bool.false 1031696 1048576 135658313 200780283904 64481 65536 135658313 200780283904 (ep892 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz174)) 247151 1048576 1 1048576 46847 262144 135658313 200780283904 11578282897 274877906944 8391026060357 52633346743730176 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz174) Bool.true 46847 262144 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz174) Bool.true 187388 1048576 135658313 200780283904 46847 262144 135658313 200780283904 (ep896 rfl rfl) rfl)) rfl)

noncomputable def ep898 := @ep874 15936543631 68719476736 1053930359155 6579168342966272 Bool.false 11578282897 274877906944 8391026060357 52633346743730176 Bool.false 38049679562017402257408 553695711453 549755813888 437946433697191 105266693487460352 Bool.false 71850164623680395542528 261389376187 1099511627776 876137359078843 210533386974920704 (ep875 (BSN.head_sum_c_succ qz151 17 18 rfl rfl) (ep885 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep886 ep897) rfl rfl

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz443 qz561)

noncomputable def ep899 := @Enclosure.Complex.IsNear.of_eq qz472 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 112544325355 549755813888 16406564380395 105266693487460352 Bool.true 113852004079 1099511627776 32724587147879 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 19 qz155 rfl)

noncomputable def ep900 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz561 128194 1000 0 1 3315143513283831 1125899906842624 250000000191479 47869750000000000000 212490753770953715607 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz366) Bool.false 55618878793361701994496 18889465931478580854784 1000000000765916 191479000000000000000 3315143513283831 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep333 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep901 := nat_lit 1022725280534395431793287313663983616

noncomputable def ep902 := BSN.cos_dyadic_bound_f 1005633536 2147483648 2 1 1048576 383332 ep901 ep75 ep901 ep901 ep76 ep901 935690 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1005633536) qz290 0 1 ep901 ep75 ep901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1005633536) qz291 0 1 ep901 ep76 ep901 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 395794871) qz16)

noncomputable def ep903 := @Enclosure.Real.IsNear.cos_image qz175 qz477 Bool.false 395794871 1048576 703 1048576 Bool.false 935690 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 212490753770953715607 562949953421312000 16024250012273229463 23934875000000000000000 395794871 1048576 703 1048576 (ep900 rfl) rfl) (Enclosure.sfrac_false_div 395794871 1048576) (BSN.cos_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70765169079036581773312) qz19) 226375608064910080 72057594037927936 Bool.false 935690 1048576 60 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 395794871 1048576 226375608064910080 72057594037927936 60 70765169079036581773312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 935690 1048576 70765169079036581773312 151115727451828646838272 1005633536 2147483648 383332 382958 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := BSN.sin_dyadic_bound_f 1005633536 2147483648 2 1 1048576 383332 ep901 ep79 ep901 ep901 ep80 ep901 473281 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1005633536) qz286 0 1 ep901 ep79 ep901 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1005633536) qz287 0 1 ep901 ep80 ep901 rfl rfl rfl rfl) rfl rfl

noncomputable def ep905 := @Enclosure.Real.IsNear.sin_image qz175 qz477 Bool.false 395794871 1048576 703 1048576 Bool.false 473281 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 212490753770953715607 562949953421312000 16024250012273229463 23934875000000000000000 395794871 1048576 703 1048576 (ep900 rfl) rfl) (Enclosure.sfrac_false_div 395794871 1048576) (BSN.sin_reduce0 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70765169079036581773312) qz19) 226375608064910080 72057594037927936 Bool.false 473281 1048576 60 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 395794871 1048576 226375608064910080 72057594037927936 60 70765169079036581773312 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 473281 1048576 70765169079036581773312 151115727451828646838272 1005633536 2147483648 383332 382958 (ep904 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep906 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 112544325355 549755813888 16406564380395 105266693487460352 Bool.true 113852004079 1099511627776 32724587147879 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz68 (Real.cos qz175) 240559 1048576 1 1048576 467845 524288 135658313 200780283904 112544325355 549755813888 16406564380395 105266693487460352 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 935690 1048576 135658313 200780283904 467845 524288 135658313 200780283904 (ep903 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz68 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 240559 1048576 1 1048576 473281 1048576 135658313 200780283904 113852004079 1099511627776 32724587147879 210533386974920704 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.false 473281 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.false 473281 1048576 135658313 200780283904 473281 1048576 135658313 200780283904 (ep905 rfl rfl) rfl)) rfl)

noncomputable def ep907 := @ep872 112544325355 549755813888 16406564380395 105266693487460352 Bool.true 113852004079 1099511627776 32724587147879 210533386974920704 Bool.false 366269333680153117589504 83280004601 68719476736 5283174396251 1224031319621632 Bool.false 162219056164260500471808 36884343027 274877906944 10568162165427 2448062639243264 (ep873 (BSN.head_sum_c_succ qz151 18 19 rfl rfl) (ep898 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep899 ep906) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz443 qz562)

noncomputable def ep908 := @Enclosure.Complex.IsNear.of_eq qz471 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.false 178125864831 1099511627776 31953271053931 210533386974920704 Bool.true 84731234875 549755813888 3993274512045 26316673371865088 (BSN.cpow_neg_s_mk qz154 128194 1000 20 qz155 rfl)

noncomputable def ep909 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz562 128194 1000 0 1 3372893643545847 1125899906842624 250000000191479 47869750000000000000 216192363870358155159 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz370) Bool.false 56587765202795681021952 18889465931478580854784 1000000000765916 191479000000000000000 3372893643545847 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep344 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep910 := nat_lit 254205528666156705430093881741953175610582336329838165522990203950648524800000

noncomputable def ep911 := nat_lit 50598726742945126599000652598888029466143679105273520861303806361600000000

noncomputable def ep912 := nat_lit 762515388544984226037083643920661750772814721631303949527248004239222374400000

noncomputable def ep913 := BSN.cos_dyadic_bound_f 1633117560 2147483648 3 2 1048576 383332 ep910 ep64 ep911 ep912 ep66 ep911 759699 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1633117560) qz290 0 2 ep910 ep64 ep911 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1633117560) qz291 0 2 ep912 ep66 ep911 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 402689657) qz16)

noncomputable def ep914 := @Enclosure.Real.IsNear.cos_image qz176 qz478 Bool.false 402689657 1048576 703 1048576 Bool.false 759699 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 216192363870358155159 562949953421312000 16024250012273229463 23934875000000000000000 402689657 1048576 703 1048576 (ep909 rfl) rfl) (Enclosure.sfrac_false_div 402689657 1048576) (BSN.cos_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114920431802729977872384) qz19) 226375608064910080 72057594037927936 Bool.false 759699 1048576 61 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 402689657 1048576 226375608064910080 72057594037927936 61 114920431802729977872384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759699 1048576 114920431802729977872384 151115727451828646838272 1633117560 2147483648 383332 382958 (ep913 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep915 := nat_lit 7113278199462265274449092541032960000

noncomputable def ep916 := BSN.sin_dyadic_bound_f 1633117560 2147483648 2 1 1048576 383332 ep915 ep79 ep915 ep915 ep80 ep915 722750 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1633117560) qz286 0 1 ep915 ep79 ep915 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1633117560) qz287 0 1 ep915 ep80 ep915 rfl rfl rfl rfl) rfl rfl

noncomputable def ep917 := @Enclosure.Real.IsNear.sin_image qz176 qz478 Bool.false 402689657 1048576 703 1048576 Bool.false 722750 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 216192363870358155159 562949953421312000 16024250012273229463 23934875000000000000000 402689657 1048576 703 1048576 (ep909 rfl) rfl) (Enclosure.sfrac_false_div 402689657 1048576) (BSN.sin_reduce0 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 114920431802729977872384) qz19) 226375608064910080 72057594037927936 Bool.false 722750 1048576 61 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 402689657 1048576 226375608064910080 72057594037927936 61 114920431802729977872384 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 722750 1048576 114920431802729977872384 151115727451828646838272 1633117560 2147483648 383332 382958 (ep916 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep918 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.false 178125864831 1099511627776 31953271053931 210533386974920704 Bool.true 84731234875 549755813888 3993274512045 26316673371865088 (@Enclosure.Real.IsNear.mulLit_ff qz70 (Real.cos qz176) 234469 1048576 1 1048576 759699 1048576 135658313 200780283904 178125864831 1099511627776 31953271053931 210533386974920704 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.false 759699 1048576 135658313 200780283904 759699 1048576 135658313 200780283904 (ep914 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 234469 1048576 1 1048576 361375 524288 135658313 200780283904 84731234875 549755813888 3993274512045 26316673371865088 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.false 361375 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.false 722750 1048576 135658313 200780283904 361375 524288 135658313 200780283904 (ep917 rfl rfl) rfl)) rfl)

noncomputable def ep919 := @ep870 178125864831 1099511627776 31953271053931 210533386974920704 Bool.true 84731234875 549755813888 3993274512045 26316673371865088 Bool.false 103808049644372064468992 1510605938447 1099511627776 940659267209103 210533386974920704 Bool.true 3013362474687894913024 10962548821 549755813888 470404071161541 105266693487460352 (ep871 (BSN.head_sum_c_succ qz151 19 20 rfl rfl) (ep907 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep908 ep918) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz443 qz563)

noncomputable def ep920 := @Enclosure.Complex.IsNear.of_eq qz470 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.false 44622827861 274877906944 979377019757 6579168342966272 Bool.true 10021198719 68719476736 7827421143521 52633346743730176 (BSN.cpow_neg_s_mk qz154 128194 1000 21 qz155 rfl)

noncomputable def ep921 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz563 128194 1000 0 1 3427826275261687 1125899906842624 250000000191479 47869750000000000000 219713380765448351639 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz374) Bool.false 57509381830540779323392 18889465931478580854784 1000000000765916 191479000000000000000 3427826275261687 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep358 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep922 := nat_lit 218059046727577379984383670560287228956907596294605126324034043805430867690625

noncomputable def ep923 := nat_lit 37234232256294845591534967784798073489987348435136568994551573981062890625

noncomputable def ep924 := nat_lit 654102671718219550261967941745292090723742814186945105834113028268330477290625

noncomputable def ep925 := BSN.cos_dyadic_bound_f 1571693295 2147483648 3 2 1048576 383332 ep922 ep64 ep923 ep924 ep66 ep923 780058 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1571693295) qz290 0 2 ep922 ep64 ep923 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1571693295) qz291 0 2 ep924 ep66 ep923 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204624031) qz32)

noncomputable def ep926 := @Enclosure.Real.IsNear.cos_image qz177 qz479 Bool.false 204624031 524288 703 1048576 Bool.false 780058 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 219713380765448351639 562949953421312000 16024250012273229463 23934875000000000000000 204624031 524288 703 1048576 (ep921 rfl) rfl) (Enclosure.sfrac_false_div 204624031 524288) (BSN.cos_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55299041723139449946112) qz33) 226375608064910080 72057594037927936 Bool.false 780058 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 204624031 524288 226375608064910080 72057594037927936 62 55299041723139449946112 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 780058 1048576 55299041723139449946112 75557863725914323419136 1571693295 2147483648 383332 382958 (ep925 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep927 := nat_lit 6101985927244903568955329551246850625

noncomputable def ep928 := BSN.sin_dyadic_bound_f 1571693295 2147483648 2 1 1048576 383332 ep927 ep79 ep927 ep927 ep80 ep927 700728 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1571693295) qz286 0 1 ep927 ep79 ep927 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1571693295) qz287 0 1 ep927 ep80 ep927 rfl rfl rfl rfl) rfl rfl

noncomputable def ep929 := @Enclosure.Real.IsNear.sin_image qz177 qz479 Bool.false 204624031 524288 703 1048576 Bool.false 700728 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 219713380765448351639 562949953421312000 16024250012273229463 23934875000000000000000 204624031 524288 703 1048576 (ep921 rfl) rfl) (Enclosure.sfrac_false_div 204624031 524288) (BSN.sin_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55299041723139449946112) qz33) 226375608064910080 72057594037927936 Bool.false 700728 1048576 62 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 204624031 524288 226375608064910080 72057594037927936 62 55299041723139449946112 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 700728 1048576 55299041723139449946112 75557863725914323419136 1571693295 2147483648 383332 382958 (ep928 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep930 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.false 44622827861 274877906944 979377019757 6579168342966272 Bool.true 10021198719 68719476736 7827421143521 52633346743730176 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz177) 114409 524288 1 524288 390029 524288 135658313 200780283904 44622827861 274877906944 979377019757 6579168342966272 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.false 780058 1048576 135658313 200780283904 390029 524288 135658313 200780283904 (ep926 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 114409 524288 1 524288 87591 131072 135658313 200780283904 10021198719 68719476736 7827421143521 52633346743730176 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 87591 131072 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 700728 1048576 135658313 200780283904 87591 131072 135658313 200780283904 (ep929 rfl rfl) rfl)) rfl)

noncomputable def ep931 := @ep868 44622827861 274877906944 979377019757 6579168342966272 Bool.true 10021198719 68719476736 7827421143521 52633346743730176 Bool.false 464295516674904612143104 1689097249891 1099511627776 971999331841327 210533386974920704 Bool.true 6262552876569201737728 91132138573 549755813888 486058913448583 105266693487460352 (ep869 (BSN.head_sum_c_succ qz151 20 21 rfl rfl) (ep919 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep920 ep930) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz443 qz564)

noncomputable def ep932 := @Enclosure.Complex.IsNear.of_eq qz469 (Complex.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.false 3355814127 17179869184 15255727889435 105266693487460352 Bool.true 93936192273 1099511627776 30407958507185 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 22 qz155 rfl)

noncomputable def ep933 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz564 128194 1000 0 1 3480203401436407 1125899906842624 250000000191479 47869750000000000000 223070597421869379479 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz378) Bool.false 58388124189833310502912 18889465931478580854784 1000000000765916 191479000000000000000 3480203401436407 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep372 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep934 := nat_lit 614612790048260426847836216443569121

noncomputable def ep935 := BSN.cos_dyadic_bound_f 885422183 2147483648 2 1 1048576 383332 ep934 ep75 ep934 ep934 ep76 ep934 960704 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 885422183) qz290 0 1 ep934 ep75 ep934 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 885422183) qz291 0 1 ep934 ep76 ep934 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz480 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 207750683) qz32)

noncomputable def ep936 := @Enclosure.Real.IsNear.cos_image qz178 qz480 Bool.false 207750683 524288 703 1048576 Bool.false 960704 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 223070597421869379479 562949953421312000 16024250012273229463 23934875000000000000000 207750683 524288 703 1048576 (ep933 rfl) rfl) (Enclosure.sfrac_false_div 207750683 524288) (BSN.cos_reduce0 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31153023546348059754496) qz33) 226375608064910080 72057594037927936 Bool.false 960704 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 207750683 524288 226375608064910080 72057594037927936 63 31153023546348059754496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 960704 1048576 31153023546348059754496 75557863725914323419136 885422183 2147483648 383332 382958 (ep935 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep937 := BSN.sin_dyadic_bound_f 885422183 2147483648 2 1 1048576 383332 ep934 ep79 ep934 ep934 ep80 ep934 420189 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 885422183) qz286 0 1 ep934 ep79 ep934 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 885422183) qz287 0 1 ep934 ep80 ep934 rfl rfl rfl rfl) rfl rfl

noncomputable def ep938 := @Enclosure.Real.IsNear.sin_image qz178 qz480 Bool.false 207750683 524288 703 1048576 Bool.false 420189 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 223070597421869379479 562949953421312000 16024250012273229463 23934875000000000000000 207750683 524288 703 1048576 (ep933 rfl) rfl) (Enclosure.sfrac_false_div 207750683 524288) (BSN.sin_reduce0 qz480 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31153023546348059754496) qz33) 226375608064910080 72057594037927936 Bool.false 420189 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q0 207750683 524288 226375608064910080 72057594037927936 63 31153023546348059754496 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 420189 1048576 31153023546348059754496 75557863725914323419136 885422183 2147483648 383332 382958 (ep937 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep939 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz74 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.false 3355814127 17179869184 15255727889435 105266693487460352 Bool.true 93936192273 1099511627776 30407958507185 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz74 (Real.cos qz178) 223557 1048576 1 1048576 15011 16384 135658313 200780283904 3355814127 17179869184 15255727889435 105266693487460352 qz380 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.false 960704 1048576 135658313 200780283904 15011 16384 135658313 200780283904 (ep936 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz74 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 223557 1048576 1 1048576 420189 1048576 135658313 200780283904 93936192273 1099511627776 30407958507185 210533386974920704 qz380 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 420189 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 420189 1048576 135658313 200780283904 420189 1048576 135658313 200780283904 (ep938 rfl rfl) rfl)) rfl)

noncomputable def ep940 := @ep866 3355814127 17179869184 15255727889435 105266693487460352 Bool.true 93936192273 1099511627776 30407958507185 210533386974920704 Bool.false 32708226445473004650496 1903869354019 1099511627776 1002510787620197 210533386974920704 Bool.true 151842813861689999491072 276200469419 1099511627776 1002525785404351 210533386974920704 (ep867 (BSN.head_sum_c_succ qz151 21 22 rfl rfl) (ep931 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep932 ep939) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz443 qz565)

noncomputable def ep941 := @Enclosure.Complex.IsNear.of_eq qz468 (Complex.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 225858874929 1099511627776 29858674569009 210533386974920704 Bool.false 39365141649 1099511627776 29695350641169 210533386974920704 (BSN.cpow_neg_s_mk qz154 128194 1000 23 qz155 rfl)

noncomputable def ep942 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz565 128194 1000 0 1 3530250507853047 1125899906842624 250000000191479 47869750000000000000 226278466801856753559 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz382) Bool.false 59227775304360265777152 18889465931478580854784 1000000000765916 191479000000000000000 3530250507853047 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep383 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep943 := nat_lit 5234726685255253329224290140415968244413830678557309899884043534937714851840000

noncomputable def ep944 := nat_lit 6608278407724293087666136584497928990324102777039387393900169238937600000000

noncomputable def ep945 := nat_lit 13699299343960776530588348051381205897956650848868224062963323269878592307200000

noncomputable def ep946 := BSN.sin_dyadic_bound_f 3002693760 2147483648 3 2 1048576 383332 ep943 ep57 ep944 ep945 ep60 ep944 1033003 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3002693760) qz286 0 2 ep943 ep57 ep944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3002693760) qz287 0 2 ep945 ep60 ep944 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz481 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 52684561) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep947 := @Enclosure.Real.IsNear.cos_image qz179 qz481 Bool.false 52684561 131072 703 1048576 Bool.false 1033003 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 226278466801856753559 562949953421312000 16024250012273229463 23934875000000000000000 52684561 131072 703 1048576 (ep942 rfl) rfl) (Enclosure.sfrac_false_div 52684561 131072) (BSN.cos_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26411973636508344123392) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 1033003 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 52684561 131072 226375608064910080 72057594037927936 63 26411973636508344123392 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1033003 1048576 26411973636508344123392 18889465931478580854784 3002693760 2147483648 383332 382958 (ep946 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep948 := nat_lit 2911118504434129313163568360935314770892272200432745227666202039071591628800000

noncomputable def ep949 := nat_lit 8720138956486939353315372809636948454696168395744156908210805778736899686400000

noncomputable def ep950 := BSN.cos_dyadic_bound_f 3002693760 2147483648 3 2 1048576 383332 ep948 ep64 ep944 ep949 ep66 ep944 180043 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3002693760) qz290 0 2 ep948 ep64 ep944 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3002693760) qz291 0 2 ep949 ep66 ep944 rfl rfl rfl rfl) rfl rfl

noncomputable def ep951 := @Enclosure.Real.IsNear.sin_image qz179 qz481 Bool.false 52684561 131072 703 1048576 Bool.true 180043 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 226278466801856753559 562949953421312000 16024250012273229463 23934875000000000000000 52684561 131072 703 1048576 (ep942 rfl) rfl) (Enclosure.sfrac_false_div 52684561 131072) (BSN.sin_reduce3 qz481 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26411973636508344123392) (@Nat.cast Real Real.instNatCast 18889465931478580854784)) 226375608064910080 72057594037927936 Bool.false 180043 1048576 63 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 52684561 131072 226375608064910080 72057594037927936 63 26411973636508344123392 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 180043 1048576 26411973636508344123392 18889465931478580854784 3002693760 2147483648 383332 382958 (ep950 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep952 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz76 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 225858874929 1099511627776 29858674569009 210533386974920704 Bool.false 39365141649 1099511627776 29695350641169 210533386974920704 (@Enclosure.Real.IsNear.mulLit_ff qz76 (Real.cos qz179) 218643 1048576 1 1048576 1033003 1048576 135658313 200780283904 225858874929 1099511627776 29858674569009 210533386974920704 qz384 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 1033003 1048576 135658313 200780283904 1033003 1048576 135658313 200780283904 (ep947 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz76 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 218643 1048576 1 1048576 180043 1048576 135658313 200780283904 39365141649 1099511627776 29695350641169 210533386974920704 qz384 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.true 180043 1048576 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.true 180043 1048576 135658313 200780283904 180043 1048576 135658313 200780283904 (ep951 rfl rfl) rfl)) rfl)

noncomputable def ep953 := @ep863 225858874929 1099511627776 29858674569009 210533386974920704 Bool.false 39365141649 1099511627776 29695350641169 210533386974920704 Bool.false ep864 532432057237 274877906944 516184731094603 105266693487460352 Bool.true 260403196751255196139520 118417663885 549755813888 64513821002845 13158336685932544 (ep865 (BSN.head_sum_c_succ qz151 22 23 rfl rfl) (ep940 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep941 ep952) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 qz443 qz566)

noncomputable def ep954 := @Enclosure.Complex.IsNear.of_eq qz467 (Complex.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.false 121313666537 1099511627776 29144832356577 210533386974920704 Bool.false 94411960783 549755813888 14602613469723 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 24 qz155 rfl)

noncomputable def ep955 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz566 128194 1000 0 1 3578169457974519 1125899906842624 250000000191479 47869750000000000000 229349927747792744343 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz386) Bool.false 60031721881041427759104 18889465931478580854784 1000000000765916 191479000000000000000 3578169457974519 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep398 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep956 := nat_lit 2261818977566339427212997970766073856

noncomputable def ep957 := BSN.sin_dyadic_bound_f 1226350072 2147483648 2 1 1048576 383332 ep956 ep79 ep956 ep956 ep80 ep956 566783 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1226350072) qz286 0 1 ep956 ep79 ep956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1226350072) qz287 0 1 ep956 ep80 ep956 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 213598765) qz32)

noncomputable def ep958 := @Enclosure.Real.IsNear.cos_image qz180 qz482 Bool.false 213598765 524288 703 1048576 Bool.false 566783 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 229349927747792744343 562949953421312000 16024250012273229463 23934875000000000000000 213598765 524288 703 1048576 (ep955 rfl) rfl) (Enclosure.sfrac_false_div 213598765 524288) (BSN.cos_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43148357251426387230720) qz33) 226375608064910080 72057594037927936 Bool.false 566783 1048576 64 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 213598765 524288 226375608064910080 72057594037927936 64 43148357251426387230720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 566783 1048576 43148357251426387230720 75557863725914323419136 1226350072 2147483648 383332 382958 (ep957 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep959 := BSN.cos_dyadic_bound_f 1226350072 2147483648 2 1 1048576 383332 ep956 ep75 ep956 ep956 ep76 ep956 882194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1226350072) qz290 0 1 ep956 ep75 ep956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1226350072) qz291 0 1 ep956 ep76 ep956 rfl rfl rfl rfl) rfl rfl

noncomputable def ep960 := @Enclosure.Real.IsNear.sin_image qz180 qz482 Bool.false 213598765 524288 703 1048576 Bool.true 882194 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 229349927747792744343 562949953421312000 16024250012273229463 23934875000000000000000 213598765 524288 703 1048576 (ep955 rfl) rfl) (Enclosure.sfrac_false_div 213598765 524288) (BSN.sin_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 43148357251426387230720) qz33) 226375608064910080 72057594037927936 Bool.false 882194 1048576 64 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q3 213598765 524288 226375608064910080 72057594037927936 64 43148357251426387230720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 882194 1048576 43148357251426387230720 75557863725914323419136 1226350072 2147483648 383332 382958 (ep959 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep961 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz78 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz78 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.false 121313666537 1099511627776 29144832356577 210533386974920704 Bool.false 94411960783 549755813888 14602613469723 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ff qz78 (Real.cos qz180) 214039 1048576 1 1048576 566783 1048576 135658313 200780283904 121313666537 1099511627776 29144832356577 210533386974920704 qz388 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.false 566783 1048576 135658313 200780283904 566783 1048576 135658313 200780283904 (ep958 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz78 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 214039 1048576 1 1048576 441097 524288 135658313 200780283904 94411960783 549755813888 14602613469723 105266693487460352 qz388 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 441097 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 882194 1048576 135658313 200780283904 441097 524288 135658313 200780283904 (ep960 rfl rfl) rfl)) rfl)

noncomputable def ep962 := @ep861 121313666537 1099511627776 29144832356577 210533386974920704 Bool.false 94411960783 549755813888 14602613469723 105266693487460352 Bool.false 618761684674171203747840 2251041895485 1099511627776 1061514294545783 210533386974920704 Bool.true 13197274846793696280576 12002851551 274877906944 530713181492483 105266693487460352 (ep862 (BSN.head_sum_c_succ qz151 23 24 rfl rfl) (ep953 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep954 ep961) rfl rfl

theorem EMRow42.d14 : Enclosure.Complex.IsNear qz172 Bool.false 2251041895485 1099511627776 1061514294545783 210533386974920704 Bool.true 12002851551 274877906944 530713181492483 105266693487460352 := ep860 (BSN.head_sum_c_succ qz151 24 25 rfl rfl) (ep962 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep963 := nat_lit 459327213701274920948349756566593

noncomputable def ep964 := nat_lit 246311731208572567174479085568000

noncomputable def ep965 := nat_lit 161081631501319039669750763989607848800367

noncomputable def ep966 := nat_lit 27092473224548814721161025303143423934464000

noncomputable abbrev qz582 := (@HAdd.hAdd Complex Complex Complex qz592 (@HAdd.hAdd Complex Complex Complex qz592 qz595 (@HMul.hMul Complex Complex Complex qz594 Complex.I (@HDiv.hDiv Complex Complex Complex qz596 (↑qz599) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz483 := qz582

noncomputable abbrev qz181 := (Complex.Stirling.logGammaStirling 1 qz483)

noncomputable abbrev qz583 := (@HAdd.hAdd Complex Complex Complex qz592 qz595 (@HMul.hMul Complex Complex Complex qz594 Complex.I (@HDiv.hDiv Complex Complex Complex qz596 (↑qz599) (2 : Complex))))

noncomputable abbrev qz484 := qz583

noncomputable abbrev qz182 := qz484

noncomputable abbrev qz183 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz443 (2 : Real)) (Real.log Real.pi))

noncomputable def ep967 := Complex.re (@HMul.hMul Complex Complex Complex qz80 (Complex.exp (@HMul.hMul Complex Complex Complex qz80 Complex.I ↑(@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183))) (zetaApproximant qz151 1 26))

noncomputable def ep968 := @Enclosure.Real.IsNear.of_eq ep967 (@HSub.hSub Real Real Real qz393 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz151 1 26))))

noncomputable def ep969 := nat_lit 9186704958178416548914176491393

noncomputable def ep970 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz151 1 26))) ep969

noncomputable def ep971 := nat_lit 4926234624171451343489581711360

noncomputable def ep972 := nat_lit 26708353016645325126577925691140301386743

noncomputable def ep973 := nat_lit 4515412204091469120193504217190570655744000

noncomputable def ep974 := nat_lit 618015972762038258389846389

noncomputable def ep975 := nat_lit 18947056246813274398036852736000

noncomputable def ep976 := nat_lit 831513401447088910283209842766040479909

noncomputable def ep977 := nat_lit 174057971073801536646848713525171216409603017444008538364968960

noncomputable def ep978 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.re (zetaApproximant qz151 1 26)) 1048575 1048576 69023621

noncomputable def ep979 := nat_lit 657084969471312248688518453

noncomputable def ep980 := nat_lit 352351757824763155709952000

noncomputable def ep981 := nat_lit 355693111237036879765470114637

noncomputable def ep982 := nat_lit 67467962236527824292185899008000

noncomputable def ep983 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.true 1048575 1048576 69023621

noncomputable abbrev qz485 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 67531293) qz32)

noncomputable def ep984 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz485 Bool.false 67531293 524288 355

noncomputable def ep985 := nat_lit 101792837395628402419329067

noncomputable def ep986 := nat_lit 301170425856000000000000000000

noncomputable def ep987 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) Bool.false 870134084865771871783 6755399441055744000 ep985 ep986

noncomputable def ep988 := nat_lit 28153460617628402419329067

noncomputable def ep989 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183 1365802967092314414631 6755399441055744000 ep988 ep986 4808621037 65536000

noncomputable def ep990 := nat_lit 57025107385763225389170688000

noncomputable def ep991 := nat_lit 8742823678041319002962461

noncomputable def ep992 := nat_lit 50195070976000000000000000000

noncomputable def ep993 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 113495775242190786391 1125899906842624000 ep991 ep992 Bool.false 1365802967092314414631 6755399441055744000

noncomputable def ep994 := nat_lit 8611751677438978151250461

noncomputable def ep995 := nat_lit 26580596617327231993473067

noncomputable def ep996 := @Enclosure.Complex.IsNear.subLitP qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 104127170621352157391 1125899906842624000 ep994 ep992 Bool.false 1386867614814488694631 6755399441055744000 ep995

noncomputable def ep997 := nat_lit 127784882772213997749368748437929984

noncomputable def ep998 := nat_lit 384439358353654063024670566500007936

noncomputable abbrev qz486 := (@HSub.hSub Complex Complex Complex qz568 qz582 qz571)

noncomputable abbrev qz487 := (Complex.log qz582)

noncomputable abbrev qz184 := (@HSub.hSub Complex Complex Complex qz390 (@HMul.hMul Complex Complex Complex qz389 qz486 qz487) qz483)

noncomputable abbrev qz185 := qz483

noncomputable def ep999 := @Enclosure.Complex.IsNear.of_eq qz181 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k)))))) Bool.true 104127170621352157391

noncomputable def ep1000 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz184 qz86) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) Bool.true 104127221941889245391 1125899906842624000

noncomputable def ep1001 := nat_lit 7155564679099512244694234955776

noncomputable def ep1002 := nat_lit 23826204198039016201607503151104000

noncomputable def ep1003 := @ep1000 32851217217009448919 191479000000000000000000 Bool.false 462292128931465768909 2251799813685248000 16899250073806920903 191479000000000000000000 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000 Bool.true ep1001 104127170621352157391 1125899906842624000 ep994 ep992 Bool.false ep1002

noncomputable def ep1004 := @Enclosure.Complex.IsNear.addLitP qz184 qz86 Bool.true 105161853793691869391 1125899906842624000 64972000016294288463 382958000000000000000000

noncomputable def ep1005 := nat_lit 13648163234367307171889152

noncomputable def ep1006 := @ep1004 Bool.false 462292128931465768909 2251799813685248000 16899250073806920903 191479000000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1005 104127221941889245391 1125899906842624000 32851217217009448919 191479000000000000000000 Bool.false 462292128931465768909 462292128931465768909 2251799813685248000

noncomputable abbrev qz186 := (@HMul.hMul Complex Complex Complex qz389 qz486 qz487)

noncomputable def ep1007 := @Enclosure.Complex.IsNear.subLitP qz186 qz185 Bool.true 102628579003295965391 1125899906842624000 64972000016294288463 382958000000000000000000 Bool.false 121325148317849821993

noncomputable def ep1008 := @ep1007 450359962737049600 16899250073806920903 191479000000000000000000 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 Bool.true 420647415174767477564000 105161853793691869391 1125899906842624000 64972000016294288463 382958000000000000000000 Bool.false 369833703145172615127200 462292128931465768909 2251799813685248000 16899250073806920903 191479000000000000000000

noncomputable abbrev qz187 := qz486

noncomputable abbrev qz188 := qz487

noncomputable def ep1009 := @Enclosure.Complex.IsNear.mul qz187 qz188 Bool.true 102628579003295965391 1125899906842624000 64972000016294288463 382958000000000000000000 Bool.false 121325148317849821993 450359962737049600 16899250073806920903

noncomputable abbrev qz189 := (Complex.re qz486)

noncomputable abbrev qz190 := (Complex.re qz487)

noncomputable abbrev qz191 := (Complex.im qz486)

noncomputable abbrev qz192 := (Complex.im qz487)

noncomputable def ep1010 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz189 qz190) (@HMul.hMul Real Real Real qz0 qz191 qz192) 65588379898830915 9007199254740992 875000004021059 382958000000000000000 55413563245324914883 562949953421312000

noncomputable def ep1011 := nat_lit 462198030156807219511917651150503936

noncomputable def ep1012 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz190 7000 4000 0 1 9369768556975845 2251799813685248 125000000574437 95739500000000000000

noncomputable def ep1013 := @Enclosure.Complex.IsNear.re_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable abbrev qz193 := (Enclosure.sfrac Bool.false 256388 4000)

noncomputable def ep1014 := @Enclosure.Complex.IsNear.of_eq qz187 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz193) Bool.false 7000 4000 0 1 Bool.false 256388 4000 0

noncomputable abbrev qz488 := (Complex.log (Complex.mk qz101 qz193))

noncomputable def ep1015 := @Enclosure.Complex.IsNear.of_eq qz188 qz488 Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1016 := BSN.log_dyadic_bound 279806544 131351806544 1 0 1 1048576 382958 0 1 4467 131631613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 279806544) (BSN.artanhQ 131351806544) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 65815806544 16000000))

noncomputable def ep1017 := @Enclosure.Real.IsNear.mulLit_ff qz102 qz584 1 2 0 1 9369768556975845 1125899906842624 125000000574437 47869750000000000000 9369768556975845 2251799813685248 125000000574437 95739500000000000000 qz406 (BSN.isNear_log_sfrac 65815806544 16000000 9369768556975845 1125899906842624 125000000574437 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65815806544) qz407)) Bool.false 314397261900784116695040 37778931862957161709568 1000000004595496 382958000000000000000 9369768556975845 1125899906842624 125000000574437 47869750000000000000 (BSN.log_rat_reduce_isNear 65815806544 16000000 12 131631613088 131072000000 4467 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep1016 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1018 := BSN.arctan_dyadic_bound_f 9000 256388 1 0 1048576 382958 0 1 1 0 1 1 36793 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz489 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 256388)))

noncomputable def ep1019 := @Enclosure.Real.IsNear.subLit_ff_p qz103 qz489 884279719003555 562949953421312 1 2000000000000000 36793 1048576 1 382958 906521872997641355264 864526627538339 562949953421312 1000000000191479 382958000000000000000 qz104 (ep1018 rfl) rfl rfl

noncomputable abbrev qz490 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 256388) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1020 := @Enclosure.Complex.IsNear.re_isNear qz188 Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (ep1015 (@congrArg Complex Complex qz185 (Complex.mk qz101 qz193) Complex.log (BSN.w_shift_mk qz154 Bool.false 128194 1000 2 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz488 Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz488) (@HMul.hMul Real Real Real qz0 qz102 qz584) Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 (Enclosure.clog_re_eq 9000 256388 4000 65815806544 16000000 rfl rfl rfl) (ep1017 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz488) qz490 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 9000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz490 (@HSub.hSub Real Real Real qz393 qz103 qz489) Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 256388 9000 rfl rfl) ep1019))))

noncomputable def ep1021 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz192 256388 4000 0 1 864526627538339 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1022 := @Enclosure.Complex.IsNear.im_isNear qz187 Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable def ep1023 := @Enclosure.Complex.IsNear.im_isNear qz188 Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (ep1015 (@congrArg Complex Complex qz185 (Complex.mk qz101 qz193) Complex.log (BSN.w_shift_mk qz154 Bool.false 128194 1000 2 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz488 Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz488) (@HMul.hMul Real Real Real qz0 qz102 qz584) Bool.false 9369768556975845 2251799813685248 125000000574437 95739500000000000000 (Enclosure.clog_re_eq 9000 256388 4000 65815806544 16000000 rfl rfl rfl) (ep1017 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz488) qz490 Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 9000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz490 (@HSub.hSub Real Real Real qz393 qz103 qz489) Bool.false 864526627538339 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 256388 9000 rfl rfl) ep1019))))

noncomputable abbrev qz194 := (@ep1014 1 (BSN.w_sub_half_mk qz443 Bool.false 128194 1000 2 qz444 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) (Enclosure.sfrac Bool.false 256388 4000) Bool.false 7000 4000 0 1 Bool.false 256388 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 256388 4000)))

noncomputable def ep1024 := @ep1010 64097000012273229463 382958000000000000000000 ep1011 102628579003295965391 1125899906842624000 64972000016294288463 382958000000000000000000 (@ep1012 65588379898830915 9007199254740992 875000004021059 382958000000000000000 (ep1013 qz194) ep1020 rfl) (@ep1021 55413563245324914883 562949953421312000 64097000012273229463 382958000000000000000000 (ep1022 qz194) ep1023 rfl) rfl

noncomputable def ep1025 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz189 qz192) (@HMul.hMul Real Real Real qz0 qz191 qz190) 6051686392768373 2251799813685248 7000000001340353 1531832000000000000000 120114811039296147393 450359962737049600

noncomputable def ep1026 := nat_lit 273199946377469308960430642130059264

noncomputable def ep1027 := @Enclosure.Real.IsNear.mulLit_ff qz189 qz192 7000 4000 0 1 864526627538339 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1028 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz190 256388 4000 0 1 9369768556975845 2251799813685248 125000000574437 95739500000000000000

noncomputable def ep1029 := @ep1025 8012125036819688389 95739500000000000000000 ep1026 121325148317849821993 450359962737049600 16899250073806920903 191479000000000000000000 (@ep1027 6051686392768373 2251799813685248 7000000001340353 1531832000000000000000 (ep1013 qz194) ep1023 rfl) (@ep1028 120114811039296147393 450359962737049600 8012125036819688389 95739500000000000000000 (ep1022 qz194) ep1020 rfl) rfl

noncomputable def ep1030 := @Enclosure.Complex.IsNear.of_eq qz185 (Complex.mk qz101 qz193) Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 (BSN.w_shift_mk qz154 Bool.false 128194 1000 2 qz155 rfl)

noncomputable abbrev qz491 := (ep1030 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 9000 4000) (Enclosure.sfrac Bool.false 256388 4000) Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 256388 4000)))

noncomputable abbrev qz195 := qz491

noncomputable def ep1031 := ep1008 (@ep1009 191479000000000000000000 (ep1024 rfl) (ep1029 rfl)) qz195 rfl rfl rfl rfl rfl rfl

noncomputable def ep1032 := @ep1006 16899250073806920903 191479000000000000000000 (ep1031 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz107 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep480 131072 1 524288 (ep482 rfl) (ep484 rfl) rfl rfl) (@ep485 1 0 1 (ep487 rfl) (ep489 rfl) rfl rfl))

noncomputable abbrev qz492 := (@HPow.hPow Complex Int Complex qz573 qz582 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz196 := qz492

noncomputable def ep1033 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz196)) Bool.false 3132357 68719476736 3 68719476736

noncomputable def ep1034 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz196) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1035 := @ep1034 0 1 0 1 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000 Bool.false 3132357 3132357 68719476736 3 68719476736 Bool.true 66924895543 66924895543 51539607552000 64097

noncomputable def ep1036 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz81 (@HMul.hMul Complex Complex Complex qz80 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz89 qz185 (@HSub.hSub Int Int Int qz402 qz91 (@HMul.hMul Int Int Int qz403 qz92 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1037 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110) qz196 Bool.false 3132357 68719476736 3 68719476736 Bool.true 66924895543 51539607552000 64097 51539607552000

noncomputable abbrev qz197 := (Complex.re qz492)

noncomputable abbrev qz198 := (Complex.im qz492)

noncomputable def ep1038 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz197) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz198) 3132357 68719476736 3 68719476736 0 1 0

noncomputable def ep1039 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz197 1 12 0 1 9397071 17179869184 9 17179869184 3132357

noncomputable def ep1040 := @Enclosure.Complex.IsNear.re_isNear qz196 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097 4294967296000

noncomputable abbrev qz493 := (@HPow.hPow Complex Nat Complex qz575 qz582 1)

noncomputable abbrev qz199 := (@Inv.inv Complex Complex.instInv qz493)

noncomputable def ep1041 := @Enclosure.Complex.IsNear.of_eq qz196 qz199 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097

noncomputable def ep1042 := @Enclosure.Complex.IsNear.of_parts qz199 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097

noncomputable abbrev qz200 := (Complex.re qz493)

noncomputable abbrev qz201 := qz493

noncomputable def ep1043 := @Enclosure.Real.IsNear.mulLit_ff qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201)) 9000 4000 0 1 1044119 4294967296 1 4294967296

noncomputable def ep1044 := @Enclosure.Complex.IsNear.re_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable def ep1045 := @Enclosure.Complex.IsNear.of_eq qz201 qz185 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0

noncomputable def ep1046 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201)) Bool.false 1044119 4294967296 1 4294967296 1044119 4294967296 1

noncomputable abbrev qz202 := (Complex.im qz493)

noncomputable def ep1047 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201) (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202)) Bool.false 4113487909 1000000 0 1

noncomputable def ep1048 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz200 qz200) (@HMul.hMul Real Real Real qz0 qz202 qz202) 81 16 0 1 4108425409 1000000

noncomputable def ep1049 := @Enclosure.Real.IsNear.mulLit_ff qz200 qz200 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1050 := @Enclosure.Real.IsNear.mulLit_ff qz202 qz202 256388 4000 0 1 256388 4000 0 1

noncomputable def ep1051 := @Enclosure.Complex.IsNear.im_isNear qz201 Bool.false 9000 4000 0 1 Bool.false 256388 4000 0 1

noncomputable abbrev qz203 := (ep1044 (@ep1045 1 (BSN.pow_one_c qz483) qz491))

noncomputable abbrev qz204 := (ep1051 (@ep1045 1 (BSN.pow_one_c qz483) qz491))

noncomputable def ep1052 := @ep1048 0 1 65815806544 4113487909 1000000 0 1 (@ep1049 81 16 0 1 qz203 qz203 rfl) (@ep1050 4108425409 1000000 0 1 qz204 qz204 rfl)

noncomputable def ep1053 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201) 4113487909 1000000 0 1 522059 522060 2147483648 (ep1047 (Enclosure.Complex.normSq_eq_mul_add_mul qz201) (ep1052 rfl rfl)) rfl

noncomputable def ep1054 := @Enclosure.Real.IsNear.of_eq (Complex.re qz199) (@HMul.hMul Real Real Real qz0 qz200 (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201))) Bool.false 9397071 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz201) (@ep1043 9397071 17179869184 9 17179869184 qz203 (@ep1046 4294967296 (ep1053 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1055 := @Enclosure.Real.IsNear.of_eq (Complex.im qz199) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201))) Bool.true 66924895543 4294967296000 64097 4294967296000 (Enclosure.Complex.inv_im_eq_mul qz201)

noncomputable def ep1056 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz202) (@Inv.inv Real Real.instInv (@DFunLike.coe qz116 Complex (fun (x : Complex) => Real) qz117 Complex.normSq qz201)) 256388 4000 0 1 1044119 4294967296 1

noncomputable def ep1057 := @ep1056 4294967296 66924895543 4294967296000 64097 4294967296000 (@Enclosure.Real.IsNear.neg qz202 Bool.false 256388 4000 0 1 qz204) (@ep1046 4294967296 (ep1053 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1058 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz198 0 1 0 1 66924895543 4294967296000 64097 4294967296000 0

noncomputable def ep1059 := @Enclosure.Complex.IsNear.im_isNear qz196 Bool.false 9397071 17179869184 9 17179869184 Bool.true 66924895543 4294967296000 64097 4294967296000

noncomputable abbrev qz205 := (@ep1041 4294967296000 (BSN.zpow_one_sub_two_mul qz483 1 1 rfl rfl) (@ep1042 4294967296000 ep1054 (ep1055 ep1057)))

noncomputable def ep1060 := @ep1038 1 3132357 3132357 68719476736 3 68719476736 (@ep1039 68719476736 3 68719476736 ep499 (ep1040 qz205) rfl) (@ep1058 1 0 1 ep519 (ep1059 qz205) rfl) rfl

noncomputable def ep1061 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz197) 66924895543 51539607552000 64097 51539607552000 0 1 0

noncomputable def ep1062 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz198 1 12 0 1 66924895543 4294967296000 64097 4294967296000 66924895543

noncomputable def ep1063 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 (@Rat.cast Complex Complex.instRatCast (bernoulli qz109)) qz110)) qz197 0 1 0 1 9397071 17179869184 9 17179869184 0

noncomputable def ep1064 := @ep1061 1 66924895543 66924895543 51539607552000 64097 51539607552000 (@ep1062 51539607552000 64097 51539607552000 ep499 (ep1059 qz205) rfl) (@ep1063 1 0 1 ep519 (ep1040 qz205) rfl) rfl

noncomputable def ep1065 := @ep1035 51539607552000 (@ep1036 0 1 0 1 (BSN.stirling_sum_base qz185) qz123) (ep1037 (ep1060 rfl) (ep1064 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1066 := @ep1003 1386867614814488694631 6755399441055744000 ep995 ep986 (ep1032 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1033 Bool.true 66924895543 51539607552000 64097 51539607552000 (BSN.stirling_sum_succ qz185 0 1 rfl) (ep1065 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1067 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz154 2) Bool.false 9368604620838629 1125899906842624 125000000574437 47869750000000000000 Bool.false 877693655090595 281474976710656

noncomputable abbrev qz206 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz484 qz411))

noncomputable def ep1068 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz154 1) qz206) Bool.false 9368604620838629 1125899906842624 125000000574437 47869750000000000000 Bool.false 877693655090595 281474976710656 1000000000191479 191479000000000000000

noncomputable def ep1069 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz154 1) qz206 Bool.false 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000 Bool.false

noncomputable def ep1070 := nat_lit 42192444279390356529193611689984

noncomputable def ep1071 := nat_lit 988195204502863070411127521280

noncomputable abbrev qz207 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz484 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1072 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz154 0) qz207) Bool.false 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1073 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz154 0) qz207 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz494 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz193))

noncomputable def ep1074 := @Enclosure.Complex.IsNear.of_eq qz207 qz494 Bool.false 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1075 := BSN.log_dyadic_bound 199806544 131271806544 1 0 1 1048576 382958 0 1 3192 131471613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 199806544) (BSN.artanhQ 131271806544) 0 0 rfl) rfl rfl rfl

noncomputable def ep1076 := @Enclosure.Real.IsNear.mulLit_ff qz102 (Real.log (Enclosure.sfrac Bool.false 65735806544 16000000)) 1 2 0 1 9368399536150245 1125899906842624 125000000574437 47869750000000000000 9368399536150245 2251799813685248 125000000574437 95739500000000000000 qz406 (BSN.isNear_log_sfrac 65735806544 16000000 9368399536150245 1125899906842624 125000000574437 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65735806544) qz407)) Bool.false 314351325184584937635840 37778931862957161709568 1000000004595496 382958000000000000000 9368399536150245 1125899906842624 125000000574437 47869750000000000000 (BSN.log_rat_reduce_isNear 65735806544 16000000 12 131471613088 131072000000 3192 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep1075 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1077 := BSN.arctan_dyadic_bound_f 1000 256388 1 0 1048576 382958 0 1 1 0 1 1 4089 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz495 := (@Nat.cast Real Real.instNatCast 256388)

noncomputable def ep1078 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz495)) 884279719003555 562949953421312 1 2000000000000000 4089 1048576 1 382958 924932588274331942912 882084453844387 562949953421312 1000000000191479 382958000000000000000 qz104 (ep1077 rfl) rfl rfl

noncomputable abbrev qz208 := (@HAdd.hAdd Complex Complex Complex qz272 qz484 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz496 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz193)

noncomputable def ep1079 := @ep1073 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000 Bool.false 9368399536150245 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 882084453844387 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz154 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz154) qz123) (ep1074 (@congrArg Complex Complex qz208 qz496 Complex.log (BSN.w_shift_mk qz154 Bool.false 128194 1000 0 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz494 Bool.false 9368399536150245 2251799813685248 125000000574437 95739500000000000000 Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz494) (@HMul.hMul Real Real Real qz0 qz102 (Real.log (Enclosure.sfrac Bool.false 65735806544 16000000))) Bool.false 9368399536150245 2251799813685248 125000000574437 95739500000000000000 (Enclosure.clog_re_eq 1000 256388 4000 65735806544 16000000 rfl rfl rfl) (ep1076 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz494) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz495 qz417)) Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 1000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz495 qz417)) (@HSub.hSub Real Real Real qz393 qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz417 qz495))) Bool.false 882084453844387 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 256388 1000 rfl rfl) ep1078)))) rfl rfl

noncomputable abbrev qz497 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz193))

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq qz206 qz497 Bool.false 9368809705527013 2251799813685248 125000000574437 95739500000000000000 Bool.false 873302856336803 562949953421312 1000000000191479 382958000000000000000

noncomputable def ep1081 := BSN.log_dyadic_bound 223806544 131295806544 1 0 1 1048576 382958 0 1 3574 131519613088 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 223806544) (BSN.artanhQ 131295806544) 0 0 rfl) rfl rfl rfl

noncomputable def ep1082 := @Enclosure.Real.IsNear.mulLit_ff qz102 (Real.log (Enclosure.sfrac Bool.false 65759806544 16000000)) 1 2 0 1 9368809705527013 1125899906842624 125000000574437 47869750000000000000 9368809705527013 2251799813685248 125000000574437 95739500000000000000 qz406 (BSN.isNear_log_sfrac 65759806544 16000000 9368809705527013 1125899906842624 125000000574437 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 65759806544) qz407)) Bool.false 314365088185046181871616 37778931862957161709568 1000000004595496 382958000000000000000 9368809705527013 1125899906842624 125000000574437 47869750000000000000 (BSN.log_rat_reduce_isNear 65759806544 16000000 12 131519613088 131072000000 3574 1048576 24973259072661432 36028797018963968 382958 1000000000000000 rfl rfl rfl rfl (ep1081 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1083 := BSN.arctan_dyadic_bound_f 5000 256388 1 0 1048576 382958 0 1 1 0 1 1 20446 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 256388) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 256388) 0 0 rfl) rfl rfl rfl

noncomputable def ep1084 := @Enclosure.Real.IsNear.subLit_ff_p qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz495)) 884279719003555 562949953421312 1 2000000000000000 20446 1048576 1 382958 915724415886219542528 873302856336803 562949953421312 1000000000191479 382958000000000000000 qz104 (ep1083 rfl) rfl rfl

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz272 qz484 qz411)

noncomputable abbrev qz498 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz193)

noncomputable def ep1085 := @ep1069 9368809705527013 2251799813685248 125000000574437 95739500000000000000 Bool.false 873302856336803 562949953421312 1000000000191479 382958000000000000000 Bool.false ep1070 9368604620838629 1125899906842624 125000000574437 47869750000000000000 Bool.false ep1071 877693655090595 281474976710656 1000000000191479 191479000000000000000 (ep1072 (BSN.log_sum_c_succ qz154 0 1 rfl) (ep1079 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1080 (@congrArg Complex Complex qz209 qz498 Complex.log (BSN.w_shift_mk qz154 Bool.false 128194 1000 1 qz155 rfl)) (@Enclosure.Complex.IsNear.of_parts qz497 Bool.false 9368809705527013 2251799813685248 125000000574437 95739500000000000000 Bool.false 873302856336803 562949953421312 1000000000191479 382958000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz497) (@HMul.hMul Real Real Real qz0 qz102 (Real.log (Enclosure.sfrac Bool.false 65759806544 16000000))) Bool.false 9368809705527013 2251799813685248 125000000574437 95739500000000000000 (Enclosure.clog_re_eq 5000 256388 4000 65759806544 16000000 rfl rfl rfl) (ep1082 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz497) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz495 qz421)) Bool.false 873302856336803 562949953421312 1000000000191479 382958000000000000000 (Enclosure.clog_im_eq 5000 256388 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz495 qz421)) (@HSub.hSub Real Real Real qz393 qz103 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz421 qz495))) Bool.false 873302856336803 562949953421312 1000000000191479 382958000000000000000 (BSN.arctan_recip 256388 5000 rfl rfl) ep1084)))) rfl rfl

noncomputable def ep1086 := @ep996 ep986 Bool.false 9368604620838629 1125899906842624 125000000574437 47869750000000000000 Bool.false 877693655090595 281474976710656 1000000000191479 191479000000000000000 Bool.true ep997 113495775242190786391 1125899906842624000 ep991 ep992 Bool.false ep998 1365802967092314414631 6755399441055744000 ep988 ep986 (@ep999 1125899906842624000 ep994 ep992 Bool.false 1386867614814488694631 6755399441055744000 ep995 ep986 (BSN.logGammaStirling_unfold 1 qz185) (ep1066 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1067 1000000000191479 191479000000000000000 (BSN.log_sum_c_eq qz154 2) (ep1068 (BSN.log_sum_c_succ qz154 1 2 rfl) (ep1085 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz210 := (@HDiv.hDiv Real Real Real qz270 qz443 (2 : Real))

noncomputable def ep1087 := @Enclosure.Real.IsNear.mulLit_ff qz210 (Real.log Real.pi) 128194 2000 0 1 75021 65536 1 262144 4808621037 65536000 64097 262144000 (@Enclosure.Real.IsNear.of_eq qz210 (Enclosure.sfrac Bool.false 128194 2000) Bool.false 128194 2000 0 1 (BSN.t_half_eq qz154 Bool.false 128194 1000 qz155) (Enclosure.Real.IsNear.const Bool.false 128194 2000)) EMRow42.d5 rfl

noncomputable def ep1088 := @ep989 64097 262144000 ep990 870134084865771871783 6755399441055744000 ep985 ep986 (@ep993 ep988 ep986 (ep1086 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1087 rfl rfl

noncomputable def ep1089 := BSN.cos_dyadic_bound_f 903185 2147483648 1 0 1048576 383332 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 903185) qz290 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 903185) qz291 0 0 rfl) rfl rfl

noncomputable def ep1090 := @ep984 1048576 Bool.true 1048575 1048576 1 191479 (@ep987 67531293 524288 355 1048576 ep1088 rfl) (Enclosure.sfrac_false_div 67531293 524288) (BSN.cos_reduce2 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31778007611883913216) qz33) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 20 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 67531293 524288 226375608064910080 72057594037927936 20 31778007611883913216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 31778007611883913216 75557863725914323419136 903185 2147483648 383332 382958 (ep1089 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1091 := nat_lit 4204190290898219444828887

noncomputable def ep1092 := nat_lit 54207962742271254724608000

noncomputable def ep1093 := nat_lit 711353706645217845535973898013

noncomputable def ep1094 := nat_lit 134935924473055648584371798016000

noncomputable abbrev qz499 := (@HPow.hPow Complex Complex Complex qz539 qz576 qz580)

noncomputable abbrev qz211 := qz499

noncomputable abbrev qz212 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz398 qz424 (@HSub.hSub Complex Complex Complex qz390 qz440 (1 : Complex))) qz397)

noncomputable def ep1095 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz151 1 26) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz152) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) Bool.false ep979 ep980 ep981

noncomputable def ep1096 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz152) (@HMul.hMul Complex Complex Complex qz80 qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) Bool.false 1074835243965 549755813888 545028284929737 105266693487460352

noncomputable def ep1097 := nat_lit 31802856752261515504341547

noncomputable def ep1098 := nat_lit 6371340720331184633680566637

noncomputable def ep1099 := nat_lit 3049657553382200153019113

noncomputable def ep1100 := nat_lit 12711648848128821474332778013

noncomputable def ep1101 := nat_lit 361236282185272898345139922729921675264

noncomputable def ep1102 := nat_lit 2311278055112778109461932285578182656

noncomputable def ep1103 := @ep1096 Bool.false 73565668653 549755813888 136256781955535 26316673371865088 Bool.true ep1097 ep980 ep1098 ep982 Bool.true ep1099 ep1092 ep1100 ep1094 Bool.false ep1101 ep979 ep980 ep981 ep982 Bool.false ep1102 ep1091 ep1092

noncomputable def ep1104 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 26, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz152) (BSN.headSumC qz151 26) Bool.false 1074835243965 549755813888 545028284929737 105266693487460352 Bool.false 73565668653 549755813888 136256781955535

noncomputable abbrev qz500 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz152)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz151 26) (@HAdd.hAdd Complex Complex Complex qz4 qz172 qz500) Bool.false 1074835243965 549755813888 545028284929737 105266693487460352 Bool.false 73565668653 549755813888 136256781955535 26316673371865088

noncomputable def ep1106 := @Enclosure.Complex.IsNear.addLitP qz172 qz500 Bool.false 2251041895485 1099511627776 1061514294545783 210533386974920704 Bool.true 12002851551 274877906944 530713181492483 105266693487460352 Bool.true

noncomputable def ep1107 := nat_lit 2363587697365942460743680

noncomputable abbrev qz213 := (@HMul.hMul Real Real Real qz267 qz443 qz577)

noncomputable def ep1108 := @Enclosure.Complex.IsNear.of_eq qz500 (Complex.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz213)))) Bool.true 101371407555 1099511627776 28542275313691 210533386974920704 Bool.false 97571371755 549755813888 14313946329657 105266693487460352 (BSN.cpow_neg_s_mk qz154 128194 1000 25 qz155 rfl)

noncomputable def ep1109 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz577 128194 1000 0 1 3624129903009015 1125899906842624 250000000191479 47869750000000000000 46459170878633766891 112589990684262400 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz428) Bool.false 60802810194841294602240 18889465931478580854784 1000000000765916 191479000000000000000 3624129903009015 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep576 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1110 := nat_lit 1080227740472095641005039540465771314400428278322436943729637874513288674348161

noncomputable def ep1111 := nat_lit 912513126369180661048312710394999918952104472250367913066604377797260414081

noncomputable def ep1112 := nat_lit 3238858195163548561693021995976523943363380626022810095362780414784271502216321

noncomputable def ep1113 := BSN.cos_dyadic_bound_f 2344390161 2147483648 3 2 1048576 383332 ep1110 ep64 ep1111 ep1112 ep66 ep1111 483377 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2344390161) qz290 0 2 ep1110 ep64 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2344390161) qz291 0 2 ep1112 ep66 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz501 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 216342373) qz32)

noncomputable def ep1114 := @Enclosure.Real.IsNear.cos_image qz213 qz501 Bool.false 216342373 524288 703 1048576 Bool.true 483377 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 46459170878633766891 112589990684262400 16024250012273229463 23934875000000000000000 216342373 524288 703 1048576 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 216342373 524288) (BSN.cos_reduce2 qz501 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82485895774442436427776) qz33) 226375608064910080 72057594037927936 Bool.false 483377 1048576 65 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 216342373 524288 226375608064910080 72057594037927936 65 82485895774442436427776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 483377 1048576 82485895774442436427776 75557863725914323419136 2344390161 2147483648 383332 382958 (ep1113 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1115 := nat_lit 1943679922348676809280232522670072365985609217402586204382894890621681805495425

noncomputable def ep1116 := nat_lit 5089112870613365350854149814985740482474482638337415653905474020730828211817601

noncomputable def ep1117 := BSN.sin_dyadic_bound_f 2344390161 2147483648 3 2 1048576 383332 ep1115 ep57 ep1111 ep1116 ep60 ep1111 930514 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2344390161) qz286 0 2 ep1115 ep57 ep1111 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2344390161) qz287 0 2 ep1116 ep60 ep1111 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1118 := @Enclosure.Real.IsNear.sin_image qz213 qz501 Bool.false 216342373 524288 703 1048576 Bool.true 930514 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz213 Bool.false 46459170878633766891 112589990684262400 16024250012273229463 23934875000000000000000 216342373 524288 703 1048576 (ep1109 rfl) rfl) (Enclosure.sfrac_false_div 216342373 524288) (BSN.sin_reduce2 qz501 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82485895774442436427776) qz33) 226375608064910080 72057594037927936 Bool.false 930514 1048576 65 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 216342373 524288 226375608064910080 72057594037927936 65 82485895774442436427776 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 930514 1048576 82485895774442436427776 75557863725914323419136 2344390161 2147483648 383332 382958 (ep1117 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1119 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz134 (Real.cos qz213)) (@HMul.hMul Real Real Real qz0 qz134 (@Neg.neg Real Real.instNeg (Real.sin qz213))) Bool.true 101371407555 1099511627776 28542275313691 210533386974920704 Bool.false 97571371755 549755813888 14313946329657 105266693487460352 (@Enclosure.Real.IsNear.mulLit_ft qz134 (Real.cos qz213) 209715 1048576 1 1048576 483377 1048576 135658313 200780283904 101371407555 1099511627776 28542275313691 210533386974920704 qz430 (@Enclosure.Real.IsNear.recentre' (Real.cos qz213) Bool.true 483377 1048576 135658313 200780283904 483377 1048576 135658313 200780283904 (ep1114 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz134 (@Neg.neg Real Real.instNeg (Real.sin qz213)) 209715 1048576 1 1048576 465257 524288 135658313 200780283904 97571371755 549755813888 14313946329657 105266693487460352 qz430 (@Enclosure.Real.IsNear.neg (Real.sin qz213) Bool.true 465257 524288 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' (Real.sin qz213) Bool.true 930514 1048576 135658313 200780283904 465257 524288 135658313 200780283904 (ep1118 rfl rfl) rfl)) rfl)

noncomputable def ep1120 := @ep1106 101371407555 1099511627776 28542275313691 210533386974920704 Bool.false 97571371755 549755813888 14313946329657 105266693487460352 Bool.false ep1107 1074835243965 549755813888 545028284929737 105266693487460352 Bool.false 20221577022272471826432 73565668653 549755813888 136256781955535 26316673371865088 EMRow42.d14 (ep1108 ep1119) rfl rfl

noncomputable def ep1121 := @Enclosure.Complex.IsNear.mul qz211 (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.true ep1097 ep980 ep1098 ep982 Bool.true

noncomputable def ep1122 := nat_lit 12024170775241029688339959

noncomputable abbrev qz214 := (Complex.re qz499)

noncomputable abbrev qz215 := (Complex.im qz499)

noncomputable def ep1123 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) 91052922305289694767367 939604687532701748559872 ep1122

noncomputable def ep1124 := nat_lit 179914565964074198112495730688

noncomputable def ep1125 := nat_lit 176175878912381577854976000

noncomputable def ep1126 := nat_lit 35813013069534586549097731

noncomputable def ep1127 := nat_lit 1297460812240919697926651904000

noncomputable def ep1128 := nat_lit 14941056640677977609365663843962395942185433300992

noncomputable def ep1129 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 212752284153 1099511627776 28095416739081 210533386974920704 1283928715517

noncomputable abbrev qz502 := (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) qz581 (Real.log (Enclosure.sfrac Bool.false 26 1)))

noncomputable abbrev qz216 := (Real.cos qz502)

noncomputable abbrev qz217 := (Real.sin qz502)

noncomputable abbrev qz585 := (@Neg.neg Real Real.instNeg qz217)

noncomputable def ep1130 := @Enclosure.Complex.IsNear.of_eq qz211 (Complex.mk (@HMul.hMul Real Real Real qz0 qz138 qz216) (@HMul.hMul Real Real Real qz0 qz138 qz585)) Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (BSN.cpow_neg_s_mk qz154 128194 1000 26 qz155 rfl)

noncomputable def ep1131 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz141 128194 1000 0 1 3668288609262839 1125899906842624 250000000191479 47869750000000000000 235126294987920191383 562949953421312000 16024250012273229463 23934875000000000000000 qz156 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 250000000191479 47869750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz435 Bool.false 61543670347942250676224 18889465931478580854784 1000000000765916 191479000000000000000 3668288609262839 1125899906842624 250000000191479 47869750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 191479 1000000000000000 rfl rfl rfl rfl (ep598 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1132 := nat_lit 5370017629260295697045437794770550448779050307785975118866776980647752790957665

noncomputable def ep1133 := nat_lit 6953819765233284912750821257372628292032891180203858934555630820226366692961

noncomputable def ep1134 := nat_lit 14053073320823730078593597656649028824805649934671509539709421070844700335005281

noncomputable def ep1135 := BSN.sin_dyadic_bound_f 3021884971 2147483648 3 2 1048576 383332 ep1132 ep57 ep1133 ep1134 ep60 ep1133 1034571 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3021884971) qz286 0 2 ep1132 ep57 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3021884971) qz287 0 2 ep1134 ep60 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz218 := qz502

noncomputable abbrev qz503 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 109489213) qz555)

noncomputable def ep1136 := @Enclosure.Real.IsNear.cos_image qz218 qz503 Bool.false 109489213 262144 703 1048576 Bool.true 1034571 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 235126294987920191383 562949953421312000 16024250012273229463 23934875000000000000000 109489213 262144 703 1048576 (ep1131 rfl) rfl) (Enclosure.sfrac_false_div 109489213 262144) (BSN.cos_reduce1 qz503 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53161562621979903655936) qz336) 226375608064910080 72057594037927936 Bool.false 1034571 1048576 66 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 109489213 262144 226375608064910080 72057594037927936 66 53161562621979903655936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1034571 1048576 53161562621979903655936 37778931862957161709568 3021884971 2147483648 383332 382958 (ep1135 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1137 := nat_lit 2986433713929156847208688028764693639673709233738965670008011936279963269062241

noncomputable def ep1138 := nat_lit 8945393502257003971800562443779335662437061918856489292154924547199437073800801

noncomputable def ep1139 := BSN.cos_dyadic_bound_f 3021884971 2147483648 3 2 1048576 383332 ep1137 ep64 ep1133 ep1138 ep66 ep1133 170804 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3021884971) qz290 0 2 ep1137 ep64 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3021884971) qz291 0 2 ep1138 ep66 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1140 := @Enclosure.Real.IsNear.sin_image qz218 qz503 Bool.false 109489213 262144 703 1048576 Bool.false 170804 1048576 1 191479 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 235126294987920191383 562949953421312000 16024250012273229463 23934875000000000000000 109489213 262144 703 1048576 (ep1131 rfl) rfl) (Enclosure.sfrac_false_div 109489213 262144) (BSN.sin_reduce1 qz503 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 53161562621979903655936) qz336) 226375608064910080 72057594037927936 Bool.false 170804 1048576 66 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q1 109489213 262144 226375608064910080 72057594037927936 66 53161562621979903655936 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 170804 1048576 53161562621979903655936 37778931862957161709568 3021884971 2147483648 383332 382958 (ep1139 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1141 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz138 qz216) (@HMul.hMul Real Real Real qz0 qz138 qz585) Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (@Enclosure.Real.IsNear.mulLit_ft qz138 qz216 205643 1048576 1 1048576 1034571 1048576 135658313 200780283904 212752284153 1099511627776 28095416739081 210533386974920704 qz437 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 1034571 1048576 135658313 200780283904 1034571 1048576 135658313 200780283904 (ep1136 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz138 qz585 205643 1048576 1 1048576 42701 262144 135658313 200780283904 8781161743 274877906944 3491252937211 26316673371865088 qz437 (@Enclosure.Real.IsNear.neg qz217 Bool.false 42701 262144 135658313 200780283904 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 170804 1048576 135658313 200780283904 42701 262144 135658313 200780283904 (ep1140 rfl rfl) rfl)) rfl)

noncomputable def ep1142 := @ep1129 2563696455216 0 1 91052922305289694767367 939604687532701748559872 ep1122 ep1124 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (ep1130 ep1141))

noncomputable def ep1143 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1283928715517 2563696455216 0 1 Bool.false

noncomputable def ep1144 := @Enclosure.Complex.IsNear.addLitP qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) Bool.false 4101987909 8216975818 0 1 Bool.true 833261000

noncomputable def ep1145 := @ep1144 4108487909 0 1 Bool.false 1 624 0 1 Bool.false 64097 156000 0 1 Bool.false 2567857431034 1283928715517 2563696455216 0 1 Bool.false 133353033503173 133353033503173 640924113804000 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz398 qz424 (@HSub.hSub Complex Complex Complex qz390 qz440 (1 : Complex)))

noncomputable def ep1146 := @Enclosure.Complex.IsNear.addLitP qz219 qz107 Bool.true 52000000 65735806544 0 1 Bool.true 13332176000 65735806544 0 1

noncomputable def ep1147 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 52000000 65735806544) (Enclosure.sfrac Bool.true 13332176000 65735806544)) Bool.true 52000000 65735806544 0 1 Bool.true 13332176000 65735806544 0 1

noncomputable def ep1148 := @ep1146 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 65631806544 4101987909 8216975818 0 1 Bool.true 13332176000 833261000 4108487909 0 1 (ep1147 (BSN.N_div_s_sub_one_mk qz154 128194 1000 26 qz155 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 52000000 65735806544) (Enclosure.sfrac Bool.true 13332176000 65735806544) Bool.true 52000000 65735806544 0 1 Bool.true 13332176000 65735806544 0 1 (Enclosure.Real.IsNear.const Bool.true 52000000 65735806544) (Enclosure.Real.IsNear.const Bool.true 13332176000 65735806544))) qz108 rfl

noncomputable def ep1149 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz145)) Bool.false 1 624 0 1

noncomputable def ep1150 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz145) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1151 := @ep1150 0 1 0 1 Bool.false 1 624 0 1 Bool.false 64097 156000 0 1 Bool.false 1 1 624 0 1 Bool.false 64097 64097 156000 0

noncomputable def ep1152 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1153 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz145 Bool.false 1 624 0 1 Bool.false 64097 156000 0 1

noncomputable def ep1154 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) 1 624 0 1 0 1 0

noncomputable def ep1155 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 1 24 0 1 1 26 0 1 1

noncomputable def ep1156 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1157 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1158 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) qz151 Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 (BSN.ascPochhammer_one_eval qz151)

noncomputable def ep1159 := ep1158 (@Enclosure.Complex.IsNear.of_eq qz151 (Complex.mk qz102 qz154) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_crit_mk qz154 Bool.false 128194 1000 qz155) (@Enclosure.Complex.IsNear.mk qz102 qz154 Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 qz406 qz156))

noncomputable def ep1160 := @ep1157 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1161 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 128194 1000 0 1 0 1 0

noncomputable def ep1162 := @ep1161 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1163 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) 64097 6000 0 1 0 1 0 1 64097

noncomputable def ep1164 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 128194 1000 0 1 64097 6000 0

noncomputable def ep1165 := @ep1164 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1166 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1167 := @ep1166 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep626) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 (@ep1156 1 24 0 1 (ep1160 rfl) (ep1162 rfl) rfl rfl) (@ep1163 64097 6000 0 1 (ep1165 rfl) (ep1167 rfl) rfl rfl)

noncomputable def ep1169 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 ep1168

noncomputable def ep1170 := @ep1155 624 0 1 ep1169 qz148

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 64097 6000 0 1 0 1 0 1 0

noncomputable def ep1172 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 64097 6000 0 1 ep1168

noncomputable def ep1173 := @ep1171 1 0 1 ep1172 qz149

noncomputable def ep1174 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146) 0 1 0 1 64097 156000 0

noncomputable def ep1175 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz147 1 24 0 1 0 1 0 1 0

noncomputable def ep1176 := @ep1175 1 0 1 ep1169 qz149

noncomputable def ep1177 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz109)) ↑qz144) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)))) qz146 64097 6000 0 1 1 26 0 1 64097

noncomputable def ep1178 := @ep1177 156000 0 1 ep1172 qz148

noncomputable def ep1179 := @ep1151 1 (@ep1152 0 1 0 1 (BSN.bern_sum_base qz151 26) qz123) (ep1153 (@ep1154 1 1 1 624 0 1 (ep1170 rfl) (ep1173 rfl) rfl rfl) (@ep1174 1 64097 64097 156000 0 1 (ep1176 rfl) (ep1178 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1180 := ep1145 (ep1148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1149 Bool.false 64097 156000 0 1 (BSN.bern_sum_succ qz151 26 0 1 1 rfl rfl) (ep1179 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1181 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 8781161743 274877906944 3491252937211 26316673371865088 133353033503173

noncomputable def ep1182 := @ep1181 640924113804000 0 1 1170994556111060016710539 ep1125 ep1126 ep1127 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (ep1130 ep1141))

noncomputable def ep1183 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))) Bool.false 1283928715517 2563696455216 0 1 Bool.false

noncomputable def ep1184 := nat_lit 9457054158843863707705823

noncomputable def ep1185 := nat_lit 234901171883175437139968000

noncomputable def ep1186 := nat_lit 1248869683230758703175534671

noncomputable def ep1187 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1))))))) ep1184 ep1185 ep1186

noncomputable def ep1188 := nat_lit 44978641491018549528123932672000

noncomputable def ep1189 := nat_lit 5189843248963678791706607616

noncomputable def ep1190 := nat_lit 9312785730714134101369283693804182193887082708992

noncomputable def ep1191 := @Enclosure.Real.IsNear.mulLit_tf qz214 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 212752284153 1099511627776 28095416739081 210533386974920704 133353033503173

noncomputable def ep1192 := @ep1191 640924113804000 0 1 ep1184 ep1185 ep1186 ep1188 (@Enclosure.Complex.IsNear.re_isNear qz211 Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (ep1130 ep1141))

noncomputable def ep1193 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz212 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz88 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz88 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz132 qz133 (@HSub.hSub Nat Nat Nat qz131 (@HMul.hMul Nat Nat Nat qz88 2 k) 1)))))) 8781161743 274877906944 3491252937211 26316673371865088 1283928715517

noncomputable def ep1194 := @ep1193 2563696455216 0 1 11274385717437010866131 704703515649526311419904 344809223016790206338699 ep1189 (@Enclosure.Complex.IsNear.im_isNear qz211 Bool.true 212752284153 1099511627776 28095416739081 210533386974920704 Bool.true 8781161743 274877906944 3491252937211 26316673371865088 (ep1130 ep1141))

noncomputable abbrev qz504 := (ep1180 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1195 := @ep1121 ep1099 ep1092 ep1100 ep1094 (@ep1123 ep1124 1170994556111060016710539 ep1125 ep1126 ep1127 ep1128 ep1097 ep980 ep1098 ep982 (ep1142 (@ep1143 133353033503173 640924113804000 0 1 qz504) rfl) (ep1182 (@ep1183 133353033503173 640924113804000 0 1 qz504) rfl) rfl rfl) (@ep1187 ep1188 11274385717437010866131 704703515649526311419904 344809223016790206338699 ep1189 ep1190 ep1099 ep1092 ep1100 ep1094 (ep1192 (@ep1183 133353033503173 640924113804000 0 1 qz504) rfl) (ep1194 (@ep1143 133353033503173 640924113804000 0 1 qz504) rfl) rfl rfl)

noncomputable def ep1196 := @ep1103 ep1093 ep1094 (@ep1104 26316673371865088 (BSN.head_sum_c_eq qz151 26) (ep1105 (BSN.head_sum_c_succ qz151 25 26 rfl rfl) (ep1120 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1195 rfl rfl rfl

noncomputable def ep1197 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz151 1 26) Bool.false ep979 ep980 ep981 ep982 Bool.false ep1091 ep1092 ep1093 ep1094 (@ep1095 ep982 Bool.false ep1091 ep1092 ep1093 ep1094 (BSN.zetaApproximant_eq_folded' qz151 1 26 rfl) (ep1196 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) (Complex.im (zetaApproximant qz151 1 26)) 441 1048576 69023621

noncomputable def ep1199 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183)) Bool.true 441 1048576 69023621

noncomputable def ep1200 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) qz485 Bool.false 67531293 524288 355

noncomputable def ep1201 := BSN.sin_dyadic_bound_f 903185 2147483648 1 0 1048576 383332 0 1 1 0 1 1 441 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 903185) qz286 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 903185) qz287 0 0 rfl) rfl rfl

noncomputable def ep1202 := @ep1200 1048576 Bool.true 441 1048576 1 191479 (@ep987 67531293 524288 355 1048576 ep1088 rfl) (Enclosure.sfrac_false_div 67531293 524288) (BSN.sin_reduce2 qz485 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31778007611883913216) qz33) 226375608064910080 72057594037927936 Bool.false 441 1048576 20 1000000000000000 382958 191479 (BSN.sin_reduce_arg_pos_rat_q2 67531293 524288 226375608064910080 72057594037927936 20 31778007611883913216 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 441 1048576 31778007611883913216 75557863725914323419136 903185 2147483648 383332 382958 (ep1201 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1203 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz151 1 26) Bool.false ep979 ep980 ep981 ep982 Bool.false ep1091 ep1092 ep1093 ep1094 (@ep1095 ep982 Bool.false ep1091 ep1092 ep1093 ep1094 (BSN.zetaApproximant_eq_folded' qz151 1 26 rfl) (ep1196 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow42.d15 : Enclosure.Real.IsNear (hardyZApproximantEM 1 26 qz154) Bool.true ep963 ep964 ep965 ep966 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 26 qz154) ep967 Bool.true ep963 ep964 ep965 ep966 (@Eq.refl Real ep967) (@ep968 Bool.true ep963 ep964 ep965 ep966 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz393 (Complex.im (@HSub.hSub Complex Complex Complex qz81 qz181 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz182 (@Nat.cast Complex Complex.instNatCast j))))) qz183) (zetaApproximant qz151 1 26)) (@ep970 ep971 ep972 ep973 ep974 ep975 ep976 ep966 ep977 ep963 ep964 ep965 ep966 (@ep978 200780283904 ep979 ep980 ep981 ep982 ep969 ep971 ep972 ep973 (@ep983 200780283904 1048575 1048576 69023621 200780283904 (ep1090 rfl rfl) rfl) ep1197 rfl) (@ep1198 200780283904 ep1091 ep1092 ep1093 ep1094 ep974 ep975 ep976 ep966 (@ep1199 200780283904 441 1048576 69023621 200780283904 (ep1202 rfl rfl) rfl) ep1203 rfl) rfl rfl))

theorem EMRow42.d16 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow42.d17 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow42.d18 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow42.d19 : @Eq Nat (Nat.pow 26 (Nat.succ (Nat.mul 2 3))) 8031810176 := @Eq.refl Nat 8031810176

noncomputable abbrev qz586 := (@HAdd.hAdd Complex Complex Complex qz592 qz591 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz505 := qz586

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz505) (@HAdd.hAdd Real Real Real qz415 (Complex.re qz271) qz294))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz506 := (@HPow.hPow Complex Complex Complex qz539 qz576 (@HSub.hSub Complex Complex Complex qz568 qz540 qz541))

noncomputable abbrev qz223 := qz506

noncomputable def ep1204 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 2335800901 34359738368 25219655 309237645312 322959730527302135 288230376151711744 402955615051

noncomputable def ep1205 := nat_lit 11770060616628621243815297024

noncomputable def ep1206 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26)) 26561 1769472 1 1769472 2374407 524288 2759 524288 2335800901 34359738368

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz587 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz507 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz587 qz224 2))

noncomputable def ep1207 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz507 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1208 := nat_lit 781950621441006189802102638025

noncomputable def ep1209 := nat_lit 19807040628566084398385987584

noncomputable def ep1210 := nat_lit 26986075409044041160201671

noncomputable def ep1211 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz508 := (@HPow.hPow Real Nat Real qz587 qz224 1)

noncomputable def ep1212 := @Enclosure.Real.IsNear.mulLit_ff qz508 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1208 ep1209 ep1210 ep1211

noncomputable def ep1213 := ep1212 (@Enclosure.Real.IsNear.of_eq qz508 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz509 := (@HPow.hPow Real Nat Real qz587 qz224 2)

noncomputable def ep1214 := @Enclosure.Real.IsNear.inv_image qz509 ep1208 ep1209 ep1210 ep1211 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz509 (@HMul.hMul Real Real Real qz0 qz508 qz224) Bool.false ep1208 ep1209 ep1210 ep1211 (BSN.pow_succ_r qz224 1 2 rfl) ep1213) rfl rfl rfl

noncomputable def ep1215 := ep1207 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz507 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1214 rfl rfl rfl) rfl)

noncomputable def ep1216 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26)) (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))))) Bool.false 2374407 524288 2759 524288

noncomputable def ep1217 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))))) Bool.false 4748814 1048576 5518 1048576

noncomputable def ep1218 := nat_lit 6141457344220128073132750821179923609410217

noncomputable def ep1219 := nat_lit 299433415525485061094658040602103382016000

noncomputable def ep1220 := nat_lit 554724085109276043110324225233027915872121128220570503145159

noncomputable def ep1221 := nat_lit 11639189709466120863359995598428347211344459286433664860160000

noncomputable def ep1222 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26)))) ep1218 ep1219 ep1220 ep1221 2371648 2377166

noncomputable def ep1223 := nat_lit 39059626593789011241679731769853862770257911636046129

noncomputable def ep1224 := nat_lit 1904722429065877081757371174987349244963780034560000

noncomputable def ep1225 := nat_lit 218895202952240764321998261624114807290059389647981777004289

noncomputable def ep1226 := nat_lit 4655675883786448345343998239371338884537783714573465944064000

noncomputable def ep1227 := nat_lit 747393226558437004515763352414647360754073137649

noncomputable def ep1228 := nat_lit 211635825451764120195263463887483249440420003840000

noncomputable def ep1229 := nat_lit 4990718485782754870219047448493931764648436067077373756291

noncomputable def ep1230 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26))) ep1223 ep1224 ep1225 ep1226 ep1227 ep1228 ep1229

noncomputable def ep1231 := nat_lit 7759459806310747242239997065618898140896306190955776573440000

noncomputable def ep1232 := nat_lit 8267839892656172882892148179347541121441968060747643548474876431117817186918775780814557937454284800000

noncomputable def ep1233 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 26)) (Complex.re (zetaApproximant qz5 1 26)) ep423 ep424 ep425 ep426 ep423 ep424 ep425 ep426 ep1223

noncomputable def ep1234 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 26)) (Complex.im (zetaApproximant qz5 1 26)) 864519072408721937570343 ep558 ep559 ep560 864519072408721937570343 ep558 ep559 ep560 ep1227

noncomputable def ep1235 := @ep1204 2017612633061982208 ep1205 342553848651837943 288230376151711744 1484531198367139 18158513697557839872 (@ep1206 25219655 309237645312 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz507) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow42.d16 EMRow42.d17 rfl) (ep1215 rfl)) (ep1216 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 26)) (@ep1217 2374407 524288 2759 524288 (@ep1222 524288 (@ep1230 ep1231 ep1232 ep1218 ep1219 ep1220 ep1221 (@ep1233 ep1224 ep1225 ep1226 ep664 ep664 rfl) (@ep1234 ep1228 ep1229 ep1231 ep670 ep670 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz505)

noncomputable abbrev qz588 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1236 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz588) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 322959730527302135 288230376151711744 402955615051 2017612633061982208 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz13 3)

noncomputable def ep1237 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz588) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 18897371 524288 1 3670016 17090193685 549755813888 2917 549755813888

noncomputable def ep1238 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz588 132281597 1048576 1 1048576 2 7 0 1 18897371 524288

noncomputable abbrev qz510 := (Complex.re qz586)

noncomputable abbrev qz511 := (Complex.im qz586)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz267 qz510 qz510) (@HMul.hMul Real Real Real qz267 qz511 qz511))

noncomputable abbrev qz227 := qz505

noncomputable def ep1239 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 132281597 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1240 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 132281597 1048576 1 1048576 132281597

noncomputable def ep1241 := @Enclosure.Real.IsNear.sqrt_image qz226 636588841 40000 0 1 66140798 66140799 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz510 qz510)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz511 qz511)

noncomputable def ep1242 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 636098841 40000 0 1

noncomputable abbrev qz230 := qz510

noncomputable def ep1243 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz512 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1244 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz512 qz13) Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 126105 1000 3 qz14)

noncomputable abbrev qz513 := (ep1244 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz13 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1245 := @ep1243 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz513)

noncomputable def ep1246 := ep1245 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz513)

noncomputable abbrev qz231 := qz511

noncomputable def ep1247 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 126105 1000 0 1 126105 1000 0 1 636098841 40000

noncomputable def ep1248 := @ep1247 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz513)

noncomputable def ep1249 := ep1248 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 126105 1000 0 1 qz513)

noncomputable def ep1250 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 17090193685 549755813888

noncomputable def ep1251 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 17090193685 549755813888

noncomputable def ep1252 := nat_lit 162706945768259638620778995660329180810338084114215596721264437

noncomputable def ep1253 := nat_lit 168364988620520016177064492728915803864363428950835200000000000000

noncomputable def ep1254 := nat_lit 553390721105835647624487639288339188974516514416651251569274473178315043381

noncomputable def ep1255 := nat_lit 1678493448626955440500103164989386127402825292747449140081266327447142400000000000000

noncomputable def ep1256 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1252 ep1253 ep1254 ep1255

noncomputable def ep1257 := nat_lit 4776006057551616595555637518826366314305804977673159037460521

noncomputable def ep1258 := nat_lit 13469199089641601294165159418313264309149074316066816000000000000

noncomputable def ep1259 := nat_lit 429379021995920195070585872494666466957473565731255868465158405381261356113

noncomputable def ep1260 := nat_lit 3356986897253910881000206329978772254805650585494898280162532654894284800000000000000

noncomputable def ep1261 := nat_lit 22890415566414318039185228149999911529225671531844690834001761

noncomputable def ep1262 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1257 ep1258 ep1259 ep1260 ep1261

noncomputable def ep1263 := nat_lit 37414441915671114706014331717536845303191873100185600000000000000

noncomputable def ep1264 := nat_lit 225800806738583700059463135360670636997186487700682211557796846991789576883

noncomputable def ep1265 := nat_lit 1118995632417970293666735443326257418268550195164966093387510884964761600000000000000

noncomputable def ep1266 := nat_lit 487007165737824025911342546134248564058168339849290519197190885887507852642443083730228431299779733535872910360576000000000000

noncomputable def ep1267 := nat_lit 2185407526653007707984167171789

noncomputable def ep1268 := nat_lit 116056878683004400771792896000000

noncomputable def ep1269 := nat_lit 3592640727291186884405176683911329

noncomputable def ep1270 := nat_lit 1057825898916249021928948450239447040000000

noncomputable def ep1271 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1267 ep1268 ep1269 ep1270 ep1267 ep1268 ep1269

noncomputable def ep1272 := nat_lit 4784392915137125110487129050319

noncomputable def ep1273 := nat_lit 193428131138340667952988160000000

noncomputable def ep1274 := nat_lit 4314933026015324301953768991809941

noncomputable def ep1275 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1267 ep1268 ep1269 ep1270 Bool.true ep1272 ep1273 ep1274

noncomputable def ep1276 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1267 ep1268 ep1269 ep1270 Bool.true ep1272 ep1273 ep1274 ep1270

noncomputable def ep1277 := nat_lit 4978005384993992890640899453

noncomputable def ep1278 := nat_lit 5802843934150220038589644800000

noncomputable def ep1279 := nat_lit 4489226476921699585348916689967

noncomputable def ep1280 := nat_lit 31734776967487470657868453507183411200000

noncomputable def ep1281 := nat_lit 2284967634352887565796985160849

noncomputable def ep1282 := nat_lit 10328999534181390694680638382737287

noncomputable abbrev qz232 := (Complex.re qz506)

noncomputable abbrev qz233 := (Complex.im qz506)

noncomputable def ep1283 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1277 ep1278 ep1279 ep1280 ep1281 ep1268 ep1282

noncomputable def ep1284 := nat_lit 3173477696748747065786845350718341120000000

noncomputable def ep1285 := nat_lit 12681578809684641104119082855537216473243278763158090547200000

noncomputable def ep1286 := nat_lit 1652852967056639096763981953499136

noncomputable def ep1287 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 1908246523 19200000 0 1 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 ep1277

noncomputable def ep1288 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 1908246523 19200000 0 1 0 1 0 1 1908246523

noncomputable def ep1289 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 5724739569 80000 0 1 1908246523 19200000 0

noncomputable def ep1290 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow42.d18 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz20)

noncomputable abbrev qz514 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 qz542)

noncomputable abbrev qz234 := qz514

noncomputable def ep1291 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1

noncomputable abbrev qz235 := (Complex.re qz514)

noncomputable abbrev qz236 := (Complex.im qz514)

noncomputable def ep1292 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 636068841 16000 0 1 636098841 20000 0 1

noncomputable def ep1293 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 636068841 40000 0 1 5 2 0 1 636068841 16000

noncomputable abbrev qz515 := (@HAdd.hAdd Complex Complex Complex qz538 qz537 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz515

noncomputable def ep1294 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1

noncomputable abbrev qz238 := (Complex.re qz515)

noncomputable abbrev qz239 := (Complex.im qz515)

noncomputable def ep1295 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 636098841 40000 0 1

noncomputable def ep1296 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1297 := @ep1296 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable abbrev qz516 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz516 qz13) Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 126105 1000 1 qz14)

noncomputable abbrev qz517 := (ep1298 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz13 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1299 := ep1297 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz517)

noncomputable def ep1300 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 126105 1000 0 1 126105 1000 0 1 636098841 40000

noncomputable def ep1301 := @ep1300 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep1302 := ep1301 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz517)

noncomputable def ep1303 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 (@ep1295 2544275364 636068841 40000 0 1 (ep1299 rfl) (ep1302 rfl) rfl rfl)

noncomputable def ep1304 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 25221 400 0 1 75663 400 0 1

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 126105 1000 0 1 25221 400

noncomputable def ep1306 := @ep1305 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep1307 := ep1306 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz517)

noncomputable def ep1308 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 126105 1000 0 1 3 2 0 1 75663 400

noncomputable def ep1309 := @ep1308 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 126105 1000 0 1 ep628)

noncomputable def ep1310 := ep1309 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 126105 1000 0 1 qz517)

noncomputable abbrev qz240 := (ep1294 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1303 (@ep1304 40353600 25221 100 0 1 (ep1307 rfl) (ep1310 rfl) rfl rfl)))

noncomputable def ep1311 := @ep1293 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz240)

noncomputable abbrev qz518 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1312 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz518 qz13) Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 (BSN.s_add_nat_mk qz13 Bool.false 126105 1000 2 qz14)

noncomputable abbrev qz519 := (ep1312 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz13 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1313 := ep1311 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz519)

noncomputable def ep1314 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 25221 100 0 1 126105 1000 0 1 636098841 20000

noncomputable def ep1315 := @ep1314 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz240)

noncomputable def ep1316 := ep1315 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz519)

noncomputable def ep1317 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 (@ep1292 22898958276000 5724739569 80000 0 1 (ep1313 rfl) (ep1316 rfl) rfl rfl)

noncomputable def ep1318 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 16042292238861 8000000 0 1 25221 40 0 1

noncomputable def ep1319 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 636068841 40000 0 1 126105 1000 0 1 16042292238861 8000000

noncomputable def ep1320 := @ep1319 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz240)

noncomputable def ep1321 := ep1320 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz519)

noncomputable def ep1322 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 25221 100 0 1 5 2 0 1 25221 40

noncomputable def ep1323 := @ep1322 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 636068841 40000 0 1 Bool.false 25221 100 0 1 qz240)

noncomputable def ep1324 := ep1323 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 126105 1000 0 1 qz519)

noncomputable abbrev qz241 := (ep1291 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1317 (@ep1318 641489921554440 16037248038861 8000000 0 1 (ep1321 rfl) (ep1324 rfl) rfl rfl)))

noncomputable def ep1325 := @ep1289 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz241)

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 16037248038861 8000000 0 1 0 1 0

noncomputable def ep1327 := @ep1326 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz241)

noncomputable def ep1328 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 5345749346287 1920000000 0 1 0 1 0 1 5345749346287

noncomputable def ep1329 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 16037248038861 8000000 0 1 5345749346287 1920000000 0

noncomputable def ep1330 := @ep1329 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz241)

noncomputable def ep1331 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 5724739569 80000 0 1 0 1 0

noncomputable def ep1332 := @ep1331 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 5724739569 80000 0 1 Bool.true 16037248038861 8000000 0 1 qz241)

noncomputable def ep1333 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 (@ep1288 1908246523 19200000 0 1 (ep1325 rfl) (ep1327 rfl) rfl rfl) (@ep1328 5345749346287 1920000000 0 1 (ep1330 rfl) (ep1332 rfl) rfl rfl)

noncomputable def ep1334 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 ep1333

noncomputable def ep1335 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 Bool.true 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286

noncomputable abbrev qz589 := (@Nat.cast Real Real.instNatCast 8031810176)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz589))

noncomputable def ep1336 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz139) (@HMul.hMul Real Real Real qz0 qz242 qz578)) Bool.true 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 Bool.true 2137181792801376635 302231454903657293676544 1932189271342400193001

noncomputable def ep1337 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz589) 49269317785032093 549755813888 1 549755813888 3067136 3067137 274877906944 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz589) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz589 qz15)) Bool.false 49269317785032093 549755813888 1 549755813888 (BSN.sqrt_natCast_div_one 8031810176) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz589 qz15)) Bool.false 49269317785032093 549755813888 1 549755813888 49269317785032093 549755813888 1 549755813888 (BSN.sqrt_enclosure 8031810176 1 24634658892516046 24634658892516047 274877906944 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1338 := nat_lit 273441585950000000000000000

noncomputable def ep1339 := nat_lit 1367207929750000000000000

noncomputable def ep1340 := nat_lit 32266625250190019745816772608

noncomputable def ep1341 := nat_lit 9903520314283042199192993792

noncomputable def ep1342 := nat_lit 87501307504000000000000000

noncomputable def ep1343 := nat_lit 108280151445646499343828049772170444800

noncomputable def ep1344 := nat_lit 2118654178215607229006287516631040000

noncomputable def ep1345 := nat_lit 34459425000000000000000000

noncomputable def ep1346 := BSN.log_dyadic_bound 10 42 10 9 ep1343 274877906944 87501307504 ep1344 ep1345 133455372207 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 10) (BSN.artanhQ 42) 0 9 ep1344 ep1343 ep1345 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1347 := @Enclosure.Real.IsNear.mulLit_ff qz13 qz141 126105 1000 0 1 3668290588642551 1125899906842624 15630468831719 ep1339 92517956936153778771 225179981368524800 394216054404784899 ep1338 qz18 (BSN.isNear_log_sfrac 26 1 3668290588642551 1125899906842624 15630468831719 ep1339 Bool.false (@Enclosure.Real.IsNear.recentre' qz435 Bool.false ep1340 ep1341 1000350005230016 ep1342 3668290588642551 1125899906842624 15630468831719 ep1339 (BSN.log_rat_reduce_isNear 26 1 4 52 32 133455372207 274877906944 24973259072661432 36028797018963968 87501307504 1000000000000000 rfl rfl rfl rfl (ep1346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1348 := nat_lit 17517795038861308932965531648

noncomputable def ep1349 := nat_lit 131772178669432053599172947550188262126973755924217431222657761552746916386332823676952047029601192296499083044738964424710094101385535980397555587281257681850904506519424966804314745737216

noncomputable def ep1350 := nat_lit 25839119757345775877310300825288425263506443747055285218960478101656152622246656416120420907700233426791529434444611529295189599565731493407137973639024201449774669962362710555386929007820800

noncomputable def ep1351 := nat_lit 950420024726119881171149805734113223858079591821757179294249700417346353576705749545680494265819803529829982140031205726355930805575024671568753667776888123935104016336007896764416

noncomputable def ep1352 := nat_lit 658778498559483670702726882089611812983782905933599985230546591382967867504314044790182297985805785543310777794463604911336294450020793918017582292953333273799220156258994008451503068286976

noncomputable def ep1353 := nat_lit 904369191507102155705860528885094884222725531146934982663616733557965341778632974564214731769508169937703530205561403525331635984800602269249829077365847050742113448682694869438542515273728000

noncomputable def ep1354 := BSN.sin_dyadic_bound_f 995771360911778 1125899906842624 4 3 549755813888 175173516000 ep1349 ep1350 ep1351 ep1352 ep1353 ep1351 425263180007 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 995771360911778) (BSN.sinEvenQ 1125899906842624) 0 3 ep1349 ep1350 ep1351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 995771360911778) (BSN.sinOddQ 1125899906842624) 0 3 ep1352 ep1353 ep1351 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz520 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 56468479575289) (@Nat.cast Real Real.instNatCast 137438953472))

noncomputable def ep1355 := @Enclosure.Real.IsNear.cos_image qz142 qz520 Bool.false 56468479575289 137438953472 397 274877906944 Bool.true 425263180007 549755813888 1 87501307504 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 92517956936153778771 225179981368524800 394216054404784899 ep1338 56468479575289 137438953472 397 274877906944 (ep1347 rfl) rfl) (Enclosure.sfrac_false_div 56468479575289 137438953472) (BSN.cos_reduce1 qz520 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1348) (@Nat.cast Real Real.instNatCast ep1209)) 226375608064910080 72057594037927936 Bool.false 425263180007 549755813888 65 1000000000000000 175002615008 87501307504 (BSN.sin_reduce_arg_pos_rat_q1 56468479575289 137438953472 226375608064910080 72057594037927936 65 ep1348 ep1209 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 425263180007 549755813888 ep1348 ep1209 995771360911778 1125899906842624 175173516000 175002615008 (ep1354 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1356 := nat_lit 50689809583035162367567817477513311784407661628375655297694946146987969367749396395038527571389904708705134170487501798599854057623559858139084675611638425296987173223868747172111705706496

noncomputable def ep1357 := nat_lit 1987624596718905836716176986560648097192803365158098862996959853973550201711281262778493915976941032830117648803431656099629969197363961031318305664540323188444205381720208504260533000601600

noncomputable def ep1358 := nat_lit 307443536781362874936080206701815101423231958186330637181231324412350540492576435711958364061417725696445112222016943838749081767447740791342900864299100619224978346804307659438900314378240

noncomputable def ep1359 := nat_lit 180873838301420431141172105777018976844545106229386996532723346711593068355726594912842946353901633987540706041112280705066327196960120453849965815473169410148422689736538973887708503054745600

noncomputable def ep1360 := BSN.cos_dyadic_bound_f 995771360911778 1125899906842624 4 3 549755813888 175173516000 ep1356 ep1357 ep1351 ep1358 ep1359 ep1351 348400175995 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 995771360911778) (BSN.cosEvenQ 1125899906842624) 0 3 ep1356 ep1357 ep1351 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 995771360911778) (BSN.cosOddQ 1125899906842624) 0 3 ep1358 ep1359 ep1351 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1361 := @Enclosure.Real.IsNear.sin_image qz142 qz520 Bool.false 56468479575289 137438953472 397 274877906944 Bool.false 348400175995 549755813888 1 87501307504 (@Enclosure.Real.IsNear.recentre' qz142 Bool.false 92517956936153778771 225179981368524800 394216054404784899 ep1338 56468479575289 137438953472 397 274877906944 (ep1347 rfl) rfl) (Enclosure.sfrac_false_div 56468479575289 137438953472) (BSN.sin_reduce1 qz520 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1348) (@Nat.cast Real Real.instNatCast ep1209)) 226375608064910080 72057594037927936 Bool.false 348400175995 549755813888 65 1000000000000000 175002615008 87501307504 (BSN.sin_reduce_arg_pos_rat_q1 56468479575289 137438953472 226375608064910080 72057594037927936 65 ep1348 ep1209 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 348400175995 549755813888 ep1348 ep1209 995771360911778 1125899906842624 175173516000 175002615008 (ep1360 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz521 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 6134273 549755813888 1 549755813888 6134273 549755813888 1 549755813888 (ep1337 rfl rfl) rfl)

noncomputable def ep1362 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz139) (@HMul.hMul Real Real Real qz0 qz242 qz578) Bool.true 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 Bool.true 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz139 6134273 549755813888 1 549755813888 425263180007 549755813888 2188306061627 1503261016347677556736 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 qz521 (@Enclosure.Real.IsNear.recentre' qz139 Bool.true 425263180007 549755813888 35012896986032 24052176261562840907776 425263180007 549755813888 2188306061627 1503261016347677556736 (ep1355 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz578 6134273 549755813888 1 549755813888 348400175995 549755813888 2188306061627 1503261016347677556736 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286 qz521 (@Enclosure.Real.IsNear.neg qz140 Bool.false 348400175995 549755813888 2188306061627 1503261016347677556736 (@Enclosure.Real.IsNear.recentre' qz140 Bool.false 348400175995 549755813888 35012896986032 24052176261562840907776 348400175995 549755813888 2188306061627 1503261016347677556736 (ep1361 rfl rfl) rfl)) rfl)

noncomputable def ep1363 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 5345749346287 1920000000 0 1 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286 ep1281

noncomputable def ep1364 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 1908246523 19200000 0 1 Bool.false 5345749346287 1920000000 0 1 ep1333

noncomputable def ep1365 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 Bool.true 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286

noncomputable def ep1366 := nat_lit 815653945026426678670438021

noncomputable def ep1367 := nat_lit 1160568786830044007717928960000

noncomputable def ep1368 := nat_lit 3687093458817038710768687185523

noncomputable def ep1369 := nat_lit 13945351772898161992126168140457

noncomputable def ep1370 := nat_lit 580284393415022003858964480000000

noncomputable def ep1371 := nat_lit 12576089732164269034784438256877523

noncomputable def ep1372 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1366 ep1367 ep1368 ep1280 ep1369 ep1370 ep1371

noncomputable def ep1373 := nat_lit 16657851243716852948357543224556620648646391122142922014720000

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 1908246523 19200000 0 1 2137181792801376635 302231454903657293676544 1932189271342400193001 ep1286 ep1366

noncomputable def ep1375 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 5345749346287 1920000000 0 1 2608680443011079911 302231454903657293676544 2352540105700850049629 ep1286 ep1369

noncomputable abbrev qz522 := (@ep1336 ep1286 (BSN.cpow_neg_s_sub_mk qz13 126105 1000 26 3 8031810176 qz14 rfl EMRow42.d19) ep1362)

noncomputable def ep1376 := ep1276 (@ep1283 ep1284 ep1285 ep1267 ep1268 ep1269 ep1270 (@ep1287 ep1278 ep1279 ep1280 ep1334 (ep1335 qz522) rfl) (@ep1363 ep1268 ep1282 ep1284 ep1364 (ep1365 qz522) rfl) rfl rfl) (@ep1372 ep1284 ep1373 ep1272 ep1273 ep1274 ep1270 (@ep1374 ep1367 ep1368 ep1280 ep1334 (ep1365 qz522) rfl) (@ep1375 ep1370 ep1371 ep1284 ep1364 (ep1335 qz522) rfl) rfl rfl)

noncomputable def ep1377 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1272 ep1273 ep1274 ep1270 ep1272 ep1273 ep1274

noncomputable def ep1378 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1267 ep1268 ep1269 ep1270 Bool.true ep1272 ep1273 ep1274

noncomputable def ep1379 := @ep1237 322959730527302135 288230376151711744 402955615051 2017612633061982208 (@ep1238 1 3670016 (ep1239 (@ep1240 1048576 1 1048576 (ep1241 (@ep1242 2546355364 636588841 40000 0 1 (ep1246 rfl) (ep1249 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1250 2917 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1251 2917 549755813888 17090193685 549755813888 2917 549755813888 (@ep1256 8545095384 8545098301 274877906944 (@ep1262 ep1263 ep1264 ep1265 ep1266 ep1252 ep1253 ep1254 ep1255 (@ep1271 ep1270 ep1257 ep1258 ep1259 ep1260 (@ep1275 ep1270 ep1376) (@ep1275 ep1270 ep1376) rfl) (@ep1377 ep1270 ep1261 ep1263 ep1264 ep1265 (@ep1378 ep1270 ep1376) (@ep1378 ep1270 ep1376) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow42.d20 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 342553848651837943 288230376151711744 1484531198367139 18158513697557839872 := ep1235 (ep1236 ep1379) rfl rfl

noncomputable abbrev qz590 := (@HAdd.hAdd Complex Complex Complex qz592 qz598 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz523 := qz590

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz523) (@HAdd.hAdd Real Real Real qz415 (Complex.re qz440) qz294))

noncomputable abbrev qz524 := (@HPow.hPow Complex Complex Complex qz539 qz576 (@HSub.hSub Complex Complex Complex qz568 qz580 qz541))

noncomputable abbrev qz244 := qz524

noncomputable def ep1380 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 12995792641 463856467968 19402483 231928233984 603557608289661101 504403158265495552 104803924831

noncomputable def ep1381 := nat_lit 286519219248739761180481945600

noncomputable def ep1382 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26)) 26561 1769472 1 1769472 489281 262144 2885 524288 12995792641 463856467968

noncomputable def ep1383 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26)) (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz151 1 26)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz151 1 26)) (Complex.im (zetaApproximant qz151 1 26))))) Bool.false 489281 262144 2885 524288

noncomputable def ep1384 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz151 1 26)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz151 1 26)) (Complex.im (zetaApproximant qz151 1 26))))) Bool.false 1957124 1048576 5770 1048576

noncomputable def ep1385 := nat_lit 421086730262740418336318271064275479478278233

noncomputable def ep1386 := nat_lit 120873434696239768076451800202161946624000000

noncomputable def ep1387 := nat_lit 373921679046359993490159175317975245387731178331662700314958071

noncomputable def ep1388 := nat_lit 18207703713398178314084647707241317076258387052452701536256000000

noncomputable def ep1389 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz151 1 26)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz151 1 26)) (Complex.im (zetaApproximant qz151 1 26)))) ep1385 ep1386 ep1387 ep1388 975677 981447

noncomputable def ep1390 := nat_lit 431760657105115349859766112454693778219882348121513209

noncomputable def ep1391 := nat_lit 124151761242200543726766602187966528341151842304000000

noncomputable def ep1392 := nat_lit 6894745386791353610264112341267453942906644907066303931449939

noncomputable def ep1393 := nat_lit 350148148334580352193935532831563789928045904854859644928000000

noncomputable def ep1394 := nat_lit 17675216002082855037284393044883173977244709658769

noncomputable def ep1395 := nat_lit 2938503224667468490574357448235894161920753664000000

noncomputable def ep1396 := nat_lit 5131639644403201918808444524022546785528547721404965293187081

noncomputable def ep1397 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz151 1 26)) (Complex.re (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz151 1 26)) (Complex.im (zetaApproximant qz151 1 26))) ep1390 ep1391 ep1392 ep1393 ep1394 ep1395 ep1396

noncomputable def ep1398 := nat_lit 6069234571132726104694882569080439025419462350817567178752000000

noncomputable def ep1399 := nat_lit 1270924492384921509589133823796462052311355095820610749653322291151716984618977843527238080949911552000000

noncomputable def ep1400 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz151 1 26)) (Complex.re (zetaApproximant qz151 1 26)) ep979 ep980 ep981 ep982 ep979 ep980 ep981 ep982 ep1390

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz151 1 26)) (Complex.im (zetaApproximant qz151 1 26)) ep1091 ep1092 ep1093 ep1094 ep1091 ep1092 ep1093 ep1094 ep1394

noncomputable def ep1402 := @ep1380 504403158265495552 ep1381 16677613559222067775 13618885273168379904 1142148474766085 13618885273168379904 (@ep1382 19402483 231928233984 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz507) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow42.d16 EMRow42.d17 rfl) (ep1215 rfl)) (ep1383 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz151 1 26)) (@ep1384 489281 262144 2885 524288 (@ep1389 524288 (@ep1397 ep1398 ep1399 ep1385 ep1386 ep1387 ep1388 (@ep1400 ep1391 ep1392 ep1393 ep1197 ep1197 rfl) (@ep1401 ep1395 ep1396 ep1398 ep1203 ep1203 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz523)

noncomputable def ep1403 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz588) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 603557608289661101 504403158265495552 104803924831 504403158265495552 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz154 3)

noncomputable def ep1404 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz588) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 134471243 3670016 1 3670016 4488376807 137438953472 373 68719476736

noncomputable def ep1405 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz588 134471243 1048576 1 1048576 2 7 0 1 134471243 3670016

noncomputable abbrev qz525 := (Complex.re qz590)

noncomputable abbrev qz526 := (Complex.im qz590)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz267 qz525 qz525) (@HMul.hMul Real Real Real qz267 qz526 qz526))

noncomputable abbrev qz247 := qz523

noncomputable def ep1406 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 134471243 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1407 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 134471243 1048576 1 1048576 134471243

noncomputable def ep1408 := @Enclosure.Real.IsNear.sqrt_image qz246 4111487909 250000 0 1 67235621 67235622 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz525 qz525)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz526 qz526)

noncomputable def ep1409 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 4108425409 250000 0 1

noncomputable abbrev qz250 := qz525

noncomputable def ep1410 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1411 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz512 qz154) Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 128194 1000 3 qz155)

noncomputable abbrev qz527 := (ep1411 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz154 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz156))

noncomputable def ep1412 := @ep1410 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz527)

noncomputable def ep1413 := ep1412 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz527)

noncomputable abbrev qz251 := qz526

noncomputable def ep1414 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 128194 1000 0 1 128194 1000 0 1 4108425409 250000

noncomputable def ep1415 := @ep1414 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz527)

noncomputable def ep1416 := ep1415 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 128194 1000 0 1 qz527)

noncomputable def ep1417 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 4488376807 137438953472

noncomputable def ep1418 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 17953507228 549755813888

noncomputable def ep1419 := nat_lit 87676009089625330110532781394945109168841581848731524917635233313

noncomputable def ep1420 := nat_lit 82209467099863289148957271840290919855646205542400000000000000000000

noncomputable def ep1421 := nat_lit 871504076240882071841764144215138606420262418441428777000004550618823074223411

noncomputable def ep1422 := nat_lit 2458730637637141758545072995589921085062732362423021201290917471846400000000000000000000

noncomputable def ep1423 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1419 ep1420 ep1421 ep1422

noncomputable def ep1424 := nat_lit 89701202389757868712078146980004386650604945841803422487500009

noncomputable def ep1425 := nat_lit 5138091693741455571809829490018182490977887846400000000000000000000

noncomputable def ep1426 := nat_lit 1129843336852102218846024181377158499943178063065325681338406995763816532121

noncomputable def ep1427 := nat_lit 122936531881857087927253649779496054253136618121151060064545873592320000000000000000000

noncomputable def ep1428 := nat_lit 86240789851389204211139531043265038982431902715262670157835233169

noncomputable def ep1429 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1424 ep1425 ep1426 ep1427 ep1428

noncomputable def ep1430 := nat_lit 848907209503840027464843660587595436421398857180122263373236410703546743580991

noncomputable def ep1431 := nat_lit 450487374043804266576863212930601807773553999925819687417979623095415867790659600644222855296855545055211107123200000000000000000000

noncomputable def ep1432 := nat_lit 9471071871216999096143331250003

noncomputable def ep1433 := nat_lit 2266735911777429702574080000000000

noncomputable def ep1434 := nat_lit 5453364015076317556089526928070017

noncomputable def ep1435 := nat_lit 4958558901169917290291945860497408000000000

noncomputable def ep1436 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1432 ep1433 ep1434 ep1435 ep1432 ep1433 ep1434

noncomputable def ep1437 := nat_lit 293667822294832302267378556345513

noncomputable def ep1438 := nat_lit 9066943647109718810296320000000000

noncomputable def ep1439 := nat_lit 264289109651391339691862377337784473

noncomputable def ep1440 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1432 ep1433 ep1434 ep1435 Bool.true ep1437 ep1438 ep1439

noncomputable def ep1441 := nat_lit 49585589011699172902919458604974080000000000

noncomputable def ep1442 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1432 ep1433 ep1434 ep1435 Bool.true ep1437 ep1438 ep1439 ep1441

noncomputable def ep1443 := nat_lit 13670170762681267160482976887

noncomputable def ep1444 := nat_lit 12089258196146291747061760000000

noncomputable def ep1445 := nat_lit 12299330199415188147575776132427

noncomputable def ep1446 := nat_lit 66114118682265563870559278139965440000000

noncomputable def ep1447 := nat_lit 24068457778439473377467778832631

noncomputable def ep1448 := nat_lit 4533471823554859405148160000000000

noncomputable def ep1449 := nat_lit 566364281265022305627667964767249

noncomputable abbrev qz252 := (Complex.re qz524)

noncomputable abbrev qz253 := (Complex.im qz524)

noncomputable def ep1450 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1443 ep1444 ep1445 ep1446 ep1447 ep1448 ep1449

noncomputable def ep1451 := nat_lit 619819862646239661286493232562176000000000

noncomputable def ep1452 := nat_lit 228996466490801404936326373034960567059456889526482370560000000

noncomputable def ep1453 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 12324963727 120000000 0 1 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 ep1443

noncomputable def ep1454 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) 12324963727 120000000 0 1 0 1 0 1 12324963727

noncomputable def ep1455 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 36974891181 500000 0 1 12324963727 120000000 0

noncomputable abbrev qz528 := (@HAdd.hAdd Complex Complex Complex qz538 qz579 qz542)

noncomputable abbrev qz254 := qz528

noncomputable def ep1456 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1

noncomputable abbrev qz255 := (Complex.re qz528)

noncomputable abbrev qz256 := (Complex.im qz528)

noncomputable def ep1457 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 4108237909 100000 0 1 4108425409 125000 0 1

noncomputable def ep1458 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 4108237909 250000 0 1 5 2 0 1 4108237909 100000

noncomputable abbrev qz529 := (@HAdd.hAdd Complex Complex Complex qz538 qz579 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz529

noncomputable def ep1459 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz80 (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1

noncomputable abbrev qz258 := (Complex.re qz529)

noncomputable abbrev qz259 := (Complex.im qz529)

noncomputable def ep1460 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 4108425409 250000 0 1

noncomputable def ep1461 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1462 := @ep1461 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1463 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz516 qz154) Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 128194 1000 1 qz155)

noncomputable abbrev qz530 := (ep1463 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz154 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz156))

noncomputable def ep1464 := ep1462 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz530)

noncomputable def ep1465 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 128194 1000 0 1 128194 1000 0 1 4108425409 250000

noncomputable def ep1466 := @ep1465 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1467 := ep1466 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz530)

noncomputable def ep1468 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 (@ep1460 16432951636 4108237909 250000 0 1 (ep1464 rfl) (ep1467 rfl) rfl rfl)

noncomputable def ep1469 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 64097 1000 0 1 192291 1000 0 1

noncomputable def ep1470 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 128194 1000 0 1 64097 1000

noncomputable def ep1471 := @ep1470 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1472 := ep1471 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz530)

noncomputable def ep1473 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 128194 1000 0 1 3 2 0 1 192291 1000

noncomputable def ep1474 := @ep1473 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 128194 1000 0 1 ep1159)

noncomputable def ep1475 := ep1474 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 128194 1000 0 1 qz530)

noncomputable abbrev qz260 := (ep1459 (BSN.ascPochhammer_succ_eval_c 1 2 qz440 rfl) (ep1468 (@ep1469 256388000 64097 250 0 1 (ep1472 rfl) (ep1475 rfl) rfl rfl)))

noncomputable def ep1476 := @ep1458 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz260)

noncomputable def ep1477 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz518 qz154) Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 (BSN.s_add_nat_mk qz154 Bool.false 128194 1000 2 qz155)

noncomputable abbrev qz531 := (ep1477 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz154 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz156))

noncomputable def ep1478 := ep1476 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz531)

noncomputable def ep1479 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 64097 250 0 1 128194 1000 0 1 4108425409 125000

noncomputable def ep1480 := @ep1479 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz260)

noncomputable def ep1481 := ep1480 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz531)

noncomputable def ep1482 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 (@ep1457 924372279525000 36974891181 500000 0 1 (ep1478 rfl) (ep1481 rfl) rfl rfl)

noncomputable def ep1483 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 263325725253173 125000000 0 1 64097 100 0 1

noncomputable def ep1484 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 4108237909 250000 0 1 128194 1000 0 1 263325725253173 125000000

noncomputable def ep1485 := @ep1484 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz260)

noncomputable def ep1486 := ep1485 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz531)

noncomputable def ep1487 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 64097 250 0 1 5 2 0 1 64097 100

noncomputable def ep1488 := @ep1487 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 4108237909 250000 0 1 Bool.false 64097 250 0 1 qz260)

noncomputable def ep1489 := ep1488 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 128194 1000 0 1 qz531)

noncomputable abbrev qz261 := (ep1456 (BSN.ascPochhammer_succ_eval_c 2 3 qz440 rfl) (ep1482 (@ep1483 26324560400317300 263245604003173 125000000 0 1 (ep1486 rfl) (ep1489 rfl) rfl rfl)))

noncomputable def ep1490 := @ep1455 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz261)

noncomputable def ep1491 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 263245604003173 125000000 0 1 0 1 0

noncomputable def ep1492 := @ep1491 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz261)

noncomputable def ep1493 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) 263245604003173 90000000000 0 1 0 1 0 1 263245604003173

noncomputable def ep1494 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 263245604003173 125000000 0 1 263245604003173 90000000000 0

noncomputable def ep1495 := @ep1494 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz261)

noncomputable def ep1496 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 36974891181 500000 0 1 0 1 0

noncomputable def ep1497 := @ep1496 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1290) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 36974891181 500000 0 1 Bool.true 263245604003173 125000000 0 1 qz261)

noncomputable def ep1498 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 (@ep1454 12324963727 120000000 0 1 (ep1490 rfl) (ep1492 rfl) rfl rfl) (@ep1493 263245604003173 90000000000 0 1 (ep1495 rfl) (ep1497 rfl) rfl rfl)

noncomputable def ep1499 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 ep1498

noncomputable def ep1500 := nat_lit 103303310441039943547748872093696

noncomputable def ep1501 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 Bool.true 274288999463968641 151115727451828646838272 32272007926380930195 ep1500

noncomputable def ep1502 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz585)) Bool.true 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 Bool.true 274288999463968641 151115727451828646838272 32272007926380930195

noncomputable def ep1503 := nat_lit 683603964875000000000000000

noncomputable def ep1504 := @Enclosure.Real.IsNear.mulLit_ff qz154 qz141 128194 1000 0 1 3668290588642551 1125899906842624 15630468831719 ep1339 235126421860221591447 562949953421312000 1001866160706692743 ep1503 qz156 (BSN.isNear_log_sfrac 26 1 3668290588642551 1125899906842624 15630468831719 ep1339 Bool.false (@Enclosure.Real.IsNear.recentre' qz435 Bool.false ep1340 ep1341 1000350005230016 ep1342 3668290588642551 1125899906842624 15630468831719 ep1339 (BSN.log_rat_reduce_isNear 26 1 4 52 32 133455372207 274877906944 24973259072661432 36028797018963968 87501307504 1000000000000000 rfl rfl rfl rfl (ep1346 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1505 := nat_lit 3484556084755132845456883712

noncomputable def ep1506 := nat_lit 2475880078570760549798248448

noncomputable def ep1507 := nat_lit 845923559493688029610463695348939660521326533406601531056860556725296199388529847969741787826666019665775247627677623504613689961764035241431288389893482543460946667779163403871995072679936

noncomputable def ep1508 := nat_lit 250617642946242416370754187527281082774998069037327822573892144292803353738174483234439136423613788875948072757406693407153998680713294294978439537736186106028084365407760048282996736

noncomputable def ep1509 := nat_lit 4226228792340591192283295477339304612276000396244172586263593599827055371900658295005313384757577308506660072163617059104249721770719412208376007747985154984906010744551156078815148449796096

noncomputable def ep1510 := BSN.sin_dyadic_bound_f 1584592648557706 1125899906842624 4 3 549755813888 175173516000 ep1507 ep1350 ep1508 ep1509 ep1353 ep1508 542433426891 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 1584592648557706) (BSN.sinEvenQ 1125899906842624) 0 3 ep1507 ep1350 ep1508 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 1584592648557706) (BSN.sinOddQ 1125899906842624) 0 3 ep1509 ep1353 ep1508 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz532 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 7175488948371) (@Nat.cast Real Real.instNatCast 17179869184))

noncomputable def ep1511 := @Enclosure.Real.IsNear.cos_image qz218 qz532 Bool.false 7175488948371 17179869184 807 549755813888 Bool.true 542433426891 549755813888 1 87501307504 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 235126421860221591447 562949953421312000 1001866160706692743 ep1503 7175488948371 17179869184 807 549755813888 (ep1504 rfl) rfl) (Enclosure.sfrac_false_div 7175488948371 17179869184) (BSN.cos_reduce1 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1505) (@Nat.cast Real Real.instNatCast ep1506)) 226375608064910080 72057594037927936 Bool.false 542433426891 549755813888 66 1000000000000000 175002615008 87501307504 (BSN.sin_reduce_arg_pos_rat_q1 7175488948371 17179869184 226375608064910080 72057594037927936 66 ep1505 ep1506 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 542433426891 549755813888 ep1505 ep1506 1584592648557706 1125899906842624 175173516000 175002615008 (ep1510 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1512 := nat_lit 22860709374154088993206508362197795212453204039076975714874299222312034019929800771344234885349163637555806740066066985984357129868997021582194033264493961944492127566835364557755975896729112653910988125546525462549667343144299658559961545505827717185536

noncomputable def ep1513 := nat_lit 139513464949296669724631503551441424864741504698355127999875505017017605761466203494133114427672940901199185940857029082404314830421246325248406733377451089719086336890422379758096079181828075336335771180313685029857199944181668349340786997313444773888000

noncomputable def ep1514 := nat_lit 1580091323028810911417088228985857240287038844724490849366648327602418091278292410635366212223025378877056672873171482802772203341716927763889953333464678867746303846945194951675311361103711226265329336363437651834668003481036803694907747270656

noncomputable def ep1515 := nat_lit 232816886668821631174845004706379689819860976710728614603552240967408358769370778647189858153646928660988908890446290810067192830885371392047142238486617060172368571129322322157717984526057425883523006729189292321751411995941900531914930049041703968505856

noncomputable def ep1516 := nat_lit 21345560137242390467868620043370538004305450218848334583980952267603693681504329134602366507433959957883475448951125449607860169054450687763006230206750016727020209544234624102988700114819695526459372990587993809568151591459795257449140410588957050404864000

noncomputable def ep1517 := BSN.cos_dyadic_bound_f 1584592648557706 1125899906842624 5 4 549755813888 175173516000 ep1512 ep1513 ep1514 ep1515 ep1516 ep1514 89428364034 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.cosEvenP 1584592648557706) (BSN.cosEvenQ 1125899906842624) 0 4 ep1512 ep1513 ep1514 rfl rfl rfl rfl) (@BSN.binarySplit_of_base4 (BSN.cosOddP 1584592648557706) (BSN.cosOddQ 1125899906842624) 0 4 ep1515 ep1516 ep1514 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1518 := @Enclosure.Real.IsNear.sin_image qz218 qz532 Bool.false 7175488948371 17179869184 807 549755813888 Bool.false 89428364034 549755813888 1 87501307504 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 235126421860221591447 562949953421312000 1001866160706692743 ep1503 7175488948371 17179869184 807 549755813888 (ep1504 rfl) rfl) (Enclosure.sfrac_false_div 7175488948371 17179869184) (BSN.sin_reduce1 qz532 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1505) (@Nat.cast Real Real.instNatCast ep1506)) 226375608064910080 72057594037927936 Bool.false 89428364034 549755813888 66 1000000000000000 175002615008 87501307504 (BSN.sin_reduce_arg_pos_rat_q1 7175488948371 17179869184 226375608064910080 72057594037927936 66 ep1505 ep1506 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 89428364034 549755813888 ep1505 ep1506 1584592648557706 1125899906842624 175173516000 175002615008 (ep1517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1519 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 qz216) (@HMul.hMul Real Real Real qz0 qz242 qz585) Bool.true 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 Bool.true 274288999463968641 151115727451828646838272 32272007926380930195 ep1500 (@Enclosure.Real.IsNear.mulLit_ft qz242 qz216 6134273 549755813888 1 549755813888 542433426891 549755813888 4447706935601 3006522032695355113472 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 qz521 (@Enclosure.Real.IsNear.recentre' qz216 Bool.true 542433426891 549755813888 71163310969616 48104352523125681815552 542433426891 549755813888 4447706935601 3006522032695355113472 (ep1511 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz585 6134273 549755813888 1 549755813888 44714182017 274877906944 4447706935601 3006522032695355113472 274288999463968641 151115727451828646838272 32272007926380930195 ep1500 qz521 (@Enclosure.Real.IsNear.neg qz217 Bool.false 44714182017 274877906944 4447706935601 3006522032695355113472 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 89428364034 549755813888 71163310969616 48104352523125681815552 44714182017 274877906944 4447706935601 3006522032695355113472 (ep1518 rfl rfl) rfl)) rfl)

noncomputable def ep1520 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 263245604003173 90000000000 0 1 274288999463968641 151115727451828646838272 32272007926380930195 ep1500 ep1447

noncomputable def ep1521 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 12324963727 120000000 0 1 Bool.false 263245604003173 90000000000 0 1 ep1498

noncomputable def ep1522 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 Bool.true 274288999463968641 151115727451828646838272 32272007926380930195 ep1500

noncomputable def ep1523 := nat_lit 1126867323036178647930161669

noncomputable def ep1524 := nat_lit 6044629098073145873530880000000

noncomputable def ep1525 := nat_lit 26516755139340096735859602451

noncomputable def ep1526 := nat_lit 826426483528319548381990976749568000000

noncomputable def ep1527 := nat_lit 291977521310278034295483313842013

noncomputable def ep1528 := nat_lit 262698104343030933887710801190724473

noncomputable def ep1529 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1523 ep1524 ep1525 ep1526 ep1527 ep1438 ep1528

noncomputable def ep1530 := nat_lit 1775113063811117058705394543505148278090352166010554941440000000

noncomputable def ep1531 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 12324963727 120000000 0 1 274288999463968641 151115727451828646838272 32272007926380930195 ep1500 ep1523

noncomputable def ep1532 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 263245604003173 90000000000 0 1 3327434724874935243 302231454903657293676544 2993760583442045244303 ep1286 ep1527

noncomputable abbrev qz533 := (@ep1502 ep1500 (BSN.cpow_neg_s_sub_mk qz154 128194 1000 26 3 8031810176 qz155 rfl EMRow42.d19) ep1519)

noncomputable def ep1533 := ep1442 (@ep1450 ep1451 ep1452 ep1432 ep1433 ep1434 ep1435 (@ep1453 ep1444 ep1445 ep1446 ep1499 (ep1501 qz533) rfl) (@ep1520 ep1448 ep1449 ep1451 ep1521 (ep1522 qz533) rfl) rfl rfl) (@ep1529 ep1441 ep1530 ep1437 ep1438 ep1439 ep1441 (@ep1531 ep1524 ep1525 ep1526 ep1499 (ep1522 qz533) rfl) (@ep1532 ep1438 ep1528 ep1441 ep1521 (ep1501 qz533) rfl) rfl rfl)

noncomputable def ep1534 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1437 ep1438 ep1439 ep1441 ep1437 ep1438 ep1439

noncomputable def ep1535 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1432 ep1433 ep1434 ep1435 Bool.true ep1437 ep1438 ep1439

noncomputable def ep1536 := @ep1404 603557608289661101 504403158265495552 104803924831 504403158265495552 (@ep1405 1 3670016 (ep1406 (@ep1407 1048576 1 1048576 (ep1408 (@ep1409 16445951636 4111487909 250000 0 1 (ep1413 rfl) (ep1416 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1417 373 68719476736 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1418 2984 549755813888 4488376807 137438953472 373 68719476736 (@ep1423 8976752122 8976755106 274877906944 (@ep1429 ep1420 ep1430 ep1422 ep1431 ep1419 ep1420 ep1421 ep1422 (@ep1436 ep1435 ep1424 ep1425 ep1426 ep1427 (@ep1440 ep1441 ep1533) (@ep1440 ep1441 ep1533) rfl) (@ep1534 ep1441 ep1428 ep1420 ep1430 ep1422 (@ep1535 ep1441 ep1533) (@ep1535 ep1441 ep1533) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow42.d21 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 16677613559222067775 13618885273168379904 1142148474766085 13618885273168379904 := ep1402 (ep1403 ep1536) rfl rfl

noncomputable def EMRow42.d22 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz534 := (EMRow42.d3 qz544 qz581 (@Enclosure.dec_le_dec qz544 qz581 126105 1000 128194 1000 (@Eq.refl Real qz544) (@Eq.refl Real qz581) rfl rfl rfl) 26 26 1 1)

noncomputable abbrev qz262 := qz534

noncomputable def ep1537 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz13 126105 1000 qz14) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 26 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz534)

noncomputable def ep1538 := @Enclosure.Real.IsNear.pos_val qz263 ep407 ep408

noncomputable def ep1539 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 26 qz13) Bool.false

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz534)

noncomputable def ep1540 := BSN.mul_neg_of_pos_neg_r qz263 qz264 (@ep1538 ep409 ep410 (@ep1539 ep407 ep408 ep409 ep410 (@Eq.refl Real (hardyZApproximantEM 1 26 qz13)) EMRow42.d11) rfl rfl rfl)

noncomputable def ep1541 := @Enclosure.Real.IsNear.neg_val qz264 ep963 ep964

noncomputable def ep1542 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 26 qz154) Bool.true

noncomputable def ep1543 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 26 qz13)

noncomputable def ep1544 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 26 qz13) Bool.false

noncomputable def ep1545 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 26 qz13) (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 342553848651837943 288230376151711744 1484531198367139 18158513697557839872 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 26))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1546 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 26 qz154)

noncomputable def ep1547 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 26 qz154) Bool.true

noncomputable def ep1548 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 26 qz154) (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 16677613559222067775 13618885273168379904 1142148474766085 13618885273168379904 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz415 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz151 1 26))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz80 (@HMul.hMul Complex Complex Complex qz80 (@HDiv.hDiv Complex Complex Complex qz87 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz151 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1549 := @List.cons EMRow42.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1537 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 26 rfl) (ep1540 (@ep1541 ep965 ep966 (@ep1542 ep963 ep964 ep965 ep966 (@Eq.refl Real (hardyZApproximantEM 1 26 qz154)) EMRow42.d15) rfl rfl rfl)) (ep1543 (hardyZErrorBoundEM 1 26 qz13) (BSN.hardyZErrorBoundEM_le_strong 1 26 qz13 rfl) (@ep1544 Bool.false ep407 ep408 ep409 ep410 342553848651837943 288230376151711744 1484531198367139 18158513697557839872 (@ep1539 ep407 ep408 ep409 ep410 (@Eq.refl Real (hardyZApproximantEM 1 26 qz13)) EMRow42.d11) (ep1545 EMRow42.d20) rfl rfl rfl rfl rfl)) (ep1546 (hardyZErrorBoundEM 1 26 qz154) (BSN.hardyZErrorBoundEM_le_strong 1 26 qz154 rfl) (@ep1547 Bool.false ep963 ep964 ep965 ep966 16677613559222067775 13618885273168379904 1142148474766085 13618885273168379904 (@ep1542 ep963 ep964 ep965 ep966 (@Eq.refl Real (hardyZApproximantEM 1 26 qz154)) EMRow42.d15) (ep1548 EMRow42.d21) rfl rfl rfl rfl rfl)))) (@List.nil EMRow42.d0)

noncomputable abbrev qz535 := (@Enclosure.dec_le_dec qz544 qz581 126105 1000 128194 1000 (@Eq.refl Real qz544) (@Eq.refl Real qz581) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1549 (@List.IsChain.singleton EMRow42.d1 EMRow42.d22 (EMRow42.d2 qz283 qz443 qz535))))

noncomputable abbrev qz536 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1550 := And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz265)) (@Option.some Real qz13))

noncomputable def ep1551 := ep1550 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz265)) (@Option.some Real qz154))

noncomputable def ep1552 := @And.intro (@Eq Nat (@List.length qz536 qz265) 1) ep1551

noncomputable def ep1553 := @And.intro (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 qz265)) (@Option.some Real qz13))

noncomputable def ep1554 := @ep1553 (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 qz265)) (@Option.some Real qz154))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1549 (@List.IsChain.singleton EMRow42.d1 EMRow42.d22 (EMRow42.d2 qz283 qz443 qz535)))

theorem EMRow42.d23 : Zeta.Certificates.BatchSpec 1 126105 1000 128194 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz13)) (@Eq (Option Real) (@Option.map qz536 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz536 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz154)))) qz266 (ep1552 (@Eq.refl Nat 1) (ep1554 (@Eq.refl (Option Real) (@Option.some Real qz13)) (@Eq.refl (Option Real) (@Option.some Real qz154))))

theorem solution : Zeta.Certificates.BatchSpec 1 126105 1000 128194 1000 := EMRow42.d23
#print axioms solution
#check solution
