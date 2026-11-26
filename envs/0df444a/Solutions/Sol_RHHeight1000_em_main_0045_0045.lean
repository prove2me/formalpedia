-- Prove2me | solution 1 for RHHeight1000.em_main_0045_0045
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-20T08:31:22.002991+00:00
-- url     : https://prove2.me/submissions/ce966ce7-9412-4fa5-806b-1c71f1c1eb74

import Definitions.Def_RHT1000_Support_20261118_S005
/- Copyright (c) 2026 Salvatore Mercuri, Bhavik Mehta.
Apache 2.0 license; see the source project LICENSE. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.defProp false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def EMRow45.d0 := @PSigma Zeta.Certificates.ZIntervalEM fun (I : Zeta.Certificates.ZIntervalEM) => Zeta.Certificates.ZIntervalEM.Certificate I

noncomputable def EMRow45.d1 := @NonemptyInterval Real Real.instLE

noncomputable def EMRow45.d2 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) => @NonemptyInterval.mk Real Real.instLE (@Prod.mk Real Real a b) h

noncomputable def EMRow45.d3 := fun (a b : Real) (h : @LE.le Real Real.instLE a b) (fc sc fb sb : Nat) => Zeta.Certificates.ZIntervalEM.mk (EMRow45.d2 a b h) fc sc fb sb

noncomputable def ep0 := nat_lit 26986075409044028275299783

noncomputable def ep1 := nat_lit 4294967296000000000000000

noncomputable def ep2 := nat_lit 26986075409044045455168967

noncomputable abbrev qz267 := (@instHMul Real Real.instMul)

noncomputable abbrev qz0 := qz267

noncomputable abbrev qz268 := (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 2 1) Real.pi)

noncomputable def ep3 := @BSN.isNear_log_image_fff qz268 884279719003555 140737488355328 1 500000000000000 ep0 ep1 ep2 ep1 4138529546116343 2251799813685248 31250000024319 12159500000000000000 4138529546116343 2251799813685248 31250000024319 12159500000000000000 963576 524288

noncomputable abbrev qz269 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 2 1) Real.pi 2 1 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 140737488355328 1 500000000000000 (Enclosure.Real.IsNear.const Bool.false 2 1) BSN.pi_near_15 rfl)

noncomputable def ep4 := @ep3 2 524288 qz269 rfl rfl rfl rfl

noncomputable def ep5 := nat_lit 53972150818088056550599566

noncomputable def ep6 := nat_lit 34359738368000000000000000

noncomputable def ep7 := nat_lit 9806206225044028275299783

noncomputable def ep8 := nat_lit 44165944593044028275299783

noncomputable def ep9 := nat_lit 13681445815609410487519367394620474863599256634174726093703677122907123617368241606644861540940610176751640793056574796245399519365549113997355475306157239709119582688278313060810592403844863400465080549957745

noncomputable def ep10 := nat_lit 231714499556395493334623298703961145503103241611736774613091488581016477543539392410113701224645713379230392133956226737605624599560350113120270717249177907454870984269546186598262646369758174842349131395304

noncomputable def ep11 := nat_lit 8978369550011295664474073352761810093897501552430546263638635096022803738134167562509900960712119243631997923545019968443113540909076206607473711060286601587364321108377403290080403445693385008949995305

noncomputable def ep12 := BSN.log_dyadic_bound ep7 ep8 5 4 ep9 1048576 389104 ep10 ep11 473518 ep5 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep7) (BSN.artanhQ ep8) 0 4 ep10 ep9 ep11 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz270 := (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))

noncomputable abbrev qz1 := qz270

noncomputable def ep13 := ep4 rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep1 4138529546116343 2251799813685248 31250000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep0) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000778208 389104000000000000000 4138529546116343 2251799813685248 31250000024319 12159500000000000000 (BSN.log_rat_reduce_isNear ep0 ep1 2 ep5 ep6 473518 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep12 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep14 := nat_lit 53972150818088090910337934

noncomputable def ep15 := nat_lit 9806206225044045455168967

noncomputable def ep16 := nat_lit 44165944593044045455168967

noncomputable def ep17 := nat_lit 13681445815609453062485491347592146866046743284321690683909457683007658987562290830600045658905080811372395010565947827677605470036294121079488508864180301737865471494204890974265645509835068840465080549957745

noncomputable def ep18 := nat_lit 231714499556396865510889920206523150079811393376960301632499817942333196803513131357563499488546302200815366867712007119763002650772307103678175657719139104636874731038771518520299266622696414842349131395304

noncomputable def ep19 := nat_lit 8978369550011421500876706511871067098718760264493934208903156435737864998391937547068187824077011975074541700434630537294838404525415248443919841847024664017658842168336182958576672102333385008949995305

noncomputable def ep20 := BSN.log_dyadic_bound ep15 ep16 5 4 ep17 1048576 389104 ep18 ep19 473518 ep14 ep6 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP ep15) (BSN.artanhQ ep16) 0 4 ep18 ep17 ep19 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep21 := ep13 (BSN.isNear_log_sfrac ep2 ep1 4138529546116343 2251799813685248 31250000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep2) (@Nat.cast Real Real.instNatCast ep1))) Bool.false 69433004117575847641088 37778931862957161709568 1000000000778208 389104000000000000000 4138529546116343 2251799813685248 31250000024319 12159500000000000000 (BSN.log_rat_reduce_isNear ep2 ep1 2 ep14 ep6 473518 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep20 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable abbrev qz2 := (Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi))

theorem EMRow45.d4 : Enclosure.Real.IsNear qz2 Bool.false 120447 65536 1 262144 := @Enclosure.Real.IsNear.of_eq qz2 (Real.log qz268) Bool.false 120447 65536 1 262144 BSN.log_two_pi_eq (@Enclosure.Real.IsNear.recentre' (Real.log qz268) Bool.false 963576 524288 2 524288 120447 65536 1 262144 (ep21 rfl rfl rfl rfl rfl rfl rfl rfl) rfl)

noncomputable def ep22 := nat_lit 8589934592000000000000000

noncomputable def ep23 := @BSN.isNear_log_image_fff Real.pi 226375608064910080 72057594037927936 1 1000000000000000 ep0 ep22 ep2 ep22 1200336 1048576 1 389104 1200336 1048576 1 389104 600168 524288 2 524288 BSN.pi_near_15 rfl rfl rfl

noncomputable def ep24 := nat_lit 17179869184000000000000000

noncomputable def ep25 := nat_lit 18396140817044028275299783

noncomputable def ep26 := nat_lit 35576010001044028275299783

noncomputable def ep27 := nat_lit 145019262663961446558303139663424756232419223153299357158415217874016130572233056993847515999529612750616182853355499335896178729185698845314776375864537073527142908641610750276034469165612529925303649396973267518946591078603565291376312767403717761600170009932259137778521478520425507632472584532570900560707662248426541531715360699177249902784721815296292248142738824858695953661559845440650653128788875447728828657762006237171740033404723254477174341920697506370253193455781322964835857351124092897592956162654178130575

noncomputable def ep28 := nat_lit 15500762873619990602332184736899274490522931101512051618692838888825382235673431503644115344741331161500627469184702974962114537943617674254904297224139410345221262767191485292268260077615645253784097850065864022184521411511133693085443040736512010941548648374196772723338837137976260321103066698629790037694560548409922339907589559883712609967105556007429010014773911317423638534096849366294542840133852248768895750397896505791271178551667935288585787166713880920071720072716082683081155281219708172458141800988558163320

noncomputable def ep29 := nat_lit 12900190794487083783367107939442176642390171280542213571554777169279725287102813254708993369099729304728646904879886535518616983985412662170766446331701281703998252143668221340329975389245922410714088123244705567402747658401492589451585970559635763980329972215329212888079422466283203384882259392047898400615815810081169907384366653346471604103896809335921621947903075223769953790093549808584241881353287841076643853121427928248525828402335494512605306631304432120211393210317325496757155861061354331245840675149075

noncomputable def ep30 := BSN.log_dyadic_bound ep25 ep26 11 10 ep27 1048576 389104 ep28 ep29 1200336 ep5 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep25) (BSN.artanhQ ep26) 0 10 ep28 ep27 ep29 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep31 := nat_lit 18396140817044045455168967

noncomputable def ep32 := nat_lit 35576010001044045455168967

noncomputable def ep33 := nat_lit 145019262663962847171784895425483977818796535899227200426399035286881207006285364467913811844950531107314785650583974625982406238691319033447632878979985852280879486690814033867010958364699188952871572448188560932645032521756218245629809291975913196623825614492380080480004685076434733043183791438169545293975334857826316990371107134320667652578346815517853870648072772035977941843998949310557583393428557296298890786965786350523173236912472938174255438182435383147950274229549088258679583524155427309880956162654178130575

noncomputable def ep34 := nat_lit 15500762873620157189619721156942591192100275120160672416764593300158228469749443299607348495591439275767946573253526107895503597951484257520435868240203420954375895980141891044871083424251900562230440202302413072793440172565998181227591194192658878334739610458454844032013325963992941389843551995646587189684848765634635122388286241104146031552341815777883628509454807838726994150833304950745987647656768534710890974432620160470644835720379148964170536679305861738540146791997074363921127776563807649880221800988558163320

noncomputable def ep35 := nat_lit 12900190794487324729109480814509220959173684627296055849229843377126536688487849343376525559792931631054411655715865486295286288812423905434305314401904993536755333953308594664509631000767632482919425633906965368325056855874260596615770736441041599390097968820060635361729170158825410327022636428624381203910573184452046894301676992229743752846881064485858738985580654099214803581683226335297196686880535448467637789069028262446657986458573827723305156755787640135484017403116612632808333639900906331245840675149075

noncomputable def ep36 := BSN.log_dyadic_bound ep31 ep32 11 10 ep33 1048576 389104 ep34 ep35 1200336 ep14 ep24 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base10 (BSN.artanhP ep31) (BSN.artanhQ ep32) 0 10 ep34 ep33 ep35 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep37 := @Enclosure.Real.IsNear.recentre' (Real.log Real.pi) Bool.false 600168 524288 2 524288 75021 65536 1 262144 (ep23 rfl rfl rfl rfl rfl (BSN.isNear_log_sfrac ep0 ep22 1200336 1048576 1 389104 Bool.false (BSN.logfrac_isNear ep5 ep24 1 ep0 ep22 1200336 1048576 389104 rfl rfl rfl (ep30 rfl))) (BSN.isNear_log_sfrac ep2 ep22 1200336 1048576 1 389104 Bool.false (BSN.logfrac_isNear ep14 ep24 1 ep2 ep22 1200336 1048576 389104 rfl rfl rfl (ep36 rfl))) rfl rfl rfl rfl rfl rfl rfl rfl) rfl

theorem EMRow45.d5 : Enclosure.Real.IsNear (Real.log Real.pi) Bool.false 75021 65536 1 262144 := ep37

noncomputable abbrev qz686 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 132339 1000)))

noncomputable abbrev qz533 := qz686

noncomputable abbrev qz271 := qz533

noncomputable abbrev qz3 := (BSN.headSumC qz271 9)

noncomputable abbrev qz687 := (@instHAdd Complex Complex.instAdd)

noncomputable abbrev qz534 := qz687

noncomputable abbrev qz272 := qz534

noncomputable abbrev qz4 := qz272

noncomputable abbrev qz5 := qz271

noncomputable abbrev qz535 := (@instHPow Complex Complex Complex.instPow)

noncomputable abbrev qz273 := qz535

noncomputable abbrev qz6 := qz273

noncomputable abbrev qz536 := (@Neg.neg Complex Complex.instNeg qz686)

noncomputable abbrev qz274 := qz536

noncomputable abbrev qz7 := qz274

noncomputable abbrev qz537 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz7)

noncomputable def ep38 := @Enclosure.Complex.IsNear.of_eq qz3 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 8) qz537) Bool.false 971102621573 549755813888 30991452005317 13369511637942272 Bool.false 594454931325 1099511627776 62008471183309 26739023275884544

noncomputable def ep39 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 8) qz537 Bool.false 114164814533 68719476736 3468093540589 1671188954742784 Bool.false 111648017185 549755813888 27749148774805 13369511637942272 Bool.false

noncomputable abbrev qz538 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz7)

noncomputable def ep40 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 7) qz538) Bool.false 114164814533 68719476736 3468093540589 1671188954742784 Bool.false 111648017185 549755813888 27749148774805 13369511637942272

noncomputable def ep41 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 7) qz538 Bool.false 353195049957 274877906944 6066305338619 3342377909485568 Bool.false 92763923585 549755813888 24281160440499 13369511637942272 Bool.false

noncomputable abbrev qz539 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz7)

noncomputable def ep42 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 6) qz539) Bool.false 353195049957 274877906944 6066305338619 3342377909485568 Bool.false 92763923585 549755813888 24281160440499 13369511637942272

noncomputable def ep43 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 6) qz539 Bool.false 722247430311 549755813888 20514520141479 13369511637942272 Bool.true 262223523275 1099511627776 41037283572793 26739023275884544 Bool.true

noncomputable abbrev qz540 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz7)

noncomputable def ep44 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 5) qz540) Bool.false 722247430311 549755813888 20514520141479 13369511637942272 Bool.true 262223523275 1099511627776 41037283572793 26739023275884544

noncomputable def ep45 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 5) qz540 Bool.false 262313765417 274877906944 16396572381547 13369511637942272 Bool.true 138686723203 274877906944 1025209840969 835594477371392 Bool.false

noncomputable abbrev qz541 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz7)

noncomputable def ep46 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 4) qz541) Bool.false 262313765417 274877906944 16396572381547 13369511637942272 Bool.true 138686723203 274877906944 1025209840969 835594477371392

noncomputable def ep47 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 4) qz541 Bool.false 875023481541 1099511627776 23599979263479 26739023275884544 Bool.true 33332461285 1099511627776 23597445369593 26739023275884544 Bool.false

noncomputable abbrev qz542 := (@Nat.cast Complex Complex.instNatCast 3)

noncomputable abbrev qz275 := qz542

noncomputable abbrev qz8 := qz275

noncomputable def ep48 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7)) Bool.false 875023481541 1099511627776 23599979263479 26739023275884544 Bool.true 33332461285 1099511627776 23597445369593 26739023275884544

noncomputable def ep49 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) Bool.false 468569754071 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 274877906944 3246638165219 6684755818971136 Bool.false

noncomputable abbrev qz543 := (@Nat.cast Complex Complex.instNatCast 2)

noncomputable abbrev qz276 := qz543

noncomputable abbrev qz9 := qz276

noncomputable def ep50 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7)) Bool.false 468569754071 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 274877906944 3246638165219 6684755818971136

noncomputable def ep51 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.true

noncomputable abbrev qz544 := (Enclosure.sfrac Bool.false 0 1)

noncomputable abbrev qz10 := qz544

noncomputable def ep52 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz5)

noncomputable abbrev qz688 := (Enclosure.sfrac Bool.false 132339 1000)

noncomputable abbrev qz545 := qz688

noncomputable abbrev qz277 := qz545

noncomputable abbrev qz278 := (Enclosure.sfrac Bool.false 2 1)

noncomputable abbrev qz11 := (@HMul.hMul Real Real Real qz267 qz277 (Real.log qz278))

noncomputable abbrev qz12 := qz277

noncomputable abbrev qz279 := (@Eq.refl Real qz545)

noncomputable abbrev qz13 := qz279

noncomputable abbrev qz280 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2)))

noncomputable def ep53 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)))) Bool.true 630941873705 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 274877906944 3246638165219 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 2 qz13 rfl)

noncomputable abbrev qz14 := (@Nat.cast Real Real.instNatCast 1)

noncomputable abbrev qz281 := (Real.sqrt (@Nat.cast Real Real.instNatCast 2))

noncomputable abbrev qz282 := (@Nat.cast Real Real.instNatCast 2)

noncomputable def ep54 := @Enclosure.Real.IsNear.inv_image qz281 1482911 1048576 1 1048576 370727 370728 524288 (@Enclosure.Real.IsNear.of_eq qz281 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 (BSN.sqrt_natCast_div_one 2) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz282 qz14)) Bool.false 1482911 1048576 1 1048576 1482911 1048576 1 1048576 (BSN.sqrt_enclosure 2 1 741455 741456 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep55 := BSN.log_dyadic_bound 1 3 6 5 613814355 524288 194552 24381081 945 363408 4 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 1) (BSN.artanhQ 3) 0 5 24381081 613814355 945 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep56 := nat_lit 3225047377454384702336996260569760000

noncomputable def ep57 := nat_lit 510423550381407695195061911147652317184

noncomputable def ep58 := nat_lit 7656353255721115427925928667214784757760

noncomputable abbrev qz15 := (BSN.cosEvenQ 2147483648)

noncomputable abbrev qz16 := (BSN.cosOddQ 2147483648)

noncomputable def ep59 := BSN.cos_dyadic_bound_f 1340090180 2147483648 2 1 1048576 389484 ep56 ep57 ep56 ep56 ep58 ep56 850951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1340090180) qz15 0 1 ep56 ep57 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1340090180) qz16 0 1 ep56 ep58 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz17 := (@Nat.cast Real Real.instNatCast 524288)

noncomputable abbrev qz18 := (Enclosure.Real.IsNear.const Bool.false 132339 1000)

noncomputable abbrev qz19 := (@Nat.cast Real Real.instNatCast 75557863725914323419136)

noncomputable abbrev qz283 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 48093051) qz17)

noncomputable abbrev qz284 := (BSN.isNear_log_sfrac 2 1 363408 524288 1 194552 Bool.false (BSN.logfrac_isNear 4 2 1 2 1 363408 524288 194552 rfl rfl rfl (ep55 rfl)))

noncomputable def ep60 := @Enclosure.Real.IsNear.cos_image qz11 qz283 Bool.false 48093051 524288 357 524288 Bool.true 850951 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 3005815707 32768000 132339 194552000 48093051 524288 357 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 132339 1000 0 1 363408 524288 1 194552 3005815707 32768000 132339 194552000 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 48093051 524288) (BSN.cos_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47150231540864911409152) qz19) 226375608064910080 72057594037927936 Bool.false 850951 1048576 14 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 48093051 524288 226375608064910080 72057594037927936 14 47150231540864911409152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 850951 1048576 47150231540864911409152 75557863725914323419136 1340090180 2147483648 389484 389104 (ep59 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep61 := nat_lit 2552117751907038475975309555738261585920

noncomputable def ep62 := nat_lit 17864824263349269331827166890167831101440

noncomputable abbrev qz20 := (BSN.sinEvenQ 2147483648)

noncomputable abbrev qz21 := (BSN.sinOddQ 2147483648)

noncomputable def ep63 := BSN.sin_dyadic_bound_f 1340090180 2147483648 2 1 1048576 389484 ep56 ep61 ep56 ep56 ep62 ep56 612692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1340090180) qz20 0 1 ep56 ep61 ep56 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1340090180) qz21 0 1 ep56 ep62 ep56 rfl rfl rfl rfl) rfl rfl

noncomputable def ep64 := @Enclosure.Real.IsNear.sin_image qz11 qz283 Bool.false 48093051 524288 357 524288 Bool.true 612692 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz11 Bool.false 3005815707 32768000 132339 194552000 48093051 524288 357 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 (Real.log qz278) 132339 1000 0 1 363408 524288 1 194552 3005815707 32768000 132339 194552000 qz18 qz284 rfl) rfl) (Enclosure.sfrac_false_div 48093051 524288) (BSN.sin_reduce2 qz283 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 47150231540864911409152) qz19) 226375608064910080 72057594037927936 Bool.false 612692 1048576 14 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 48093051 524288 226375608064910080 72057594037927936 14 47150231540864911409152 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 612692 1048576 47150231540864911409152 75557863725914323419136 1340090180 2147483648 389484 389104 (ep63 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz285 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 2))) Bool.false 741455 1048576 1 1048576 741455 1048576 1 1048576 (ep54 rfl rfl) rfl)

noncomputable def ep65 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz11)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11))) Bool.true 630941873705 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 274877906944 3246638165219 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ft qz280 (Real.cos qz11) 741455 1048576 1 1048576 850951 1048576 8747419 12750159872 630941873705 1099511627776 12992346881497 26739023275884544 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz11) Bool.true 850951 1048576 69979352 102001278976 850951 1048576 8747419 12750159872 (ep60 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz11)) 741455 1048576 1 1048576 153173 262144 8747419 12750159872 113570886715 274877906944 3246638165219 6684755818971136 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz11) Bool.true 153173 262144 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz11) Bool.true 612692 1048576 69979352 102001278976 153173 262144 8747419 12750159872 (ep64 rfl rfl) rfl)) rfl)

noncomputable abbrev qz546 := (Enclosure.Real.IsNear.const Bool.false 0 1)

noncomputable abbrev qz22 := qz546

noncomputable def ep66 := @ep51 630941873705 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 274877906944 3246638165219 6684755818971136 Bool.false 468569754071 468569754071 1099511627776 12992346881497 26739023275884544 Bool.false 113570886715 113570886715 274877906944 3246638165219 6684755818971136 (ep52 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep53 ep65) rfl rfl

noncomputable abbrev qz547 := (Real.log (Enclosure.sfrac Bool.false 3 1))

noncomputable abbrev qz23 := (@HMul.hMul Real Real Real qz267 qz277 qz547)

noncomputable abbrev qz286 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3)))

noncomputable def ep67 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz7) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23)))) Bool.false 203226863735 549755813888 5303816190991 13369511637942272 Bool.true 487616008145 1099511627776 10610892708717 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 3 qz13 rfl)

noncomputable abbrev qz287 := (Real.sqrt (@Nat.cast Real Real.instNatCast 3))

noncomputable abbrev qz288 := (@Nat.cast Real Real.instNatCast 3)

noncomputable def ep68 := @Enclosure.Real.IsNear.inv_image qz287 1816187 1048576 1 1048576 302697 302698 524288 (@Enclosure.Real.IsNear.of_eq qz287 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz288 qz14)) Bool.false 1816187 1048576 1 1048576 (BSN.sqrt_natCast_div_one 3) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz288 qz14)) Bool.false 1816187 1048576 1 1048576 1816187 1048576 1 1048576 (BSN.sqrt_enclosure 3 1 908093 908094 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep69 := BSN.log_dyadic_bound 1 2 10 9 171633298636800 524288 194552 16925142283965 34459425 575989 3 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base9 (BSN.artanhP 1) (BSN.artanhQ 2) 0 9 16925142283965 171633298636800 34459425 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep70 := nat_lit 447481618661006711759981812633140088178184724751251260302513769403092809900001

noncomputable def ep71 := nat_lit 18237254054877300779212430138868345486890022584838388836214569481246317918289920

noncomputable def ep72 := nat_lit 156743164792234665190765030974392840374911601761675994089509982346991460321

noncomputable def ep73 := nat_lit 1342131369653435665949563907837471478853804351050230428919362288244584446779361

noncomputable def ep74 := nat_lit 820676432469478535064559356249075546910051016317727497629655626656084306323046400

noncomputable def ep75 := BSN.cos_dyadic_bound_f 1881042363 2147483648 3 2 1048576 389484 ep70 ep71 ep72 ep73 ep74 ep72 671386 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1881042363) qz15 0 2 ep70 ep71 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1881042363) qz16 0 2 ep73 ep74 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz289 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4764113) (@Nat.cast Real Real.instNatCast 32768))

noncomputable abbrev qz290 := (BSN.isNear_log_sfrac 3 1 575989 524288 1 194552 Bool.false (BSN.logfrac_isNear 3 1 2 3 1 575989 524288 194552 rfl rfl rfl (ep69 rfl)))

noncomputable abbrev qz291 := (@Nat.cast Real Real.instNatCast 4722366482869645213696)

noncomputable def ep76 := @Enclosure.Real.IsNear.cos_image qz23 qz289 Bool.false 4764113 32768 357 524288 Bool.false 671386 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 76225808271 524288000 132339 194552000 4764113 32768 357 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 132339 1000 0 1 575989 524288 1 194552 76225808271 524288000 132339 194552000 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 4764113 32768) (BSN.cos_reduce0 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4136455903100383789056) qz291) 226375608064910080 72057594037927936 Bool.false 671386 1048576 23 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 4764113 32768 226375608064910080 72057594037927936 23 4136455903100383789056 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 671386 1048576 4136455903100383789056 4722366482869645213696 1881042363 2147483648 389484 389104 (ep75 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep77 := nat_lit 805341519057978293435814650714872644448432575270842927749253176939689464651745

noncomputable def ep78 := nat_lit 164135286493895707012911871249815109382010203263545499525931125331216861264609280

noncomputable def ep79 := nat_lit 2108974013361231912397777132298326956575764030735069716305232447251577278390241

noncomputable def ep80 := nat_lit 3009146919054754628570050972913277005336853726498334157975403964405642456517836800

noncomputable def ep81 := BSN.sin_dyadic_bound_f 1881042363 2147483648 3 2 1048576 389484 ep77 ep78 ep72 ep79 ep80 ep72 805451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1881042363) qz20 0 2 ep77 ep78 ep72 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1881042363) qz21 0 2 ep79 ep80 ep72 rfl rfl rfl rfl) rfl rfl

noncomputable def ep82 := @Enclosure.Real.IsNear.sin_image qz23 qz289 Bool.false 4764113 32768 357 524288 Bool.false 805451 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz23 Bool.false 76225808271 524288000 132339 194552000 4764113 32768 357 524288 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz547 132339 1000 0 1 575989 524288 1 194552 76225808271 524288000 132339 194552000 qz18 qz290 rfl) rfl) (Enclosure.sfrac_false_div 4764113 32768) (BSN.sin_reduce0 qz289 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4136455903100383789056) qz291) 226375608064910080 72057594037927936 Bool.false 805451 1048576 23 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 4764113 32768 226375608064910080 72057594037927936 23 4136455903100383789056 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 805451 1048576 4136455903100383789056 4722366482869645213696 1881042363 2147483648 389484 389104 (ep81 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz292 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 3))) Bool.false 605395 1048576 1 1048576 605395 1048576 1 1048576 (ep68 rfl rfl) rfl)

noncomputable def ep83 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz23)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23))) Bool.false 203226863735 549755813888 5303816190991 13369511637942272 Bool.true 487616008145 1099511627776 10610892708717 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz286 (Real.cos qz23) 605395 1048576 1 1048576 335693 524288 8747419 12750159872 203226863735 549755813888 5303816190991 13369511637942272 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz23) Bool.false 671386 1048576 69979352 102001278976 335693 524288 8747419 12750159872 (ep76 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz286 (@Neg.neg Real Real.instNeg (Real.sin qz23)) 605395 1048576 1 1048576 805451 1048576 8747419 12750159872 487616008145 1099511627776 10610892708717 26739023275884544 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz23) Bool.false 805451 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz23) Bool.false 805451 1048576 69979352 102001278976 805451 1048576 8747419 12750159872 (ep82 rfl rfl) rfl)) rfl)

noncomputable def ep84 := @ep49 203226863735 549755813888 5303816190991 13369511637942272 Bool.true 487616008145 1099511627776 10610892708717 26739023275884544 Bool.false 481049246265683799441408 875023481541 1099511627776 23599979263479 26739023275884544 Bool.true 9162357191312712663040 33332461285 1099511627776 23597445369593 26739023275884544 (ep50 (BSN.head_sum_c_succ qz5 2 3 rfl rfl) (ep66 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep67 ep83) rfl rfl

noncomputable abbrev qz548 := (Real.log (Enclosure.sfrac Bool.false 4 1))

noncomputable abbrev qz24 := (@HMul.hMul Real Real Real qz267 qz277 qz548)

noncomputable abbrev qz293 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4)))

noncomputable def ep85 := @Enclosure.Complex.IsNear.of_eq qz541 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz24)))) Bool.false 174231580127 1099511627776 9193165499615 26739023275884544 Bool.true 521414431527 1099511627776 9209269541415 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 4 qz13 rfl)

noncomputable abbrev qz294 := (Real.sqrt (@Nat.cast Real Real.instNatCast 4))

noncomputable abbrev qz295 := (@Nat.cast Real Real.instNatCast 4)

noncomputable def ep86 := @Enclosure.Real.IsNear.inv_image qz294 2097153 1048576 1 1048576 262143 262144 524288 (@Enclosure.Real.IsNear.of_eq qz294 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 (BSN.sqrt_natCast_div_one 4) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz295 qz14)) Bool.false 2097153 1048576 1 1048576 2097153 1048576 1 1048576 (BSN.sqrt_enclosure 4 1 1048576 1048577 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep87 := nat_lit 318077276165597140789031982421875

noncomputable def ep88 := nat_lit 49379992292270016474244603430625

noncomputable def ep89 := nat_lit 20095619060363156210525625

noncomputable def ep90 := BSN.log_dyadic_bound 3 5 14 13 ep87 524288 194552 ep88 ep89 726817 8 2 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base13 (BSN.artanhP 3) (BSN.artanhQ 5) 0 13 ep88 ep87 ep89 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep91 := nat_lit 1847837689596997294120952943348640662126868254641076883517523987090427084800000

noncomputable def ep92 := nat_lit 2666954631069093632304545687722828985282950413887313905807390677401600000000

noncomputable def ep93 := nat_lit 5538179159528853695098249738670476328410038863095456022740957179916478054400000

noncomputable def ep94 := BSN.cos_dyadic_bound_f 2680723080 2147483648 3 2 1048576 389484 ep91 ep71 ep92 ep93 ep74 ep92 332321 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2680723080) qz15 0 2 ep91 ep71 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2680723080) qz16 0 2 ep93 ep74 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz25 := (@Nat.cast Real Real.instNatCast 1048576)

noncomputable abbrev qz26 := (@Nat.cast Real Real.instNatCast 151115727451828646838272)

noncomputable abbrev qz296 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 192372469) qz25)

noncomputable abbrev qz297 := (BSN.isNear_log_sfrac 4 1 726817 524288 1 194552 Bool.false (BSN.logfrac_isNear 8 2 1 4 1 726817 524288 194552 rfl rfl rfl (ep90 rfl)))

noncomputable def ep95 := @Enclosure.Real.IsNear.cos_image qz24 qz296 Bool.false 192372469 1048576 715 1048576 Bool.false 332321 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 96186234963 524288000 132339 194552000 192372469 1048576 715 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 132339 1000 0 1 726817 524288 1 194552 96186234963 524288000 132339 194552000 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 192372469 1048576) (BSN.cos_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188639116688299747442688) qz26) 226375608064910080 72057594037927936 Bool.false 332321 1048576 29 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 192372469 1048576 226375608064910080 72057594037927936 29 188639116688299747442688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 332321 1048576 188639116688299747442688 151115727451828646838272 2680723080 2147483648 389484 389104 (ep94 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep96 := nat_lit 3323974277569739854511871661477374928640136498022828539206897264220847472640000

noncomputable def ep97 := nat_lit 8701328990899016324507361277517764042367042241770638142075328488053093171200000

noncomputable def ep98 := BSN.sin_dyadic_bound_f 2680723080 2147483648 3 2 1048576 389484 ep96 ep78 ep92 ep97 ep80 ep92 994521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2680723080) qz20 0 2 ep96 ep78 ep92 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2680723080) qz21 0 2 ep97 ep80 ep92 rfl rfl rfl rfl) rfl rfl

noncomputable def ep99 := @Enclosure.Real.IsNear.sin_image qz24 qz296 Bool.false 192372469 1048576 715 1048576 Bool.false 994521 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz24 Bool.false 96186234963 524288000 132339 194552000 192372469 1048576 715 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz548 132339 1000 0 1 726817 524288 1 194552 96186234963 524288000 132339 194552000 qz18 qz297 rfl) rfl) (Enclosure.sfrac_false_div 192372469 1048576) (BSN.sin_reduce0 qz296 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 188639116688299747442688) qz26) 226375608064910080 72057594037927936 Bool.false 994521 1048576 29 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 192372469 1048576 226375608064910080 72057594037927936 29 188639116688299747442688 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 994521 1048576 188639116688299747442688 151115727451828646838272 2680723080 2147483648 389484 389104 (ep98 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz298 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 4))) Bool.false 524287 1048576 1 1048576 524287 1048576 1 1048576 (ep86 rfl rfl) rfl)

noncomputable def ep100 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz24)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz24))) Bool.false 174231580127 1099511627776 9193165499615 26739023275884544 Bool.true 521414431527 1099511627776 9209269541415 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz293 (Real.cos qz24) 524287 1048576 1 1048576 332321 1048576 17519157 25500319744 174231580127 1099511627776 9193165499615 26739023275884544 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz24) Bool.false 332321 1048576 140153256 204002557952 332321 1048576 17519157 25500319744 (ep95 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz293 (@Neg.neg Real Real.instNeg (Real.sin qz24)) 524287 1048576 1 1048576 994521 1048576 17519157 25500319744 521414431527 1099511627776 9209269541415 26739023275884544 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz24) Bool.false 994521 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz24) Bool.false 994521 1048576 140153256 204002557952 994521 1048576 17519157 25500319744 (ep99 rfl rfl) rfl)) rfl)

noncomputable def ep101 := @ep47 174231580127 1099511627776 9193165499615 26739023275884544 Bool.true 521414431527 1099511627776 9209269541415 26739023275884544 Bool.false 1153668140806789941690368 262313765417 274877906944 16396572381547 13369511637942272 Bool.true 609950659119400313946112 138686723203 274877906944 1025209840969 835594477371392 (ep48 (BSN.head_sum_c_succ qz5 3 4 rfl rfl) (ep84 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep85 ep100) rfl rfl

noncomputable abbrev qz549 := (Real.log (Enclosure.sfrac Bool.false 5 1))

noncomputable abbrev qz27 := (@HMul.hMul Real Real Real qz267 qz277 qz549)

noncomputable abbrev qz299 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5)))

noncomputable def ep102 := @Enclosure.Complex.IsNear.of_eq qz540 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz27)))) Bool.false 197619899477 549755813888 1029486939983 3342377909485568 Bool.false 292523369537 1099511627776 8230568661785 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 5 qz13 rfl)

noncomputable abbrev qz300 := (Real.sqrt (@Nat.cast Real Real.instNatCast 5))

noncomputable abbrev qz301 := (@Nat.cast Real Real.instNatCast 5)

noncomputable def ep103 := @Enclosure.Real.IsNear.inv_image qz300 2344687 1048576 1 1048576 234468 234469 524288 (@Enclosure.Real.IsNear.of_eq qz300 (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 (BSN.sqrt_natCast_div_one 5) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz301 qz14)) Bool.false 2344687 1048576 1 1048576 2344687 1048576 1 1048576 (BSN.sqrt_enclosure 5 1 1172343 1172344 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep104 := nat_lit 3696382175741467532940033205863946875

noncomputable def ep105 := nat_lit 765440954430599474856563326857688500

noncomputable def ep106 := nat_lit 108794268166472120024432640000

noncomputable def ep107 := BSN.log_dyadic_bound 2 3 18 17 ep104 524288 194552 ep105 ep106 843808 5 1 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_rec (BSN.artanhP 2) (BSN.artanhQ 3) 0 17 8 307084260767580 1483365253795425 132843110400 1663129201793174588340 2491889415829100854875 818968088287641600 ep105 ep104 ep106 rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base8 (BSN.artanhP 2) (BSN.artanhQ 3) 0 8 307084260767580 1483365253795425 132843110400 rfl rfl rfl rfl) (@BSN.binarySplit_of_base9 (BSN.artanhP 2) (BSN.artanhQ 3) 8 17 1663129201793174588340 2491889415829100854875 818968088287641600 rfl rfl rfl rfl)) rfl rfl

noncomputable def ep108 := nat_lit 1039602373265328794538052583333383794226582118408420263070477379001414152355840

noncomputable def ep109 := nat_lit 261164291095610473109284212176473316906450892403544625341342006781920935936

noncomputable def ep110 := nat_lit 2722345283033134902071770305720100409032723675339113997695935724611771098464256

noncomputable def ep111 := BSN.sin_dyadic_bound_f 2004999296 2147483648 3 2 1048576 389484 ep108 ep78 ep109 ep110 ep80 ep109 842842 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2004999296) qz20 0 2 ep108 ep78 ep109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2004999296) qz21 0 2 ep110 ep80 ep109 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz302 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 223337413) qz25)

noncomputable abbrev qz303 := (BSN.isNear_log_sfrac 5 1 843808 524288 1 194552 Bool.false (BSN.logfrac_isNear 5 1 2 5 1 843808 524288 194552 rfl rfl rfl (ep107 rfl rfl)))

noncomputable def ep112 := @Enclosure.Real.IsNear.cos_image qz27 qz302 Bool.false 223337413 1048576 715 1048576 Bool.false 842842 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 3489647091 16384000 132339 194552000 223337413 1048576 715 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 132339 1000 0 1 843808 524288 1 194552 3489647091 16384000 132339 194552000 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 223337413 1048576) (BSN.cos_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141089282563492687118336) qz26) 226375608064910080 72057594037927936 Bool.false 842842 1048576 33 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 223337413 1048576 226375608064910080 72057594037927936 33 141089282563492687118336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 842842 1048576 141089282563492687118336 151115727451828646838272 2004999296 2147483648 389484 389104 (ep111 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep113 := nat_lit 577672947054558490509188894835069429377837377290190610428194695892688716169216

noncomputable def ep114 := nat_lit 1732496512581484250581348116080855341499699230085764742033901403664502306635776

noncomputable def ep115 := BSN.cos_dyadic_bound_f 2004999296 2147483648 3 2 1048576 389484 ep113 ep71 ep109 ep114 ep74 ep109 623801 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2004999296) qz15 0 2 ep113 ep71 ep109 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2004999296) qz16 0 2 ep114 ep74 ep109 rfl rfl rfl rfl) rfl rfl

noncomputable def ep116 := @Enclosure.Real.IsNear.sin_image qz27 qz302 Bool.false 223337413 1048576 715 1048576 Bool.true 623801 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz27 Bool.false 3489647091 16384000 132339 194552000 223337413 1048576 715 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz12 qz549 132339 1000 0 1 843808 524288 1 194552 3489647091 16384000 132339 194552000 qz18 qz303 rfl) rfl) (Enclosure.sfrac_false_div 223337413 1048576) (BSN.sin_reduce3 qz302 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 141089282563492687118336) qz26) 226375608064910080 72057594037927936 Bool.false 623801 1048576 33 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 223337413 1048576 226375608064910080 72057594037927936 33 141089282563492687118336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 623801 1048576 141089282563492687118336 151115727451828646838272 2004999296 2147483648 389484 389104 (ep115 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz304 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 5))) Bool.false 468937 1048576 1 1048576 468937 1048576 1 1048576 (ep103 rfl rfl) rfl)

noncomputable def ep117 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz27)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz27))) Bool.false 197619899477 549755813888 1029486939983 3342377909485568 Bool.false 292523369537 1099511627776 8230568661785 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz299 (Real.cos qz27) 468937 1048576 1 1048576 421421 524288 17519157 25500319744 197619899477 549755813888 1029486939983 3342377909485568 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz27) Bool.false 842842 1048576 140153256 204002557952 421421 524288 17519157 25500319744 (ep112 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz299 (@Neg.neg Real Real.instNeg (Real.sin qz27)) 468937 1048576 1 1048576 623801 1048576 17519157 25500319744 292523369537 1099511627776 8230568661785 26739023275884544 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz27) Bool.true 623801 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz27) Bool.true 623801 1048576 140153256 204002557952 623801 1048576 17519157 25500319744 (ep116 rfl rfl) rfl)) rfl)

noncomputable def ep118 := @ep45 197619899477 549755813888 1029486939983 3342377909485568 Bool.false 292523369537 1099511627776 8230568661785 26739023275884544 Bool.false 198529861939570182979584 722247430311 549755813888 20514520141479 13369511637942272 Bool.true 72079453229313268121600 262223523275 1099511627776 41037283572793 26739023275884544 (ep46 (BSN.head_sum_c_succ qz5 4 5 rfl rfl) (ep101 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep102 ep117) rfl rfl

noncomputable abbrev qz550 := (Real.log (Enclosure.sfrac Bool.false 6 1))

noncomputable abbrev qz28 := (@HMul.hMul Real Real Real qz267 qz277 qz550)

noncomputable abbrev qz305 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6)))

noncomputable def ep119 := @Enclosure.Complex.IsNear.of_eq qz539 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz28)))) Bool.true 15857330397 549755813888 3750701212997 13369511637942272 Bool.false 447751370445 1099511627776 7525037308205 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 6 qz13 rfl)

noncomputable abbrev qz306 := (Real.sqrt (@Nat.cast Real Real.instNatCast 6))

noncomputable abbrev qz307 := (@Nat.cast Real Real.instNatCast 6)

noncomputable abbrev qz551 := (@HDiv.hDiv Real Real Real qz1 qz307 qz14)

noncomputable def ep120 := @Enclosure.Real.IsNear.inv_image qz306 2568477 1048576 1 1048576 214039 214040 524288 (@Enclosure.Real.IsNear.of_eq qz306 (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 (BSN.sqrt_natCast_div_one 6) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz551) Bool.false 2568477 1048576 1 1048576 2568477 1048576 1 1048576 (BSN.sqrt_enclosure 6 1 1284238 1284239 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep121 := BSN.log_dyadic_bound 2 10 4 3 105000000 524288 194552 1434560 960 212580 12 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 10) 0 3 1434560 105000000 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep122 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz550 132339 1000 0 1 4034681531866359 2251799813685248 62500000024319 12159500000000000000 533945719245662083701 2251799813685248000 8271187503218352141 12159500000000000000000 qz18 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000389104 194552000000000000000 4034681531866359 2251799813685248 62500000024319 12159500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep123 := nat_lit 3859365711227162353811407160562688560316917286485825056227367087302823116800000

noncomputable def ep124 := nat_lit 11597392108220628202511961223418020251708816556231974676129046436249600000000

noncomputable def ep125 := nat_lit 11554902349465045805029197559241229640447334226345011219329843169035970150400000

noncomputable def ep126 := BSN.cos_dyadic_bound_f 3221402880 2147483648 3 2 1048576 389484 ep123 ep71 ep124 ep125 ep74 ep124 74086 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3221402880) qz15 0 2 ep123 ep71 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3221402880) qz16 0 2 ep125 ep74 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz308 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 124318925) qz17)

noncomputable def ep127 := @Enclosure.Real.IsNear.cos_image qz28 qz308 Bool.false 124318925 524288 715 1048576 Bool.true 74086 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 533945719245662083701 2251799813685248000 8271187503218352141 12159500000000000000000 124318925 524288 715 1048576 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 124318925 524288) (BSN.cos_reduce2 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113343037592884058521600) qz19) 226375608064910080 72057594037927936 Bool.false 74086 1048576 37 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 124318925 524288 226375608064910080 72057594037927936 37 113343037592884058521600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 74086 1048576 113343037592884058521600 75557863725914323419136 3221402880 2147483648 389484 389104 (ep126 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep128 := nat_lit 6937580366522315734298523320034104992369084062429499521468357519996081930240000

noncomputable def ep129 := nat_lit 18151076610811803048930160758108550566273405889081456501989108381950096179200000

noncomputable def ep130 := BSN.sin_dyadic_bound_f 3221402880 2147483648 3 2 1048576 389484 ep128 ep78 ep124 ep129 ep80 ep124 1045955 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3221402880) qz20 0 2 ep128 ep78 ep124 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3221402880) qz21 0 2 ep129 ep80 ep124 rfl rfl rfl rfl) rfl rfl

noncomputable def ep131 := @Enclosure.Real.IsNear.sin_image qz28 qz308 Bool.false 124318925 524288 715 1048576 Bool.true 1045955 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz28 Bool.false 533945719245662083701 2251799813685248000 8271187503218352141 12159500000000000000000 124318925 524288 715 1048576 (ep122 rfl) rfl) (Enclosure.sfrac_false_div 124318925 524288) (BSN.sin_reduce2 qz308 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113343037592884058521600) qz19) 226375608064910080 72057594037927936 Bool.false 1045955 1048576 37 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 124318925 524288 226375608064910080 72057594037927936 37 113343037592884058521600 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1045955 1048576 113343037592884058521600 75557863725914323419136 3221402880 2147483648 389484 389104 (ep130 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz309 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 6))) Bool.false 428079 1048576 1 1048576 428079 1048576 1 1048576 (ep120 rfl rfl) rfl)

noncomputable def ep132 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz28)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz28))) Bool.true 15857330397 549755813888 3750701212997 13369511637942272 Bool.false 447751370445 1099511627776 7525037308205 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz28) 428079 1048576 1 1048576 37043 524288 17519157 25500319744 15857330397 549755813888 3750701212997 13369511637942272 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz28) Bool.true 74086 1048576 140153256 204002557952 37043 524288 17519157 25500319744 (ep127 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz305 (@Neg.neg Real Real.instNeg (Real.sin qz28)) 428079 1048576 1 1048576 1045955 1048576 17519157 25500319744 447751370445 1099511627776 7525037308205 26739023275884544 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz28) Bool.true 1045955 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz28) Bool.true 1045955 1048576 140153256 204002557952 1045955 1048576 17519157 25500319744 (ep131 rfl rfl) rfl)) rfl)

noncomputable def ep133 := @ep43 15857330397 549755813888 3750701212997 13369511637942272 Bool.false 447751370445 1099511627776 7525037308205 26739023275884544 Bool.false 388342064300646708805632 353195049957 274877906944 6066305338619 3342377909485568 Bool.false 203990025239663654993920 92763923585 549755813888 24281160440499 13369511637942272 (ep44 (BSN.head_sum_c_succ qz5 5 6 rfl rfl) (ep118 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep119 ep132) rfl rfl

noncomputable abbrev qz552 := (Real.log (Enclosure.sfrac Bool.false 7 1))

noncomputable abbrev qz29 := (@HMul.hMul Real Real Real qz267 qz277 qz552)

noncomputable abbrev qz310 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7)))

noncomputable def ep134 := @Enclosure.Complex.IsNear.of_eq qz538 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz29)))) Bool.false 103464208175 274877906944 869881742559 3342377909485568 Bool.false 590127925 17179869184 1733994167153 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 7 qz13 rfl)

noncomputable abbrev qz311 := (Real.sqrt (@Nat.cast Real Real.instNatCast 7))

noncomputable abbrev qz312 := (@Nat.cast Real Real.instNatCast 7)

noncomputable abbrev qz553 := (@HDiv.hDiv Real Real Real qz1 qz312 qz14)

noncomputable def ep135 := @Enclosure.Real.IsNear.inv_image qz311 2774271 1048576 1 1048576 198162 198163 524288 (@Enclosure.Real.IsNear.of_eq qz311 (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 (BSN.sqrt_natCast_div_one 7) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz553) Bool.false 2774271 1048576 1 1048576 2774271 1048576 1 1048576 (BSN.sqrt_enclosure 7 1 1387135 1387136 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep136 := BSN.log_dyadic_bound 3 11 5 4 202569142545 524288 194552 5259111624 688905 293399 14 8 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 3) (BSN.artanhQ 11) 0 4 5259111624 202569142545 688905 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep137 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz552 132339 1000 0 1 4381796493761783 2251799813685248 62500000024319 12159500000000000000 579882566187940600437 2251799813685248000 8271187503218352141 12159500000000000000000 qz18 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000389104 194552000000000000000 4381796493761783 2251799813685248 62500000024319 12159500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep138 := nat_lit 6569134122591783073357732753091623758001473671859820327126734527311741383147520

noncomputable def ep139 := nat_lit 10400100596207777002914681900052911898580582315717608457182168763506580586496

noncomputable def ep140 := nat_lit 17188036824870333553170295344544643223120443435883605681163152631627931063484416

noncomputable def ep141 := BSN.sin_dyadic_bound_f 3177822916 2147483648 3 2 1048576 389484 ep138 ep78 ep139 ep140 ep80 ep139 1044236 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3177822916) qz20 0 2 ep138 ep78 ep139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3177822916) qz21 0 2 ep140 ep80 ep139 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz313 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 135014431) qz17)

noncomputable def ep142 := @Enclosure.Real.IsNear.cos_image qz29 qz313 Bool.false 135014431 524288 357 524288 Bool.false 1044236 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 579882566187940600437 2251799813685248000 8271187503218352141 12159500000000000000000 135014431 524288 357 524288 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 135014431 524288) (BSN.cos_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111809703934566504333312) qz19) 226375608064910080 72057594037927936 Bool.false 1044236 1048576 40 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 135014431 524288 226375608064910080 72057594037927936 40 111809703934566504333312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1044236 1048576 111809703934566504333312 75557863725914323419136 3177822916 2147483648 389484 389104 (ep141 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep143 := nat_lit 3654141223927082941644480277006481159733521187617996896606933479068081470898176

noncomputable def ep144 := nat_lit 10941623470588833270927611467219337655403402398222555472906436099677231251521536

noncomputable def ep145 := BSN.cos_dyadic_bound_f 3177822916 2147483648 3 2 1048576 389484 ep143 ep71 ep139 ep144 ep74 ep139 95296 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3177822916) qz15 0 2 ep143 ep71 ep139 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3177822916) qz16 0 2 ep144 ep74 ep139 rfl rfl rfl rfl) rfl rfl

noncomputable def ep146 := @Enclosure.Real.IsNear.sin_image qz29 qz313 Bool.false 135014431 524288 357 524288 Bool.true 95296 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz29 Bool.false 579882566187940600437 2251799813685248000 8271187503218352141 12159500000000000000000 135014431 524288 357 524288 (ep137 rfl) rfl) (Enclosure.sfrac_false_div 135014431 524288) (BSN.sin_reduce3 qz313 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 111809703934566504333312) qz19) 226375608064910080 72057594037927936 Bool.false 95296 1048576 40 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 135014431 524288 226375608064910080 72057594037927936 40 111809703934566504333312 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 95296 1048576 111809703934566504333312 75557863725914323419136 3177822916 2147483648 389484 389104 (ep145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz314 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 7))) Bool.false 396325 1048576 1 1048576 396325 1048576 1 1048576 (ep135 rfl rfl) rfl)

noncomputable def ep147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz29)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz29))) Bool.false 103464208175 274877906944 869881742559 3342377909485568 Bool.false 590127925 17179869184 1733994167153 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz310 (Real.cos qz29) 396325 1048576 1 1048576 261059 262144 8747419 12750159872 103464208175 274877906944 869881742559 3342377909485568 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz29) Bool.false 1044236 1048576 69979352 102001278976 261059 262144 8747419 12750159872 (ep142 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz29)) 396325 1048576 1 1048576 1489 16384 8747419 12750159872 590127925 17179869184 1733994167153 6684755818971136 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz29) Bool.true 1489 16384 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz29) Bool.true 95296 1048576 69979352 102001278976 1489 16384 8747419 12750159872 (ep146 rfl rfl) rfl)) rfl)

noncomputable def ep148 := @ep41 103464208175 274877906944 869881742559 3342377909485568 Bool.false 590127925 17179869184 1733994167153 6684755818971136 Bool.false 125525541061923971268608 114164814533 68719476736 3468093540589 1671188954742784 Bool.false 1918098329891283927040 111648017185 549755813888 27749148774805 13369511637942272 (ep42 (BSN.head_sum_c_succ qz5 6 7 rfl rfl) (ep133 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep134 ep147) rfl rfl

noncomputable abbrev qz554 := (Real.log (Enclosure.sfrac Bool.false 8 1))

noncomputable abbrev qz30 := (@HMul.hMul Real Real Real qz267 qz277 qz554)

noncomputable abbrev qz315 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8)))

noncomputable def ep149 := @Enclosure.Complex.IsNear.of_eq qz537 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz30)))) Bool.false 57784105309 549755813888 3246703680605 13369511637942272 Bool.false 371158896955 1099511627776 6510173633699 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 8 qz13 rfl)

noncomputable abbrev qz316 := (Real.sqrt (@Nat.cast Real Real.instNatCast 8))

noncomputable abbrev qz317 := (@Nat.cast Real Real.instNatCast 8)

noncomputable abbrev qz555 := (@HDiv.hDiv Real Real Real qz1 qz317 qz14)

noncomputable def ep150 := @Enclosure.Real.IsNear.inv_image qz316 2965821 1048576 1 1048576 185363 185364 524288 (@Enclosure.Real.IsNear.of_eq qz316 (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 (BSN.sqrt_natCast_div_one 8) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz555) Bool.false 2965821 1048576 1 1048576 2965821 1048576 1 1048576 (BSN.sqrt_enclosure 8 1 1482910 1482911 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep151 := BSN.log_dyadic_bound 0 16 1 0 1 524288 194552 0 1 0 16 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 16) 0 0 rfl) rfl rfl rfl

noncomputable def ep152 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz554 132339 1000 0 1 9364972152248037 4503599627370496 125000000072957 24319000000000000000 1239351049656352968543 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000583656 194552000000000000000 9364972152248037 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep153 := nat_lit 176571709796730451734082442077515441

noncomputable def ep154 := BSN.sin_dyadic_bound_f 648231723 2147483648 2 1 1048576 389484 ep153 ep61 ep153 ep153 ep62 ep153 311734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 648231723) qz20 0 1 ep153 ep61 ep153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 648231723) qz21 0 1 ep153 ep62 ep153 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz318 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144279451) qz17)

noncomputable def ep155 := @Enclosure.Real.IsNear.cos_image qz30 qz318 Bool.false 144279451 524288 357 524288 Bool.false 311734 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 1239351049656352968543 4503599627370496000 16542375009655056423 24319000000000000000000 144279451 524288 357 524288 (ep152 rfl) rfl) (Enclosure.sfrac_false_div 144279451 524288) (BSN.cos_reduce3 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22807626147505763254272) qz19) 226375608064910080 72057594037927936 Bool.false 311734 1048576 43 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 144279451 524288 226375608064910080 72057594037927936 43 22807626147505763254272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 311734 1048576 22807626147505763254272 75557863725914323419136 648231723 2147483648 389484 389104 (ep154 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep156 := BSN.cos_dyadic_bound_f 648231723 2147483648 2 1 1048576 389484 ep153 ep57 ep153 ep153 ep58 ep153 1001165 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 648231723) qz15 0 1 ep153 ep57 ep153 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 648231723) qz16 0 1 ep153 ep58 ep153 rfl rfl rfl rfl) rfl rfl

noncomputable def ep157 := @Enclosure.Real.IsNear.sin_image qz30 qz318 Bool.false 144279451 524288 357 524288 Bool.true 1001165 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz30 Bool.false 1239351049656352968543 4503599627370496000 16542375009655056423 24319000000000000000000 144279451 524288 357 524288 (ep152 rfl) rfl) (Enclosure.sfrac_false_div 144279451 524288) (BSN.sin_reduce3 qz318 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22807626147505763254272) qz19) 226375608064910080 72057594037927936 Bool.false 1001165 1048576 43 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 144279451 524288 226375608064910080 72057594037927936 43 22807626147505763254272 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1001165 1048576 22807626147505763254272 75557863725914323419136 648231723 2147483648 389484 389104 (ep156 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz319 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 8))) Bool.false 370727 1048576 1 1048576 370727 1048576 1 1048576 (ep150 rfl rfl) rfl)

noncomputable def ep158 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz30)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz30))) Bool.false 57784105309 549755813888 3246703680605 13369511637942272 Bool.false 371158896955 1099511627776 6510173633699 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz315 (Real.cos qz30) 370727 1048576 1 1048576 155867 524288 8747419 12750159872 57784105309 549755813888 3246703680605 13369511637942272 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz30) Bool.false 311734 1048576 69979352 102001278976 155867 524288 8747419 12750159872 (ep155 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz315 (@Neg.neg Real Real.instNeg (Real.sin qz30)) 370727 1048576 1 1048576 1001165 1048576 8747419 12750159872 371158896955 1099511627776 6510173633699 26739023275884544 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz30) Bool.true 1001165 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz30) Bool.true 1001165 1048576 69979352 102001278976 1001165 1048576 8747419 12750159872 (ep157 rfl rfl) rfl)) rfl)

noncomputable def ep159 := @ep39 57784105309 549755813888 3246703680605 13369511637942272 Bool.false 371158896955 1099511627776 6510173633699 26739023275884544 Bool.false 66733664011454385225728 971102621573 549755813888 30991452005317 13369511637942272 Bool.false 326805054590310521241600 594454931325 1099511627776 62008471183309 26739023275884544 (ep40 (BSN.head_sum_c_succ qz5 7 8 rfl rfl) (ep148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep149 ep158) rfl rfl

theorem EMRow45.d6 : Enclosure.Complex.IsNear qz3 Bool.false 971102621573 549755813888 30991452005317 13369511637942272 Bool.false 594454931325 1099511627776 62008471183309 26739023275884544 := ep38 (BSN.head_sum_c_succ qz5 8 9 rfl rfl) (ep159 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz31 := (BSN.headSumC qz271 17)

noncomputable abbrev qz556 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz7)

noncomputable def ep160 := @Enclosure.Complex.IsNear.of_eq qz31 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 16) qz556) Bool.false 1134916158007 1099511627776 104214457420255 26739023275884544 Bool.true 157955903609 1099511627776 104164829491041 26739023275884544

noncomputable def ep161 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 16) qz556 Bool.false 1354616109163 1099511627776 99607909048235 26739023275884544 Bool.false 3619244279 549755813888 49781668799229 13369511637942272 Bool.true

noncomputable abbrev qz557 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz7)

noncomputable def ep162 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 15) qz557) Bool.false 1354616109163 1099511627776 99607909048235 26739023275884544 Bool.false 3619244279 549755813888 49781668799229 13369511637942272

noncomputable def ep163 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 15) qz557 Bool.false 1078783012435 1099511627776 94839961051989 26739023275884544 Bool.false 74402020651 1099511627776 94814133106677 26739023275884544 Bool.false

noncomputable abbrev qz558 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz7)

noncomputable def ep164 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 14) qz558) Bool.false 1078783012435 1099511627776 94839961051989 26739023275884544 Bool.false 74402020651 1099511627776 94814133106677 26739023275884544

noncomputable def ep165 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 14) qz558 Bool.false 1331845804351 1099511627776 89915177322689 26739023275884544 Bool.true 74965256405 1099511627776 89898347893757 26739023275884544 Bool.true

noncomputable abbrev qz559 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz7)

noncomputable def ep166 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 13) qz559) Bool.false 1331845804351 1099511627776 89915177322689 26739023275884544 Bool.true 74965256405 1099511627776 89898347893757 26739023275884544

noncomputable def ep167 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 13) qz559 Bool.false 1030347273667 1099511627776 84802046854325 26739023275884544 Bool.true 29215308629 1099511627776 84806603456717 26739023275884544 Bool.false

noncomputable abbrev qz560 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz7)

noncomputable def ep168 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 12) qz560) Bool.false 1030347273667 1099511627776 84802046854325 26739023275884544 Bool.true 29215308629 1099511627776 84806603456717 26739023275884544

noncomputable def ep169 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 12) qz560 Bool.false 1197195676249 1099511627776 79485628290025 26739023275884544 Bool.false 240793442341 1099511627776 79481896879941 26739023275884544 Bool.true

noncomputable abbrev qz561 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz7)

noncomputable def ep170 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 11) qz561) Bool.false 1197195676249 1099511627776 79485628290025 26739023275884544 Bool.false 240793442341 1099511627776 79481896879941 26739023275884544

noncomputable def ep171 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 11) qz561 Bool.false 1528517462911 1099511627776 73929009812467 26739023275884544 Bool.false 229495888103 1099511627776 73949894872391 26739023275884544 Bool.true

noncomputable abbrev qz562 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz7)

noncomputable def ep172 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 10) qz562) Bool.false 1528517462911 1099511627776 73929009812467 26739023275884544 Bool.false 229495888103 1099511627776 73949894872391 26739023275884544

noncomputable def ep173 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 10) qz562 Bool.false 1876185213521 1099511627776 68102398251737 26739023275884544 Bool.false 116973403625 549755813888 34074227553017 13369511637942272 Bool.true

noncomputable abbrev qz563 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz7)

noncomputable def ep174 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 10) (@HAdd.hAdd Complex Complex Complex qz4 qz3 qz563) Bool.false 1876185213521 1099511627776 68102398251737 26739023275884544 Bool.false 116973403625 549755813888 34074227553017 13369511637942272

noncomputable def ep175 := @Enclosure.Complex.IsNear.addLitP qz3 qz563 Bool.false 971102621573 549755813888 30991452005317 13369511637942272 Bool.false 594454931325 1099511627776 62008471183309 26739023275884544 Bool.true

noncomputable abbrev qz564 := (Real.log (Enclosure.sfrac Bool.false 9 1))

noncomputable abbrev qz32 := (@HMul.hMul Real Real Real qz267 qz277 qz564)

noncomputable abbrev qz320 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9)))

noncomputable def ep176 := @Enclosure.Complex.IsNear.of_eq qz563 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz32)))) Bool.true 66020029625 1099511627776 6119494241103 26739023275884544 Bool.true 360508124075 1099511627776 6139983922725 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 9 qz13 rfl)

noncomputable abbrev qz321 := (Real.sqrt (@Nat.cast Real Real.instNatCast 9))

noncomputable abbrev qz322 := (@Nat.cast Real Real.instNatCast 9)

noncomputable abbrev qz565 := (@HDiv.hDiv Real Real Real qz1 qz322 qz14)

noncomputable def ep177 := @Enclosure.Real.IsNear.inv_image qz321 3145729 1048576 1 1048576 174762 174763 524288 (@Enclosure.Real.IsNear.of_eq qz321 (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 (BSN.sqrt_natCast_div_one 9) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz565) Bool.false 3145729 1048576 1 1048576 3145729 1048576 1 1048576 (BSN.sqrt_enclosure 9 1 1572864 1572865 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep178 := BSN.log_dyadic_bound 1 17 3 2 1252815 524288 194552 1448 3 61752 18 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 1) (BSN.artanhQ 17) 0 2 1448 1252815 3 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep179 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz564 132339 1000 0 1 9895417793173221 4503599627370496 125000000072957 24319000000000000000 1309549695330750893919 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000583656 194552000000000000000 9895417793173221 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep180 := nat_lit 22888738669298049189518867313401521

noncomputable def ep181 := BSN.sin_dyadic_bound_f 388960469 2147483648 2 1 1048576 389484 ep180 ep61 ep180 ep180 ep62 ep180 188885 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 388960469) qz20 0 1 ep180 ep61 ep180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 388960469) qz21 0 1 ep180 ep62 ep180 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz323 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 152451649) qz17)

noncomputable def ep182 := @Enclosure.Real.IsNear.cos_image qz32 qz323 Bool.false 152451649 524288 357 524288 Bool.true 188885 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 1309549695330750893919 4503599627370496000 16542375009655056423 24319000000000000000000 152451649 524288 357 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 152451649 524288) (BSN.cos_reduce1 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13685329899283208470528) qz19) 226375608064910080 72057594037927936 Bool.false 188885 1048576 46 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 152451649 524288 226375608064910080 72057594037927936 46 13685329899283208470528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 188885 1048576 13685329899283208470528 75557863725914323419136 388960469 2147483648 389484 389104 (ep181 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep183 := BSN.cos_dyadic_bound_f 388960469 2147483648 2 1 1048576 389484 ep180 ep57 ep180 ep180 ep58 ep180 1031423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 388960469) qz15 0 1 ep180 ep57 ep180 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 388960469) qz16 0 1 ep180 ep58 ep180 rfl rfl rfl rfl) rfl rfl

noncomputable def ep184 := @Enclosure.Real.IsNear.sin_image qz32 qz323 Bool.false 152451649 524288 357 524288 Bool.false 1031423 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz32 Bool.false 1309549695330750893919 4503599627370496000 16542375009655056423 24319000000000000000000 152451649 524288 357 524288 (ep179 rfl) rfl) (Enclosure.sfrac_false_div 152451649 524288) (BSN.sin_reduce1 qz323 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13685329899283208470528) qz19) 226375608064910080 72057594037927936 Bool.false 1031423 1048576 46 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 152451649 524288 226375608064910080 72057594037927936 46 13685329899283208470528 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1031423 1048576 13685329899283208470528 75557863725914323419136 388960469 2147483648 389484 389104 (ep183 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz324 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 9))) Bool.false 349525 1048576 1 1048576 349525 1048576 1 1048576 (ep177 rfl rfl) rfl)

noncomputable def ep185 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz32)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz32))) Bool.true 66020029625 1099511627776 6119494241103 26739023275884544 Bool.true 360508124075 1099511627776 6139983922725 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz320 (Real.cos qz32) 349525 1048576 1 1048576 188885 1048576 8747419 12750159872 66020029625 1099511627776 6119494241103 26739023275884544 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz32) Bool.true 188885 1048576 69979352 102001278976 188885 1048576 8747419 12750159872 (ep182 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz320 (@Neg.neg Real Real.instNeg (Real.sin qz32)) 349525 1048576 1 1048576 1031423 1048576 8747419 12750159872 360508124075 1099511627776 6139983922725 26739023275884544 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz32) Bool.false 1031423 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz32) Bool.false 1031423 1048576 69979352 102001278976 1031423 1048576 8747419 12750159872 (ep184 rfl rfl) rfl)) rfl)

noncomputable def ep186 := @ep175 66020029625 1099511627776 6119494241103 26739023275884544 Bool.true 360508124075 1099511627776 6139983922725 26739023275884544 Bool.false 1031443729063868417179648 1876185213521 1099511627776 68102398251737 26739023275884544 Bool.false 257227234852445618176000 116973403625 549755813888 34074227553017 13369511637942272 EMRow45.d6 (ep176 ep185) rfl rfl

noncomputable abbrev qz33 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 10)))

noncomputable abbrev qz566 := (Real.log (Enclosure.sfrac Bool.false 10 1))

noncomputable abbrev qz34 := (@HMul.hMul Real Real Real qz267 qz277 qz566)

noncomputable def ep187 := @Enclosure.Complex.IsNear.of_eq qz562 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)))) Bool.true 173833875305 549755813888 2913305780365 13369511637942272 Bool.true 4450919147 1099511627776 5801439766357 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 10 qz13 rfl)

noncomputable abbrev qz325 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10) qz14)

noncomputable def ep188 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) 3315889 1048576 1 1048576 165794 165795 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 10)) (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 (BSN.sqrt_natCast_div_one 10) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz325) Bool.false 3315889 1048576 1 1048576 3315889 1048576 1 1048576 (BSN.sqrt_enclosure 10 1 1657944 1657945 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep189 := BSN.log_dyadic_bound 2 18 3 2 1574640 524288 194552 6528 48 116991 20 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 18) 0 2 6528 1574640 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep190 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz566 132339 1000 0 1 10369917190100709 4503599627370496 125000000072957 24319000000000000000 1372344471020737728351 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000583656 194552000000000000000 10369917190100709 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep191 := nat_lit 8074759097948956846160176153924339179500338528376157864139610638632716456755200

noncomputable def ep192 := nat_lit 15702395956528771021586429037677628985840995915236436620421919121457513824256

noncomputable def ep193 := nat_lit 21122755663079554682098845232312267404142858342836697318218297136889040459595776

noncomputable def ep194 := BSN.sin_dyadic_bound_f 3345767364 2147483648 3 2 1048576 389484 ep191 ep78 ep192 ep193 ep80 ep192 1048490 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3345767364) qz20 0 2 ep191 ep78 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3345767364) qz21 0 2 ep193 ep80 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz326 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 159761923) qz17)

noncomputable def ep195 := @Enclosure.Real.IsNear.cos_image qz34 qz326 Bool.false 159761923 524288 357 524288 Bool.true 1048490 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 1372344471020737728351 4503599627370496000 16542375009655056423 24319000000000000000000 159761923 524288 357 524288 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 159761923 524288) (BSN.cos_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117718723886237809115136) qz19) 226375608064910080 72057594037927936 Bool.false 1048490 1048576 48 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 159761923 524288 226375608064910080 72057594037927936 48 117718723886237809115136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048490 1048576 117718723886237809115136 75557863725914323419136 3345767364 2147483648 389484 389104 (ep194 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep196 := nat_lit 4492956119285655479431914053974711823716117402837970563019971207738823593230336

noncomputable def ep197 := nat_lit 13447463565943908896252569303848780213176670216683438815819069784973555752042496

noncomputable def ep198 := BSN.cos_dyadic_bound_f 3345767364 2147483648 3 2 1048576 389484 ep196 ep71 ep192 ep197 ep74 ep192 13423 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3345767364) qz15 0 2 ep196 ep71 ep192 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3345767364) qz16 0 2 ep197 ep74 ep192 rfl rfl rfl rfl) rfl rfl

noncomputable def ep199 := @Enclosure.Real.IsNear.sin_image qz34 qz326 Bool.false 159761923 524288 357 524288 Bool.false 13423 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz34 Bool.false 1372344471020737728351 4503599627370496000 16542375009655056423 24319000000000000000000 159761923 524288 357 524288 (ep190 rfl) rfl) (Enclosure.sfrac_false_div 159761923 524288) (BSN.sin_reduce1 qz326 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117718723886237809115136) qz19) 226375608064910080 72057594037927936 Bool.false 13423 1048576 48 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 159761923 524288 226375608064910080 72057594037927936 48 117718723886237809115136 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 13423 1048576 117718723886237809115136 75557863725914323419136 3345767364 2147483648 389484 389104 (ep198 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz327 := (@Enclosure.Real.IsNear.recentre' qz33 Bool.false 331589 1048576 1 1048576 331589 1048576 1 1048576 (ep188 rfl rfl) rfl)

noncomputable def ep200 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz34)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34))) Bool.true 173833875305 549755813888 2913305780365 13369511637942272 Bool.true 4450919147 1099511627776 5801439766357 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz34) 331589 1048576 1 1048576 524245 524288 8747419 12750159872 173833875305 549755813888 2913305780365 13369511637942272 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz34) Bool.true 1048490 1048576 69979352 102001278976 524245 524288 8747419 12750159872 (ep195 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz34)) 331589 1048576 1 1048576 13423 1048576 8747419 12750159872 4450919147 1099511627776 5801439766357 26739023275884544 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz34) Bool.false 13423 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz34) Bool.false 13423 1048576 69979352 102001278976 13423 1048576 8747419 12750159872 (ep199 rfl rfl) rfl)) rfl)

noncomputable def ep201 := @ep173 173833875305 549755813888 2913305780365 13369511637942272 Bool.true 4450919147 1099511627776 5801439766357 26739023275884544 Bool.false 840311361864657658707968 1528517462911 1099511627776 73929009812467 26739023275884544 Bool.false 126166698748014141374464 229495888103 1099511627776 73949894872391 26739023275884544 (ep174 (BSN.head_sum_c_succ qz5 9 10 rfl rfl) (ep186 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep187 ep200) rfl rfl

noncomputable abbrev qz35 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 11)))

noncomputable abbrev qz567 := (Real.log (Enclosure.sfrac Bool.false 11 1))

noncomputable abbrev qz36 := (@HMul.hMul Real Real Real qz267 qz277 qz567)

noncomputable def ep202 := @Enclosure.Complex.IsNear.of_eq qz561 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)))) Bool.true 165660893331 549755813888 2778309238779 13369511637942272 Bool.false 5648777119 549755813888 2766001003775 13369511637942272 (BSN.cpow_neg_s_mk qz12 132339 1000 11 qz13 rfl)

noncomputable abbrev qz328 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11) qz14)

noncomputable def ep203 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) 3477733 1048576 1 1048576 158078 158079 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 11)) (Real.sqrt qz328) Bool.false 3477733 1048576 1 1048576 (BSN.sqrt_natCast_div_one 11) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz328) Bool.false 3477733 1048576 1 1048576 3477733 1048576 1 1048576 (BSN.sqrt_enclosure 11 1 1738866 1738867 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep204 := BSN.log_dyadic_bound 3 19 4 3 4939817505 524288 194552 41676111 10935 166961 22 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 3) (BSN.artanhQ 19) 0 3 41676111 4939817505 10935 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep205 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz567 132339 1000 0 1 10799156221662949 4503599627370496 125000000072957 24319000000000000000 1429149535218653007711 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 45294944137145793642496 18889465931478580854784 1000000000583656 194552000000000000000 10799156221662949 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep206 := BSN.cos_dyadic_bound_f 73198609 2147483648 1 0 1048576 389484 0 1 1 0 1 1 1047966 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 73198609) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 73198609) qz16 0 0 rfl) rfl rfl

noncomputable abbrev qz329 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 166374903) qz17)

noncomputable def ep207 := @Enclosure.Real.IsNear.cos_image qz36 qz329 Bool.false 166374903 524288 357 524288 Bool.true 1047966 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 1429149535218653007711 4503599627370496000 16542375009655056423 24319000000000000000000 166374903 524288 357 524288 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 166374903 524288) (BSN.cos_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2575447117890989326336) qz19) 226375608064910080 72057594037927936 Bool.false 1047966 1048576 50 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 166374903 524288 226375608064910080 72057594037927936 50 2575447117890989326336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1047966 1048576 2575447117890989326336 75557863725914323419136 73198609 2147483648 389484 389104 (ep206 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep208 := BSN.sin_dyadic_bound_f 73198609 2147483648 1 0 1048576 389484 0 1 1 0 1 1 35734 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 73198609) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 73198609) qz21 0 0 rfl) rfl rfl

noncomputable def ep209 := @Enclosure.Real.IsNear.sin_image qz36 qz329 Bool.false 166374903 524288 357 524288 Bool.true 35734 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz36 Bool.false 1429149535218653007711 4503599627370496000 16542375009655056423 24319000000000000000000 166374903 524288 357 524288 (ep205 rfl) rfl) (Enclosure.sfrac_false_div 166374903 524288) (BSN.sin_reduce2 qz329 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2575447117890989326336) qz19) 226375608064910080 72057594037927936 Bool.false 35734 1048576 50 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 166374903 524288 226375608064910080 72057594037927936 50 2575447117890989326336 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 35734 1048576 2575447117890989326336 75557863725914323419136 73198609 2147483648 389484 389104 (ep208 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz330 := (@Enclosure.Real.IsNear.recentre' qz35 Bool.false 316157 1048576 1 1048576 316157 1048576 1 1048576 (ep203 rfl rfl) rfl)

noncomputable def ep210 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz36)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36))) Bool.true 165660893331 549755813888 2778309238779 13369511637942272 Bool.false 5648777119 549755813888 2766001003775 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz36) 316157 1048576 1 1048576 523983 524288 8747419 12750159872 165660893331 549755813888 2778309238779 13369511637942272 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz36) Bool.true 1047966 1048576 69979352 102001278976 523983 524288 8747419 12750159872 (ep207 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz35 (@Neg.neg Real Real.instNeg (Real.sin qz36)) 316157 1048576 1 1048576 17867 524288 8747419 12750159872 5648777119 549755813888 2766001003775 13369511637942272 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz36) Bool.true 17867 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz36) Bool.true 35734 1048576 69979352 102001278976 17867 524288 8747419 12750159872 (ep209 rfl rfl) rfl)) rfl)

noncomputable def ep211 := @ep171 165660893331 549755813888 2778309238779 13369511637942272 Bool.false 5648777119 549755813888 2766001003775 13369511637942272 Bool.false 658165283379463545946112 1197195676249 1099511627776 79485628290025 26739023275884544 Bool.false 132377594873069655031808 240793442341 1099511627776 79481896879941 26739023275884544 (ep172 (BSN.head_sum_c_succ qz5 10 11 rfl rfl) (ep201 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep202 ep210) rfl rfl

noncomputable abbrev qz37 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 12)))

noncomputable abbrev qz568 := (Real.log (Enclosure.sfrac Bool.false 12 1))

noncomputable abbrev qz38 := (@HMul.hMul Real Real Real qz267 qz277 qz568)

noncomputable def ep212 := @Enclosure.Complex.IsNear.of_eq qz560 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)))) Bool.true 83424201291 549755813888 1329104641075 6684755818971136 Bool.true 135004375485 549755813888 665588322097 3342377909485568 (BSN.cpow_neg_s_mk qz12 132339 1000 12 qz13 rfl)

noncomputable abbrev qz331 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 12) qz14)

noncomputable def ep213 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) 3632373 1048576 1 1048576 151348 151349 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 12)) (Real.sqrt qz331) Bool.false 3632373 1048576 1 1048576 (BSN.sqrt_natCast_div_one 12) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz331) Bool.false 3632373 1048576 1 1048576 3632373 1048576 1 1048576 (BSN.sqrt_enclosure 12 1 1816186 1816187 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep214 := BSN.log_dyadic_bound 4 20 4 3 6720000000 524288 194552 91811840 61440 212580 24 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 4) (BSN.artanhQ 20) 0 3 91811840 6720000000 61440 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep215 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz568 132339 1000 0 1 11191020447815397 4503599627370496 125000000072957 24319000000000000000 1481008455043441823583 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 46938541828353910898688 18889465931478580854784 1000000000583656 194552000000000000000 11191020447815397 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep216 := nat_lit 1996195615409391618300246610335667216

noncomputable def ep217 := BSN.sin_dyadic_bound_f 1188641186 2147483648 2 1 1048576 389484 ep216 ep61 ep216 ep216 ep62 ep216 551206 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1188641186) qz20 0 1 ep216 ep61 ep216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1188641186) qz21 0 1 ep216 ep62 ep216 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz332 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 344824151) qz25)

noncomputable def ep218 := @Enclosure.Real.IsNear.cos_image qz38 qz332 Bool.false 344824151 1048576 715 1048576 Bool.true 551206 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 1481008455043441823583 4503599627370496000 16542375009655056423 24319000000000000000000 344824151 1048576 715 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 344824151 1048576) (BSN.cos_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83643187587653883133952) qz26) 226375608064910080 72057594037927936 Bool.false 551206 1048576 52 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 344824151 1048576 226375608064910080 72057594037927936 52 83643187587653883133952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 551206 1048576 83643187587653883133952 151115727451828646838272 1188641186 2147483648 389484 389104 (ep217 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep219 := BSN.cos_dyadic_bound_f 1188641186 2147483648 2 1 1048576 389484 ep216 ep57 ep216 ep216 ep58 ep216 892010 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1188641186) qz15 0 1 ep216 ep57 ep216 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1188641186) qz16 0 1 ep216 ep58 ep216 rfl rfl rfl rfl) rfl rfl

noncomputable def ep220 := @Enclosure.Real.IsNear.sin_image qz38 qz332 Bool.false 344824151 1048576 715 1048576 Bool.false 892010 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz38 Bool.false 1481008455043441823583 4503599627370496000 16542375009655056423 24319000000000000000000 344824151 1048576 715 1048576 (ep215 rfl) rfl) (Enclosure.sfrac_false_div 344824151 1048576) (BSN.sin_reduce1 qz332 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 83643187587653883133952) qz26) 226375608064910080 72057594037927936 Bool.false 892010 1048576 52 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 344824151 1048576 226375608064910080 72057594037927936 52 83643187587653883133952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 892010 1048576 83643187587653883133952 151115727451828646838272 1188641186 2147483648 389484 389104 (ep219 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz333 := (@Enclosure.Real.IsNear.recentre' qz37 Bool.false 302697 1048576 1 1048576 302697 1048576 1 1048576 (ep213 rfl rfl) rfl)

noncomputable def ep221 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz38)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38))) Bool.true 83424201291 549755813888 1329104641075 6684755818971136 Bool.true 135004375485 549755813888 665588322097 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ft qz37 (Real.cos qz38) 302697 1048576 1 1048576 275603 524288 17519157 25500319744 83424201291 549755813888 1329104641075 6684755818971136 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz38) Bool.true 551206 1048576 140153256 204002557952 275603 524288 17519157 25500319744 (ep218 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz38)) 302697 1048576 1 1048576 446005 524288 17519157 25500319744 135004375485 549755813888 665588322097 3342377909485568 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz38) Bool.false 446005 524288 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz38) Bool.false 892010 1048576 140153256 204002557952 446005 524288 17519157 25500319744 (ep220 rfl rfl) rfl)) rfl)

noncomputable def ep222 := @ep169 83424201291 549755813888 1329104641075 6684755818971136 Bool.true 135004375485 549755813888 665588322097 3342377909485568 Bool.false 566439404022083455287296 1030347273667 1099511627776 84802046854325 26739023275884544 Bool.true 16061285773325004439552 29215308629 1099511627776 84806603456717 26739023275884544 (ep170 (BSN.head_sum_c_succ qz5 11 12 rfl rfl) (ep211 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep212 ep221) rfl rfl

noncomputable abbrev qz39 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 13)))

noncomputable abbrev qz569 := (Real.log (Enclosure.sfrac Bool.false 13 1))

noncomputable abbrev qz40 := (@HMul.hMul Real Real Real qz267 qz277 qz569)

noncomputable def ep223 := @Enclosure.Complex.IsNear.of_eq qz559 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)))) Bool.false 75374632671 274877906944 1278282617091 6684755818971136 Bool.true 357421467 8589934592 318234027315 1671188954742784 (BSN.cpow_neg_s_mk qz12 132339 1000 13 qz13 rfl)

noncomputable abbrev qz334 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13) qz14)

noncomputable def ep224 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) 3780695 1048576 1 1048576 145411 145412 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 13)) (Real.sqrt qz334) Bool.false 3780695 1048576 1 1048576 (BSN.sqrt_natCast_div_one 13) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz334) Bool.false 3780695 1048576 1 1048576 3780695 1048576 1 1048576 (BSN.sqrt_enclosure 13 1 1890347 1890348 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep225 := BSN.log_dyadic_bound 5 21 5 4 35742602096145 524288 194552 699352521000 41015625 254545 26 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 5) (BSN.artanhQ 21) 0 4 699352521000 35742602096145 41015625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep226 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz569 132339 1000 0 1 11551497052968677 4503599627370496 125000000072957 24319000000000000000 1528713568492821745503 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 48450490295254733815808 18889465931478580854784 1000000000583656 194552000000000000000 11551497052968677 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep225 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep227 := nat_lit 10938209598242826335767078364868241

noncomputable def ep228 := BSN.cos_dyadic_bound_f 323397427 2147483648 2 1 1048576 389484 ep227 ep57 ep227 ep227 ep58 ep227 1036708 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 323397427) qz15 0 1 ep227 ep57 ep227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 323397427) qz16 0 1 ep227 ep58 ep227 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz41 := (@Nat.cast Real Real.instNatCast 262144)

noncomputable abbrev qz335 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 88982841) qz41)

noncomputable abbrev qz336 := (@Nat.cast Real Real.instNatCast 37778931862957161709568)

noncomputable def ep229 := @Enclosure.Real.IsNear.cos_image qz40 qz335 Bool.false 88982841 262144 357 524288 Bool.false 1036708 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1528713568492821745503 4503599627370496000 16542375009655056423 24319000000000000000000 88982841 262144 357 524288 (ep226 rfl) rfl) (Enclosure.sfrac_false_div 88982841 262144) (BSN.cos_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5689267716336786604032) qz336) 226375608064910080 72057594037927936 Bool.false 1036708 1048576 54 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 88982841 262144 226375608064910080 72057594037927936 54 5689267716336786604032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036708 1048576 5689267716336786604032 37778931862957161709568 323397427 2147483648 389484 389104 (ep228 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep230 := BSN.sin_dyadic_bound_f 323397427 2147483648 2 1 1048576 389484 ep227 ep61 ep227 ep227 ep62 ep227 157312 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 323397427) qz20 0 1 ep227 ep61 ep227 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 323397427) qz21 0 1 ep227 ep62 ep227 rfl rfl rfl rfl) rfl rfl

noncomputable def ep231 := @Enclosure.Real.IsNear.sin_image qz40 qz335 Bool.false 88982841 262144 357 524288 Bool.false 157312 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz40 Bool.false 1528713568492821745503 4503599627370496000 16542375009655056423 24319000000000000000000 88982841 262144 357 524288 (ep226 rfl) rfl) (Enclosure.sfrac_false_div 88982841 262144) (BSN.sin_reduce0 qz335 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 5689267716336786604032) qz336) 226375608064910080 72057594037927936 Bool.false 157312 1048576 54 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 88982841 262144 226375608064910080 72057594037927936 54 5689267716336786604032 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 157312 1048576 5689267716336786604032 37778931862957161709568 323397427 2147483648 389484 389104 (ep230 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz337 := (@Enclosure.Real.IsNear.recentre' qz39 Bool.false 290823 1048576 1 1048576 290823 1048576 1 1048576 (ep224 rfl rfl) rfl)

noncomputable def ep232 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz40)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40))) Bool.false 75374632671 274877906944 1278282617091 6684755818971136 Bool.true 357421467 8589934592 318234027315 1671188954742784 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz40) 290823 1048576 1 1048576 259177 262144 8747419 12750159872 75374632671 274877906944 1278282617091 6684755818971136 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz40) Bool.false 1036708 1048576 69979352 102001278976 259177 262144 8747419 12750159872 (ep229 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz39 (@Neg.neg Real Real.instNeg (Real.sin qz40)) 290823 1048576 1 1048576 1229 8192 8747419 12750159872 357421467 8589934592 318234027315 1671188954742784 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz40) Bool.false 1229 8192 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz40) Bool.false 157312 1048576 69979352 102001278976 1229 8192 8747419 12750159872 (ep231 rfl rfl) rfl)) rfl)

noncomputable def ep233 := @ep167 75374632671 274877906944 1278282617091 6684755818971136 Bool.true 357421467 8589934592 318234027315 1671188954742784 Bool.false 366094987072151008313344 1331845804351 1099511627776 89915177322689 26739023275884544 Bool.true 643946649191459061760 74965256405 1099511627776 89898347893757 26739023275884544 (ep168 (BSN.head_sum_c_succ qz5 12 13 rfl rfl) (ep222 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep223 ep232) rfl rfl

noncomputable abbrev qz42 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 14)))

noncomputable abbrev qz570 := (Real.log (Enclosure.sfrac Bool.false 14 1))

noncomputable abbrev qz43 := (@HMul.hMul Real Real Real qz267 qz277 qz570)

noncomputable def ep234 := @Enclosure.Complex.IsNear.of_eq qz558 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)))) Bool.true 63265697979 274877906944 1231195932325 6684755818971136 Bool.false 291732963 2147483648 614473151615 3342377909485568 (BSN.cpow_neg_s_mk qz12 132339 1000 14 qz13 rfl)

noncomputable abbrev qz338 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14) qz14)

noncomputable def ep235 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) 3923413 1048576 1 1048576 140121 140122 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 14)) (Real.sqrt qz338) Bool.false 3923413 1048576 1 1048576 (BSN.sqrt_natCast_div_one 14) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz338) Bool.false 3923413 1048576 1 1048576 3923413 1048576 1 1048576 (BSN.sqrt_enclosure 14 1 1961706 1961707 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep236 := BSN.log_dyadic_bound 6 22 5 4 51857700491520 524288 194552 1346332575744 176359680 293399 28 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 6) (BSN.artanhQ 22) 0 4 1346332575744 51857700491520 176359680 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep237 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz570 132339 1000 0 1 11885250371606245 4503599627370496 125000000072957 24319000000000000000 314576429785599771411 900719925474099200 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 49850353174629559828480 18889465931478580854784 1000000000583656 194552000000000000000 11885250371606245 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep238 := nat_lit 1719154193277166332651845286841321441

noncomputable def ep239 := BSN.cos_dyadic_bound_f 1145061223 2147483648 2 1 1048576 389484 ep238 ep57 ep238 ep238 ep58 ep238 903012 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1145061223) qz15 0 1 ep238 ep57 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1145061223) qz16 0 1 ep238 ep58 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz339 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 366215163) qz25)

noncomputable def ep240 := @Enclosure.Real.IsNear.cos_image qz43 qz339 Bool.false 366215163 1048576 357 524288 Bool.true 903012 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 314576429785599771411 900719925474099200 16542375009655056423 24319000000000000000000 366215163 1048576 357 524288 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 366215163 1048576) (BSN.cos_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80576520271018774757376) qz26) 226375608064910080 72057594037927936 Bool.false 903012 1048576 55 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 366215163 1048576 226375608064910080 72057594037927936 55 80576520271018774757376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 903012 1048576 80576520271018774757376 151115727451828646838272 1145061223 2147483648 389484 389104 (ep239 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep241 := BSN.sin_dyadic_bound_f 1145061223 2147483648 2 1 1048576 389484 ep238 ep61 ep238 ep238 ep62 ep238 532992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1145061223) qz20 0 1 ep238 ep61 ep238 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1145061223) qz21 0 1 ep238 ep62 ep238 rfl rfl rfl rfl) rfl rfl

noncomputable def ep242 := @Enclosure.Real.IsNear.sin_image qz43 qz339 Bool.false 366215163 1048576 357 524288 Bool.true 532992 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz43 Bool.false 314576429785599771411 900719925474099200 16542375009655056423 24319000000000000000000 366215163 1048576 357 524288 (ep237 rfl) rfl) (Enclosure.sfrac_false_div 366215163 1048576) (BSN.sin_reduce2 qz339 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 80576520271018774757376) qz26) 226375608064910080 72057594037927936 Bool.false 532992 1048576 55 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 366215163 1048576 226375608064910080 72057594037927936 55 80576520271018774757376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 532992 1048576 80576520271018774757376 151115727451828646838272 1145061223 2147483648 389484 389104 (ep241 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz340 := (@Enclosure.Real.IsNear.recentre' qz42 Bool.false 280243 1048576 1 1048576 280243 1048576 1 1048576 (ep235 rfl rfl) rfl)

noncomputable def ep243 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz43)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43))) Bool.true 63265697979 274877906944 1231195932325 6684755818971136 Bool.false 291732963 2147483648 614473151615 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz43) 280243 1048576 1 1048576 225753 262144 8747419 12750159872 63265697979 274877906944 1231195932325 6684755818971136 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz43) Bool.true 903012 1048576 69979352 102001278976 225753 262144 8747419 12750159872 (ep240 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz42 (@Neg.neg Real Real.instNeg (Real.sin qz43)) 280243 1048576 1 1048576 1041 2048 8747419 12750159872 291732963 2147483648 614473151615 3342377909485568 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz43) Bool.true 1041 2048 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz43) Bool.true 532992 1048576 69979352 102001278976 1041 2048 8747419 12750159872 (ep242 rfl rfl) rfl)) rfl)

noncomputable def ep244 := @ep165 63265697979 274877906944 1231195932325 6684755818971136 Bool.false 291732963 2147483648 614473151615 3342377909485568 Bool.false 296533616504875924848640 1078783012435 1099511627776 94839961051989 26739023275884544 Bool.false 159777122726180814848 74402020651 1099511627776 94814133106677 26739023275884544 (ep166 (BSN.head_sum_c_succ qz5 13 14 rfl rfl) (ep233 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep234 ep243) rfl rfl

noncomputable abbrev qz44 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 15)))

noncomputable abbrev qz571 := (Real.log (Enclosure.sfrac Bool.false 15 1))

noncomputable abbrev qz45 := (@HMul.hMul Real Real Real qz267 qz277 qz571)

noncomputable def ep245 := @Enclosure.Complex.IsNear.of_eq qz557 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)))) Bool.false 34479137091 137438953472 2383973998123 13369511637942272 Bool.true 67163532093 1099511627776 4749204491781 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 15 qz13 rfl)

noncomputable abbrev qz341 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15) qz14)

noncomputable def ep246 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) 4061117 1048576 1 1048576 135370 135371 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 15)) (Real.sqrt qz341) Bool.false 4061117 1048576 1 1048576 (BSN.sqrt_natCast_div_one 15) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz341) Bool.false 4061117 1048576 1 1048576 4061117 1048576 1 1048576 (BSN.sqrt_enclosure 15 1 2030558 2030559 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep247 := BSN.log_dyadic_bound 7 23 6 5 430628584065881355 524288 194552 14087658153505881 266939110305 329571 30 16 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 7) (BSN.artanhQ 23) 0 5 14087658153505881 430628584065881355 266939110305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep248 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz571 132339 1000 0 1 12195965485668069 4503599627370496 125000000072957 24319000000000000000 1614001876407826583391 4503599627370496000 16542375009655056423 24319000000000000000000 qz18 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 51153586820399524478976 18889465931478580854784 1000000000583656 194552000000000000000 12195965485668069 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep247 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep249 := nat_lit 69213328530312340205036895551596816

noncomputable def ep250 := BSN.cos_dyadic_bound_f 512917402 2147483648 2 1 1048576 389484 ep249 ep57 ep249 ep249 ep58 ep249 1018808 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 512917402) qz15 0 1 ep249 ep57 ep249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 512917402) qz16 0 1 ep249 ep58 ep249 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz342 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 375789095) qz25)

noncomputable def ep251 := @Enclosure.Real.IsNear.cos_image qz45 qz342 Bool.false 375789095 1048576 715 1048576 Bool.false 1018808 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 1614001876407826583391 4503599627370496000 16542375009655056423 24319000000000000000000 375789095 1048576 715 1048576 (ep248 rfl) rfl) (Enclosure.sfrac_false_div 375789095 1048576) (BSN.cos_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36093353462846822809600) qz26) 226375608064910080 72057594037927936 Bool.false 1018808 1048576 57 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 375789095 1048576 226375608064910080 72057594037927936 57 36093353462846822809600 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1018808 1048576 36093353462846822809600 151115727451828646838272 512917402 2147483648 389484 389104 (ep250 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep252 := BSN.sin_dyadic_bound_f 512917402 2147483648 2 1 1048576 389484 ep249 ep61 ep249 ep249 ep62 ep249 248073 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 512917402) qz20 0 1 ep249 ep61 ep249 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 512917402) qz21 0 1 ep249 ep62 ep249 rfl rfl rfl rfl) rfl rfl

noncomputable def ep253 := @Enclosure.Real.IsNear.sin_image qz45 qz342 Bool.false 375789095 1048576 715 1048576 Bool.false 248073 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz45 Bool.false 1614001876407826583391 4503599627370496000 16542375009655056423 24319000000000000000000 375789095 1048576 715 1048576 (ep248 rfl) rfl) (Enclosure.sfrac_false_div 375789095 1048576) (BSN.sin_reduce0 qz342 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36093353462846822809600) qz26) 226375608064910080 72057594037927936 Bool.false 248073 1048576 57 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 375789095 1048576 226375608064910080 72057594037927936 57 36093353462846822809600 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 248073 1048576 36093353462846822809600 151115727451828646838272 512917402 2147483648 389484 389104 (ep252 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz343 := (@Enclosure.Real.IsNear.recentre' qz44 Bool.false 270741 1048576 1 1048576 270741 1048576 1 1048576 (ep246 rfl rfl) rfl)

noncomputable def ep254 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz45)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45))) Bool.false 34479137091 137438953472 2383973998123 13369511637942272 Bool.true 67163532093 1099511627776 4749204491781 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz45) 270741 1048576 1 1048576 127351 131072 17519157 25500319744 34479137091 137438953472 2383973998123 13369511637942272 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz45) Bool.false 1018808 1048576 140153256 204002557952 127351 131072 17519157 25500319744 (ep251 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz44 (@Neg.neg Real Real.instNeg (Real.sin qz45)) 270741 1048576 1 1048576 248073 1048576 17519157 25500319744 67163532093 1099511627776 4749204491781 26739023275884544 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz45) Bool.false 248073 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz45) Bool.false 248073 1048576 140153256 204002557952 248073 1048576 17519157 25500319744 (ep253 rfl rfl) rfl)) rfl)

noncomputable def ep255 := @ep163 34479137091 137438953472 2383973998123 13369511637942272 Bool.true 67163532093 1099511627776 4749204491781 26739023275884544 Bool.false 186177020399675229863936 1354616109163 1099511627776 99607909048235 26739023275884544 Bool.false 7958802337044530987008 3619244279 549755813888 49781668799229 13369511637942272 (ep164 (BSN.head_sum_c_succ qz5 14 15 rfl rfl) (ep244 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep245 ep254) rfl rfl

noncomputable abbrev qz46 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 16)))

noncomputable abbrev qz572 := (Real.log (Enclosure.sfrac Bool.false 16 1))

noncomputable abbrev qz47 := (@HMul.hMul Real Real Real qz267 qz277 qz572)

noncomputable def ep256 := @Enclosure.Complex.IsNear.of_eq qz556 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)))) Bool.true 54924987789 274877906944 1151637093005 6684755818971136 Bool.true 165194392167 1099511627776 4601491892583 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 16 qz13 rfl)

noncomputable abbrev qz344 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 16) qz14)

noncomputable def ep257 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) 4194305 1048576 1 1048576 131071 131072 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 16)) (Real.sqrt qz344) Bool.false 4194305 1048576 1 1048576 (BSN.sqrt_natCast_div_one 16) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz344) Bool.false 4194305 1048576 1 1048576 4194305 1048576 1 1048576 (BSN.sqrt_enclosure 16 1 2097152 2097153 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep258 := BSN.log_dyadic_bound 0 32 1 0 1 524288 194552 0 1 0 32 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 32) 0 0 rfl) rfl rfl rfl

noncomputable def ep259 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz572 132339 1000 0 1 3121657384082679 1125899906842624 31250000024319 6079750000000000000 413117016552117656181 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 52372720210750067441664 18889465931478580854784 1000000000778208 194552000000000000000 3121657384082679 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep260 := nat_lit 1006258797650985392479572889417500128308953078192424804526844934937672839530625

noncomputable def ep261 := nat_lit 244684043536839394845518162748542245203835320354306092302433218871062890625

noncomputable def ep262 := nat_lit 2635043553015425906997702919068050315269308995223396087706580413910970954090625

noncomputable def ep263 := BSN.sin_dyadic_bound_f 1988729455 2147483648 3 2 1048576 389484 ep260 ep78 ep261 ep262 ep80 ep261 838092 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1988729455) qz20 0 2 ep260 ep78 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1988729455) qz21 0 2 ep262 ep80 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz345 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 384745203) qz25)

noncomputable def ep264 := @Enclosure.Real.IsNear.cos_image qz47 qz345 Bool.false 384745203 1048576 357 524288 Bool.true 838092 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 413117016552117656181 1125899906842624000 4135593753218352141 6079750000000000000000 384745203 1048576 357 524288 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 384745203 1048576) (BSN.cos_reduce1 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139944394299168444645376) qz26) 226375608064910080 72057594037927936 Bool.false 838092 1048576 58 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 384745203 1048576 226375608064910080 72057594037927936 58 139944394299168444645376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 838092 1048576 139944394299168444645376 151115727451828646838272 1988729455 2147483648 389484 389104 (ep263 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep265 := nat_lit 559141413825452702219694057748721645613953414693726805222603823062649827690625

noncomputable def ep266 := nat_lit 1676934873389284427869391136920667852351452573440471803483206602750207357290625

noncomputable def ep267 := BSN.cos_dyadic_bound_f 1988729455 2147483648 3 2 1048576 389484 ep265 ep71 ep261 ep266 ep74 ep261 630169 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1988729455) qz15 0 2 ep265 ep71 ep261 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1988729455) qz16 0 2 ep266 ep74 ep261 rfl rfl rfl rfl) rfl rfl

noncomputable def ep268 := @Enclosure.Real.IsNear.sin_image qz47 qz345 Bool.false 384745203 1048576 357 524288 Bool.false 630169 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz47 Bool.false 413117016552117656181 1125899906842624000 4135593753218352141 6079750000000000000000 384745203 1048576 357 524288 (ep259 rfl) rfl) (Enclosure.sfrac_false_div 384745203 1048576) (BSN.sin_reduce1 qz345 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 139944394299168444645376) qz26) 226375608064910080 72057594037927936 Bool.false 630169 1048576 58 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 384745203 1048576 226375608064910080 72057594037927936 58 139944394299168444645376 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 630169 1048576 139944394299168444645376 151115727451828646838272 1988729455 2147483648 389484 389104 (ep267 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz346 := (@Enclosure.Real.IsNear.recentre' qz46 Bool.false 262143 1048576 1 1048576 262143 1048576 1 1048576 (ep257 rfl rfl) rfl)

noncomputable def ep269 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz47)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47))) Bool.true 54924987789 274877906944 1151637093005 6684755818971136 Bool.true 165194392167 1099511627776 4601491892583 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz47) 262143 1048576 1 1048576 209523 262144 8747419 12750159872 54924987789 274877906944 1151637093005 6684755818971136 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz47) Bool.true 838092 1048576 69979352 102001278976 209523 262144 8747419 12750159872 (ep264 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz47)) 262143 1048576 1 1048576 630169 1048576 8747419 12750159872 165194392167 1099511627776 4601491892583 26739023275884544 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz47) Bool.false 630169 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz47) Bool.false 630169 1048576 69979352 102001278976 630169 1048576 8747419 12750159872 (ep268 rfl rfl) rfl)) rfl)

noncomputable def ep270 := @ep161 54924987789 274877906944 1151637093005 6684755818971136 Bool.true 165194392167 1099511627776 4601491892583 26739023275884544 Bool.false 311963378069890146500608 1134916158007 1099511627776 104214457420255 26739023275884544 Bool.true 86837176346980271521792 157955903609 1099511627776 104164829491041 26739023275884544 (ep162 (BSN.head_sum_c_succ qz5 15 16 rfl rfl) (ep255 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep256 ep269) rfl rfl

theorem EMRow45.d7 : Enclosure.Complex.IsNear qz31 Bool.false 1134916158007 1099511627776 104214457420255 26739023275884544 Bool.true 157955903609 1099511627776 104164829491041 26739023275884544 := ep160 (BSN.head_sum_c_succ qz5 16 17 rfl rfl) (ep270 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz48 := (BSN.headSumC qz271 25)

noncomputable abbrev qz573 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz7)

noncomputable def ep271 := @Enclosure.Complex.IsNear.of_eq qz48 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 24) qz573) Bool.false 2435906542585 1099511627776 136968267258687 26739023275884544 Bool.true 194796793641 1099511627776 136863475423099 26739023275884544

noncomputable def ep272 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 24) qz573 Bool.false 139286679307 68719476736 66600058289767 13369511637942272 Bool.true 280762561445 1099511627776 133109112911695 26739023275884544 Bool.false

noncomputable abbrev qz574 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz7)

noncomputable def ep273 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 23) qz574) Bool.false 139286679307 68719476736 66600058289767 13369511637942272 Bool.true 280762561445 1099511627776 133109112911695 26739023275884544

noncomputable def ep274 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 23) qz574 Bool.false 1003446462245 549755813888 32336249917275 6684755818971136 Bool.true 13896007691 68719476736 64636077876225 13369511637942272 Bool.false

noncomputable abbrev qz575 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz7)

noncomputable def ep275 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 22) qz575) Bool.false 1003446462245 549755813888 32336249917275 6684755818971136 Bool.true 13896007691 68719476736 64636077876225 13369511637942272

noncomputable def ep276 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 22) qz575 Bool.false 910731114749 549755813888 15676714641879 3342377909485568 Bool.true 78925872455 1099511627776 125345444290579 26739023275884544 Bool.false

noncomputable abbrev qz576 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz7)

noncomputable def ep277 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 21) qz576) Bool.false 910731114749 549755813888 15676714641879 3342377909485568 Bool.true 78925872455 1099511627776 125345444290579 26739023275884544

noncomputable def ep278 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 21) qz576 Bool.false 412936121657 274877906944 60687236384851 13369511637942272 Bool.false 90672656237 1099511627776 121306225265647 26739023275884544 Bool.false

noncomputable abbrev qz577 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz7)

noncomputable def ep279 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 20) qz577) Bool.false 412936121657 274877906944 60687236384851 13369511637942272 Bool.false 90672656237 1099511627776 121306225265647 26739023275884544

noncomputable def ep280 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 20) qz577 Bool.false 1450426824069 1099511627776 1412669608951 322156906938368 Bool.false 7243816453 34359738368 705961281483 161078453469184 Bool.false

noncomputable def ep281 := nat_lit 1816112269162385745379328

noncomputable abbrev qz578 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz7)

noncomputable def ep282 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 19) qz578) Bool.false 1450426824069 1099511627776 1412669608951 322156906938368 Bool.false 7243816453 34359738368 705961281483 161078453469184

noncomputable def ep283 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 19) qz578 Bool.false 1199614718371 1099511627776 113017663789235 26739023275884544 Bool.false 64660924929 274877906944 56489150491439 13369511637942272 Bool.false

noncomputable abbrev qz579 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz7)

noncomputable def ep284 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 18) qz579) Bool.false 1199614718371 1099511627776 113017663789235 26739023275884544 Bool.false 64660924929 274877906944 56489150491439 13369511637942272

noncomputable def ep285 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 18) qz579 Bool.false 63296598583 68719476736 6792212010137 1671188954742784 Bool.false 79083308045 1099511627776 108636748517303 26739023275884544 Bool.false

noncomputable abbrev qz580 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz7)

noncomputable def ep286 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 18) (@HAdd.hAdd Complex Complex Complex qz4 qz31 qz580) Bool.false 63296598583 68719476736 6792212010137 1671188954742784 Bool.false 79083308045 1099511627776 108636748517303 26739023275884544

noncomputable def ep287 := @Enclosure.Complex.IsNear.addLitP qz31 qz580 Bool.false 1134916158007 1099511627776 104214457420255 26739023275884544 Bool.true 157955903609 1099511627776 104164829491041 26739023275884544 Bool.true

noncomputable abbrev qz49 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 17)))

noncomputable abbrev qz581 := (Real.log (Enclosure.sfrac Bool.false 17 1))

noncomputable abbrev qz50 := (@HMul.hMul Real Real Real qz267 qz277 qz581)

noncomputable def ep288 := @Enclosure.Complex.IsNear.of_eq qz580 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)))) Bool.true 122170580679 1099511627776 4460934741937 26739023275884544 Bool.false 118519605827 549755813888 2235959513131 13369511637942272 (BSN.cpow_neg_s_mk qz12 132339 1000 17 qz13 rfl)

noncomputable abbrev qz347 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 17) qz14)

noncomputable def ep289 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) 4323389 1048576 1 1048576 127158 127159 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 17)) (Real.sqrt qz347) Bool.false 4323389 1048576 1 1048576 (BSN.sqrt_natCast_div_one 17) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz347) Bool.false 4323389 1048576 1 1048576 4323389 1048576 1 1048576 (BSN.sqrt_enclosure 17 1 2161694 2161695 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep290 := BSN.log_dyadic_bound 1 33 2 1 3267 524288 194552 1 1 31784 34 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 33) 0 1 1 3267 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep291 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz581 132339 1000 0 1 3189913004350711 1125899906842624 31250000024319 6079750000000000000 422149897082768743029 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 53517859495200818200576 18889465931478580854784 1000000000778208 194552000000000000000 3189913004350711 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep290 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep292 := nat_lit 1093003661019818149506933213974114668715301866532293390751378154892327104086016

noncomputable def ep293 := nat_lit 934206815829311086663727000619131073742532278775135359939494009446282100736

noncomputable def ep294 := nat_lit 3277142569427795826347472187921105743998420535039329901534255476658088748056576

noncomputable def ep295 := BSN.cos_dyadic_bound_f 2351285572 2147483648 3 2 1048576 389484 ep292 ep71 ep293 ep294 ep74 ep293 480387 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2351285572) qz15 0 2 ep292 ep71 ep293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2351285572) qz16 0 2 ep294 ep74 ep293 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz348 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 393157729) qz25)

noncomputable def ep296 := @Enclosure.Real.IsNear.cos_image qz50 qz348 Bool.false 393157729 1048576 357 524288 Bool.true 480387 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 422149897082768743029 1125899906842624000 4135593753218352141 6079750000000000000000 393157729 1048576 357 524288 (ep291 rfl) rfl) (Enclosure.sfrac_false_div 393157729 1048576) (BSN.cos_reduce2 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165457012970840179867648) qz26) 226375608064910080 72057594037927936 Bool.false 480387 1048576 59 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 393157729 1048576 226375608064910080 72057594037927936 59 165457012970840179867648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 480387 1048576 165457012970840179867648 151115727451828646838272 2351285572 2147483648 389484 389104 (ep295 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep297 := nat_lit 1966659224383009220243148803552911098828549333935107995064529083598631761674240

noncomputable def ep298 := nat_lit 5149261633777490977925077022732812379955379393759646910776721752457313014317056

noncomputable def ep299 := BSN.sin_dyadic_bound_f 2351285572 2147483648 3 2 1048576 389484 ep297 ep78 ep293 ep298 ep80 ep293 932062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2351285572) qz20 0 2 ep297 ep78 ep293 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2351285572) qz21 0 2 ep298 ep80 ep293 rfl rfl rfl rfl) rfl rfl

noncomputable def ep300 := @Enclosure.Real.IsNear.sin_image qz50 qz348 Bool.false 393157729 1048576 357 524288 Bool.true 932062 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz50 Bool.false 422149897082768743029 1125899906842624000 4135593753218352141 6079750000000000000000 393157729 1048576 357 524288 (ep291 rfl) rfl) (Enclosure.sfrac_false_div 393157729 1048576) (BSN.sin_reduce2 qz348 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 165457012970840179867648) qz26) 226375608064910080 72057594037927936 Bool.false 932062 1048576 59 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 393157729 1048576 226375608064910080 72057594037927936 59 165457012970840179867648 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 932062 1048576 165457012970840179867648 151115727451828646838272 2351285572 2147483648 389484 389104 (ep299 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz349 := (@Enclosure.Real.IsNear.recentre' qz49 Bool.false 254317 1048576 1 1048576 254317 1048576 1 1048576 (ep289 rfl rfl) rfl)

noncomputable def ep301 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz50)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50))) Bool.true 122170580679 1099511627776 4460934741937 26739023275884544 Bool.false 118519605827 549755813888 2235959513131 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz50) 254317 1048576 1 1048576 480387 1048576 8747419 12750159872 122170580679 1099511627776 4460934741937 26739023275884544 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz50) Bool.true 480387 1048576 69979352 102001278976 480387 1048576 8747419 12750159872 (ep296 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz50)) 254317 1048576 1 1048576 466031 524288 8747419 12750159872 118519605827 549755813888 2235959513131 13369511637942272 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz50) Bool.true 466031 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz50) Bool.true 932062 1048576 69979352 102001278976 466031 524288 8747419 12750159872 (ep300 rfl rfl) rfl)) rfl)

noncomputable def ep302 := @ep287 122170580679 1099511627776 4460934741937 26739023275884544 Bool.false 118519605827 549755813888 2235959513131 13369511637942272 Bool.false 1113525538250854160662528 63296598583 68719476736 6792212010137 1671188954742784 Bool.false 43476508379234393128960 79083308045 1099511627776 108636748517303 26739023275884544 EMRow45.d7 (ep288 ep301) rfl rfl

noncomputable abbrev qz51 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 18)))

noncomputable abbrev qz582 := (Real.log (Enclosure.sfrac Bool.false 18 1))

noncomputable abbrev qz52 := (@HMul.hMul Real Real Real qz267 qz277 qz582)

noncomputable def ep303 := @Enclosure.Complex.IsNear.of_eq qz579 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)))) Bool.false 186869141043 1099511627776 4342271627043 26739023275884544 Bool.false 179560391671 1099511627776 4341552465575 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 18 qz13 rfl)

noncomputable abbrev qz350 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18) qz14)

noncomputable def ep304 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) 4448731 1048576 1 1048576 123575 123576 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 18)) (Real.sqrt qz350) Bool.false 4448731 1048576 1 1048576 (BSN.sqrt_natCast_div_one 18) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz350) Bool.false 4448731 1048576 1 1048576 4448731 1048576 1 1048576 (BSN.sqrt_enclosure 18 1 2224365 2224366 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep305 := BSN.log_dyadic_bound 2 34 3 2 20045040 524288 194552 23168 48 61752 36 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 2) (BSN.artanhQ 34) 0 2 23168 20045040 48 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep306 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz582 132339 1000 0 1 3254268794313975 1125899906842624 31250000024319 6079750000000000000 17226667118828685501 45035996273704960 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 54597570484265130393600 18889465931478580854784 1000000000778208 194552000000000000000 3254268794313975 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep305 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep307 := nat_lit 8946234573345140976442341289020422416

noncomputable def ep308 := BSN.sin_dyadic_bound_f 1729458202 2147483648 2 1 1048576 389484 ep307 ep61 ep307 ep307 ep62 ep307 756093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1729458202) qz20 0 1 ep307 ep61 ep307 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1729458202) qz21 0 1 ep307 ep62 ep307 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz351 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 401089599) qz25)

noncomputable def ep309 := @Enclosure.Real.IsNear.cos_image qz52 qz351 Bool.false 401089599 1048576 357 524288 Bool.false 756093 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 17226667118828685501 45035996273704960 4135593753218352141 6079750000000000000000 401089599 1048576 357 524288 (ep306 rfl) rfl) (Enclosure.sfrac_false_div 401089599 1048576) (BSN.cos_reduce3 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121699801802723335077888) qz26) 226375608064910080 72057594037927936 Bool.false 756093 1048576 60 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 401089599 1048576 226375608064910080 72057594037927936 60 121699801802723335077888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 756093 1048576 121699801802723335077888 151115727451828646838272 1729458202 2147483648 389484 389104 (ep308 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep310 := nat_lit 319725852056062061838409147891269968833899234004464619051944022510985767035136

noncomputable def ep311 := nat_lit 80035113041315916601134026655419349426797655905153284908636285523075277056

noncomputable def ep312 := nat_lit 959017485942103553682025175620499067802844106701583550586014794961911150551296

noncomputable def ep313 := BSN.cos_dyadic_bound_f 1729458202 2147483648 3 2 1048576 389484 ep310 ep71 ep311 ep312 ep74 ep311 726521 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1729458202) qz15 0 2 ep310 ep71 ep311 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1729458202) qz16 0 2 ep312 ep74 ep311 rfl rfl rfl rfl) rfl rfl

noncomputable def ep314 := @Enclosure.Real.IsNear.sin_image qz52 qz351 Bool.false 401089599 1048576 357 524288 Bool.true 726521 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz52 Bool.false 17226667118828685501 45035996273704960 4135593753218352141 6079750000000000000000 401089599 1048576 357 524288 (ep306 rfl) rfl) (Enclosure.sfrac_false_div 401089599 1048576) (BSN.sin_reduce3 qz351 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 121699801802723335077888) qz26) 226375608064910080 72057594037927936 Bool.false 726521 1048576 60 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 401089599 1048576 226375608064910080 72057594037927936 60 121699801802723335077888 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 726521 1048576 121699801802723335077888 151115727451828646838272 1729458202 2147483648 389484 389104 (ep313 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz352 := (@Enclosure.Real.IsNear.recentre' qz51 Bool.false 247151 1048576 1 1048576 247151 1048576 1 1048576 (ep304 rfl rfl) rfl)

noncomputable def ep315 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz52)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52))) Bool.false 186869141043 1099511627776 4342271627043 26739023275884544 Bool.false 179560391671 1099511627776 4341552465575 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz52) 247151 1048576 1 1048576 756093 1048576 8747419 12750159872 186869141043 1099511627776 4342271627043 26739023275884544 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz52) Bool.false 756093 1048576 69979352 102001278976 756093 1048576 8747419 12750159872 (ep309 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz52)) 247151 1048576 1 1048576 726521 1048576 8747419 12750159872 179560391671 1099511627776 4341552465575 26739023275884544 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz52) Bool.true 726521 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz52) Bool.true 726521 1048576 69979352 102001278976 726521 1048576 8747419 12750159872 (ep314 rfl rfl) rfl)) rfl)

noncomputable def ep316 := @ep285 186869141043 1099511627776 4342271627043 26739023275884544 Bool.false 179560391671 1099511627776 4341552465575 26739023275884544 Bool.false 82436895731259126317056 1199614718371 1099511627776 113017663789235 26739023275884544 Bool.false 284381755288746108911616 64660924929 274877906944 56489150491439 13369511637942272 (ep286 (BSN.head_sum_c_succ qz5 17 18 rfl rfl) (ep302 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep303 ep315) rfl rfl

noncomputable abbrev qz53 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 19)))

noncomputable abbrev qz583 := (Real.log (Enclosure.sfrac Bool.false 19 1))

noncomputable abbrev qz54 := (@HMul.hMul Real Real Real qz267 qz277 qz583)

noncomputable def ep317 := @Enclosure.Complex.IsNear.of_eq qz578 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)))) Bool.false 125406052849 549755813888 2116956876849 13369511637942272 Bool.true 6710393305 274877906944 1052817935825 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 19 qz13 rfl)

noncomputable abbrev qz353 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 19) qz14)

noncomputable def ep318 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) 4570637 1048576 1 1048576 120279 120280 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 19)) (Real.sqrt qz353) Bool.false 4570637 1048576 1 1048576 (BSN.sqrt_natCast_div_one 19) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz353) Bool.false 4570637 1048576 1 1048576 4570637 1048576 1 1048576 (BSN.sqrt_enclosure 19 1 2285318 2285319 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep319 := BSN.log_dyadic_bound 3 35 3 2 22509375 524288 194552 55368 243 90099 38 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 3) (BSN.artanhQ 35) 0 2 55368 22509375 243 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep320 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz583 132339 1000 0 1 3315143513283831 1125899906842624 31250000024319 6079750000000000000 438722777404468910709 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz353) Bool.false 55618878793361701994496 18889465931478580854784 1000000000778208 194552000000000000000 3315143513283831 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep319 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep321 := nat_lit 2747694289335701328335216859347521

noncomputable def ep322 := BSN.cos_dyadic_bound_f 228950767 2147483648 2 1 1048576 389484 ep321 ep57 ep321 ep321 ep58 ep321 1042622 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 228950767) qz15 0 1 ep321 ep57 ep321 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 228950767) qz16 0 1 ep321 ep58 ep321 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz354 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 204296213) qz17)

noncomputable def ep323 := @Enclosure.Real.IsNear.cos_image qz54 qz354 Bool.false 204296213 524288 357 524288 Bool.false 1042622 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 438722777404468910709 1125899906842624000 4135593753218352141 6079750000000000000000 204296213 524288 357 524288 (ep320 rfl) rfl) (Enclosure.sfrac_false_div 204296213 524288) (BSN.cos_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8055488998488529698816) qz19) 226375608064910080 72057594037927936 Bool.false 1042622 1048576 62 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 204296213 524288 226375608064910080 72057594037927936 62 8055488998488529698816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1042622 1048576 8055488998488529698816 75557863725914323419136 228950767 2147483648 389484 389104 (ep322 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep324 := BSN.sin_dyadic_bound_f 228950767 2147483648 1 0 1048576 389484 0 1 1 0 1 1 111580 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 228950767) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 228950767) qz21 0 0 rfl) rfl rfl

noncomputable def ep325 := @Enclosure.Real.IsNear.sin_image qz54 qz354 Bool.false 204296213 524288 357 524288 Bool.false 111580 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz54 Bool.false 438722777404468910709 1125899906842624000 4135593753218352141 6079750000000000000000 204296213 524288 357 524288 (ep320 rfl) rfl) (Enclosure.sfrac_false_div 204296213 524288) (BSN.sin_reduce0 qz354 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 8055488998488529698816) qz19) 226375608064910080 72057594037927936 Bool.false 111580 1048576 62 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 204296213 524288 226375608064910080 72057594037927936 62 8055488998488529698816 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 111580 1048576 8055488998488529698816 75557863725914323419136 228950767 2147483648 389484 389104 (ep324 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz355 := (@Enclosure.Real.IsNear.recentre' qz53 Bool.false 240559 1048576 1 1048576 240559 1048576 1 1048576 (ep318 rfl rfl) rfl)

noncomputable def ep326 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz54)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54))) Bool.false 125406052849 549755813888 2116956876849 13369511637942272 Bool.true 6710393305 274877906944 1052817935825 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz54) 240559 1048576 1 1048576 521311 524288 8747419 12750159872 125406052849 549755813888 2116956876849 13369511637942272 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz54) Bool.false 1042622 1048576 69979352 102001278976 521311 524288 8747419 12750159872 (ep323 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz53 (@Neg.neg Real Real.instNeg (Real.sin qz54)) 240559 1048576 1 1048576 27895 262144 8747419 12750159872 6710393305 274877906944 1052817935825 6684755818971136 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz54) Bool.false 27895 262144 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz54) Bool.false 111580 1048576 69979352 102001278976 27895 262144 8747419 12750159872 (ep325 rfl rfl) rfl)) rfl)

noncomputable def ep327 := @ep283 125406052849 549755813888 2116956876849 13369511637942272 Bool.true 6710393305 274877906944 1052817935825 6684755818971136 Bool.false 797380579151040082870272 1450426824069 1099511627776 1412669608951 322156906938368 Bool.false 15929320839097201197056 7243816453 34359738368 705961281483 161078453469184 (ep284 (BSN.head_sum_c_succ qz5 18 19 rfl rfl) (ep316 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep317 ep326) rfl rfl

noncomputable abbrev qz55 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 20)))

noncomputable abbrev qz584 := (Real.log (Enclosure.sfrac Bool.false 20 1))

noncomputable abbrev qz56 := (@HMul.hMul Real Real Real qz267 qz277 qz584)

noncomputable def ep328 := @Enclosure.Complex.IsNear.of_eq qz577 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)))) Bool.false 201317662559 1099511627776 4122895226769 26739023275884544 Bool.true 141129470259 1099511627776 4116652539469 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 20 qz13 rfl)

noncomputable abbrev qz356 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 20) qz14)

noncomputable def ep329 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) 4689375 1048576 1 1048576 117234 117235 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 20)) (Real.sqrt qz356) Bool.false 4689375 1048576 1 1048576 (BSN.sqrt_natCast_div_one 20) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz356) Bool.false 4689375 1048576 1 1048576 4689375 1048576 1 1048576 (BSN.sqrt_enclosure 20 1 2344687 2344688 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep330 := BSN.log_dyadic_bound 4 36 3 2 25194240 524288 194552 104448 768 116991 40 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.artanhP 4) (BSN.artanhQ 36) 0 2 104448 25194240 768 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep331 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz584 132339 1000 0 1 3372893643545847 1125899906842624 31250000024319 6079750000000000000 446365371893213846133 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 56587765202795681021952 18889465931478580854784 1000000000778208 194552000000000000000 3372893643545847 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep332 := nat_lit 2972120460144961656963784967273178081

noncomputable def ep333 := BSN.cos_dyadic_bound_f 1313005671 2147483648 2 1 1048576 389484 ep332 ep57 ep332 ep332 ep58 ep332 858611 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1313005671) qz15 0 1 ep332 ep57 ep332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1313005671) qz16 0 1 ep332 ep58 ep332 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz357 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 415710147) qz25)

noncomputable def ep334 := @Enclosure.Real.IsNear.cos_image qz56 qz357 Bool.false 415710147 1048576 357 524288 Bool.false 858611 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 446365371893213846133 1125899906842624000 4135593753218352141 6079750000000000000000 415710147 1048576 357 524288 (ep331 rfl) rfl) (Enclosure.sfrac_false_div 415710147 1048576) (BSN.cos_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92394560174361384321024) qz26) 226375608064910080 72057594037927936 Bool.false 858611 1048576 63 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 415710147 1048576 226375608064910080 72057594037927936 63 92394560174361384321024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 858611 1048576 92394560174361384321024 151115727451828646838272 1313005671 2147483648 389484 389104 (ep333 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep335 := BSN.sin_dyadic_bound_f 1313005671 2147483648 2 1 1048576 389484 ep332 ep61 ep332 ep332 ep62 ep332 601911 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1313005671) qz20 0 1 ep332 ep61 ep332 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1313005671) qz21 0 1 ep332 ep62 ep332 rfl rfl rfl rfl) rfl rfl

noncomputable def ep336 := @Enclosure.Real.IsNear.sin_image qz56 qz357 Bool.false 415710147 1048576 357 524288 Bool.false 601911 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz56 Bool.false 446365371893213846133 1125899906842624000 4135593753218352141 6079750000000000000000 415710147 1048576 357 524288 (ep331 rfl) rfl) (Enclosure.sfrac_false_div 415710147 1048576) (BSN.sin_reduce0 qz357 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 92394560174361384321024) qz26) 226375608064910080 72057594037927936 Bool.false 601911 1048576 63 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 415710147 1048576 226375608064910080 72057594037927936 63 92394560174361384321024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 601911 1048576 92394560174361384321024 151115727451828646838272 1313005671 2147483648 389484 389104 (ep335 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz358 := (@Enclosure.Real.IsNear.recentre' qz55 Bool.false 234469 1048576 1 1048576 234469 1048576 1 1048576 (ep329 rfl rfl) rfl)

noncomputable def ep337 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz56)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56))) Bool.false 201317662559 1099511627776 4122895226769 26739023275884544 Bool.true 141129470259 1099511627776 4116652539469 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz56) 234469 1048576 1 1048576 858611 1048576 8747419 12750159872 201317662559 1099511627776 4122895226769 26739023275884544 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz56) Bool.false 858611 1048576 69979352 102001278976 858611 1048576 8747419 12750159872 (ep334 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz56)) 234469 1048576 1 1048576 601911 1048576 8747419 12750159872 141129470259 1099511627776 4116652539469 26739023275884544 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz56) Bool.false 601911 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz56) Bool.false 601911 1048576 69979352 102001278976 601911 1048576 8747419 12750159872 (ep336 rfl rfl) rfl)) rfl)

noncomputable def ep338 := @ep280 201317662559 1099511627776 4122895226769 26739023275884544 Bool.true 141129470259 1099511627776 4116652539469 26739023275884544 Bool.false ep281 412936121657 274877906944 60687236384851 13369511637942272 Bool.false 3115488745434923401216 90672656237 1099511627776 121306225265647 26739023275884544 (ep282 (BSN.head_sum_c_succ qz5 19 20 rfl rfl) (ep327 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep328 ep337) rfl rfl

noncomputable abbrev qz57 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 21)))

noncomputable abbrev qz585 := (Real.log (Enclosure.sfrac Bool.false 21 1))

noncomputable abbrev qz58 := (@HMul.hMul Real Real Real qz267 qz277 qz585)

noncomputable def ep339 := @Enclosure.Complex.IsNear.of_eq qz576 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)))) Bool.false 84858871435 549755813888 2019622182665 13369511637942272 Bool.true 42399632173 274877906944 1009804756233 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 21 qz13 rfl)

noncomputable abbrev qz359 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 21) qz14)

noncomputable def ep340 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) 4805179 1048576 1 1048576 114408 114410 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 21)) (Real.sqrt qz359) Bool.false 4805179 1048576 1 1048576 (BSN.sqrt_natCast_div_one 21) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz359) Bool.false 4805179 1048576 1 1048576 4805179 1048576 1 1048576 (BSN.sqrt_enclosure 21 1 2402589 2402590 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep341 := BSN.log_dyadic_bound 5 37 4 3 269401272945 524288 194552 1658093375 234375 142571 42 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 5) (BSN.artanhQ 37) 0 3 1658093375 269401272945 234375 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep342 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz585 132339 1000 0 1 3427826275261687 1125899906842624 31250000024319 6079750000000000000 453635101441856395893 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 57509381830540779323392 18889465931478580854784 1000000000778208 194552000000000000000 3427826275261687 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep343 := nat_lit 288688596538106611733701451774331860111515813420509150547374708427183024800000

noncomputable def ep344 := nat_lit 65253741252120627261389794412905053942865606236765341069852593424100000000

noncomputable def ep345 := nat_lit 865935282131815593946581575734169770226661709049053920959984420094700874400000

noncomputable def ep346 := BSN.cos_dyadic_bound_f 1685876190 2147483648 3 2 1048576 389484 ep343 ep71 ep344 ep345 ep74 ep344 741715 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1685876190) qz15 0 2 ep343 ep71 ep344 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1685876190) qz16 0 2 ep345 ep74 ep344 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz360 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 211240305) qz17)

noncomputable def ep347 := @Enclosure.Real.IsNear.cos_image qz58 qz360 Bool.false 211240305 524288 357 524288 Bool.false 741715 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 453635101441856395893 1125899906842624000 4135593753218352141 6079750000000000000000 211240305 524288 357 524288 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 211240305 524288) (BSN.cos_reduce0 qz360 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59316495185450075422720) qz19) 226375608064910080 72057594037927936 Bool.false 741715 1048576 64 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 211240305 524288 226375608064910080 72057594037927936 64 59316495185450075422720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 741715 1048576 59316495185450075422720 75557863725914323419136 1685876190 2147483648 389484 389104 (ep346 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep348 := nat_lit 8077978785074929079947081096839210000

noncomputable def ep349 := BSN.sin_dyadic_bound_f 1685876190 2147483648 2 1 1048576 389484 ep348 ep61 ep348 ep348 ep62 ep348 741194 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1685876190) qz20 0 1 ep348 ep61 ep348 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1685876190) qz21 0 1 ep348 ep62 ep348 rfl rfl rfl rfl) rfl rfl

noncomputable def ep350 := @Enclosure.Real.IsNear.sin_image qz58 qz360 Bool.false 211240305 524288 357 524288 Bool.false 741194 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz58 Bool.false 453635101441856395893 1125899906842624000 4135593753218352141 6079750000000000000000 211240305 524288 357 524288 (ep342 rfl) rfl) (Enclosure.sfrac_false_div 211240305 524288) (BSN.sin_reduce0 qz360 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 59316495185450075422720) qz19) 226375608064910080 72057594037927936 Bool.false 741194 1048576 64 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 211240305 524288 226375608064910080 72057594037927936 64 59316495185450075422720 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 741194 1048576 59316495185450075422720 75557863725914323419136 1685876190 2147483648 389484 389104 (ep349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz361 := (@Enclosure.Real.IsNear.recentre' qz57 Bool.false 228818 1048576 2 1048576 114409 524288 1 524288 (ep340 rfl rfl) rfl)

noncomputable def ep351 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz58)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58))) Bool.false 84858871435 549755813888 2019622182665 13369511637942272 Bool.true 42399632173 274877906944 1009804756233 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz58) 114409 524288 1 524288 741715 1048576 8747419 12750159872 84858871435 549755813888 2019622182665 13369511637942272 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz58) Bool.false 741715 1048576 69979352 102001278976 741715 1048576 8747419 12750159872 (ep347 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz58)) 114409 524288 1 524288 370597 524288 8747419 12750159872 42399632173 274877906944 1009804756233 6684755818971136 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz58) Bool.false 370597 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz58) Bool.false 741194 1048576 69979352 102001278976 370597 524288 8747419 12750159872 (ep350 rfl rfl) rfl)) rfl)

noncomputable def ep352 := @ep278 84858871435 549755813888 2019622182665 13369511637942272 Bool.true 42399632173 274877906944 1009804756233 6684755818971136 Bool.false 250339862610981007917056 910731114749 549755813888 15676714641879 3342377909485568 Bool.true 21694978624159502827520 78925872455 1099511627776 125345444290579 26739023275884544 (ep279 (BSN.head_sum_c_succ qz5 20 21 rfl rfl) (ep338 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep339 ep351) rfl rfl

noncomputable abbrev qz59 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 22)))

noncomputable abbrev qz586 := (Real.log (Enclosure.sfrac Bool.false 22 1))

noncomputable abbrev qz60 := (@HMul.hMul Real Real Real qz267 qz277 qz586)

noncomputable def ep353 := @Enclosure.Complex.IsNear.of_eq qz575 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)))) Bool.false 11589418437 68719476736 982820633517 6684755818971136 Bool.true 143410250601 1099511627776 3926711461871 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 22 qz13 rfl)

noncomputable abbrev qz362 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22) qz14)

noncomputable def ep354 := @Enclosure.Real.IsNear.inv_image (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) 4918257 1048576 1 1048576 111778 111779 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt (@Nat.cast Real Real.instNatCast 22)) (Real.sqrt qz362) Bool.false 4918257 1048576 1 1048576 (BSN.sqrt_natCast_div_one 22) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz362) Bool.false 4918257 1048576 1 1048576 4918257 1048576 1 1048576 (BSN.sqrt_enclosure 22 1 2459128 2459129 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep355 := BSN.log_dyadic_bound 6 38 4 3 316148320320 524288 194552 2667271104 699840 166961 44 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 6) (BSN.artanhQ 38) 0 3 2667271104 316148320320 699840 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep356 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz586 132339 1000 0 1 3480203401436407 1125899906842624 31250000024319 6079750000000000000 460566637942692665973 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 58388124189833310502912 18889465931478580854784 1000000000778208 194552000000000000000 3480203401436407 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep357 := nat_lit 142725583536029539402625319659359941828322049264863033019474248330663865508096

noncomputable def ep358 := nat_lit 15953246435729518887447014323475038958980724893449795813532053028142735616

noncomputable def ep359 := nat_lit 428144844115217159170101064949432875407048186344802199466795680885935311053056

noncomputable def ep360 := BSN.cos_dyadic_bound_f 1413696342 2147483648 3 2 1048576 389484 ep357 ep71 ep358 ep359 ep74 ep358 829456 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1413696342) qz15 0 2 ep357 ep71 ep358 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1413696342) qz16 0 2 ep359 ep74 ep358 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz363 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 428936107) qz25)

noncomputable def ep361 := @Enclosure.Real.IsNear.cos_image qz60 qz363 Bool.false 428936107 1048576 357 524288 Bool.false 829456 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 460566637942692665973 1125899906842624000 4135593753218352141 6079750000000000000000 428936107 1048576 357 524288 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 428936107 1048576) (BSN.cos_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99480036239938896789504) qz26) 226375608064910080 72057594037927936 Bool.false 829456 1048576 65 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 428936107 1048576 226375608064910080 72057594037927936 65 99480036239938896789504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 829456 1048576 99480036239938896789504 151115727451828646838272 1413696342 2147483648 389484 389104 (ep360 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep362 := nat_lit 3994151528889398418268520029099969296

noncomputable def ep363 := BSN.sin_dyadic_bound_f 1413696342 2147483648 2 1 1048576 389484 ep362 ep61 ep362 ep362 ep62 ep362 641493 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1413696342) qz20 0 1 ep362 ep61 ep362 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1413696342) qz21 0 1 ep362 ep62 ep362 rfl rfl rfl rfl) rfl rfl

noncomputable def ep364 := @Enclosure.Real.IsNear.sin_image qz60 qz363 Bool.false 428936107 1048576 357 524288 Bool.false 641493 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz60 Bool.false 460566637942692665973 1125899906842624000 4135593753218352141 6079750000000000000000 428936107 1048576 357 524288 (ep356 rfl) rfl) (Enclosure.sfrac_false_div 428936107 1048576) (BSN.sin_reduce0 qz363 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 99480036239938896789504) qz26) 226375608064910080 72057594037927936 Bool.false 641493 1048576 65 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 428936107 1048576 226375608064910080 72057594037927936 65 99480036239938896789504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 641493 1048576 99480036239938896789504 151115727451828646838272 1413696342 2147483648 389484 389104 (ep363 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz364 := (@Enclosure.Real.IsNear.recentre' qz59 Bool.false 223557 1048576 1 1048576 223557 1048576 1 1048576 (ep354 rfl rfl) rfl)

noncomputable def ep365 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz60)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60))) Bool.false 11589418437 68719476736 982820633517 6684755818971136 Bool.true 143410250601 1099511627776 3926711461871 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz60) 223557 1048576 1 1048576 51841 65536 8747419 12750159872 11589418437 68719476736 982820633517 6684755818971136 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz60) Bool.false 829456 1048576 69979352 102001278976 51841 65536 8747419 12750159872 (ep361 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz60)) 223557 1048576 1 1048576 641493 1048576 8747419 12750159872 143410250601 1099511627776 3926711461871 26739023275884544 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz60) Bool.false 641493 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz60) Bool.false 641493 1048576 69979352 102001278976 641493 1048576 8747419 12750159872 (ep364 rfl rfl) rfl)) rfl)

noncomputable def ep366 := @ep276 11589418437 68719476736 982820633517 6684755818971136 Bool.true 143410250601 1099511627776 3926711461871 26739023275884544 Bool.false 68956315818066779832320 1003446462245 549755813888 32336249917275 6684755818971136 Bool.true 244461152574707603603456 13896007691 68719476736 64636077876225 13369511637942272 (ep277 (BSN.head_sum_c_succ qz5 21 22 rfl rfl) (ep352 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep353 ep365) rfl rfl

noncomputable abbrev qz587 := (@Nat.cast Real Real.instNatCast 23)

noncomputable abbrev qz61 := (@Inv.inv Real Real.instInv (Real.sqrt qz587))

noncomputable abbrev qz588 := (Real.log (Enclosure.sfrac Bool.false 23 1))

noncomputable abbrev qz62 := (@HMul.hMul Real Real Real qz267 qz277 qz588)

noncomputable def ep367 := @Enclosure.Complex.IsNear.of_eq qz574 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)))) Bool.false 110846972211 549755813888 1927558455217 13369511637942272 Bool.true 58426438389 1099511627776 3836957159245 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 23 qz13 rfl)

noncomputable abbrev qz589 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23) qz14)

noncomputable def ep368 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz587) 5028793 1048576 1 1048576 109321 109322 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz587) (Real.sqrt qz589) Bool.false 5028793 1048576 1 1048576 (BSN.sqrt_natCast_div_one 23) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz589) Bool.false 5028793 1048576 1 1048576 5028793 1048576 1 1048576 (BSN.sqrt_enclosure 23 1 2514396 2514397 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep369 := BSN.log_dyadic_bound 7 39 4 3 369468094905 524288 194552 4046006391 1764735 190266 46 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 7) (BSN.artanhQ 39) 0 3 4046006391 369468094905 1764735 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep370 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz588 132339 1000 0 1 3530250507853047 1125899906842624 31250000024319 6079750000000000000 467189821958764386933 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz589) Bool.false 59227775304360265777152 18889465931478580854784 1000000000778208 194552000000000000000 3530250507853047 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep371 := nat_lit 93775102652281006542931503971176081

noncomputable def ep372 := BSN.cos_dyadic_bound_f 553377997 2147483648 2 1 1048576 389484 ep371 ep57 ep371 ep371 ep58 ep371 1013954 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 553377997) qz15 0 1 ep371 ep57 ep371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 553377997) qz16 0 1 ep371 ep58 ep371 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz365 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435104427) qz25)

noncomputable def ep373 := @Enclosure.Real.IsNear.cos_image qz62 qz365 Bool.false 435104427 1048576 715 1048576 Bool.false 1013954 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 467189821958764386933 1125899906842624000 4135593753218352141 6079750000000000000000 435104427 1048576 715 1048576 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 435104427 1048576) (BSN.cos_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38940514742917580980224) qz26) 226375608064910080 72057594037927936 Bool.false 1013954 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 435104427 1048576 226375608064910080 72057594037927936 66 38940514742917580980224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1013954 1048576 38940514742917580980224 151115727451828646838272 553377997 2147483648 389484 389104 (ep372 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep374 := BSN.sin_dyadic_bound_f 553377997 2147483648 2 1 1048576 389484 ep371 ep61 ep371 ep371 ep62 ep371 267223 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 553377997) qz20 0 1 ep371 ep61 ep371 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 553377997) qz21 0 1 ep371 ep62 ep371 rfl rfl rfl rfl) rfl rfl

noncomputable def ep375 := @Enclosure.Real.IsNear.sin_image qz62 qz365 Bool.false 435104427 1048576 715 1048576 Bool.false 267223 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz62 Bool.false 467189821958764386933 1125899906842624000 4135593753218352141 6079750000000000000000 435104427 1048576 715 1048576 (ep370 rfl) rfl) (Enclosure.sfrac_false_div 435104427 1048576) (BSN.sin_reduce0 qz365 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 38940514742917580980224) qz26) 226375608064910080 72057594037927936 Bool.false 267223 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 435104427 1048576 226375608064910080 72057594037927936 66 38940514742917580980224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 267223 1048576 38940514742917580980224 151115727451828646838272 553377997 2147483648 389484 389104 (ep374 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz366 := (@Enclosure.Real.IsNear.recentre' qz61 Bool.false 218643 1048576 1 1048576 218643 1048576 1 1048576 (ep368 rfl rfl) rfl)

noncomputable def ep376 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz62)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62))) Bool.false 110846972211 549755813888 1927558455217 13369511637942272 Bool.true 58426438389 1099511627776 3836957159245 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz62) 218643 1048576 1 1048576 506977 524288 17519157 25500319744 110846972211 549755813888 1927558455217 13369511637942272 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz62) Bool.false 1013954 1048576 140153256 204002557952 506977 524288 17519157 25500319744 (ep373 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz62)) 218643 1048576 1 1048576 267223 1048576 17519157 25500319744 58426438389 1099511627776 3836957159245 26739023275884544 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz62) Bool.false 267223 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz62) Bool.false 267223 1048576 140153256 204002557952 267223 1048576 17519157 25500319744 (ep375 rfl rfl) rfl)) rfl)

noncomputable def ep377 := @ep274 110846972211 549755813888 1927558455217 13369511637942272 Bool.true 58426438389 1099511627776 3836957159245 26739023275884544 Bool.false 612589293969413062524928 139286679307 68719476736 66600058289767 13369511637942272 Bool.true 19293856309559448043520 280762561445 1099511627776 133109112911695 26739023275884544 (ep275 (BSN.head_sum_c_succ qz5 22 23 rfl rfl) (ep366 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep367 ep376) rfl rfl

noncomputable abbrev qz590 := (@Nat.cast Real Real.instNatCast 24)

noncomputable abbrev qz63 := (@Inv.inv Real Real.instInv (Real.sqrt qz590))

noncomputable abbrev qz591 := (Real.log (Enclosure.sfrac Bool.false 24 1))

noncomputable abbrev qz64 := (@HMul.hMul Real Real Real qz267 qz277 qz591)

noncomputable def ep378 := @Enclosure.Complex.IsNear.of_eq qz573 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)))) Bool.false 207319673673 1099511627776 3768150679153 26739023275884544 Bool.false 21491441951 274877906944 938590627851 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 24 qz13 rfl)

noncomputable abbrev qz592 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24) qz14)

noncomputable def ep379 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz590) 5136953 1048576 1 1048576 107019 107020 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz590) (Real.sqrt qz592) Bool.false 5136953 1048576 1 1048576 (BSN.sqrt_natCast_div_one 24) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz592) Bool.false 5136953 1048576 1 1048576 5136953 1048576 1 1048576 (BSN.sqrt_enclosure 24 1 2568476 2568477 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep380 := BSN.log_dyadic_bound 8 40 4 3 430080000000 524288 194552 5875957760 3932160 212580 48 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 8) (BSN.artanhQ 40) 0 3 5875957760 430080000000 3932160 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep381 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz591 132339 1000 0 1 3578169457974519 1125899906842624 31250000024319 6079750000000000000 473531367898889869941 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz592) Bool.false 60031721881041427759104 18889465931478580854784 1000000000778208 194552000000000000000 3578169457974519 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep380 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep382 := nat_lit 2633105107278173680910009765275521357517588070134696580480730724878978305517505

noncomputable def ep383 := nat_lit 1674100311834860176451455599181162209690971809893220374106919637574548219841

noncomputable def ep384 := nat_lit 6893517213795103200192913695227691197539897657898663925415264504793632007808961

noncomputable def ep385 := BSN.sin_dyadic_bound_f 2529138919 2147483648 3 2 1048576 389484 ep382 ep78 ep383 ep384 ep80 ep383 968607 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2529138919) qz20 0 2 ep382 ep78 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2529138919) qz21 0 2 ep384 ep80 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz367 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110252613) qz41)

noncomputable def ep386 := @Enclosure.Real.IsNear.cos_image qz64 qz367 Bool.false 110252613 262144 357 524288 Bool.false 968607 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 473531367898889869941 1125899906842624000 4135593753218352141 6079750000000000000000 110252613 262144 357 524288 (ep381 rfl) rfl) (Enclosure.sfrac_false_div 110252613 262144) (BSN.cos_reduce3 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44493082397952700317696) qz336) 226375608064910080 72057594037927936 Bool.false 968607 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 110252613 262144 226375608064910080 72057594037927936 66 44493082397952700317696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 968607 1048576 44493082397952700317696 37778931862957161709568 2529138919 2147483648 389484 389104 (ep385 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep387 := nat_lit 1463580215293134205028428294308259048491856026434783975988897922549465524496321

noncomputable def ep388 := nat_lit 4387392445255732894732381971726414821056186135684565487218479928373247477049281

noncomputable def ep389 := BSN.cos_dyadic_bound_f 2529138919 2147483648 3 2 1048576 389484 ep387 ep71 ep383 ep388 ep74 ep383 401636 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2529138919) qz15 0 2 ep387 ep71 ep383 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2529138919) qz16 0 2 ep388 ep74 ep383 rfl rfl rfl rfl) rfl rfl

noncomputable def ep390 := @Enclosure.Real.IsNear.sin_image qz64 qz367 Bool.false 110252613 262144 357 524288 Bool.true 401636 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz64 Bool.false 473531367898889869941 1125899906842624000 4135593753218352141 6079750000000000000000 110252613 262144 357 524288 (ep381 rfl) rfl) (Enclosure.sfrac_false_div 110252613 262144) (BSN.sin_reduce3 qz367 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44493082397952700317696) qz336) 226375608064910080 72057594037927936 Bool.false 401636 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 110252613 262144 226375608064910080 72057594037927936 66 44493082397952700317696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 401636 1048576 44493082397952700317696 37778931862957161709568 2529138919 2147483648 389484 389104 (ep389 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz368 := (@Enclosure.Real.IsNear.recentre' qz63 Bool.false 214039 1048576 1 1048576 214039 1048576 1 1048576 (ep379 rfl rfl) rfl)

noncomputable def ep391 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz64)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64))) Bool.false 207319673673 1099511627776 3768150679153 26739023275884544 Bool.false 21491441951 274877906944 938590627851 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz64) 214039 1048576 1 1048576 968607 1048576 8747419 12750159872 207319673673 1099511627776 3768150679153 26739023275884544 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz64) Bool.false 968607 1048576 69979352 102001278976 968607 1048576 8747419 12750159872 (ep386 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz64)) 214039 1048576 1 1048576 100409 262144 8747419 12750159872 21491441951 274877906944 938590627851 6684755818971136 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz64) Bool.true 100409 262144 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz64) Bool.true 401636 1048576 69979352 102001278976 100409 262144 8747419 12750159872 (ep390 rfl rfl) rfl)) rfl)

noncomputable def ep392 := @ep272 207319673673 1099511627776 3768150679153 26739023275884544 Bool.false 21491441951 274877906944 938590627851 6684755818971136 Bool.false 167394222984240100802560 2435906542585 1099511627776 136968267258687 26739023275884544 Bool.true 53545334915440368943104 194796793641 1099511627776 136863475423099 26739023275884544 (ep273 (BSN.head_sum_c_succ qz5 23 24 rfl rfl) (ep377 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep378 ep391) rfl rfl

theorem EMRow45.d8 : Enclosure.Complex.IsNear qz48 Bool.false 2435906542585 1099511627776 136968267258687 26739023275884544 Bool.true 194796793641 1099511627776 136863475423099 26739023275884544 := ep271 (BSN.head_sum_c_succ qz5 24 25 rfl rfl) (ep392 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz65 := (BSN.headSumC qz271 33)

noncomputable abbrev qz593 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz7)

noncomputable def ep393 := @Enclosure.Complex.IsNear.of_eq qz65 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 32) qz593) Bool.false 2397094195321 1099511627776 164679692454009 26739023275884544 Bool.true 51038480035 1099511627776 164572417940349 26739023275884544

noncomputable def ep394 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 32) qz593 Bool.false 68836498983 34359738368 40352821089433 6684755818971136 Bool.true 55023413809 1099511627776 161328981979455 26739023275884544 Bool.false

noncomputable abbrev qz594 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz7)

noncomputable def ep395 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 31) qz594) Bool.false 68836498983 34359738368 40352821089433 6684755818971136 Bool.true 55023413809 1099511627776 161328981979455 26739023275884544

noncomputable def ep396 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 31) qz594 Bool.false 2295744299795 1099511627776 158099895448493 26739023275884544 Bool.false 59598271249 549755813888 19750887756021 3342377909485568 Bool.true

noncomputable def ep397 := nat_lit 2421968993510377553657856

noncomputable abbrev qz595 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz7)

noncomputable def ep398 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 30) qz595) Bool.false 2295744299795 1099511627776 158099895448493 26739023275884544 Bool.false 59598271249 549755813888 19750887756021 3342377909485568

noncomputable def ep399 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 30) qz595 Bool.false 2426249461351 1099511627776 154734035614673 26739023275884544 Bool.true 33335093423 1099511627776 154638444191803 26739023275884544 Bool.true

noncomputable abbrev qz596 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz7)

noncomputable def ep400 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 29) qz596) Bool.false 2426249461351 1099511627776 154734035614673 26739023275884544 Bool.true 33335093423 1099511627776 154638444191803 26739023275884544

noncomputable def ep401 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 29) qz596 Bool.false 2245318336201 1099511627776 151300177982271 26739023275884544 Bool.true 127943217623 1099511627776 151215367901671 26739023275884544 Bool.false

noncomputable def ep402 := nat_lit 1333844747320340605042688

noncomputable abbrev qz597 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz7)

noncomputable def ep403 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 28) qz597) Bool.false 2245318336201 1099511627776 151300177982271 26739023275884544 Bool.true 127943217623 1099511627776 151215367901671 26739023275884544

noncomputable def ep404 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 28) qz597 Bool.false 1080925148567 549755813888 445235748111 80539226734592 Bool.false 15586047567 274877906944 444940810795 80539226734592 Bool.false

noncomputable def ep405 := nat_lit 1234376809355830768959488

noncomputable abbrev qz598 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz7)

noncomputable def ep406 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 27) qz598) Bool.false 1080925148567 549755813888 445235748111 80539226734592 Bool.false 15586047567 274877906944 444940810795 80539226734592

noncomputable def ep407 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 27) qz598 Bool.false 2346129713351 1099511627776 144265602367075 26739023275884544 Bool.false 83172670449 549755813888 72088678796255 13369511637942272 Bool.true

noncomputable def ep408 := nat_lit 2376979539209833607593984

noncomputable abbrev qz599 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz7)

noncomputable def ep409 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz5 26) qz599) Bool.false 2346129713351 1099511627776 144265602367075 26739023275884544 Bool.false 83172670449 549755813888 72088678796255 13369511637942272

noncomputable def ep410 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz5 26) qz599 Bool.false 625052601115 274877906944 70322335759035 13369511637942272 Bool.false 15493244889 1099511627776 140556808551805 26739023275884544 Bool.true

noncomputable abbrev qz600 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz7)

noncomputable def ep411 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 26) (@HAdd.hAdd Complex Complex Complex qz4 qz48 qz600) Bool.false 625052601115 274877906944 70322335759035 13369511637942272 Bool.false 15493244889 1099511627776 140556808551805 26739023275884544

noncomputable def ep412 := @Enclosure.Complex.IsNear.addLitP qz48 qz600 Bool.false 2435906542585 1099511627776 136968267258687 26739023275884544 Bool.true 194796793641 1099511627776 136863475423099 26739023275884544 Bool.false

noncomputable def ep413 := nat_lit 2749010411590305930280960

noncomputable abbrev qz601 := (@Nat.cast Real Real.instNatCast 25)

noncomputable abbrev qz66 := (@Inv.inv Real Real.instInv (Real.sqrt qz601))

noncomputable abbrev qz602 := (Real.log (Enclosure.sfrac Bool.false 25 1))

noncomputable abbrev qz67 := (@HMul.hMul Real Real Real qz267 qz277 qz602)

noncomputable def ep414 := @Enclosure.Complex.IsNear.of_eq qz600 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)))) Bool.false 64303861875 1099511627776 3676404259383 26739023275884544 Bool.false 105145019265 549755813888 1846666564353 13369511637942272 (BSN.cpow_neg_s_mk qz12 132339 1000 25 qz13 rfl)

noncomputable abbrev qz603 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25) qz14)

noncomputable def ep415 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz601) 5242881 1048576 1 1048576 104857 104858 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz601) (Real.sqrt qz603) Bool.false 5242881 1048576 1 1048576 (BSN.sqrt_natCast_div_one 25) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz603) Bool.false 5242881 1048576 1 1048576 5242881 1048576 1 1048576 (BSN.sqrt_enclosure 25 1 2621440 2621441 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep416 := BSN.log_dyadic_bound 9 41 5 4 7545754341519345 524288 194552 124828057765224 4519905705 233982 50 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 9) (BSN.artanhQ 41) 0 4 124828057765224 7545754341519345 4519905705 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep417 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz602 132339 1000 0 1 3624129903009015 1125899906842624 31250000024319 6079750000000000000 95922745446862007217 225179981368524800 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 60802810194841294602240 18889465931478580854784 1000000000778208 194552000000000000000 3624129903009015 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep418 := nat_lit 164940116641468366734691678299264016

noncomputable def ep419 := BSN.sin_dyadic_bound_f 637281886 2147483648 2 1 1048576 389484 ep418 ep61 ep418 ep418 ep62 ep418 306625 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 637281886) qz20 0 1 ep418 ep61 ep418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 637281886) qz21 0 1 ep418 ep62 ep418 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz369 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 446675091) qz25)

noncomputable def ep420 := @Enclosure.Real.IsNear.cos_image qz67 qz369 Bool.false 446675091 1048576 357 524288 Bool.false 306625 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 95922745446862007217 225179981368524800 4135593753218352141 6079750000000000000000 446675091 1048576 357 524288 (ep417 rfl) rfl) (Enclosure.sfrac_false_div 446675091 1048576) (BSN.cos_reduce3 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44844726049554323996672) qz26) 226375608064910080 72057594037927936 Bool.false 306625 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 446675091 1048576 226375608064910080 72057594037927936 67 44844726049554323996672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 306625 1048576 44844726049554323996672 151115727451828646838272 637281886 2147483648 389484 389104 (ep419 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep421 := BSN.cos_dyadic_bound_f 637281886 2147483648 2 1 1048576 389484 ep418 ep57 ep418 ep418 ep58 ep418 1002742 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 637281886) qz15 0 1 ep418 ep57 ep418 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 637281886) qz16 0 1 ep418 ep58 ep418 rfl rfl rfl rfl) rfl rfl

noncomputable def ep422 := @Enclosure.Real.IsNear.sin_image qz67 qz369 Bool.false 446675091 1048576 357 524288 Bool.true 1002742 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz67 Bool.false 95922745446862007217 225179981368524800 4135593753218352141 6079750000000000000000 446675091 1048576 357 524288 (ep417 rfl) rfl) (Enclosure.sfrac_false_div 446675091 1048576) (BSN.sin_reduce3 qz369 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 44844726049554323996672) qz26) 226375608064910080 72057594037927936 Bool.false 1002742 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 446675091 1048576 226375608064910080 72057594037927936 67 44844726049554323996672 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1002742 1048576 44844726049554323996672 151115727451828646838272 637281886 2147483648 389484 389104 (ep421 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz370 := (@Enclosure.Real.IsNear.recentre' qz66 Bool.false 209715 1048576 1 1048576 209715 1048576 1 1048576 (ep415 rfl rfl) rfl)

noncomputable def ep423 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz67)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67))) Bool.false 64303861875 1099511627776 3676404259383 26739023275884544 Bool.false 105145019265 549755813888 1846666564353 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz67) 209715 1048576 1 1048576 306625 1048576 8747419 12750159872 64303861875 1099511627776 3676404259383 26739023275884544 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz67) Bool.false 306625 1048576 69979352 102001278976 306625 1048576 8747419 12750159872 (ep420 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz67)) 209715 1048576 1 1048576 501371 524288 8747419 12750159872 105145019265 549755813888 1846666564353 13369511637942272 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz67) Bool.true 501371 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz67) Bool.true 1002742 1048576 69979352 102001278976 501371 524288 8747419 12750159872 (ep422 rfl rfl) rfl)) rfl)

noncomputable def ep424 := @ep412 64303861875 1099511627776 3676404259383 26739023275884544 Bool.false 105145019265 549755813888 1846666564353 13369511637942272 Bool.false ep413 625052601115 274877906944 70322335759035 13369511637942272 Bool.false 8517501453718291218432 15493244889 1099511627776 140556808551805 26739023275884544 EMRow45.d8 (ep414 ep423) rfl rfl

noncomputable abbrev qz604 := (@Nat.cast Real Real.instNatCast 26)

noncomputable abbrev qz68 := (@Inv.inv Real Real.instInv (Real.sqrt qz604))

noncomputable abbrev qz605 := (Real.log (Enclosure.sfrac Bool.false 26 1))

noncomputable abbrev qz69 := (@HMul.hMul Real Real Real qz267 qz277 qz605)

noncomputable def ep425 := @Enclosure.Complex.IsNear.of_eq qz599 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)))) Bool.true 154080691109 1099511627776 3620930849005 26739023275884544 Bool.false 150852096009 1099511627776 3620549040705 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 26 qz13 rfl)

noncomputable abbrev qz606 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26) qz14)

noncomputable def ep426 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz604) 5346709 1048576 1 1048576 102821 102822 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz604) (Real.sqrt qz606) Bool.false 5346709 1048576 1 1048576 (BSN.sqrt_natCast_div_one 26) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz606) Bool.false 5346709 1048576 1 1048576 5346709 1048576 1 1048576 (BSN.sqrt_enclosure 26 1 2673354 2673355 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep427 := BSN.log_dyadic_bound 10 42 5 4 9150106136613120 524288 194552 179034245376000 10500000000 254545 52 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 10) (BSN.artanhQ 42) 0 4 179034245376000 9150106136613120 10500000000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep428 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz605 132339 1000 0 1 3668288609262839 1125899906842624 31250000024319 6079750000000000000 485457646261234850421 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz606) Bool.false 61543670347942250676224 18889465931478580854784 1000000000778208 194552000000000000000 3668288609262839 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep427 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep429 := nat_lit 273919907055865598332346455654482433397546442076872653880445271683814209355776

noncomputable def ep430 := nat_lit 58749393999633024292265678961772143264501405399371318219016234888746500096

noncomputable def ep431 := nat_lit 821642222379597528948454835605523755906110323419819219004897782581665135067136

noncomputable def ep432 := BSN.cos_dyadic_bound_f 1663893112 2147483648 3 2 1048576 389484 ep429 ep71 ep430 ep431 ep74 ep430 749263 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1663893112) qz15 0 2 ep429 ep71 ep430 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1663893112) qz16 0 2 ep431 ep74 ep430 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz371 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14128677) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep433 := @Enclosure.Real.IsNear.cos_image qz69 qz371 Bool.false 14128677 32768 715 1048576 Bool.true 749263 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 485457646261234850421 1125899906842624000 4135593753218352141 6079750000000000000000 14128677 32768 715 1048576 (ep428 rfl) rfl) (Enclosure.sfrac_false_div 14128677 32768) (BSN.cos_reduce2 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3658939648572374646784) qz291) 226375608064910080 72057594037927936 Bool.false 749263 1048576 68 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 14128677 32768 226375608064910080 72057594037927936 68 3658939648572374646784 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 749263 1048576 3658939648572374646784 4722366482869645213696 1663893112 2147483648 389484 389104 (ep432 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep434 := nat_lit 7664815327170839560479112689152167936

noncomputable def ep435 := BSN.sin_dyadic_bound_f 1663893112 2147483648 2 1 1048576 389484 ep434 ep61 ep434 ep434 ep62 ep434 733563 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1663893112) qz20 0 1 ep434 ep61 ep434 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1663893112) qz21 0 1 ep434 ep62 ep434 rfl rfl rfl rfl) rfl rfl

noncomputable def ep436 := @Enclosure.Real.IsNear.sin_image qz69 qz371 Bool.false 14128677 32768 715 1048576 Bool.true 733563 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz69 Bool.false 485457646261234850421 1125899906842624000 4135593753218352141 6079750000000000000000 14128677 32768 715 1048576 (ep428 rfl) rfl) (Enclosure.sfrac_false_div 14128677 32768) (BSN.sin_reduce2 qz371 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 3658939648572374646784) qz291) 226375608064910080 72057594037927936 Bool.false 733563 1048576 68 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 14128677 32768 226375608064910080 72057594037927936 68 3658939648572374646784 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 733563 1048576 3658939648572374646784 4722366482869645213696 1663893112 2147483648 389484 389104 (ep435 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz372 := (@Enclosure.Real.IsNear.recentre' qz68 Bool.false 205643 1048576 1 1048576 205643 1048576 1 1048576 (ep426 rfl rfl) rfl)

noncomputable def ep437 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz69)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69))) Bool.true 154080691109 1099511627776 3620930849005 26739023275884544 Bool.false 150852096009 1099511627776 3620549040705 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz69) 205643 1048576 1 1048576 749263 1048576 17519157 25500319744 154080691109 1099511627776 3620930849005 26739023275884544 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz69) Bool.true 749263 1048576 140153256 204002557952 749263 1048576 17519157 25500319744 (ep433 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz69)) 205643 1048576 1 1048576 733563 1048576 17519157 25500319744 150852096009 1099511627776 3620549040705 26739023275884544 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz69) Bool.true 733563 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz69) Bool.true 733563 1048576 140153256 204002557952 733563 1048576 17519157 25500319744 (ep436 rfl rfl) rfl)) rfl)

noncomputable def ep438 := @ep410 154080691109 1099511627776 3620930849005 26739023275884544 Bool.false 150852096009 1099511627776 3620549040705 26739023275884544 Bool.false 644899225025049572409344 2346129713351 1099511627776 144265602367075 26739023275884544 Bool.false 182898636543713605582848 83172670449 549755813888 72088678796255 13369511637942272 (ep411 (BSN.head_sum_c_succ qz5 25 26 rfl rfl) (ep424 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep425 ep437) rfl rfl

noncomputable abbrev qz607 := (@Nat.cast Real Real.instNatCast 27)

noncomputable abbrev qz70 := (@Inv.inv Real Real.instInv (Real.sqrt qz607))

noncomputable abbrev qz608 := (Real.log (Enclosure.sfrac Bool.false 27 1))

noncomputable abbrev qz71 := (@HMul.hMul Real Real Real qz267 qz277 qz608)

noncomputable def ep439 := @Enclosure.Complex.IsNear.of_eq qz598 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)))) Bool.true 184279416217 1099511627776 3552666005777 26739023275884544 Bool.true 52000575315 549755813888 1771495795715 13369511637942272 (BSN.cpow_neg_s_mk qz12 132339 1000 27 qz13 rfl)

noncomputable abbrev qz609 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27) qz14)

noncomputable def ep440 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz607) 5448561 1048576 1 1048576 100899 100900 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz607) (Real.sqrt qz609) Bool.false 5448561 1048576 1 1048576 (BSN.sqrt_natCast_div_one 27) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz609) Bool.false 5448561 1048576 1 1048576 5448561 1048576 1 1048576 (BSN.sqrt_enclosure 27 1 2724280 2724281 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep441 := BSN.log_dyadic_bound 11 43 5 4 11045349262332945 524288 194552 250863800262504 22507682505 274332 54 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 11) (BSN.artanhQ 43) 0 4 250863800262504 11045349262332945 22507682505 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep442 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz608 132339 1000 0 1 3710780868205815 1125899906842624 31250000024319 6079750000000000000 98216205863497870257 225179981368524800 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz609) Bool.false 62256572154556490711040 18889465931478580854784 1000000000778208 194552000000000000000 3710780868205815 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep443 := nat_lit 1707979390265575733001350803967077963446931884914895889144973575044944141930625

noncomputable def ep444 := nat_lit 704700055786895901795272587952596963637938078946684322043135706443062890625

noncomputable def ep445 := nat_lit 4472138412509995754972059759533280937753217322649289839810670476831088746090625

noncomputable def ep446 := BSN.sin_dyadic_bound_f 2269867665 2147483648 3 2 1048576 389484 ep443 ep78 ep444 ep445 ep80 ep444 913183 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2269867665) qz20 0 2 ep443 ep78 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2269867665) qz21 0 2 ep445 ep80 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz373 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14292339) (@Nat.cast Real Real.instNatCast 32768))

noncomputable def ep447 := @Enclosure.Real.IsNear.cos_image qz71 qz373 Bool.false 14292339 32768 357 524288 Bool.true 913183 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 98216205863497870257 225179981368524800 4135593753218352141 6079750000000000000000 14292339 32768 357 524288 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 14292339 32768) (BSN.cos_reduce1 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4991491784230177865728) qz291) 226375608064910080 72057594037927936 Bool.false 913183 1048576 69 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 14292339 32768 226375608064910080 72057594037927936 69 4991491784230177865728 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 913183 1048576 4991491784230177865728 4722366482869645213696 2269867665 2147483648 389484 389104 (ep446 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep448 := nat_lit 949190639061225138734881678909688911676579019654474020334782268672276995690625

noncomputable def ep449 := nat_lit 2846162517072101624401054491553161541102461182805528692360260534603944861290625

noncomputable def ep450 := BSN.cos_dyadic_bound_f 2269867665 2147483648 3 2 1048576 389484 ep448 ep71 ep444 ep449 ep74 ep444 515370 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2269867665) qz15 0 2 ep448 ep71 ep444 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2269867665) qz16 0 2 ep449 ep74 ep444 rfl rfl rfl rfl) rfl rfl

noncomputable def ep451 := @Enclosure.Real.IsNear.sin_image qz71 qz373 Bool.false 14292339 32768 357 524288 Bool.false 515370 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz71 Bool.false 98216205863497870257 225179981368524800 4135593753218352141 6079750000000000000000 14292339 32768 357 524288 (ep442 rfl) rfl) (Enclosure.sfrac_false_div 14292339 32768) (BSN.sin_reduce1 qz373 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 4991491784230177865728) qz291) 226375608064910080 72057594037927936 Bool.false 515370 1048576 69 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 14292339 32768 226375608064910080 72057594037927936 69 4991491784230177865728 4722366482869645213696 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 515370 1048576 4991491784230177865728 4722366482869645213696 2269867665 2147483648 389484 389104 (ep450 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz374 := (@Enclosure.Real.IsNear.recentre' qz70 Bool.false 201799 1048576 1 1048576 201799 1048576 1 1048576 (ep440 rfl rfl) rfl)

noncomputable def ep452 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz71)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71))) Bool.true 184279416217 1099511627776 3552666005777 26739023275884544 Bool.true 52000575315 549755813888 1771495795715 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz71) 201799 1048576 1 1048576 913183 1048576 8747419 12750159872 184279416217 1099511627776 3552666005777 26739023275884544 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz71) Bool.true 913183 1048576 69979352 102001278976 913183 1048576 8747419 12750159872 (ep447 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz71)) 201799 1048576 1 1048576 257685 524288 8747419 12750159872 52000575315 549755813888 1771495795715 13369511637942272 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz71) Bool.false 257685 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz71) Bool.false 515370 1048576 69979352 102001278976 257685 524288 8747419 12750159872 (ep451 rfl rfl) rfl)) rfl)

noncomputable def ep453 := @ep407 184279416217 1099511627776 3552666005777 26739023275884544 Bool.true 52000575315 549755813888 1771495795715 13369511637942272 Bool.false ep408 1080925148567 549755813888 445235748111 80539226734592 Bool.false 17137040530986334420992 15586047567 274877906944 444940810795 80539226734592 (ep409 (BSN.head_sum_c_succ qz5 26 27 rfl rfl) (ep438 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep439 ep452) rfl rfl

noncomputable abbrev qz610 := (@Nat.cast Real Real.instNatCast 28)

noncomputable abbrev qz72 := (@Inv.inv Real Real.instInv (Real.sqrt qz610))

noncomputable abbrev qz611 := (Real.log (Enclosure.sfrac Bool.false 28 1))

noncomputable abbrev qz73 := (@HMul.hMul Real Real Real qz267 qz277 qz611)

noncomputable def ep454 := @Enclosure.Complex.IsNear.of_eq qz597 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)))) Bool.false 83468039067 1099511627776 3481909609419 26739023275884544 Bool.true 190287407891 1099511627776 3495018717731 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 28 qz13 rfl)

noncomputable abbrev qz612 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 28) qz14)

noncomputable def ep455 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz610) 5548543 1048576 1 1048576 99081 99082 524288 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz610) (Real.sqrt qz612) Bool.false 5548543 1048576 1 1048576 (BSN.sqrt_natCast_div_one 28) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz612) Bool.false 5548543 1048576 1 1048576 5548543 1048576 1 1048576 (BSN.sqrt_enclosure 28 1 2774271 2774272 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep456 := BSN.log_dyadic_bound 12 44 5 4 13275571325829120 524288 194552 344661139390464 45148078080 293399 56 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base4 (BSN.artanhP 12) (BSN.artanhQ 44) 0 4 344661139390464 13275571325829120 45148078080 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep457 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz611 132339 1000 0 1 3751726938922231 1125899906842624 31250000024319 6079750000000000000 496499791370029128309 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz612) Bool.false 62943533227317076688896 18889465931478580854784 1000000000778208 194552000000000000000 3751726938922231 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep458 := nat_lit 1365171670595761838962999087833748035168900921020106114557172177108177552157281

noncomputable def ep459 := nat_lit 1456765629636639290427258657504942970811787380259502748655958906288631458401

noncomputable def ep460 := nat_lit 4092601480528012238308142746186234219565079188299799338174204613511955393555041

noncomputable def ep461 := BSN.cos_dyadic_bound_f 2485556907 2147483648 3 2 1048576 389484 ep458 ep71 ep459 ep460 ep74 ep459 421209 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2485556907) qz15 0 2 ep458 ep71 ep459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2485556907) qz16 0 2 ep460 ep74 ep459 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz375 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 462401463) qz25)

noncomputable def ep462 := @Enclosure.Real.IsNear.cos_image qz73 qz375 Bool.false 462401463 1048576 715 1048576 Bool.false 421209 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 496499791370029128309 1125899906842624000 4135593753218352141 6079750000000000000000 462401463 1048576 715 1048576 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 462401463 1048576) (BSN.cos_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174905518159987617038336) qz26) 226375608064910080 72057594037927936 Bool.false 421209 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 462401463 1048576 226375608064910080 72057594037927936 70 174905518159987617038336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 421209 1048576 174905518159987617038336 151115727451828646838272 2485556907 2147483648 389484 389104 (ep461 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep463 := nat_lit 2456143594568661998701056551174742508927372227931983404003985151669688688716385

noncomputable def ep464 := nat_lit 6430398460469941152032551596202650949047517703110964958417375273286622114753121

noncomputable def ep465 := BSN.sin_dyadic_bound_f 2485556907 2147483648 3 2 1048576 389484 ep463 ep78 ep459 ep464 ep80 ep459 960257 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2485556907) qz20 0 2 ep463 ep78 ep459 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2485556907) qz21 0 2 ep464 ep80 ep459 rfl rfl rfl rfl) rfl rfl

noncomputable def ep466 := @Enclosure.Real.IsNear.sin_image qz73 qz375 Bool.false 462401463 1048576 715 1048576 Bool.false 960257 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz73 Bool.false 496499791370029128309 1125899906842624000 4135593753218352141 6079750000000000000000 462401463 1048576 715 1048576 (ep457 rfl) rfl) (Enclosure.sfrac_false_div 462401463 1048576) (BSN.sin_reduce0 qz375 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 174905518159987617038336) qz26) 226375608064910080 72057594037927936 Bool.false 960257 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 462401463 1048576 226375608064910080 72057594037927936 70 174905518159987617038336 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 960257 1048576 174905518159987617038336 151115727451828646838272 2485556907 2147483648 389484 389104 (ep465 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz376 := (@Enclosure.Real.IsNear.recentre' qz72 Bool.false 198163 1048576 1 1048576 198163 1048576 1 1048576 (ep455 rfl rfl) rfl)

noncomputable def ep467 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz73)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73))) Bool.false 83468039067 1099511627776 3481909609419 26739023275884544 Bool.true 190287407891 1099511627776 3495018717731 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz72 (Real.cos qz73) 198163 1048576 1 1048576 421209 1048576 17519157 25500319744 83468039067 1099511627776 3481909609419 26739023275884544 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz73) Bool.false 421209 1048576 140153256 204002557952 421209 1048576 17519157 25500319744 (ep462 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz73)) 198163 1048576 1 1048576 960257 1048576 17519157 25500319744 190287407891 1099511627776 3495018717731 26739023275884544 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz73) Bool.false 960257 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz73) Bool.false 960257 1048576 140153256 204002557952 960257 1048576 17519157 25500319744 (ep466 rfl rfl) rfl)) rfl)

noncomputable def ep468 := @ep404 83468039067 1099511627776 3481909609419 26739023275884544 Bool.true 190287407891 1099511627776 3495018717731 26739023275884544 Bool.false ep405 2245318336201 1099511627776 151300177982271 26739023275884544 Bool.true 35168763867890934874112 127943217623 1099511627776 151215367901671 26739023275884544 (ep406 (BSN.head_sum_c_succ qz5 27 28 rfl rfl) (ep453 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep454 ep467) rfl rfl

noncomputable abbrev qz613 := (Real.log (Enclosure.sfrac Bool.false 29 1))

noncomputable abbrev qz74 := (@HMul.hMul Real Real Real qz267 qz277 qz613)

noncomputable abbrev qz377 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29)))

noncomputable def ep469 := @Enclosure.Complex.IsNear.of_eq qz596 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz74)))) Bool.false 90465562575 549755813888 1716928816201 13369511637942272 Bool.false 11826015525 137438953472 855769072533 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 29 qz13 rfl)

noncomputable abbrev qz378 := (Real.sqrt (@Nat.cast Real Real.instNatCast 29))

noncomputable abbrev qz379 := (@Nat.cast Real Real.instNatCast 29)

noncomputable abbrev qz614 := (@HDiv.hDiv Real Real Real qz1 qz379 qz14)

noncomputable def ep470 := @Enclosure.Real.IsNear.inv_image qz378 5646755 1048576 1 1048576 97357 97358 524288 (@Enclosure.Real.IsNear.of_eq qz378 (Real.sqrt qz614) Bool.false 5646755 1048576 1 1048576 (BSN.sqrt_natCast_div_one 29) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz614) Bool.false 5646755 1048576 1 1048576 5646755 1048576 1 1048576 (BSN.sqrt_enclosure 29 1 2823377 2823378 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep471 := BSN.log_dyadic_bound 13 45 6 5 353956287581982421875 524288 194552 10371179520995104305 130276274797305 311797 58 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 13) (BSN.artanhQ 45) 0 5 10371179520995104305 353956287581982421875 130276274797305 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep472 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz613 132339 1000 0 1 3791236343078135 1125899906842624 31250000024319 6079750000000000000 100345685281323461553 225179981368524800 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 63606391034871975772160 18889465931478580854784 1000000000778208 194552000000000000000 3791236343078135 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep471 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep473 := nat_lit 1924569195779973899062952259989897954017505026699882961005230103860400731698145

noncomputable def ep474 := nat_lit 894665502137295937656801499123264982839803034916867798156671914219806897121

noncomputable def ep475 := nat_lit 5039089863848852208884859192784485545787915388824113778578587088916122228995041

noncomputable def ep476 := BSN.sin_dyadic_bound_f 2338608837 2147483648 3 2 1048576 389484 ep473 ep78 ep474 ep475 ep80 ep474 929210 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2338608837) qz20 0 2 ep473 ep78 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2338608837) qz21 0 2 ep475 ep80 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz380 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 467271009) qz25)

noncomputable def ep477 := @Enclosure.Real.IsNear.cos_image qz74 qz380 Bool.false 467271009 1048576 715 1048576 Bool.false 929210 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 100345685281323461553 225179981368524800 4135593753218352141 6079750000000000000000 467271009 1048576 715 1048576 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 467271009 1048576) (BSN.cos_reduce3 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164564966987205818974208) qz26) 226375608064910080 72057594037927936 Bool.false 929210 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 467271009 1048576 226375608064910080 72057594037927936 70 164564966987205818974208 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 929210 1048576 164564966987205818974208 151115727451828646838272 2338608837 2147483648 389484 389104 (ep476 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep478 := nat_lit 1069602737878713186562820945105109203335431593959898030690975245217653654008801

noncomputable def ep479 := nat_lit 3207018882631864967813149232317081080040615175809860356476612391824521348232161

noncomputable def ep480 := BSN.cos_dyadic_bound_f 2338608837 2147483648 3 2 1048576 389484 ep478 ep71 ep474 ep479 ep74 ep474 485880 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2338608837) qz15 0 2 ep478 ep71 ep474 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2338608837) qz16 0 2 ep479 ep74 ep474 rfl rfl rfl rfl) rfl rfl

noncomputable def ep481 := @Enclosure.Real.IsNear.sin_image qz74 qz380 Bool.false 467271009 1048576 715 1048576 Bool.true 485880 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz74 Bool.false 100345685281323461553 225179981368524800 4135593753218352141 6079750000000000000000 467271009 1048576 715 1048576 (ep472 rfl) rfl) (Enclosure.sfrac_false_div 467271009 1048576) (BSN.sin_reduce3 qz380 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 164564966987205818974208) qz26) 226375608064910080 72057594037927936 Bool.false 485880 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 467271009 1048576 226375608064910080 72057594037927936 70 164564966987205818974208 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 485880 1048576 164564966987205818974208 151115727451828646838272 2338608837 2147483648 389484 389104 (ep480 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz381 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 29))) Bool.false 194715 1048576 1 1048576 194715 1048576 1 1048576 (ep470 rfl rfl) rfl)

noncomputable def ep482 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz74)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz74))) Bool.false 90465562575 549755813888 1716928816201 13369511637942272 Bool.false 11826015525 137438953472 855769072533 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz377 (Real.cos qz74) 194715 1048576 1 1048576 464605 524288 17519157 25500319744 90465562575 549755813888 1716928816201 13369511637942272 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz74) Bool.false 929210 1048576 140153256 204002557952 464605 524288 17519157 25500319744 (ep477 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz377 (@Neg.neg Real Real.instNeg (Real.sin qz74)) 194715 1048576 1 1048576 60735 131072 17519157 25500319744 11826015525 137438953472 855769072533 6684755818971136 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz74) Bool.true 60735 131072 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz74) Bool.true 485880 1048576 140153256 204002557952 60735 131072 17519157 25500319744 (ep481 rfl rfl) rfl)) rfl)

noncomputable def ep483 := @ep401 90465562575 549755813888 1716928816201 13369511637942272 Bool.false 11826015525 137438953472 855769072533 6684755818971136 Bool.false ep402 2426249461351 1099511627776 154734035614673 26739023275884544 Bool.true 4581540353948470214656 33335093423 1099511627776 154638444191803 26739023275884544 (ep403 (BSN.head_sum_c_succ qz5 28 29 rfl rfl) (ep468 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep469 ep482) rfl rfl

noncomputable abbrev qz615 := (Real.log (Enclosure.sfrac Bool.false 30 1))

noncomputable abbrev qz75 := (@HMul.hMul Real Real Real qz267 qz277 qz615)

noncomputable abbrev qz382 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30)))

noncomputable def ep484 := @Enclosure.Complex.IsNear.of_eq qz595 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz75)))) Bool.true 32626290389 274877906944 841464958455 6684755818971136 Bool.false 152531635921 1099511627776 3368657856365 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 30 qz13 rfl)

noncomputable abbrev qz383 := (Real.sqrt (@Nat.cast Real Real.instNatCast 30))

noncomputable abbrev qz384 := (@Nat.cast Real Real.instNatCast 30)

noncomputable abbrev qz616 := (@HDiv.hDiv Real Real Real qz1 qz384 qz14)

noncomputable def ep485 := @Enclosure.Real.IsNear.inv_image qz383 5743287 1048576 1 1048576 95721 95722 524288 (@Enclosure.Real.IsNear.of_eq qz383 (Real.sqrt qz616) Bool.false 5743287 1048576 1 1048576 (BSN.sqrt_natCast_div_one 30) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz616) Bool.false 5743287 1048576 1 1048576 5743287 1048576 1 1048576 (BSN.sqrt_enclosure 30 1 2871643 2871644 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep486 := BSN.log_dyadic_bound 14 46 6 5 440963670083462507520 524288 194552 14425761949190022144 273345648952320 329571 60 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 14) (BSN.artanhQ 46) 0 5 14425761949190022144 440963670083462507520 273345648952320 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep487 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz615 132339 1000 0 1 3829405717437687 1125899906842624 31250000024319 6079750000000000000 506779723239986059893 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 64246766873087041339392 18889465931478580854784 1000000000778208 194552000000000000000 3829405717437687 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep488 := nat_lit 421757653327256026844120542822344326046353774766308854027714216526529798635776

noncomputable def ep489 := nat_lit 139245650811184200281093612161272777297605989705868489744123084483772580096

noncomputable def ep490 := nat_lit 1264994468680145712131799441242710432584466112319514825103654403410621850747136

noncomputable def ep491 := BSN.cos_dyadic_bound_f 1853415134 2147483648 3 2 1048576 389484 ep488 ep71 ep489 ep490 ep74 ep489 681692 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1853415134) qz15 0 2 ep488 ep71 ep489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1853415134) qz16 0 2 ep490 ep74 ep489 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz385 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 117993849) qz41)

noncomputable def ep492 := @Enclosure.Real.IsNear.cos_image qz75 qz385 Bool.false 117993849 262144 357 524288 Bool.true 681692 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 506779723239986059893 1125899906842624000 4135593753218352141 6079750000000000000000 117993849 262144 357 524288 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 117993849 262144) (BSN.cos_reduce2 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32605623866750935236608) qz336) 226375608064910080 72057594037927936 Bool.false 681692 1048576 71 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 117993849 262144 226375608064910080 72057594037927936 71 32605623866750935236608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 681692 1048576 32605623866750935236608 37778931862957161709568 1853415134 2147483648 389484 389104 (ep491 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep493 := nat_lit 759052379468411900959192102190490768661598709787591242458090291280166619480320

noncomputable def ep494 := nat_lit 1987768881839765442378381354174452809617133830222262800311603135025557895414016

noncomputable def ep495 := BSN.sin_dyadic_bound_f 1853415134 2147483648 3 2 1048576 389484 ep493 ep78 ep489 ep494 ep80 ep489 796747 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1853415134) qz20 0 2 ep493 ep78 ep489 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1853415134) qz21 0 2 ep494 ep80 ep489 rfl rfl rfl rfl) rfl rfl

noncomputable def ep496 := @Enclosure.Real.IsNear.sin_image qz75 qz385 Bool.false 117993849 262144 357 524288 Bool.true 796747 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz75 Bool.false 506779723239986059893 1125899906842624000 4135593753218352141 6079750000000000000000 117993849 262144 357 524288 (ep487 rfl) rfl) (Enclosure.sfrac_false_div 117993849 262144) (BSN.sin_reduce2 qz385 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 32605623866750935236608) qz336) 226375608064910080 72057594037927936 Bool.false 796747 1048576 71 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 117993849 262144 226375608064910080 72057594037927936 71 32605623866750935236608 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 796747 1048576 32605623866750935236608 37778931862957161709568 1853415134 2147483648 389484 389104 (ep495 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz386 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 30))) Bool.false 191443 1048576 1 1048576 191443 1048576 1 1048576 (ep485 rfl rfl) rfl)

noncomputable def ep497 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz75)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz75))) Bool.true 32626290389 274877906944 841464958455 6684755818971136 Bool.false 152531635921 1099511627776 3368657856365 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz382 (Real.cos qz75) 191443 1048576 1 1048576 170423 262144 8747419 12750159872 32626290389 274877906944 841464958455 6684755818971136 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz75) Bool.true 681692 1048576 69979352 102001278976 170423 262144 8747419 12750159872 (ep492 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz382 (@Neg.neg Real Real.instNeg (Real.sin qz75)) 191443 1048576 1 1048576 796747 1048576 8747419 12750159872 152531635921 1099511627776 3368657856365 26739023275884544 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz75) Bool.true 796747 1048576 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz75) Bool.true 796747 1048576 69979352 102001278976 796747 1048576 8747419 12750159872 (ep496 rfl rfl) rfl)) rfl)

noncomputable def ep498 := @ep399 32626290389 274877906944 841464958455 6684755818971136 Bool.false 152531635921 1099511627776 3368657856365 26739023275884544 Bool.false 631049388006268448276480 2295744299795 1099511627776 158099895448493 26739023275884544 Bool.false 131057984467247141224448 59598271249 549755813888 19750887756021 3342377909485568 (ep400 (BSN.head_sum_c_succ qz5 29 30 rfl rfl) (ep483 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep484 ep497) rfl rfl

noncomputable abbrev qz617 := (Real.log (Enclosure.sfrac Bool.false 31 1))

noncomputable abbrev qz76 := (@HMul.hMul Real Real Real qz267 qz277 qz617)

noncomputable abbrev qz387 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31)))

noncomputable def ep499 := @Enclosure.Complex.IsNear.of_eq qz594 (Complex.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz76)))) Bool.true 92976332339 1099511627776 3311388909239 26739023275884544 Bool.true 174219956307 1099511627776 3321879931287 26739023275884544 (BSN.cpow_neg_s_mk qz12 132339 1000 31 qz13 rfl)

noncomputable abbrev qz388 := (Real.sqrt (@Nat.cast Real Real.instNatCast 31))

noncomputable abbrev qz389 := (@Nat.cast Real Real.instNatCast 31)

noncomputable abbrev qz618 := (@HDiv.hDiv Real Real Real qz1 qz389 qz14)

noncomputable def ep500 := @Enclosure.Real.IsNear.inv_image qz388 5838225 1048576 1 1048576 94164 94165 524288 (@Enclosure.Real.IsNear.of_eq qz388 (Real.sqrt qz618) Bool.false 5838225 1048576 1 1048576 (BSN.sqrt_natCast_div_one 31) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz618) Bool.false 5838225 1048576 1 1048576 5838225 1048576 1 1048576 (BSN.sqrt_enclosure 31 1 2919112 2919113 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep501 := BSN.log_dyadic_bound 15 47 6 5 546767979591453359355 524288 194552 19788004106328479625 544934619140625 346763 62 32 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base5 (BSN.artanhP 15) (BSN.artanhQ 47) 0 5 19788004106328479625 546767979591453359355 544934619140625 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep502 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz617 132339 1000 0 1 3866325256314103 1125899906842624 31250000024319 6079750000000000000 511665618095352076917 1125899906842624000 4135593753218352141 6079750000000000000000 qz18 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz618) Bool.false 64866173951437069877248 18889465931478580854784 1000000000778208 194552000000000000000 3866325256314103 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep501 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep503 := nat_lit 1228249953484062194871036955058507776

noncomputable def ep504 := BSN.sin_dyadic_bound_f 1052741368 2147483648 2 1 1048576 389484 ep503 ep61 ep503 ep503 ep62 ep503 493691 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1052741368) qz20 0 1 ep503 ep61 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1052741368) qz21 0 1 ep503 ep62 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz390 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 119131435) qz41)

noncomputable def ep505 := @Enclosure.Real.IsNear.cos_image qz76 qz390 Bool.false 119131435 262144 715 1048576 Bool.true 493691 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 511665618095352076917 1125899906842624000 4135593753218352141 6079750000000000000000 119131435 262144 715 1048576 (ep502 rfl) rfl) (Enclosure.sfrac_false_div 119131435 262144) (BSN.cos_reduce1 qz390 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18520022007508149207040) qz336) 226375608064910080 72057594037927936 Bool.false 493691 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 119131435 262144 226375608064910080 72057594037927936 72 18520022007508149207040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 493691 1048576 18520022007508149207040 37778931862957161709568 1052741368 2147483648 389484 389104 (ep504 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep506 := BSN.cos_dyadic_bound_f 1052741368 2147483648 2 1 1048576 389484 ep503 ep57 ep503 ep503 ep58 ep503 925083 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1052741368) qz15 0 1 ep503 ep57 ep503 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1052741368) qz16 0 1 ep503 ep58 ep503 rfl rfl rfl rfl) rfl rfl

noncomputable def ep507 := @Enclosure.Real.IsNear.sin_image qz76 qz390 Bool.false 119131435 262144 715 1048576 Bool.false 925083 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz76 Bool.false 511665618095352076917 1125899906842624000 4135593753218352141 6079750000000000000000 119131435 262144 715 1048576 (ep502 rfl) rfl) (Enclosure.sfrac_false_div 119131435 262144) (BSN.sin_reduce1 qz390 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18520022007508149207040) qz336) 226375608064910080 72057594037927936 Bool.false 925083 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 119131435 262144 226375608064910080 72057594037927936 72 18520022007508149207040 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 925083 1048576 18520022007508149207040 37778931862957161709568 1052741368 2147483648 389484 389104 (ep506 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz391 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 31))) Bool.false 188329 1048576 1 1048576 188329 1048576 1 1048576 (ep500 rfl rfl) rfl)

noncomputable def ep508 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz76)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz76))) Bool.true 92976332339 1099511627776 3311388909239 26739023275884544 Bool.true 174219956307 1099511627776 3321879931287 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz387 (Real.cos qz76) 188329 1048576 1 1048576 493691 1048576 17519157 25500319744 92976332339 1099511627776 3311388909239 26739023275884544 qz391 (@Enclosure.Real.IsNear.recentre' (Real.cos qz76) Bool.true 493691 1048576 140153256 204002557952 493691 1048576 17519157 25500319744 (ep505 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz387 (@Neg.neg Real Real.instNeg (Real.sin qz76)) 188329 1048576 1 1048576 925083 1048576 17519157 25500319744 174219956307 1099511627776 3321879931287 26739023275884544 qz391 (@Enclosure.Real.IsNear.neg (Real.sin qz76) Bool.false 925083 1048576 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz76) Bool.false 925083 1048576 140153256 204002557952 925083 1048576 17519157 25500319744 (ep507 rfl rfl) rfl)) rfl)

noncomputable def ep509 := @ep396 92976332339 1099511627776 3311388909239 26739023275884544 Bool.true 174219956307 1099511627776 3321879931287 26739023275884544 Bool.false ep397 68836498983 34359738368 40352821089433 6684755818971136 Bool.true 30249441641463013179392 55023413809 1099511627776 161328981979455 26739023275884544 (ep398 (BSN.head_sum_c_succ qz5 30 31 rfl rfl) (ep498 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep499 ep508) rfl rfl

noncomputable abbrev qz619 := (Real.log (Enclosure.sfrac Bool.false 32 1))

noncomputable abbrev qz77 := (@HMul.hMul Real Real Real qz267 qz277 qz619)

noncomputable abbrev qz392 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32)))

noncomputable def ep510 := @Enclosure.Complex.IsNear.of_eq qz593 (Complex.mk (@HMul.hMul Real Real Real qz0 qz392 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz392 (@Neg.neg Real Real.instNeg (Real.sin qz77)))) Bool.false 194326227865 1099511627776 3268408096277 26739023275884544 Bool.false 1992466887 549755813888 1621717980447 13369511637942272 (BSN.cpow_neg_s_mk qz12 132339 1000 32 qz13 rfl)

noncomputable abbrev qz393 := (Real.sqrt (@Nat.cast Real Real.instNatCast 32))

noncomputable abbrev qz394 := (@Nat.cast Real Real.instNatCast 32)

noncomputable abbrev qz620 := (@HDiv.hDiv Real Real Real qz1 qz394 qz14)

noncomputable def ep511 := @Enclosure.Real.IsNear.inv_image qz393 5931641 1048576 1 1048576 92681 92682 524288 (@Enclosure.Real.IsNear.of_eq qz393 (Real.sqrt qz620) Bool.false 5931641 1048576 1 1048576 (BSN.sqrt_natCast_div_one 32) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz620) Bool.false 5931641 1048576 1 1048576 5931641 1048576 1 1048576 (BSN.sqrt_enclosure 32 1 2965820 2965821 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep512 := BSN.log_dyadic_bound 0 64 1 0 1 524288 194552 0 1 0 64 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.artanhP 0) (BSN.artanhQ 64) 0 0 rfl) rfl rfl rfl

noncomputable def ep513 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz619 132339 1000 0 1 15608286920413395 4503599627370496 25000000024319 4863800000000000000 413117016552117656181 900719925474099200 3308475003218352141 4863800000000000000000 qz18 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 65465900263437584302080 18889465931478580854784 1000000000972760 194552000000000000000 15608286920413395 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep514 := nat_lit 7915963180747796863384304052317298122195520293447553215688597739205423670558720

noncomputable def ep515 := nat_lit 15092023090466749367768224317457694285562079770936098911737439749086495440896

noncomputable def ep516 := nat_lit 20707849816954902762268219202412277862621166925114457119041609652610921954082816

noncomputable def ep517 := BSN.sin_dyadic_bound_f 3329227188 2147483648 3 2 1048576 389484 ep514 ep78 ep515 ep516 ep80 ep515 1048355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3329227188) qz20 0 2 ep514 ep78 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3329227188) qz21 0 2 ep516 ep80 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz395 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 30058219) (@Nat.cast Real Real.instNatCast 65536))

noncomputable abbrev qz621 := (@Nat.cast Real Real.instNatCast 9444732965739290427392)

noncomputable def ep518 := @Enclosure.Real.IsNear.cos_image qz77 qz395 Bool.false 30058219 65536 357 524288 Bool.false 1048355 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 413117016552117656181 900719925474099200 3308475003218352141 4863800000000000000000 30058219 65536 357 524288 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 30058219 65536) (BSN.cos_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14642096018957835173888) qz621) 226375608064910080 72057594037927936 Bool.false 1048355 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 30058219 65536 226375608064910080 72057594037927936 72 14642096018957835173888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048355 1048576 14642096018957835173888 9444732965739290427392 3329227188 2147483648 389484 389104 (ep517 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep519 := nat_lit 4404464888455650146043621462095146820902205531813501163787770939447051592728576

noncomputable def ep520 := nat_lit 13183210619186016939395327937650525074135492435898631293539837938842981787303936

noncomputable def ep521 := BSN.cos_dyadic_bound_f 3329227188 2147483648 3 2 1048576 389484 ep519 ep71 ep515 ep520 ep74 ep515 21498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3329227188) qz15 0 2 ep519 ep71 ep515 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3329227188) qz16 0 2 ep520 ep74 ep515 rfl rfl rfl rfl) rfl rfl

noncomputable def ep522 := @Enclosure.Real.IsNear.sin_image qz77 qz395 Bool.false 30058219 65536 357 524288 Bool.true 21498 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz77 Bool.false 413117016552117656181 900719925474099200 3308475003218352141 4863800000000000000000 30058219 65536 357 524288 (ep513 rfl) rfl) (Enclosure.sfrac_false_div 30058219 65536) (BSN.sin_reduce3 qz395 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14642096018957835173888) qz621) 226375608064910080 72057594037927936 Bool.false 21498 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 30058219 65536 226375608064910080 72057594037927936 72 14642096018957835173888 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21498 1048576 14642096018957835173888 9444732965739290427392 3329227188 2147483648 389484 389104 (ep521 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz396 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 32))) Bool.false 185363 1048576 1 1048576 185363 1048576 1 1048576 (ep511 rfl rfl) rfl)

noncomputable def ep523 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz392 (Real.cos qz77)) (@HMul.hMul Real Real Real qz0 qz392 (@Neg.neg Real Real.instNeg (Real.sin qz77))) Bool.false 194326227865 1099511627776 3268408096277 26739023275884544 Bool.false 1992466887 549755813888 1621717980447 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz392 (Real.cos qz77) 185363 1048576 1 1048576 1048355 1048576 8747419 12750159872 194326227865 1099511627776 3268408096277 26739023275884544 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz77) Bool.false 1048355 1048576 69979352 102001278976 1048355 1048576 8747419 12750159872 (ep518 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz392 (@Neg.neg Real Real.instNeg (Real.sin qz77)) 185363 1048576 1 1048576 10749 524288 8747419 12750159872 1992466887 549755813888 1621717980447 13369511637942272 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz77) Bool.true 10749 524288 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz77) Bool.true 21498 1048576 69979352 102001278976 10749 524288 8747419 12750159872 (ep522 rfl rfl) rfl)) rfl)

noncomputable def ep524 := @ep394 194326227865 1099511627776 3268408096277 26739023275884544 Bool.false 1992466887 549755813888 1621717980447 13369511637942272 Bool.false 82363529394681049776128 2397094195321 1099511627776 164679692454009 26739023275884544 Bool.true 28058701131247863726080 51038480035 1099511627776 164572417940349 26739023275884544 (ep395 (BSN.head_sum_c_succ qz5 31 32 rfl rfl) (ep509 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep510 ep523) rfl rfl

theorem EMRow45.d9 : Enclosure.Complex.IsNear qz65 Bool.false 2397094195321 1099511627776 164679692454009 26739023275884544 Bool.true 51038480035 1099511627776 164572417940349 26739023275884544 := ep393 (BSN.head_sum_c_succ qz5 32 33 rfl rfl) (ep524 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

theorem EMRow45.d10 : @Eq Nat (BSN.factNat (Nat.mul 2 1)) 2 := @Eq.refl Nat 2

theorem EMRow45.d11 : @Eq Nat (Nat.pow 34 1) 34 := @Eq.refl Nat 34

noncomputable def ep525 := nat_lit 3937856506233751176424906779423

noncomputable def ep526 := nat_lit 1900433589130765056187616460800

noncomputable def ep527 := nat_lit 2030886032596488467419622031567523153849

noncomputable def ep528 := nat_lit 286605357002031393085260116040345452544000

noncomputable abbrev qz689 := (@instHMul Complex Complex.instMul)

noncomputable abbrev qz622 := qz689

noncomputable abbrev qz397 := qz622

noncomputable abbrev qz78 := qz397

noncomputable abbrev qz623 := (@instHSub Complex Complex.instSub)

noncomputable abbrev qz398 := qz623

noncomputable abbrev qz79 := qz398

noncomputable abbrev qz690 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (4 : Complex))

noncomputable abbrev qz691 := (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid))

noncomputable abbrev qz624 := (@HAdd.hAdd Complex Complex Complex qz687 (@HAdd.hAdd Complex Complex Complex qz687 qz690 (@HMul.hMul Complex Complex Complex qz689 Complex.I (@HDiv.hDiv Complex Complex Complex qz691 (↑qz688) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz399 := qz624

noncomputable abbrev qz80 := (Complex.Stirling.logGammaStirling 1 qz399)

noncomputable abbrev qz625 := (@HAdd.hAdd Complex Complex Complex qz687 qz690 (@HMul.hMul Complex Complex Complex qz689 Complex.I (@HDiv.hDiv Complex Complex Complex qz691 (↑qz688) (2 : Complex))))

noncomputable abbrev qz400 := qz625

noncomputable abbrev qz81 := qz400

noncomputable abbrev qz82 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real)) (Real.log Real.pi))

noncomputable abbrev qz401 := (@instHSub Real Real.instSub)

noncomputable def ep529 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82))) (zetaApproximant qz5 1 34))

noncomputable def ep530 := @Enclosure.Real.IsNear.of_eq ep529 (@HSub.hSub Real Real Real qz401 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 34))))

noncomputable def ep531 := nat_lit 6694361087395411925100992335983

noncomputable def ep532 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 34))) ep531

noncomputable def ep533 := nat_lit 3230737101522300595518947983360

noncomputable def ep534 := nat_lit 8116634748814523461481098027922591779

noncomputable def ep535 := nat_lit 1146421428008125572341040464161381810176

noncomputable def ep536 := nat_lit 50267980349251786508109639

noncomputable def ep537 := nat_lit 32307371015223005955189479833600

noncomputable def ep538 := nat_lit 575781797619200683115841528958403033

noncomputable def ep539 := nat_lit 95535119000677131028420038680115150848000

noncomputable def ep540 := nat_lit 216277044957726162539990715237116827869551293273823489304821760

noncomputable def ep541 := @Enclosure.Real.IsNear.mulLit_tf (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.re (zetaApproximant qz5 1 34)) 1048575 1048576 9007507

noncomputable def ep542 := nat_lit 159606158057254176503850281

noncomputable def ep543 := nat_lit 77026774919564738166784000

noncomputable def ep544 := nat_lit 17830601905451390975891994379

noncomputable def ep545 := nat_lit 2809821208903342301217030144000

noncomputable def ep546 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.true 1048575 1048576 72060056

noncomputable abbrev qz402 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35412727) qz41)

noncomputable def ep547 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz402 Bool.false 35412727 262144 365

noncomputable def ep548 := nat_lit 8850739206942839119495523

noncomputable def ep549 := nat_lit 25500319744000000000000000000

noncomputable def ep550 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) Bool.false 608386017607191561711 4503599627370496000 ep548 ep549

noncomputable def ep551 := nat_lit 2414034924942839119495523

noncomputable def ep552 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82 949516513600131499503 4503599627370496000 ep551 ep549 9928204119 131072000

noncomputable def ep553 := nat_lit 79742372099809812376584192000

noncomputable def ep554 := nat_lit 6375079936000000000000000000

noncomputable def ep555 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 58585053748199385541 562949953421312000 1127000866663225632675701 ep554 Bool.false 949516513600131499503 4503599627370496000

noncomputable def ep556 := nat_lit 2282962924917338799751523

noncomputable def ep557 := @Enclosure.Complex.IsNear.subLitP qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 53864930068354151041 562949953421312000 1110616866586724673443701 ep554 Bool.false 963562910616464347503 4503599627370496000 ep556

noncomputable def ep558 := nat_lit 65960906557467808179392418188099584

noncomputable def ep559 := nat_lit 267265138551980294908465987838803968

noncomputable abbrev qz692 := (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex))

noncomputable abbrev qz626 := qz692

noncomputable abbrev qz403 := (@HSub.hSub Complex Complex Complex qz623 qz624 qz626)

noncomputable abbrev qz404 := (Complex.log qz624)

noncomputable abbrev qz83 := (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 qz403 qz404) qz399)

noncomputable abbrev qz405 := qz626

noncomputable abbrev qz84 := (@HMul.hMul Complex Complex Complex qz397 qz405 ↑(Real.log (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)))

noncomputable abbrev qz627 := qz691

noncomputable abbrev qz406 := qz627

noncomputable abbrev qz85 := qz406

noncomputable abbrev qz86 := (@instHMul Nat instMulNat)

noncomputable abbrev qz628 := (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))

noncomputable abbrev qz407 := qz628

noncomputable abbrev qz87 := qz407

noncomputable abbrev qz88 := qz399

noncomputable abbrev qz89 := (@OfNat.ofNat Int 1 (@instOfNat 1))

noncomputable abbrev qz90 := (@OfNat.ofNat Int 2 (@instOfNat 2))

noncomputable abbrev qz408 := (@instHSub Int Int.instSub)

noncomputable abbrev qz409 := (@instHMul Int Int.instMul)

noncomputable def ep560 := @Enclosure.Complex.IsNear.of_eq qz80 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 53864930068354151041

noncomputable def ep561 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz83 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 53864954148189287041 562949953421312000

noncomputable def ep562 := nat_lit 3701569808718529972271029682176

noncomputable def ep563 := nat_lit 33107769509890284573402914095104000

noncomputable def ep564 := @ep561 16946664249845218891 97276000000000000000000 Bool.false 963568575863223570799 4503599627370496000 544292971169083887 6079750000000000000000 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000 Bool.true ep562 53864930068354151041 562949953421312000 1110616866586724673443701 ep554 Bool.false ep563

noncomputable def ep565 := @Enclosure.Complex.IsNear.addLitP qz83 qz84 Bool.true 54382270074090599041 562949953421312000 16761125004239750141 97276000000000000000000

noncomputable def ep566 := nat_lit 7060187270111466231037952

noncomputable def ep567 := @ep565 Bool.false 963568575863223570799 4503599627370496000 544292971169083887 6079750000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep566 53864954148189287041 562949953421312000 16946664249845218891 97276000000000000000000 Bool.false 963568575863223570799 963568575863223570799 4503599627370496000

noncomputable abbrev qz91 := (@HMul.hMul Complex Complex Complex qz397 qz403 qz404)

noncomputable def ep568 := @Enclosure.Complex.IsNear.subLitP qz91 qz88 Bool.true 53115632678892647041 562949953421312000 16761125004239750141 97276000000000000000000 Bool.false 1261569511406515605871

noncomputable def ep569 := nat_lit 3854274303452894283196000

noncomputable def ep570 := @ep568 4503599627370496000 544292971169083887 6079750000000000000000 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 Bool.true 217529080296362396164000 54382270074090599041 562949953421312000 16761125004239750141 97276000000000000000000 Bool.false ep569 963568575863223570799 4503599627370496000 544292971169083887 6079750000000000000000

noncomputable abbrev qz92 := qz403

noncomputable abbrev qz93 := qz404

noncomputable def ep571 := @Enclosure.Complex.IsNear.mul qz92 qz93 Bool.true 53115632678892647041 562949953421312000 16761125004239750141 97276000000000000000000 Bool.false 1261569511406515605871 4503599627370496000 544292971169083887

noncomputable abbrev qz94 := (Complex.re qz403)

noncomputable abbrev qz95 := (Complex.re qz404)

noncomputable abbrev qz96 := (Complex.im qz403)

noncomputable abbrev qz97 := (Complex.im qz404)

noncomputable def ep572 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz94 qz95) (@HMul.hMul Real Real Real qz0 qz96 qz97) 66089379243974723 9007199254740992 109375000510699 48638000000000000000 114492437763282134457 1125899906842624000

noncomputable def ep573 := nat_lit 956846174160836261727557055460409344

noncomputable def ep574 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz95 7000 4000 0 1 9441339891996389 2251799813685248 15625000072957 12159500000000000000

noncomputable def ep575 := @Enclosure.Complex.IsNear.re_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable abbrev qz629 := (Enclosure.sfrac Bool.false 264678 4000)

noncomputable abbrev qz410 := qz629

noncomputable def ep576 := @Enclosure.Complex.IsNear.of_eq qz92 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz410) Bool.false 7000 4000 0 1 Bool.false 264678 4000 0

noncomputable abbrev qz630 := (Enclosure.sfrac Bool.false 9000 4000)

noncomputable abbrev qz411 := (Complex.log (Complex.mk qz630 qz629))

noncomputable def ep577 := @Enclosure.Complex.IsNear.of_eq qz93 qz411 Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000

noncomputable def ep578 := BSN.log_dyadic_bound 4599443684 135671443684 2 1 55220221893902350475568 1048576 389104 21154882202287491856 21154882202287491856 71123 140270887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4599443684) (BSN.artanhQ 135671443684) 0 1 21154882202287491856 55220221893902350475568 21154882202287491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz98 := (Enclosure.sfrac Bool.false 1 2)

noncomputable abbrev qz412 := (Enclosure.Real.IsNear.const Bool.false 1 2)

noncomputable abbrev qz631 := (Real.log (Enclosure.sfrac Bool.false 70135443684 16000000))

noncomputable abbrev qz632 := (@Nat.cast Real Real.instNatCast 16000000)

noncomputable def ep579 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz631 1 2 0 1 9441339891996389 1125899906842624 15625000072957 6079750000000000000 9441339891996389 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 70135443684 16000000 9441339891996389 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70135443684) qz632)) Bool.false 316798797394880178946048 37778931862957161709568 1000000004669248 389104000000000000000 9441339891996389 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 70135443684 16000000 12 140270887368 131072000000 71123 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep578 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep580 := BSN.arctan_dyadic_bound_f 9000 264678 1 0 1048576 389104 0 1 1 0 1 1 35641 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz99 := (@HMul.hMul Real Real Real qz267 (Enclosure.sfrac Bool.false 1 2) Real.pi)

noncomputable abbrev qz100 := (@Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 1 2) Real.pi 1 2 0 1 226375608064910080 72057594037927936 1 1000000000000000 884279719003555 562949953421312 1 2000000000000000 qz412 BSN.pi_near_15 rfl)

noncomputable abbrev qz413 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 264678)))

noncomputable def ep581 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz413 884279719003555 562949953421312 1 2000000000000000 35641 1048576 1 389104 907170391343982706688 865145102828963 562949953421312 125000000024319 48638000000000000000 qz100 (ep580 rfl) rfl rfl

noncomputable abbrev qz414 := (Complex.mk qz630 qz629)

noncomputable abbrev qz415 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 264678) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep582 := @Enclosure.Complex.IsNear.re_isNear qz93 Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (ep577 (@congrArg Complex Complex qz88 qz414 Complex.log (BSN.w_shift_mk qz12 Bool.false 132339 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz411 Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz411) (@HMul.hMul Real Real Real qz0 qz98 qz631) Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 9000 264678 4000 70135443684 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz411) qz415 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 9000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz415 (@HSub.hSub Real Real Real qz401 qz99 qz413) Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 264678 9000 rfl rfl) ep581))))

noncomputable def ep583 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz97 264678 4000 0 1 865145102828963 562949953421312 125000000024319 48638000000000000000

noncomputable def ep584 := @Enclosure.Complex.IsNear.im_isNear qz92 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable def ep585 := @Enclosure.Complex.IsNear.im_isNear qz93 Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (ep577 (@congrArg Complex Complex qz88 qz414 Complex.log (BSN.w_shift_mk qz12 Bool.false 132339 1000 2 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz411 Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz411) (@HMul.hMul Real Real Real qz0 qz98 qz631) Bool.false 9441339891996389 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 9000 264678 4000 70135443684 16000000 rfl rfl rfl) (ep579 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz411) qz415 Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 9000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz415 (@HSub.hSub Real Real Real qz401 qz99 qz413) Bool.false 865145102828963 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 264678 9000 rfl rfl) ep581))))

noncomputable abbrev qz101 := (@ep576 1 (BSN.w_sub_half_mk qz277 Bool.false 132339 1000 2 qz279 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz410 Bool.false 7000 4000 0 1 Bool.false 264678 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 264678 4000)))

noncomputable def ep586 := @ep572 16542375003218352141 97276000000000000000000 ep573 53115632678892647041 562949953421312000 16761125004239750141 97276000000000000000000 (@ep574 66089379243974723 9007199254740992 109375000510699 48638000000000000000 (ep575 qz101) ep582 rfl) (@ep583 114492437763282134457 1125899906842624000 16542375003218352141 97276000000000000000000 (ep584 qz101) ep585 rfl) rfl

noncomputable def ep587 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz94 qz97) (@HMul.hMul Real Real Real qz0 qz96 qz95) 6056015719802741 2251799813685248 875000000170233 194552000000000000000 1249457479966910123871 4503599627370496000

noncomputable def ep588 := nat_lit 2840801990736181192834191508014891008

noncomputable def ep589 := @Enclosure.Real.IsNear.mulLit_ff qz94 qz97 7000 4000 0 1 865145102828963 562949953421312 125000000024319 48638000000000000000

noncomputable def ep590 := @Enclosure.Real.IsNear.mulLit_ff qz96 qz95 264678 4000 0 1 9441339891996389 2251799813685248 15625000072957 12159500000000000000

noncomputable def ep591 := @ep587 2067796884655056423 24319000000000000000000 ep588 1261569511406515605871 4503599627370496000 544292971169083887 6079750000000000000000 (@ep589 6056015719802741 2251799813685248 875000000170233 194552000000000000000 (ep575 qz101) ep585 rfl) (@ep590 1249457479966910123871 4503599627370496000 2067796884655056423 24319000000000000000000 (ep584 qz101) ep582 rfl) rfl

noncomputable def ep592 := @Enclosure.Complex.IsNear.of_eq qz88 qz414 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 (BSN.w_shift_mk qz12 Bool.false 132339 1000 2 qz13 rfl)

noncomputable abbrev qz416 := (ep592 (@Enclosure.Complex.IsNear.mk qz630 qz629 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 264678 4000)))

noncomputable abbrev qz102 := qz416

noncomputable def ep593 := ep570 (@ep571 6079750000000000000000 (ep586 rfl) (ep591 rfl)) qz102 rfl rfl rfl rfl rfl rfl

noncomputable abbrev qz103 := qz405

noncomputable def ep594 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re qz103) (Complex.re ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz103) (Complex.im ↑qz2)) 120447 131072 1 524288 0 1 0 1 120447 120447

noncomputable def ep595 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz103) (Complex.re ↑qz2) 1 2 0 1 120447 65536 1 262144 120447 131072 1 524288

noncomputable abbrev qz104 := (@Enclosure.Complex.IsNear.of_eq qz405 (Complex.mk (Enclosure.sfrac Bool.false 1 2) qz544) Bool.false 1 2 0 1 Bool.false 0 1 0 1 BSN.half_c_mk (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 2) qz544 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz412 qz546))

noncomputable def ep596 := ep595 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow45.d4)

noncomputable def ep597 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz103) (Complex.im ↑qz2) 0 1 0 1 0 1 0 1 0 1 0 1

noncomputable def ep598 := ep597 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep599 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re qz103) (Complex.im ↑qz2)) (@HMul.hMul Real Real Real qz0 (Complex.im qz103) (Complex.re ↑qz2)) 0 1 0 1 0 1 0 1 0 0

noncomputable def ep600 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re qz103) (Complex.im ↑qz2) 1 2 0 1 0 1 0 1 0 1 0 1

noncomputable def ep601 := ep600 (@Enclosure.Complex.IsNear.re_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.im ↑qz2) qz10 Bool.false 0 1 0 1 (@Eq.trans Real (Complex.im ↑qz2) (0 : Real) qz10 (Complex.ofReal_im qz2) Enclosure.sfrac_zero_eq) qz22)

noncomputable def ep602 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im qz103) (Complex.re ↑qz2) 0 1 0 1 120447 65536 1 262144 0 1 0 1

noncomputable def ep603 := ep602 (@Enclosure.Complex.IsNear.im_isNear qz103 Bool.false 1 2 0 1 Bool.false 0 1 0 1 qz104) (@Enclosure.Real.IsNear.of_eq (Complex.re ↑qz2) qz2 Bool.false 120447 65536 1 262144 (Complex.ofReal_re qz2) EMRow45.d4)

noncomputable def ep604 := @ep567 544292971169083887 6079750000000000000000 (ep593 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz103 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep594 131072 1 524288 (ep596 rfl) (ep598 rfl) rfl rfl) (@ep599 1 0 1 (ep601 rfl) (ep603 rfl) rfl rfl))

noncomputable abbrev qz105 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)

noncomputable abbrev qz417 := (@Nat.cast Complex Complex.instNatCast 1)

noncomputable abbrev qz106 := (@HMul.hMul Complex Complex Complex qz397 (@HMul.hMul Complex Complex Complex qz397 (2 : Complex) qz417) (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 (2 : Complex) qz417) (1 : Complex)))

noncomputable abbrev qz418 := (@HPow.hPow Complex Int Complex qz628 qz624 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz107 := qz418

noncomputable def ep605 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107)) Bool.false 2939433 68719476736 3 68719476736

noncomputable def ep606 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107) Bool.false 0 1 0 1 Bool.false

noncomputable def ep607 := @ep606 0 1 0 1 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000 Bool.false 2939433 2939433 68719476736 3 68719476736 Bool.true 43222402643 43222402643 34359738368000 44113

noncomputable def ep608 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz88 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep609 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz107 Bool.false 2939433 68719476736 3 68719476736 Bool.true 43222402643 34359738368000 44113 34359738368000

noncomputable abbrev qz108 := (Complex.re qz418)

noncomputable abbrev qz109 := (Complex.im qz418)

noncomputable def ep610 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109) 2939433 68719476736 3 68719476736 0 1 0

noncomputable def ep611 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108 1 12 0 1 8818299 17179869184 9 17179869184 2939433

noncomputable def ep612 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1

noncomputable abbrev qz419 := (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 12) qz10 Bool.false 1 12 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 12) qz22)

noncomputable def ep613 := @Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep612 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz419)

noncomputable def ep614 := @Enclosure.Complex.IsNear.re_isNear qz107 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339 8589934592000

noncomputable abbrev qz633 := (@instHPow Complex Nat (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))

noncomputable abbrev qz420 := (@HPow.hPow Complex Nat Complex qz633 qz624 1)

noncomputable abbrev qz110 := (@Inv.inv Complex Complex.instInv qz420)

noncomputable def ep615 := @Enclosure.Complex.IsNear.of_eq qz107 qz110 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339

noncomputable def ep616 := @Enclosure.Complex.IsNear.of_parts qz110 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339

noncomputable abbrev qz111 := (Complex.re qz420)

noncomputable abbrev qz112 := (@MonoidWithZeroHom Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz113 := (@MonoidWithZeroHom.funLike Complex Real (@instMulZeroOneClassOfSemiring Complex Complex.instSemiring) (@instMulZeroOneClassOfSemiring Real Real.semiring))

noncomputable abbrev qz114 := qz420

noncomputable def ep617 := @Enclosure.Real.IsNear.mulLit_ff qz111 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) 9000 4000 0 1 979811 4294967296 1 4294967296

noncomputable def ep618 := @Enclosure.Complex.IsNear.re_isNear qz114 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable def ep619 := @Enclosure.Complex.IsNear.of_eq qz114 qz88 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0

noncomputable def ep620 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) Bool.false 979811 4294967296 1 4294967296 979811 4294967296 1

noncomputable abbrev qz115 := (Complex.im qz420)

noncomputable abbrev qz421 := (@instHAdd Real Real.instAdd)

noncomputable def ep621 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 qz111 qz111) (@HMul.hMul Real Real Real qz0 qz115 qz115)) Bool.false 17533860921 4000000 0 1

noncomputable def ep622 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz111 qz111) (@HMul.hMul Real Real Real qz0 qz115 qz115) 81 16 0 1 17513610921 4000000

noncomputable def ep623 := @Enclosure.Real.IsNear.mulLit_ff qz111 qz111 9000 4000 0 1 9000 4000 0 1

noncomputable def ep624 := @Enclosure.Real.IsNear.mulLit_ff qz115 qz115 264678 4000 0 1 264678 4000 0 1

noncomputable def ep625 := @Enclosure.Complex.IsNear.im_isNear qz114 Bool.false 9000 4000 0 1 Bool.false 264678 4000 0 1

noncomputable abbrev qz116 := (ep618 (@ep619 1 (BSN.pow_one_c qz399) qz416))

noncomputable abbrev qz117 := (ep625 (@ep619 1 (BSN.pow_one_c qz399) qz416))

noncomputable def ep626 := @ep622 0 1 280541774736 17533860921 4000000 0 1 (@ep623 81 16 0 1 qz116 qz116 rfl) (@ep624 17513610921 4000000 0 1 qz117 qz117 rfl)

noncomputable def ep627 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114) 17533860921 4000000 0 1 489905 489906 2147483648 (ep621 (Enclosure.Complex.normSq_eq_mul_add_mul qz114) (ep626 rfl rfl)) rfl

noncomputable def ep628 := @Enclosure.Real.IsNear.of_eq (Complex.re qz110) (@HMul.hMul Real Real Real qz0 qz111 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114))) Bool.false 8818299 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz114) (@ep617 8818299 17179869184 9 17179869184 qz116 (@ep620 4294967296 (ep627 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep629 := @Enclosure.Real.IsNear.of_eq (Complex.im qz110) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz115) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114))) Bool.true 129667207929 8589934592000 132339 8589934592000 (Enclosure.Complex.inv_im_eq_mul qz114)

noncomputable def ep630 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz115) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz114)) 264678 4000 0 1 979811 4294967296 1

noncomputable def ep631 := @ep630 4294967296 129667207929 8589934592000 132339 8589934592000 (@Enclosure.Real.IsNear.neg qz115 Bool.false 264678 4000 0 1 qz117) (@ep620 4294967296 (ep627 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep632 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109 0 1 0 1 129667207929 8589934592000 132339 8589934592000 0

noncomputable def ep633 := @Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (ep612 (BSN.stirling_coeff_mk 1 1 6 Bool.false BSN.bern_real_1 rfl rfl) qz419)

noncomputable def ep634 := @Enclosure.Complex.IsNear.im_isNear qz107 Bool.false 8818299 17179869184 9 17179869184 Bool.true 129667207929 8589934592000 132339 8589934592000

noncomputable abbrev qz118 := (@ep615 8589934592000 (BSN.zpow_one_sub_two_mul qz399 1 1 rfl rfl) (@ep616 8589934592000 ep628 (ep629 ep631)))

noncomputable def ep635 := @ep610 1 2939433 2939433 68719476736 3 68719476736 (@ep611 68719476736 3 68719476736 ep613 (ep614 qz118) rfl) (@ep632 1 0 1 ep633 (ep634 qz118) rfl) rfl

noncomputable def ep636 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108) 43222402643 34359738368000 44113 34359738368000 0 1 0

noncomputable def ep637 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz109 1 12 0 1 129667207929 8589934592000 132339 8589934592000 43222402643

noncomputable def ep638 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz108 0 1 0 1 8818299 17179869184 9 17179869184 0

noncomputable def ep639 := @ep636 1 43222402643 43222402643 34359738368000 44113 34359738368000 (@ep637 34359738368000 44113 34359738368000 ep613 (ep634 qz118) rfl) (@ep638 1 0 1 ep633 (ep614 qz118) rfl) rfl

noncomputable abbrev qz119 := (@Enclosure.Complex.IsNear.mk qz544 qz544 Bool.false 0 1 0 1 Bool.false 0 1 0 1 qz546 qz546)

noncomputable def ep640 := @ep607 34359738368000 (@ep608 0 1 0 1 (BSN.stirling_sum_base qz88) qz119) (ep609 (ep635 rfl) (ep639 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep641 := @ep564 963562910616464347503 4503599627370496000 ep556 ep549 (ep604 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep605 Bool.true 43222402643 34359738368000 44113 34359738368000 (BSN.stirling_sum_succ qz88 0 1 rfl) (ep640 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep642 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz12 2) Bool.false 9440247359690469 1125899906842624 15625000072957 6079750000000000000 Bool.false 877899813520803 281474976710656

noncomputable abbrev qz120 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz400 qz417))

noncomputable def ep643 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 1) qz120) Bool.false 9440247359690469 1125899906842624 15625000072957 6079750000000000000 Bool.false 877899813520803 281474976710656 125000000024319 24319000000000000000

noncomputable def ep644 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 1) qz120 Bool.false 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000 Bool.false

noncomputable def ep645 := nat_lit 42515094491387304909630943002624

noncomputable def ep646 := nat_lit 988427318260229079212671107072

noncomputable abbrev qz121 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz400 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep647 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz12 0) qz121) Bool.false 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000

noncomputable def ep648 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz12 0) qz121 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz422 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz629))

noncomputable def ep649 := @Enclosure.Complex.IsNear.of_eq qz121 qz422 Bool.false 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000

noncomputable def ep650 := BSN.log_dyadic_bound 4519443684 135591443684 2 1 55155118800934030475568 1048576 389104 20425371212847491856 20425371212847491856 69926 140110887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4519443684) (BSN.artanhQ 135591443684) 0 1 20425371212847491856 55155118800934030475568 20425371212847491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep651 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 70055443684 16000000)) 1 2 0 1 9440054623033061 1125899906842624 15625000072957 6079750000000000000 9440054623033061 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 70055443684 16000000 9440054623033061 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70055443684) qz632)) Bool.false 316755670924848479076352 37778931862957161709568 1000000004669248 389104000000000000000 9440054623033061 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 70055443684 16000000 12 140110887368 131072000000 69926 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep650 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep652 := BSN.arctan_dyadic_bound_f 1000 264678 1 0 1048576 389104 0 1 1 0 1 1 3961 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz423 := (@Nat.cast Real Real.instNatCast 1000)

noncomputable abbrev qz424 := (@Nat.cast Real Real.instNatCast 264678)

noncomputable def ep653 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz424)) 884279719003555 562949953421312 1 2000000000000000 3961 1048576 1 389104 925004645868369870848 882153173321123 562949953421312 125000000024319 48638000000000000000 qz100 (ep652 rfl) rfl rfl

noncomputable abbrev qz122 := (@HAdd.hAdd Complex Complex Complex qz272 qz400 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz425 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz629)

noncomputable def ep654 := @ep648 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000 Bool.false 9440054623033061 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 882153173321123 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz12 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz12) qz119) (ep649 (@congrArg Complex Complex qz122 qz425 Complex.log (BSN.w_shift_mk qz12 Bool.false 132339 1000 0 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz422 Bool.false 9440054623033061 2251799813685248 15625000072957 12159500000000000000 Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz422) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 70055443684 16000000))) Bool.false 9440054623033061 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 1000 264678 4000 70055443684 16000000 rfl rfl rfl) (ep651 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz422) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz423)) Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 1000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz423)) (@HSub.hSub Real Real Real qz401 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz424))) Bool.false 882153173321123 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 264678 1000 rfl rfl) ep653)))) rfl rfl

noncomputable abbrev qz426 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz629))

noncomputable def ep655 := @Enclosure.Complex.IsNear.of_eq qz120 qz426 Bool.false 9440440096347877 2251799813685248 15625000072957 12159500000000000000 Bool.false 873646453720483 562949953421312 125000000024319 48638000000000000000

noncomputable def ep656 := BSN.log_dyadic_bound 4543443684 135615443684 2 1 55174645696824526475568 1048576 389104 20642880509679491856 20642880509679491856 70285 140158887368 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 4543443684) (BSN.artanhQ 135615443684) 0 1 20642880509679491856 55174645696824526475568 20642880509679491856 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep657 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 70079443684 16000000)) 1 2 0 1 9440440096347877 1125899906842624 15625000072957 6079750000000000000 9440440096347877 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 70079443684 16000000 9440440096347877 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 70079443684) qz632)) Bool.false 316768605262978287140864 37778931862957161709568 1000000004669248 389104000000000000000 9440440096347877 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 70079443684 16000000 12 140158887368 131072000000 70285 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep656 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep658 := BSN.arctan_dyadic_bound_f 5000 264678 1 0 1048576 389104 0 1 1 0 1 1 19806 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 264678) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 264678) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz427 := (@Nat.cast Real Real.instNatCast 5000)

noncomputable def ep659 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz424)) 884279719003555 562949953421312 1 2000000000000000 19806 1048576 1 389104 916084703856409182208 873646453720483 562949953421312 125000000024319 48638000000000000000 qz100 (ep658 rfl) rfl rfl

noncomputable abbrev qz123 := (@HAdd.hAdd Complex Complex Complex qz272 qz400 qz417)

noncomputable abbrev qz428 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz629)

noncomputable def ep660 := @ep644 9440440096347877 2251799813685248 15625000072957 12159500000000000000 Bool.false 873646453720483 562949953421312 125000000024319 48638000000000000000 Bool.false ep645 9440247359690469 1125899906842624 15625000072957 6079750000000000000 Bool.false ep646 877899813520803 281474976710656 125000000024319 24319000000000000000 (ep647 (BSN.log_sum_c_succ qz12 0 1 rfl) (ep654 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep655 (@congrArg Complex Complex qz123 qz428 Complex.log (BSN.w_shift_mk qz12 Bool.false 132339 1000 1 qz13 rfl)) (@Enclosure.Complex.IsNear.of_parts qz426 Bool.false 9440440096347877 2251799813685248 15625000072957 12159500000000000000 Bool.false 873646453720483 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz426) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 70079443684 16000000))) Bool.false 9440440096347877 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 5000 264678 4000 70079443684 16000000 rfl rfl rfl) (ep657 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz426) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz427)) Bool.false 873646453720483 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 5000 264678 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz424 qz427)) (@HSub.hSub Real Real Real qz401 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz424))) Bool.false 873646453720483 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 264678 5000 rfl rfl) ep659)))) rfl rfl

noncomputable def ep661 := @ep557 ep549 Bool.false 9440247359690469 1125899906842624 15625000072957 6079750000000000000 Bool.false 877899813520803 281474976710656 125000000024319 24319000000000000000 Bool.true ep558 58585053748199385541 562949953421312000 1127000866663225632675701 ep554 Bool.false ep559 949516513600131499503 4503599627370496000 ep551 ep549 (@ep560 562949953421312000 1110616866586724673443701 ep554 Bool.false 963562910616464347503 4503599627370496000 ep556 ep549 (BSN.logGammaStirling_unfold 1 qz88) (ep641 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep642 125000000024319 24319000000000000000 (BSN.log_sum_c_eq qz12 2) (ep643 (BSN.log_sum_c_succ qz12 1 2 rfl) (ep660 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz124 := (@HDiv.hDiv Real Real Real qz270 qz277 (2 : Real))

noncomputable def ep662 := @Enclosure.Real.IsNear.mulLit_ff qz124 (Real.log Real.pi) 132339 2000 0 1 75021 65536 1 262144 9928204119 131072000 132339 524288000 (@Enclosure.Real.IsNear.of_eq qz124 (Enclosure.sfrac Bool.false 132339 2000) Bool.false 132339 2000 0 1 (BSN.t_half_eq qz12 Bool.false 132339 1000 qz13) (Enclosure.Real.IsNear.const Bool.false 132339 2000)) EMRow45.d5 rfl

noncomputable def ep663 := @ep552 132339 524288000 ep553 608386017607191561711 4503599627370496000 ep548 ep549 (@ep555 ep551 ep549 (ep661 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep662 rfl rfl

noncomputable def ep664 := BSN.cos_dyadic_bound_f 748936 2147483648 1 0 1048576 389484 0 1 1 0 1 1 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 748936) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 748936) qz16 0 0 rfl) rfl rfl

noncomputable def ep665 := @ep547 1048576 Bool.true 1048575 1048576 1 194552 (@ep550 35412727 262144 365 1048576 ep663 rfl) (Enclosure.sfrac_false_div 35412727 262144) (BSN.cos_reduce2 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13175435109517492224) qz336) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 35412727 262144 226375608064910080 72057594037927936 21 13175435109517492224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048575 1048576 13175435109517492224 37778931862957161709568 748936 2147483648 389484 389104 (ep664 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep666 := nat_lit 154053549839129476333568000

noncomputable def ep667 := nat_lit 4193123836763789410798859003

noncomputable def ep668 := nat_lit 661134402094904070874595328000

noncomputable abbrev qz634 := (@Nat.cast Complex Complex.instNatCast 34)

noncomputable abbrev qz429 := (@HPow.hPow Complex Complex Complex qz535 qz634 qz536)

noncomputable abbrev qz125 := qz429

noncomputable abbrev qz430 := qz634

noncomputable abbrev qz126 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz271 (1 : Complex))) qz405)

noncomputable abbrev qz127 := (@instHSub Nat instSubNat)

noncomputable abbrev qz431 := qz633

noncomputable abbrev qz128 := qz431

noncomputable abbrev qz129 := qz430

noncomputable def ep669 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz5 1 34) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false ep542 ep543 ep544

noncomputable def ep670 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (@HMul.hMul Complex Complex Complex qz78 qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 2279644796735 1099511627776 167888743079499 26739023275884544

noncomputable def ep671 := nat_lit 188321326476310581740520379

noncomputable def ep672 := nat_lit 13334903189715605012465457

noncomputable def ep673 := nat_lit 44540464625046301525235003

noncomputable def ep674 := nat_lit 175488826648605077412722835193705005056

noncomputable def ep675 := nat_lit 757126423271476887222022797281722368

noncomputable def ep676 := @ep670 Bool.false 100088622117 1099511627776 167785955469977 26739023275884544 Bool.true 95369619938243067889719 ep543 ep671 ep545 Bool.true ep672 ep666 ep673 ep668 Bool.false ep674 ep542 ep543 ep544 ep545 Bool.false ep675 688602470537695705590543 ep666

noncomputable def ep677 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz7) (BSN.headSumC qz5 34) Bool.false 2279644796735 1099511627776 167888743079499 26739023275884544 Bool.false 100088622117 1099511627776 167785955469977

noncomputable abbrev qz635 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz7)

noncomputable def ep678 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz5 34) (@HAdd.hAdd Complex Complex Complex qz4 qz65 qz635) Bool.false 2279644796735 1099511627776 167888743079499 26739023275884544 Bool.false 100088622117 1099511627776 167785955469977 26739023275884544

noncomputable def ep679 := @Enclosure.Complex.IsNear.addLitP qz65 qz635 Bool.false 2397094195321 1099511627776 164679692454009 26739023275884544 Bool.true 51038480035 1099511627776 164572417940349 26739023275884544 Bool.true

noncomputable def ep680 := nat_lit 1253247980604594250055680

noncomputable abbrev qz636 := (Real.log (Enclosure.sfrac Bool.false 33 1))

noncomputable abbrev qz130 := (@HMul.hMul Real Real Real qz267 qz277 qz636)

noncomputable abbrev qz432 := (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33)))

noncomputable def ep681 := @Enclosure.Complex.IsNear.of_eq qz635 (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz130)))) Bool.true 58724699293 549755813888 1604525312745 13369511637942272 Bool.false 18890887769 137438953472 803384382407 6684755818971136 (BSN.cpow_neg_s_mk qz12 132339 1000 33 qz13 rfl)

noncomputable abbrev qz433 := (Real.sqrt (@Nat.cast Real Real.instNatCast 33))

noncomputable abbrev qz434 := (@Nat.cast Real Real.instNatCast 33)

noncomputable abbrev qz637 := (@HDiv.hDiv Real Real Real qz1 qz434 qz14)

noncomputable def ep682 := @Enclosure.Real.IsNear.inv_image qz433 6023611 1048576 1 1048576 91266 91267 524288 (@Enclosure.Real.IsNear.of_eq qz433 (Real.sqrt qz637) Bool.false 6023611 1048576 1 1048576 (BSN.sqrt_natCast_div_one 33) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz637) Bool.false 6023611 1048576 1 1048576 6023611 1048576 1 1048576 (BSN.sqrt_enclosure 33 1 3011805 3011806 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep683 := BSN.log_dyadic_bound 1 65 2 1 12675 524288 194552 1 1 16133 66 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 1) (BSN.artanhQ 65) 0 1 1 12675 1 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep684 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz636 132339 1000 0 1 15746868335186131 4503599627370496 25000000024319 4863800000000000000 2083924808610197390409 4503599627370496000 3308475003218352141 4863800000000000000000 qz18 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 66047152845744529997824 18889465931478580854784 1000000000972760 194552000000000000000 15746868335186131 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep683 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep685 := nat_lit 521625531135130991840856984620086017054893576310744614034612971290383142164001

noncomputable def ep686 := nat_lit 212963659600557676179189883025746746628306392822579171963413112083311564321

noncomputable def ep687 := nat_lit 1564450666086191860170212574094206557671424116146588683759912087646982803363361

noncomputable def ep688 := BSN.cos_dyadic_bound_f 1954511309 2147483648 3 2 1048576 389484 ep685 ep71 ep686 ep687 ep74 ep686 643442 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1954511309) qz15 0 2 ep685 ep71 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1954511309) qz16 0 2 ep687 ep74 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz435 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 242600777) qz17)

noncomputable def ep689 := @Enclosure.Real.IsNear.cos_image qz130 qz435 Bool.false 242600777 524288 357 524288 Bool.true 643442 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 2083924808610197390409 4503599627370496000 3308475003218352141 4863800000000000000000 242600777 524288 357 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 242600777 524288) (BSN.cos_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68768253169910136438784) qz19) 226375608064910080 72057594037927936 Bool.false 643442 1048576 73 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 242600777 524288 226375608064910080 72057594037927936 73 68768253169910136438784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 643442 1048576 68768253169910136438784 75557863725914323419136 1954511309 2147483648 389484 389104 (ep688 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep690 := nat_lit 938755585115555339172599220409734233301505792245082241924732617833023006643745

noncomputable def ep691 := nat_lit 2458300781758529747309660222214881306771307436005883600667311330238353941534241

noncomputable def ep692 := BSN.sin_dyadic_bound_f 1954511309 2147483648 3 2 1048576 389484 ep690 ep78 ep686 ep691 ep80 ep686 827944 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 1954511309) qz20 0 2 ep690 ep78 ep686 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 1954511309) qz21 0 2 ep691 ep80 ep686 rfl rfl rfl rfl) rfl rfl

noncomputable def ep693 := @Enclosure.Real.IsNear.sin_image qz130 qz435 Bool.false 242600777 524288 357 524288 Bool.true 827944 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz130 Bool.false 2083924808610197390409 4503599627370496000 3308475003218352141 4863800000000000000000 242600777 524288 357 524288 (ep684 rfl) rfl) (Enclosure.sfrac_false_div 242600777 524288) (BSN.sin_reduce2 qz435 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 68768253169910136438784) qz19) 226375608064910080 72057594037927936 Bool.false 827944 1048576 73 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 242600777 524288 226375608064910080 72057594037927936 73 68768253169910136438784 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 827944 1048576 68768253169910136438784 75557863725914323419136 1954511309 2147483648 389484 389104 (ep692 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz436 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt (@Nat.cast Real Real.instNatCast 33))) Bool.false 182533 1048576 1 1048576 182533 1048576 1 1048576 (ep682 rfl rfl) rfl)

noncomputable def ep694 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz130)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz130))) Bool.true 58724699293 549755813888 1604525312745 13369511637942272 Bool.false 18890887769 137438953472 803384382407 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ft qz432 (Real.cos qz130) 182533 1048576 1 1048576 321721 524288 8747419 12750159872 58724699293 549755813888 1604525312745 13369511637942272 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz130) Bool.true 643442 1048576 69979352 102001278976 321721 524288 8747419 12750159872 (ep689 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (@Neg.neg Real Real.instNeg (Real.sin qz130)) 182533 1048576 1 1048576 103493 131072 8747419 12750159872 18890887769 137438953472 803384382407 6684755818971136 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz130) Bool.true 103493 131072 8747419 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz130) Bool.true 827944 1048576 69979352 102001278976 103493 131072 8747419 12750159872 (ep693 rfl rfl) rfl)) rfl)

noncomputable def ep695 := @ep679 58724699293 549755813888 1604525312745 13369511637942272 Bool.false 18890887769 137438953472 803384382407 6684755818971136 Bool.false ep680 2279644796735 1099511627776 167888743079499 26739023275884544 Bool.false 13756075478214953140224 100088622117 1099511627776 167785955469977 26739023275884544 EMRow45.d9 (ep681 ep694) rfl rfl

noncomputable def ep696 := @Enclosure.Complex.IsNear.mul qz125 (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.true 95369619938243067889719 ep543 ep671 ep545 Bool.true

noncomputable def ep697 := nat_lit 1326505148059285416539681

noncomputable abbrev qz131 := (Complex.re qz429)

noncomputable abbrev qz132 := (Complex.im qz429)

noncomputable def ep698 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 3906286557738113415867 308107099678258952667136 ep697

noncomputable def ep699 := nat_lit 22478569671226738409736241152

noncomputable def ep700 := nat_lit 3751363828149984112176709

noncomputable def ep701 := nat_lit 468303534817223716869505024000

noncomputable def ep702 := nat_lit 29384056996589929339936927730446387854163574784

noncomputable def ep703 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 27865762353 1099511627776 3154238402593 26739023275884544 420546889217

noncomputable abbrev qz638 := (Real.log (Enclosure.sfrac Bool.false 34 1))

noncomputable abbrev qz133 := (@HMul.hMul Real Real Real qz267 qz277 qz638)

noncomputable abbrev qz134 := (Real.sin (@HMul.hMul Real Real Real qz267 qz277 qz638))

noncomputable abbrev qz639 := (@Nat.cast Real Real.instNatCast 34)

noncomputable abbrev qz437 := (@Inv.inv Real Real.instInv (Real.sqrt qz639))

noncomputable abbrev qz640 := (@Neg.neg Real Real.instNeg qz134)

noncomputable def ep704 := @Enclosure.Complex.IsNear.of_eq qz125 (Complex.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz437 qz640)) Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (BSN.cpow_neg_s_mk qz12 132339 1000 34 qz13 rfl)

noncomputable abbrev qz438 := (Real.sqrt qz639)

noncomputable abbrev qz439 := (@HDiv.hDiv Real Real Real qz1 qz639 qz14)

noncomputable def ep705 := @Enclosure.Real.IsNear.inv_image qz438 6114197 1048576 1 1048576 89914 89915 524288 (@Enclosure.Real.IsNear.of_eq qz438 (Real.sqrt qz439) Bool.false 6114197 1048576 1 1048576 (BSN.sqrt_natCast_div_one 34) (@Enclosure.Real.IsNear.recentre' (Real.sqrt qz439) Bool.false 6114197 1048576 1 1048576 6114197 1048576 1 1048576 (BSN.sqrt_enclosure 34 1 3057098 3057099 524288 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep706 := BSN.log_dyadic_bound 2 66 2 1 13068 524288 194552 4 4 31784 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 2) (BSN.artanhQ 66) 0 1 4 13068 4 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz135 := qz638

noncomputable abbrev qz440 := (Real.log (@HDiv.hDiv Real Real Real qz1 qz639 qz14))

noncomputable def ep707 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz135 132339 1000 0 1 15881309401485523 4503599627370496 25000000024319 4863800000000000000 2101716604883192628297 4503599627370496000 3308475003218352141 4863800000000000000000 qz18 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false 66611039547888335060992 18889465931478580854784 1000000000972760 194552000000000000000 15881309401485523 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep706 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep708 := BSN.sin_dyadic_bound_f 318521831 2147483648 1 0 1048576 389484 0 1 1 0 1 1 154957 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 318521831) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 318521831) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz441 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 489344029) qz25)

noncomputable def ep709 := @Enclosure.Real.IsNear.cos_image qz133 qz441 Bool.false 489344029 1048576 715 1048576 Bool.true 154957 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2101716604883192628297 4503599627370496000 3308475003218352141 4863800000000000000000 489344029 1048576 715 1048576 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 489344029 1048576) (BSN.cos_reduce1 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22413981257537870102528) qz26) 226375608064910080 72057594037927936 Bool.false 154957 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 489344029 1048576 226375608064910080 72057594037927936 74 22413981257537870102528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 154957 1048576 22413981257537870102528 151115727451828646838272 318521831 2147483648 389484 389104 (ep708 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep710 := nat_lit 10293351757413407376815738534538721

noncomputable def ep711 := BSN.cos_dyadic_bound_f 318521831 2147483648 2 1 1048576 389484 ep710 ep57 ep710 ep710 ep58 ep710 1037062 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 318521831) qz15 0 1 ep710 ep57 ep710 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 318521831) qz16 0 1 ep710 ep58 ep710 rfl rfl rfl rfl) rfl rfl

noncomputable def ep712 := @Enclosure.Real.IsNear.sin_image qz133 qz441 Bool.false 489344029 1048576 715 1048576 Bool.false 1037062 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2101716604883192628297 4503599627370496000 3308475003218352141 4863800000000000000000 489344029 1048576 715 1048576 (ep707 rfl) rfl) (Enclosure.sfrac_false_div 489344029 1048576) (BSN.sin_reduce1 qz441 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 22413981257537870102528) qz26) 226375608064910080 72057594037927936 Bool.false 1037062 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 489344029 1048576 226375608064910080 72057594037927936 74 22413981257537870102528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1037062 1048576 22413981257537870102528 151115727451828646838272 318521831 2147483648 389484 389104 (ep711 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz442 := (@Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (Real.sqrt qz639)) Bool.false 179829 1048576 1 1048576 179829 1048576 1 1048576 (ep705 rfl rfl) rfl)

noncomputable def ep713 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz437 qz640) Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ft qz437 (Real.cos qz133) 179829 1048576 1 1048576 154957 1048576 17519157 25500319744 27865762353 1099511627776 3154238402593 26739023275884544 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.true 154957 1048576 140153256 204002557952 154957 1048576 17519157 25500319744 (ep709 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz437 qz640 179829 1048576 1 1048576 518531 524288 17519157 25500319744 93246911199 549755813888 396961289261 3342377909485568 qz442 (@Enclosure.Real.IsNear.neg qz134 Bool.false 518531 524288 17519157 25500319744 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1037062 1048576 140153256 204002557952 518531 524288 17519157 25500319744 (ep712 rfl rfl) rfl)) rfl)

noncomputable def ep714 := @ep703 840665324208 0 1 3906286557738113415867 308107099678258952667136 ep697 ep699 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (ep704 ep713))

noncomputable def ep715 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 420546889217 840665324208 0 1 Bool.false

noncomputable def ep716 := @Enclosure.Complex.IsNear.addLitP qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 1028227113 2060454226 0 1 Bool.true 264678000

noncomputable def ep717 := @ep716 1030227113 0 1 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1 Bool.false 841093778434 420546889217 840665324208 0 1 Bool.false 9450200635769 9450200635769 140110887368000 0 1

noncomputable abbrev qz136 := (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz271 (1 : Complex)))

noncomputable def ep718 := @Enclosure.Complex.IsNear.addLitP qz136 qz103 Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1

noncomputable def ep719 := @Enclosure.Complex.IsNear.of_eq qz136 (Complex.mk (Enclosure.sfrac Bool.true 68000000 70055443684) (Enclosure.sfrac Bool.true 17998104000 70055443684)) Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1

noncomputable def ep720 := @ep718 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 69919443684 1028227113 2060454226 0 1 Bool.true 17998104000 264678000 1030227113 0 1 (ep719 (BSN.N_div_s_sub_one_mk qz12 132339 1000 34 qz13 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 68000000 70055443684) (Enclosure.sfrac Bool.true 17998104000 70055443684) Bool.true 68000000 70055443684 0 1 Bool.true 17998104000 70055443684 0 1 (Enclosure.Real.IsNear.const Bool.true 68000000 70055443684) (Enclosure.Real.IsNear.const Bool.true 17998104000 70055443684))) qz104 rfl

noncomputable abbrev qz137 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 1)))

noncomputable abbrev qz443 := (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz633 qz634 1))

noncomputable abbrev qz138 := qz443

noncomputable def ep721 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz138)) Bool.false 1 816 0 1

noncomputable def ep722 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz138) Bool.false 0 1 0 1 Bool.false

noncomputable def ep723 := @ep722 0 1 0 1 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1 Bool.false 1 1 816 0 1 Bool.false 44113 44113 136000 0

noncomputable def ep724 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep725 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz138 Bool.false 1 816 0 1 Bool.false 44113 136000 0 1

noncomputable abbrev qz139 := (Complex.re qz443)

noncomputable abbrev qz140 := (Complex.im qz443)

noncomputable def ep726 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 1 816 0 1 0 1 0

noncomputable def ep727 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 1 34 0 1 1

noncomputable def ep728 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep729 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep730 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (Complex.mk (Enclosure.sfrac Bool.false 1 12) qz10) Bool.false 1 12 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 1 1 6 2 Bool.false BSN.bern_real_1 EMRow45.d10 rfl) qz419

noncomputable def ep731 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz5 Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 (BSN.ascPochhammer_one_eval qz5)

noncomputable def ep732 := ep731 (@Enclosure.Complex.IsNear.of_eq qz5 (Complex.mk qz98 qz12) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_crit_mk qz12 Bool.false 132339 1000 qz13) (@Enclosure.Complex.IsNear.mk qz98 qz12 Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 qz412 qz18))

noncomputable def ep733 := @ep729 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep734 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 132339 1000 0 1 0 1 0

noncomputable def ep735 := @ep734 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep736 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) 44113 4000 0 1 0 1 0 1 44113

noncomputable def ep737 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 132339 1000 0 1 44113 4000 0

noncomputable def ep738 := @ep737 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep739 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep740 := @ep739 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep741 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 (@ep728 1 24 0 1 (ep733 rfl) (ep735 rfl) rfl rfl) (@ep736 44113 4000 0 1 (ep738 rfl) (ep740 rfl) rfl rfl)

noncomputable def ep742 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 ep741

noncomputable abbrev qz141 := (@Enclosure.Complex.IsNear.re_isNear qz443 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz443 (Complex.mk (Enclosure.sfrac Bool.false 1 34) qz544) Bool.false 1 34 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 34 1 34 EMRow45.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 34) qz544 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 34) qz546)))

noncomputable def ep743 := @ep727 816 0 1 ep742 qz141

noncomputable def ep744 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 44113 4000 0 1 0 1 0 1 0

noncomputable def ep745 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 44113 4000 0 1 ep741

noncomputable abbrev qz142 := (@Enclosure.Complex.IsNear.im_isNear qz443 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (@Enclosure.Complex.IsNear.of_eq qz443 (Complex.mk (Enclosure.sfrac Bool.false 1 34) qz544) Bool.false 1 34 0 1 Bool.false 0 1 0 1 (BSN.natCast_pow_inv_mk 34 1 34 EMRow45.d11 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 34) qz544 Bool.false 1 34 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 34) qz546)))

noncomputable def ep746 := @ep744 1 0 1 ep745 qz142

noncomputable def ep747 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 0 1 0 1 44113 136000 0

noncomputable def ep748 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 0 1 0 1 0

noncomputable def ep749 := @ep748 1 0 1 ep742 qz142

noncomputable def ep750 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 44113 4000 0 1 1 34 0 1 44113

noncomputable def ep751 := @ep750 136000 0 1 ep745 qz141

noncomputable def ep752 := @ep723 1 (@ep724 0 1 0 1 (BSN.bern_sum_base qz5 34) qz119) (ep725 (@ep726 1 1 1 816 0 1 (ep743 rfl) (ep746 rfl) rfl rfl) (@ep747 1 44113 44113 136000 0 1 (ep749 rfl) (ep751 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep753 := ep717 (ep720 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep721 Bool.false 44113 136000 0 1 (BSN.bern_sum_succ qz5 34 0 1 1 rfl rfl) (ep752 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep754 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 93246911199 549755813888 396961289261 3342377909485568 9450200635769

noncomputable def ep755 := @ep754 140110887368000 0 1 881202019496285286077031 ep543 ep700 ep701 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (ep704 ep713))

noncomputable def ep756 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 420546889217 840665324208 0 1 Bool.false

noncomputable def ep757 := nat_lit 29808185757551363578149017

noncomputable def ep758 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 263337045104508465404457 ep666 ep757

noncomputable def ep759 := nat_lit 3746428278537789734956040192000

noncomputable def ep760 := nat_lit 2809821208903342301217030144

noncomputable def ep761 := nat_lit 2054289173136819583397374101077060333308609560576

noncomputable def ep762 := @Enclosure.Real.IsNear.mulLit_tf qz131 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 27865762353 1099511627776 3154238402593 26739023275884544 9450200635769

noncomputable def ep763 := @ep762 140110887368000 0 1 263337045104508465404457 ep666 ep757 ep759 (@Enclosure.Complex.IsNear.re_isNear qz125 Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (ep704 ep713))

noncomputable def ep764 := @Enclosure.Real.IsNear.mulLit_tf qz132 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz126 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 93246911199 549755813888 396961289261 3342377909485568 420546889217

noncomputable def ep765 := @ep764 840665324208 0 1 13071566144611096547061 154053549839129476333568 166940835338283258798637 ep760 (@Enclosure.Complex.IsNear.im_isNear qz125 Bool.true 27865762353 1099511627776 3154238402593 26739023275884544 Bool.true 93246911199 549755813888 396961289261 3342377909485568 (ep704 ep713))

noncomputable abbrev qz641 := (ep753 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep766 := @ep696 ep672 ep666 ep673 ep668 (@ep698 ep699 881202019496285286077031 ep543 ep700 ep701 ep702 95369619938243067889719 ep543 ep671 ep545 (ep714 (@ep715 9450200635769 140110887368000 0 1 qz641) rfl) (ep755 (@ep756 9450200635769 140110887368000 0 1 qz641) rfl) rfl rfl) (@ep758 ep759 13071566144611096547061 154053549839129476333568 166940835338283258798637 ep760 ep761 ep672 ep666 ep673 ep668 (ep763 (@ep756 9450200635769 140110887368000 0 1 qz641) rfl) (ep765 (@ep715 9450200635769 140110887368000 0 1 qz641) rfl) rfl rfl)

noncomputable def ep767 := @ep676 ep667 ep668 (@ep677 26739023275884544 (BSN.head_sum_c_eq qz5 34) (ep678 (BSN.head_sum_c_succ qz5 33 34 rfl rfl) (ep695 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep766 rfl rfl rfl

noncomputable def ep768 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz5 1 34) Bool.false ep542 ep543 ep544 ep545 Bool.false 688602470537695705590543 ep666 ep667 ep668 (@ep669 ep545 Bool.false 688602470537695705590543 ep666 ep667 ep668 (BSN.zetaApproximant_eq_folded' qz5 1 34 rfl) (ep767 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep769 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) (Complex.im (zetaApproximant qz5 1 34)) 365 1048576 9007507

noncomputable def ep770 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82)) Bool.true 365 1048576 72060056

noncomputable def ep771 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) qz402 Bool.false 35412727 262144 365

noncomputable def ep772 := BSN.sin_dyadic_bound_f 748936 2147483648 1 0 1048576 389484 0 1 1 0 1 1 365 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 748936) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 748936) qz21 0 0 rfl) rfl rfl

noncomputable def ep773 := @ep771 1048576 Bool.true 365 1048576 1 194552 (@ep550 35412727 262144 365 1048576 ep663 rfl) (Enclosure.sfrac_false_div 35412727 262144) (BSN.sin_reduce2 qz402 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 13175435109517492224) qz336) 226375608064910080 72057594037927936 Bool.false 365 1048576 21 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 35412727 262144 226375608064910080 72057594037927936 21 13175435109517492224 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 365 1048576 13175435109517492224 37778931862957161709568 748936 2147483648 389484 389104 (ep772 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep774 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz5 1 34) Bool.false ep542 ep543 ep544 ep545 Bool.false 688602470537695705590543 ep666 ep667 ep668 (@ep669 ep545 Bool.false 688602470537695705590543 ep666 ep667 ep668 (BSN.zetaApproximant_eq_folded' qz5 1 34 rfl) (ep767 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow45.d12 : Enclosure.Real.IsNear (hardyZApproximantEM 1 34 qz12) Bool.true ep525 ep526 ep527 ep528 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 34 qz12) ep529 Bool.true ep525 ep526 ep527 ep528 (@Eq.refl Real ep529) (@ep530 Bool.true ep525 ep526 ep527 ep528 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz80 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz81 (@Nat.cast Complex Complex.instNatCast j))))) qz82) (zetaApproximant qz5 1 34)) (@ep532 ep533 ep534 ep535 ep536 ep537 ep538 ep539 ep540 ep525 ep526 ep527 ep528 (@ep541 25500319744 ep542 ep543 ep544 ep545 ep531 ep533 ep534 ep535 (@ep546 204002557952 1048575 1048576 9007507 25500319744 (ep665 rfl rfl) rfl) ep768 rfl) (@ep769 25500319744 688602470537695705590543 ep666 ep667 ep668 ep536 ep537 ep538 ep539 (@ep770 204002557952 365 1048576 9007507 25500319744 (ep773 rfl rfl) rfl) ep774 rfl) rfl rfl))

noncomputable abbrev qz693 := (@HAdd.hAdd Complex Complex Complex (@instHAdd Complex Complex.instAdd) (@HDiv.hDiv Complex Complex Complex (@instHDiv Complex (@DivInvMonoid.toDiv Complex Complex.instDivInvMonoid)) (1 : Complex) (2 : Complex)) (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul) Complex.I ↑(Enclosure.sfrac Bool.false 134395 1000)))

noncomputable abbrev qz642 := qz693

noncomputable abbrev qz444 := qz642

noncomputable abbrev qz143 := (BSN.headSumC qz444 9)

noncomputable abbrev qz144 := qz444

noncomputable abbrev qz643 := (@Neg.neg Complex Complex.instNeg qz693)

noncomputable abbrev qz445 := qz643

noncomputable abbrev qz145 := qz445

noncomputable abbrev qz644 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 8) qz145)

noncomputable def ep775 := @Enclosure.Complex.IsNear.of_eq qz143 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 8) qz644) Bool.true 410248711963 549755813888 7866566672861 3342377909485568 Bool.false 749100856717 1099511627776 62901752994821 26739023275884544

noncomputable def ep776 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 8) qz644 Bool.true 108827461641 274877906944 28156625341563 13369511637942272 Bool.false 801497927989 1099511627776 56304300731789 26739023275884544 Bool.true

noncomputable abbrev qz645 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 7) qz145)

noncomputable def ep777 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 8) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 7) qz645) Bool.true 108827461641 274877906944 28156625341563 13369511637942272 Bool.false 801497927989 1099511627776 56304300731789 26739023275884544

noncomputable def ep778 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 7) qz645 Bool.true 136439182439 1099511627776 49255231666509 26739023275884544 Bool.false 64092684733 137438953472 12311725584013 6684755818971136 Bool.true

noncomputable abbrev qz646 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 6) qz145)

noncomputable def ep779 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 7) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 6) qz646) Bool.true 136439182439 1099511627776 49255231666509 26739023275884544 Bool.false 64092684733 137438953472 12311725584013 6684755818971136

noncomputable def ep780 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 6) qz646 Bool.false 16867242967 274877906944 20819971110261 13369511637942272 Bool.false 228156798731 274877906944 1300639983801 835594477371392 Bool.true

noncomputable abbrev qz647 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 5) qz145)

noncomputable def ep781 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 6) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 5) qz647) Bool.false 16867242967 274877906944 20819971110261 13369511637942272 Bool.false 228156798731 274877906944 1300639983801 835594477371392

noncomputable def ep782 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 5) qz647 Bool.false 505925535805 1099511627776 33287764453717 26739023275884544 Bool.false 283800863151 274877906944 16639748616993 13369511637942272 Bool.true

noncomputable abbrev qz648 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 4) qz145)

noncomputable def ep783 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 5) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 4) qz648) Bool.false 505925535805 1099511627776 33287764453717 26739023275884544 Bool.false 283800863151 274877906944 16639748616993 13369511637942272

noncomputable def ep784 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 4) qz648 Bool.false 822599078101 1099511627776 23960490199229 26739023275884544 Bool.false 685817666285 1099511627776 23946067135347 26739023275884544 Bool.true

noncomputable def ep785 := nat_lit 1248169396029559305928704

noncomputable def ep786 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 4) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz145)) Bool.false 822599078101 1099511627776 23960490199229 26739023275884544 Bool.false 685817666285 1099511627776 23946067135347 26739023275884544

noncomputable def ep787 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 3) (@HPow.hPow Complex Complex Complex qz6 qz8 qz145) Bool.false 1457386005351 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 274877906944 3298159231307 6684755818971136 Bool.true

noncomputable def ep788 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 3) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz145)) Bool.false 1457386005351 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 274877906944 3298159231307 6684755818971136

noncomputable def ep789 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 2) (@HPow.hPow Complex Complex Complex qz6 qz9 qz145) Bool.false 1 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable def ep790 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 2) (Complex.mk (Enclosure.sfrac Bool.false 1 1) qz10) Bool.false 1 1 0 1 Bool.false 0 1 0 1 (BSN.head_sum_c_two qz144)

noncomputable abbrev qz694 := (Enclosure.sfrac Bool.false 134395 1000)

noncomputable abbrev qz649 := qz694

noncomputable abbrev qz446 := qz649

noncomputable abbrev qz146 := (@HMul.hMul Real Real Real qz267 qz446 (Real.log qz278))

noncomputable abbrev qz147 := qz446

noncomputable abbrev qz447 := (@Eq.refl Real qz649)

noncomputable abbrev qz148 := qz447

noncomputable def ep791 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz9 qz145) (Complex.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz146)))) Bool.false 357874377575 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 274877906944 3298159231307 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 2 qz148 rfl)

noncomputable def ep792 := nat_lit 1113436213412395998864496382736921616

noncomputable def ep793 := BSN.sin_dyadic_bound_f 1027226786 2147483648 2 1 1048576 389484 ep792 ep61 ep792 ep792 ep62 ep792 482665 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1027226786) qz20 0 1 ep792 ep61 ep792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1027226786) qz21 0 1 ep792 ep62 ep792 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz149 := (Enclosure.Real.IsNear.const Bool.false 134395 1000)

noncomputable abbrev qz448 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 24420109) qz41)

noncomputable def ep794 := @Enclosure.Real.IsNear.cos_image qz146 qz448 Bool.false 24420109 262144 725 1048576 Bool.false 482665 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 610502727 6553600 26879 38910400 24420109 262144 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 (Real.log qz278) 134395 1000 0 1 363408 524288 1 194552 610502727 6553600 26879 38910400 qz149 qz284 rfl) rfl) (Enclosure.sfrac_false_div 24420109 262144) (BSN.cos_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18071164734401169850368) qz336) 226375608064910080 72057594037927936 Bool.false 482665 1048576 14 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 24420109 262144 226375608064910080 72057594037927936 14 18071164734401169850368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 482665 1048576 18071164734401169850368 37778931862957161709568 1027226786 2147483648 389484 389104 (ep793 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep795 := BSN.cos_dyadic_bound_f 1027226786 2147483648 2 1 1048576 389484 ep792 ep57 ep792 ep792 ep58 ep792 930884 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1027226786) qz15 0 1 ep792 ep57 ep792 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1027226786) qz16 0 1 ep792 ep58 ep792 rfl rfl rfl rfl) rfl rfl

noncomputable def ep796 := @Enclosure.Real.IsNear.sin_image qz146 qz448 Bool.false 24420109 262144 725 1048576 Bool.true 930884 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz146 Bool.false 610502727 6553600 26879 38910400 24420109 262144 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 (Real.log qz278) 134395 1000 0 1 363408 524288 1 194552 610502727 6553600 26879 38910400 qz149 qz284 rfl) rfl) (Enclosure.sfrac_false_div 24420109 262144) (BSN.sin_reduce3 qz448 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 18071164734401169850368) qz336) 226375608064910080 72057594037927936 Bool.false 930884 1048576 14 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 24420109 262144 226375608064910080 72057594037927936 14 18071164734401169850368 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 930884 1048576 18071164734401169850368 37778931862957161709568 1027226786 2147483648 389484 389104 (ep795 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep797 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz280 (Real.cos qz146)) (@HMul.hMul Real Real Real qz0 qz280 (@Neg.neg Real Real.instNeg (Real.sin qz146))) Bool.false 357874377575 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 274877906944 3298159231307 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz280 (Real.cos qz146) 741455 1048576 1 1048576 482665 1048576 17762347 25500319744 357874377575 1099511627776 13181736687367 26739023275884544 qz285 (@Enclosure.Real.IsNear.recentre' (Real.cos qz146) Bool.false 482665 1048576 142098776 204002557952 482665 1048576 17762347 25500319744 (ep794 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz280 (@Neg.neg Real Real.instNeg (Real.sin qz146)) 741455 1048576 1 1048576 232721 262144 17762347 25500319744 172552149055 274877906944 3298159231307 6684755818971136 qz285 (@Enclosure.Real.IsNear.neg (Real.sin qz146) Bool.true 232721 262144 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz146) Bool.true 930884 1048576 142098776 204002557952 232721 262144 17762347 25500319744 (ep796 rfl rfl) rfl)) rfl)

noncomputable def ep798 := @ep789 357874377575 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 274877906944 3298159231307 6684755818971136 Bool.false 1457386005351 1457386005351 1099511627776 13181736687367 26739023275884544 Bool.false 172552149055 172552149055 274877906944 3298159231307 6684755818971136 (ep790 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 1 1) qz10 Bool.false 1 1 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.false 1 1) qz22)) (ep791 ep797) rfl rfl

noncomputable abbrev qz150 := (@HMul.hMul Real Real Real qz267 qz446 qz547)

noncomputable def ep799 := @Enclosure.Complex.IsNear.of_eq (@HPow.hPow Complex Complex Complex qz6 qz8 qz145) (Complex.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz150)))) Bool.true 317393463625 549755813888 5389376755931 13369511637942272 Bool.true 4390929935 1099511627776 10753430210119 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 3 qz148 rfl)

noncomputable def ep800 := nat_lit 8197678126503949591954578563341088482167306235736975103644113647344964086499265

noncomputable def ep801 := nat_lit 16183141768389360294410103268527231707405838222482536494480125684246859188161

noncomputable def ep802 := nat_lit 21443908101790094728928184641553806697197621165046153545695901253843268168812481

noncomputable def ep803 := BSN.sin_dyadic_bound_f 3358403353 2147483648 3 2 1048576 389484 ep800 ep78 ep801 ep802 ep80 ep801 1048550 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3358403353) qz20 0 2 ep800 ep78 ep801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3358403353) qz21 0 2 ep802 ep80 ep801 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz449 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 154820083) qz25)

noncomputable def ep804 := @Enclosure.Real.IsNear.cos_image qz150 qz449 Bool.false 154820083 1048576 725 1048576 Bool.true 1048550 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 15482008331 104857600 26879 38910400 154820083 1048576 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz547 134395 1000 0 1 575989 524288 1 194552 15482008331 104857600 26879 38910400 qz149 qz290 rfl) rfl) (Enclosure.sfrac_false_div 154820083 1048576) (BSN.cos_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236326626453399258791936) qz26) 226375608064910080 72057594037927936 Bool.false 1048550 1048576 23 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 154820083 1048576 226375608064910080 72057594037927936 23 236326626453399258791936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048550 1048576 236326626453399258791936 151115727451828646838272 3358403353 2147483648 389484 389104 (ep803 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep805 := nat_lit 4561458133288145044550059247753283481962906059063867296022054304384645318805441

noncomputable def ep806 := nat_lit 13652008116327656413061357536722795982473906500746636815077202661785442238040001

noncomputable def ep807 := BSN.cos_dyadic_bound_f 3358403353 2147483648 3 2 1048576 389484 ep805 ep71 ep801 ep806 ep74 ep801 7253 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3358403353) qz15 0 2 ep805 ep71 ep801 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3358403353) qz16 0 2 ep806 ep74 ep801 rfl rfl rfl rfl) rfl rfl

noncomputable def ep808 := @Enclosure.Real.IsNear.sin_image qz150 qz449 Bool.false 154820083 1048576 725 1048576 Bool.false 7253 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz150 Bool.false 15482008331 104857600 26879 38910400 154820083 1048576 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz547 134395 1000 0 1 575989 524288 1 194552 15482008331 104857600 26879 38910400 qz149 qz290 rfl) rfl) (Enclosure.sfrac_false_div 154820083 1048576) (BSN.sin_reduce1 qz449 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 236326626453399258791936) qz26) 226375608064910080 72057594037927936 Bool.false 7253 1048576 23 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 154820083 1048576 226375608064910080 72057594037927936 23 236326626453399258791936 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 7253 1048576 236326626453399258791936 151115727451828646838272 3358403353 2147483648 389484 389104 (ep807 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep809 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz286 (Real.cos qz150)) (@HMul.hMul Real Real Real qz0 qz286 (@Neg.neg Real Real.instNeg (Real.sin qz150))) Bool.true 317393463625 549755813888 5389376755931 13369511637942272 Bool.true 4390929935 1099511627776 10753430210119 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz286 (Real.cos qz150) 605395 1048576 1 1048576 524275 524288 17762347 25500319744 317393463625 549755813888 5389376755931 13369511637942272 qz292 (@Enclosure.Real.IsNear.recentre' (Real.cos qz150) Bool.true 1048550 1048576 142098776 204002557952 524275 524288 17762347 25500319744 (ep804 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz286 (@Neg.neg Real Real.instNeg (Real.sin qz150)) 605395 1048576 1 1048576 7253 1048576 17762347 25500319744 4390929935 1099511627776 10753430210119 26739023275884544 qz292 (@Enclosure.Real.IsNear.neg (Real.sin qz150) Bool.false 7253 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz150) Bool.false 7253 1048576 142098776 204002557952 7253 1048576 17762347 25500319744 (ep808 rfl rfl) rfl)) rfl)

noncomputable def ep810 := @ep787 317393463625 549755813888 5389376755931 13369511637942272 Bool.true 4390929935 1099511627776 10753430210119 26739023275884544 Bool.false 452228625684933732466688 822599078101 1099511627776 23960490199229 26739023275884544 Bool.false 188516124653639476183040 685817666285 1099511627776 23946067135347 26739023275884544 (ep788 (BSN.head_sum_c_succ qz144 2 3 rfl rfl) (ep798 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep799 ep809) rfl rfl

noncomputable abbrev qz151 := (@HMul.hMul Real Real Real qz267 qz446 qz548)

noncomputable def ep811 := @Enclosure.Complex.IsNear.of_eq qz648 (Complex.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz151)))) Bool.true 39584192787 137438953472 1165909281811 3342377909485568 Bool.false 449385786319 1099511627776 9333430098639 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 4 qz148 rfl)

noncomputable def ep812 := nat_lit 637524029892213394966475671356574641602027380372692735961634281726375561854976

noncomputable def ep813 := nat_lit 318054973196790738414656602600748988513113608422013950970078378557450551296

noncomputable def ep814 := nat_lit 1911935979730246603422597700864522426829055913901234179982962688422011784462336

noncomputable def ep815 := BSN.cos_dyadic_bound_f 2055004484 2147483648 3 2 1048576 389484 ep812 ep71 ep813 ep814 ep74 ep813 604008 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2055004484) qz15 0 2 ep812 ep71 ep813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2055004484) qz16 0 2 ep814 ep74 ep813 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz450 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195361141) qz25)

noncomputable def ep816 := @Enclosure.Real.IsNear.cos_image qz151 qz450 Bool.false 195361141 1048576 725 1048576 Bool.true 604008 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 19536114143 104857600 26879 38910400 195361141 1048576 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz548 134395 1000 0 1 726817 524288 1 194552 19536114143 104857600 26879 38910400 qz149 qz297 rfl) rfl) (Enclosure.sfrac_false_div 195361141 1048576) (BSN.cos_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144608084860801764032512) qz26) 226375608064910080 72057594037927936 Bool.false 604008 1048576 29 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 195361141 1048576 226375608064910080 72057594037927936 29 144608084860801764032512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 604008 1048576 144608084860801764032512 151115727451828646838272 2055004484 2147483648 389484 389104 (ep815 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep817 := nat_lit 1147288809827426678348924483159753755692838793784109313570165644404630050897920

noncomputable def ep818 := nat_lit 3004289079591417924956416583299906242737937514068555417715529894161128546697216

noncomputable def ep819 := BSN.sin_dyadic_bound_f 2055004484 2147483648 3 2 1048576 389484 ep817 ep78 ep813 ep818 ep80 ep813 857137 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2055004484) qz20 0 2 ep817 ep78 ep813 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2055004484) qz21 0 2 ep818 ep80 ep813 rfl rfl rfl rfl) rfl rfl

noncomputable def ep820 := @Enclosure.Real.IsNear.sin_image qz151 qz450 Bool.false 195361141 1048576 725 1048576 Bool.true 857137 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz151 Bool.false 19536114143 104857600 26879 38910400 195361141 1048576 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz548 134395 1000 0 1 726817 524288 1 194552 19536114143 104857600 26879 38910400 qz149 qz297 rfl) rfl) (Enclosure.sfrac_false_div 195361141 1048576) (BSN.sin_reduce2 qz450 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 144608084860801764032512) qz26) 226375608064910080 72057594037927936 Bool.false 857137 1048576 29 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 195361141 1048576 226375608064910080 72057594037927936 29 144608084860801764032512 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 857137 1048576 144608084860801764032512 151115727451828646838272 2055004484 2147483648 389484 389104 (ep819 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep821 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz293 (Real.cos qz151)) (@HMul.hMul Real Real Real qz0 qz293 (@Neg.neg Real Real.instNeg (Real.sin qz151))) Bool.true 39584192787 137438953472 1165909281811 3342377909485568 Bool.false 449385786319 1099511627776 9333430098639 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz293 (Real.cos qz151) 524287 1048576 1 1048576 75501 131072 17762347 25500319744 39584192787 137438953472 1165909281811 3342377909485568 qz298 (@Enclosure.Real.IsNear.recentre' (Real.cos qz151) Bool.true 604008 1048576 142098776 204002557952 75501 131072 17762347 25500319744 (ep816 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz293 (@Neg.neg Real Real.instNeg (Real.sin qz151)) 524287 1048576 1 1048576 857137 1048576 17762347 25500319744 449385786319 1099511627776 9333430098639 26739023275884544 qz298 (@Enclosure.Real.IsNear.neg (Real.sin qz151) Bool.true 857137 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz151) Bool.true 857137 1048576 142098776 204002557952 857137 1048576 17762347 25500319744 (ep820 rfl rfl) rfl)) rfl)

noncomputable def ep822 := @ep784 39584192787 137438953472 1165909281811 3342377909485568 Bool.false 449385786319 1099511627776 9333430098639 26739023275884544 Bool.false 69533876175800065064960 505925535805 1099511627776 33287764453717 26739023275884544 Bool.false ep785 283800863151 274877906944 16639748616993 13369511637942272 (ep786 (BSN.head_sum_c_succ qz144 3 4 rfl rfl) (ep810 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep811 ep821) rfl rfl

noncomputable abbrev qz152 := (@HMul.hMul Real Real Real qz267 qz446 qz549)

noncomputable def ep823 := @Enclosure.Complex.IsNear.of_eq qz647 (Complex.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz152)))) Bool.true 438456563937 1099511627776 8352177766805 26739023275884544 Bool.true 13911016105 68719476736 4170491123823 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 5 qz148 rfl)

noncomputable def ep824 := nat_lit 2011286305375635232208859496585203388742801802681441479556562298829931737579520

noncomputable def ep825 := nat_lit 977064512284582678409884866786962692847096750538898131366618594958859370496

noncomputable def ep826 := nat_lit 5266072695344869617162920772700734745204633231331474230435450543019887826108416

noncomputable def ep827 := BSN.sin_dyadic_bound_f 2364505916 2147483648 3 2 1048576 389484 ep824 ep78 ep825 ep826 ep80 ep825 935001 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2364505916) qz20 0 2 ep824 ep78 ep825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2364505916) qz21 0 2 ep826 ep80 ep825 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz451 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14175447) (@Nat.cast Real Real.instNatCast 65536))

noncomputable def ep828 := @Enclosure.Real.IsNear.cos_image qz152 qz451 Bool.false 14175447 65536 725 1048576 Bool.true 935001 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 708772351 3276800 26879 38910400 14175447 65536 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz549 134395 1000 0 1 843808 524288 1 194552 708772351 3276800 26879 38910400 qz149 qz303 rfl) rfl) (Enclosure.sfrac_false_div 14175447 65536) (BSN.cos_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10399206994880153780224) qz621) 226375608064910080 72057594037927936 Bool.false 935001 1048576 34 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 14175447 65536 226375608064910080 72057594037927936 34 10399206994880153780224 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 935001 1048576 10399206994880153780224 9444732965739290427392 2364505916 2147483648 389484 389104 (ep827 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep829 := nat_lit 1117815531658590499084215224710351643831710822267706998923141996503277125042176

noncomputable def ep830 := nat_lit 3351492465951202331895825904397481006109438273302043200506692752319913656385536

noncomputable def ep831 := BSN.cos_dyadic_bound_f 2364505916 2147483648 3 2 1048576 389484 ep829 ep71 ep825 ep830 ep74 ep825 474640 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2364505916) qz15 0 2 ep829 ep71 ep825 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2364505916) qz16 0 2 ep830 ep74 ep825 rfl rfl rfl rfl) rfl rfl

noncomputable def ep832 := @Enclosure.Real.IsNear.sin_image qz152 qz451 Bool.false 14175447 65536 725 1048576 Bool.false 474640 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz152 Bool.false 708772351 3276800 26879 38910400 14175447 65536 725 1048576 (@Enclosure.Real.IsNear.mulLit_ff qz147 qz549 134395 1000 0 1 843808 524288 1 194552 708772351 3276800 26879 38910400 qz149 qz303 rfl) rfl) (Enclosure.sfrac_false_div 14175447 65536) (BSN.sin_reduce1 qz451 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 10399206994880153780224) qz621) 226375608064910080 72057594037927936 Bool.false 474640 1048576 34 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 14175447 65536 226375608064910080 72057594037927936 34 10399206994880153780224 9444732965739290427392 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 474640 1048576 10399206994880153780224 9444732965739290427392 2364505916 2147483648 389484 389104 (ep831 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep833 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz299 (Real.cos qz152)) (@HMul.hMul Real Real Real qz0 qz299 (@Neg.neg Real Real.instNeg (Real.sin qz152))) Bool.true 438456563937 1099511627776 8352177766805 26739023275884544 Bool.true 13911016105 68719476736 4170491123823 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz299 (Real.cos qz152) 468937 1048576 1 1048576 935001 1048576 17762347 25500319744 438456563937 1099511627776 8352177766805 26739023275884544 qz304 (@Enclosure.Real.IsNear.recentre' (Real.cos qz152) Bool.true 935001 1048576 142098776 204002557952 935001 1048576 17762347 25500319744 (ep828 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz299 (@Neg.neg Real Real.instNeg (Real.sin qz152)) 468937 1048576 1 1048576 29665 65536 17762347 25500319744 13911016105 68719476736 4170491123823 13369511637942272 qz304 (@Enclosure.Real.IsNear.neg (Real.sin qz152) Bool.false 29665 65536 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz152) Bool.false 474640 1048576 142098776 204002557952 29665 65536 17762347 25500319744 (ep832 rfl rfl) rfl)) rfl)

noncomputable def ep834 := @ep782 438456563937 1099511627776 8352177766805 26739023275884544 Bool.true 13911016105 68719476736 4170491123823 13369511637942272 Bool.false 74182919082957831405568 16867242967 274877906944 20819971110261 13369511637942272 Bool.false 15678815822555188822016 228156798731 274877906944 1300639983801 835594477371392 (ep783 (BSN.head_sum_c_succ qz144 4 5 rfl rfl) (ep822 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep823 ep833) rfl rfl

noncomputable abbrev qz153 := (@HMul.hMul Real Real Real qz267 qz446 qz550)

noncomputable def ep835 := @Enclosure.Complex.IsNear.of_eq qz646 (Complex.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz153)))) Bool.true 203908154307 1099511627776 7615289445987 26739023275884544 Bool.true 99971429265 274877906944 1906605713605 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 6 qz148 rfl)

noncomputable def ep836 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz550 134395 1000 0 1 4034681531866359 2251799813685248 62500000024319 12159500000000000000 108448204895035863561 450359962737049600 1679937500653670401 2431900000000000000000 qz149 (BSN.isNear_log_sfrac 6 1 4034681531866359 2251799813685248 62500000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz551) Bool.false 33845361775666394038272 18889465931478580854784 1000000000389104 194552000000000000000 4034681531866359 2251799813685248 62500000024319 12159500000000000000 (BSN.log_rat_reduce_isNear 6 1 2 12 8 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep121 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep837 := nat_lit 1051548095693173078531029969693251856

noncomputable def ep838 := BSN.sin_dyadic_bound_f 1012645146 2147483648 2 1 1048576 389484 ep837 ep61 ep837 ep837 ep62 ep837 476333 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1012645146) qz20 0 1 ep837 ep61 ep837 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1012645146) qz21 0 1 ep837 ep62 ep837 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz452 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 252500653) qz25)

noncomputable def ep839 := @Enclosure.Real.IsNear.cos_image qz153 qz452 Bool.false 252500653 1048576 725 1048576 Bool.true 476333 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 108448204895035863561 450359962737049600 1679937500653670401 2431900000000000000000 252500653 1048576 725 1048576 (ep836 rfl) rfl) (Enclosure.sfrac_false_div 252500653 1048576) (BSN.cos_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71258567223934950834176) qz26) 226375608064910080 72057594037927936 Bool.false 476333 1048576 38 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 252500653 1048576 226375608064910080 72057594037927936 38 71258567223934950834176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 476333 1048576 71258567223934950834176 151115727451828646838272 1012645146 2147483648 389484 389104 (ep838 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep840 := BSN.cos_dyadic_bound_f 1012645146 2147483648 2 1 1048576 389484 ep837 ep57 ep837 ep837 ep58 ep837 934140 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1012645146) qz15 0 1 ep837 ep57 ep837 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1012645146) qz16 0 1 ep837 ep58 ep837 rfl rfl rfl rfl) rfl rfl

noncomputable def ep841 := @Enclosure.Real.IsNear.sin_image qz153 qz452 Bool.false 252500653 1048576 725 1048576 Bool.false 934140 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz153 Bool.false 108448204895035863561 450359962737049600 1679937500653670401 2431900000000000000000 252500653 1048576 725 1048576 (ep836 rfl) rfl) (Enclosure.sfrac_false_div 252500653 1048576) (BSN.sin_reduce1 qz452 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 71258567223934950834176) qz26) 226375608064910080 72057594037927936 Bool.false 934140 1048576 38 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 252500653 1048576 226375608064910080 72057594037927936 38 71258567223934950834176 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 934140 1048576 71258567223934950834176 151115727451828646838272 1012645146 2147483648 389484 389104 (ep840 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep842 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz305 (Real.cos qz153)) (@HMul.hMul Real Real Real qz0 qz305 (@Neg.neg Real Real.instNeg (Real.sin qz153))) Bool.true 203908154307 1099511627776 7615289445987 26739023275884544 Bool.true 99971429265 274877906944 1906605713605 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ft qz305 (Real.cos qz153) 428079 1048576 1 1048576 476333 1048576 17762347 25500319744 203908154307 1099511627776 7615289445987 26739023275884544 qz309 (@Enclosure.Real.IsNear.recentre' (Real.cos qz153) Bool.true 476333 1048576 142098776 204002557952 476333 1048576 17762347 25500319744 (ep839 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz305 (@Neg.neg Real Real.instNeg (Real.sin qz153)) 428079 1048576 1 1048576 233535 262144 17762347 25500319744 99971429265 274877906944 1906605713605 6684755818971136 qz309 (@Enclosure.Real.IsNear.neg (Real.sin qz153) Bool.false 233535 262144 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz153) Bool.false 934140 1048576 142098776 204002557952 233535 262144 17762347 25500319744 (ep841 rfl rfl) rfl)) rfl)

noncomputable def ep843 := @ep780 203908154307 1099511627776 7615289445987 26739023275884544 Bool.true 99971429265 274877906944 1906605713605 6684755818971136 Bool.true 37504116893982880956416 136439182439 1099511627776 49255231666509 26739023275884544 Bool.false 35235326059657406971904 64092684733 137438953472 12311725584013 6684755818971136 (ep781 (BSN.head_sum_c_succ qz144 5 6 rfl rfl) (ep834 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep835 ep842) rfl rfl

noncomputable abbrev qz154 := (@HMul.hMul Real Real Real qz267 qz446 qz552)

noncomputable def ep844 := @Enclosure.Complex.IsNear.of_eq qz645 (Complex.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz154)))) Bool.true 298870664125 1099511627776 7058019016617 26739023275884544 Bool.false 288756450125 1099511627776 7057398395737 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 7 qz148 rfl)

noncomputable def ep845 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz552 134395 1000 0 1 4381796493761783 2251799813685248 62500000024319 12159500000000000000 117778307955822965257 450359962737049600 1679937500653670401 2431900000000000000000 qz149 (BSN.isNear_log_sfrac 7 1 4381796493761783 2251799813685248 62500000024319 12159500000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz553) Bool.false 36757173121942042968064 18889465931478580854784 1000000000389104 194552000000000000000 4381796493761783 2251799813685248 62500000024319 12159500000000000000 (BSN.log_rat_reduce_isNear 7 1 2 14 8 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep136 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep846 := nat_lit 264671992614634370285480994800790465783207192631583351066577359261420137513216

noncomputable def ep847 := nat_lit 54850231159091122433653543031096498951367108393155282278783078892450119936

noncomputable def ep848 := nat_lit 793906277381584928611575677316309204351718843677963742635174511626475512299776

noncomputable def ep849 := BSN.cos_dyadic_bound_f 1649670878 2147483648 3 2 1048576 389484 ep846 ep71 ep847 ep848 ep74 ep847 754105 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1649670878) qz15 0 2 ep846 ep71 ep847 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1649670878) qz16 0 2 ep848 ep74 ep847 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz453 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 34277999) (@Nat.cast Real Real.instNatCast 131072))

noncomputable abbrev qz454 := (@Nat.cast Real Real.instNatCast 18889465931478580854784)

noncomputable def ep850 := @Enclosure.Real.IsNear.cos_image qz154 qz453 Bool.false 34277999 131072 725 1048576 Bool.true 754105 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 117778307955822965257 450359962737049600 1679937500653670401 2431900000000000000000 34277999 131072 725 1048576 (ep845 rfl) rfl) (Enclosure.sfrac_false_div 34277999 131072) (BSN.cos_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14510658501873099603968) qz454) 226375608064910080 72057594037927936 Bool.false 754105 1048576 41 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 34277999 131072 226375608064910080 72057594037927936 41 14510658501873099603968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 754105 1048576 14510658501873099603968 18889465931478580854784 1649670878 2147483648 389484 389104 (ep849 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep851 := nat_lit 7406094190536002252313121379341501456

noncomputable def ep852 := BSN.sin_dyadic_bound_f 1649670878 2147483648 2 1 1048576 389484 ep851 ep61 ep851 ep851 ep62 ep851 728585 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1649670878) qz20 0 1 ep851 ep61 ep851 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1649670878) qz21 0 1 ep851 ep62 ep851 rfl rfl rfl rfl) rfl rfl

noncomputable def ep853 := @Enclosure.Real.IsNear.sin_image qz154 qz453 Bool.false 34277999 131072 725 1048576 Bool.true 728585 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz154 Bool.false 117778307955822965257 450359962737049600 1679937500653670401 2431900000000000000000 34277999 131072 725 1048576 (ep845 rfl) rfl) (Enclosure.sfrac_false_div 34277999 131072) (BSN.sin_reduce2 qz453 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 14510658501873099603968) qz454) 226375608064910080 72057594037927936 Bool.false 728585 1048576 41 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 34277999 131072 226375608064910080 72057594037927936 41 14510658501873099603968 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 728585 1048576 14510658501873099603968 18889465931478580854784 1649670878 2147483648 389484 389104 (ep852 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep854 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz310 (Real.cos qz154)) (@HMul.hMul Real Real Real qz0 qz310 (@Neg.neg Real Real.instNeg (Real.sin qz154))) Bool.true 298870664125 1099511627776 7058019016617 26739023275884544 Bool.false 288756450125 1099511627776 7057398395737 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz310 (Real.cos qz154) 396325 1048576 1 1048576 754105 1048576 17762347 25500319744 298870664125 1099511627776 7058019016617 26739023275884544 qz314 (@Enclosure.Real.IsNear.recentre' (Real.cos qz154) Bool.true 754105 1048576 142098776 204002557952 754105 1048576 17762347 25500319744 (ep850 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz310 (@Neg.neg Real Real.instNeg (Real.sin qz154)) 396325 1048576 1 1048576 728585 1048576 17762347 25500319744 288756450125 1099511627776 7057398395737 26739023275884544 qz314 (@Enclosure.Real.IsNear.neg (Real.sin qz154) Bool.true 728585 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz154) Bool.true 728585 1048576 142098776 204002557952 728585 1048576 17762347 25500319744 (ep853 rfl rfl) rfl)) rfl)

noncomputable def ep855 := @ep778 298870664125 1099511627776 7058019016617 26739023275884544 Bool.false 288756450125 1099511627776 7057398395737 26739023275884544 Bool.true 478628237982504440561664 108827461641 274877906944 28156625341563 13369511637942272 Bool.false 110157036432784577527808 801497927989 1099511627776 56304300731789 26739023275884544 (ep779 (BSN.head_sum_c_succ qz144 6 7 rfl rfl) (ep843 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep844 ep854) rfl rfl

noncomputable abbrev qz155 := (@HMul.hMul Real Real Real qz267 qz446 qz554)

noncomputable def ep856 := @Enclosure.Complex.IsNear.of_eq qz644 (Complex.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz155)))) Bool.true 192593788681 549755813888 3309641349881 13369511637942272 Bool.true 6549633909 137438953472 824681532879 3342377909485568 (BSN.cpow_neg_s_mk qz147 134395 1000 8 qz148 rfl)

noncomputable def ep857 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz554 134395 1000 0 1 9364972152248037 4503599627370496 125000000072957 24319000000000000000 251721086480274986523 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 8 1 9364972152248037 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz555) Bool.false 39279540158062550581248 18889465931478580854784 1000000000583656 194552000000000000000 9364972152248037 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 8 1 3 16 16 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep151 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep858 := nat_lit 5817794137914917612020055800722139535238775362638754379617560600459116900000000

noncomputable def ep859 := nat_lit 8160091996116706734682390044346446758654278830554537243581443789062500000000

noncomputable def ep860 := nat_lit 15223868307497738125339231798962375964206590450709173172032574473163014500000000

noncomputable def ep861 := BSN.sin_dyadic_bound_f 3082917350 2147483648 3 2 1048576 389484 ep858 ep78 ep859 ep860 ep80 ep859 1039006 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3082917350) qz20 0 2 ep858 ep78 ep859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3082917350) qz21 0 2 ep860 ep80 ep859 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz455 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 36630239) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep862 := @Enclosure.Real.IsNear.cos_image qz155 qz455 Bool.false 36630239 131072 363 524288 Bool.true 1039006 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 251721086480274986523 900719925474099200 3359875001961011203 4863800000000000000000 36630239 131072 363 524288 (ep857 rfl) rfl) (Enclosure.sfrac_false_div 36630239 131072) (BSN.cos_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27117627798301481893888) qz454) 226375608064910080 72057594037927936 Bool.false 1039006 1048576 44 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 36630239 131072 226375608064910080 72057594037927936 44 27117627798301481893888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1039006 1048576 27117627798301481893888 18889465931478580854784 3082917350 2147483648 389484 389104 (ep861 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep863 := nat_lit 3235734561951006098559889840420898162580943769835110005229125419716870500000000

noncomputable def ep864 := nat_lit 9690883501860784882210304741174001594225522751844220941200213371572486500000000

noncomputable def ep865 := BSN.cos_dyadic_bound_f 3082917350 2147483648 3 2 1048576 389484 ep863 ep71 ep859 ep864 ep74 ep859 141336 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3082917350) qz15 0 2 ep863 ep71 ep859 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3082917350) qz16 0 2 ep864 ep74 ep859 rfl rfl rfl rfl) rfl rfl

noncomputable def ep866 := @Enclosure.Real.IsNear.sin_image qz155 qz455 Bool.false 36630239 131072 363 524288 Bool.false 141336 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz155 Bool.false 251721086480274986523 900719925474099200 3359875001961011203 4863800000000000000000 36630239 131072 363 524288 (ep857 rfl) rfl) (Enclosure.sfrac_false_div 36630239 131072) (BSN.sin_reduce1 qz455 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 27117627798301481893888) qz454) 226375608064910080 72057594037927936 Bool.false 141336 1048576 44 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 36630239 131072 226375608064910080 72057594037927936 44 27117627798301481893888 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 141336 1048576 27117627798301481893888 18889465931478580854784 3082917350 2147483648 389484 389104 (ep865 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep867 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz315 (Real.cos qz155)) (@HMul.hMul Real Real Real qz0 qz315 (@Neg.neg Real Real.instNeg (Real.sin qz155))) Bool.true 192593788681 549755813888 3309641349881 13369511637942272 Bool.true 6549633909 137438953472 824681532879 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ft qz315 (Real.cos qz155) 370727 1048576 1 1048576 519503 524288 8893333 12750159872 192593788681 549755813888 3309641349881 13369511637942272 qz319 (@Enclosure.Real.IsNear.recentre' (Real.cos qz155) Bool.true 1039006 1048576 71146664 102001278976 519503 524288 8893333 12750159872 (ep862 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz315 (@Neg.neg Real Real.instNeg (Real.sin qz155)) 370727 1048576 1 1048576 17667 131072 8893333 12750159872 6549633909 137438953472 824681532879 3342377909485568 qz319 (@Enclosure.Real.IsNear.neg (Real.sin qz155) Bool.false 17667 131072 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz155) Bool.false 141336 1048576 71146664 102001278976 17667 131072 8893333 12750159872 (ep866 rfl rfl) rfl)) rfl)

noncomputable def ep868 := @ep776 192593788681 549755813888 3309641349881 13369511637942272 Bool.true 6549633909 137438953472 824681532879 3342377909485568 Bool.true 112768307270861373571072 410248711963 549755813888 7866566672861 3342377909485568 Bool.false 102955637792163101671424 749100856717 1099511627776 62901752994821 26739023275884544 (ep777 (BSN.head_sum_c_succ qz144 7 8 rfl rfl) (ep855 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep856 ep867) rfl rfl

theorem EMRow45.d13 : Enclosure.Complex.IsNear qz143 Bool.true 410248711963 549755813888 7866566672861 3342377909485568 Bool.false 749100856717 1099511627776 62901752994821 26739023275884544 := ep775 (BSN.head_sum_c_succ qz144 8 9 rfl rfl) (ep868 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz156 := (BSN.headSumC qz444 17)

noncomputable abbrev qz650 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 16) qz145)

noncomputable def ep869 := @Enclosure.Complex.IsNear.of_eq qz156 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 16) qz650) Bool.true 34345821403 137438953472 26439736377523 6684755818971136 Bool.true 41011627499 274877906944 26435903800399 6684755818971136

noncomputable def ep870 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 16) qz650 Bool.true 182236121513 1099511627776 101094068770461 26739023275884544 Bool.false 94787983201 1099511627776 101063310439727 26739023275884544 Bool.true

noncomputable abbrev qz651 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 15) qz145)

noncomputable def ep871 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 16) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 15) qz651) Bool.true 182236121513 1099511627776 101094068770461 26739023275884544 Bool.false 94787983201 1099511627776 101063310439727 26739023275884544

noncomputable def ep872 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 15) qz651 Bool.true 434492550479 1099511627776 96262396774393 26739023275884544 Bool.true 2215528451 68719476736 48121299374725 13369511637942272 Bool.false

noncomputable abbrev qz652 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 14) qz145)

noncomputable def ep873 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 15) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 14) qz652) Bool.true 434492550479 1099511627776 96262396774393 26739023275884544 Bool.true 2215528451 68719476736 48121299374725 13369511637942272

noncomputable def ep874 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 14) qz652 Bool.true 155933250423 1099511627776 91260432710277 26739023275884544 Bool.false 58124962727 1099511627776 91256687438363 26739023275884544 Bool.true

noncomputable abbrev qz653 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 13) qz145)

noncomputable def ep875 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 14) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 13) qz653) Bool.true 155933250423 1099511627776 91260432710277 26739023275884544 Bool.false 58124962727 1099511627776 91256687438363 26739023275884544

noncomputable def ep876 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 13) qz653 Bool.true 177555617097 549755813888 43039030191293 13369511637942272 Bool.true 86395849163 549755813888 43035830540463 13369511637942272 Bool.false

noncomputable abbrev qz654 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 12) qz145)

noncomputable def ep877 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 13) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 12) qz654) Bool.true 177555617097 549755813888 43039030191293 13369511637942272 Bool.true 86395849163 549755813888 43035830540463 13369511637942272

noncomputable def ep878 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 12) qz654 Bool.true 269858224095 549755813888 10085825261311 3342377909485568 Bool.false 21350545835 274877906944 40337145298369 13369511637942272 Bool.false

noncomputable abbrev qz655 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 11) qz145)

noncomputable def ep879 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 12) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 11) qz655) Bool.true 269858224095 549755813888 10085825261311 3342377909485568 Bool.false 21350545835 274877906944 40337145298369 13369511637942272

noncomputable def ep880 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 11) qz655 Bool.true 457130865121 1099511627776 75064541451439 26739023275884544 Bool.false 203232653833 549755813888 37516943055835 13369511637942272 Bool.true

noncomputable abbrev qz656 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 10) qz145)

noncomputable def ep881 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 11) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 10) qz656) Bool.true 457130865121 1099511627776 75064541451439 26739023275884544 Bool.false 203232653833 549755813888 37516943055835 13369511637942272

noncomputable def ep882 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 10) qz656 Bool.true 227014425013 549755813888 34583216684127 13369511637942272 Bool.false 11783557003 17179869184 4319406639649 1671188954742784 Bool.true

noncomputable abbrev qz657 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 9) qz145)

noncomputable def ep883 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 10) (@HAdd.hAdd Complex Complex Complex qz4 qz143 qz657) Bool.true 227014425013 549755813888 34583216684127 13369511637942272 Bool.false 11783557003 17179869184 4319406639649 1671188954742784

noncomputable def ep884 := @Enclosure.Complex.IsNear.addLitP qz143 qz657 Bool.true 410248711963 549755813888 7866566672861 3342377909485568 Bool.false 749100856717 1099511627776 62901752994821 26739023275884544 Bool.false

noncomputable abbrev qz157 := (@HMul.hMul Real Real Real qz267 qz446 qz564)

noncomputable def ep885 := @Enclosure.Complex.IsNear.of_eq qz657 (Complex.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz157)))) Bool.false 91617143475 274877906944 3116949992683 13369511637942272 Bool.false 5046791475 1099511627776 6208753239563 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 9 qz148 rfl)

noncomputable def ep886 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz564 134395 1000 0 1 9895417793173221 4503599627370496 125000000072957 24319000000000000000 265978934862703007259 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 9 1 9895417793173221 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz565) Bool.false 41504390431577613533184 18889465931478580854784 1000000000583656 194552000000000000000 9895417793173221 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 9 1 3 18 16 61752 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep178 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep887 := nat_lit 8054631524502739851166416669453561055986400029398237933272162421153113163790465

noncomputable def ep888 := nat_lit 15624363445776921037924158860490166150483071219428174516475055723612478994561

noncomputable def ep889 := nat_lit 21070166928118775071374452162794723449054075104544882304590894346134209510602881

noncomputable def ep890 := BSN.sin_dyadic_bound_f 3343684497 2147483648 3 2 1048576 389484 ep887 ep78 ep888 ep889 ep80 ep888 1048476 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3343684497) qz20 0 2 ep887 ep78 ep888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3343684497) qz21 0 2 ep889 ep80 ep888 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz456 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 309640233) qz25)

noncomputable def ep891 := @Enclosure.Real.IsNear.cos_image qz157 qz456 Bool.false 309640233 1048576 725 1048576 Bool.false 1048476 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 265978934862703007259 900719925474099200 3359875001961011203 4863800000000000000000 309640233 1048576 725 1048576 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 309640233 1048576) (BSN.cos_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235290879022128447881216) qz26) 226375608064910080 72057594037927936 Bool.false 1048476 1048576 46 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 309640233 1048576 226375608064910080 72057594037927936 46 235290879022128447881216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048476 1048576 235290879022128447881216 151115727451828646838272 3343684497 2147483648 389484 389104 (ep890 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep892 := nat_lit 4481739452921867437775975553634418438281548047985433596047412480962223970547841

noncomputable def ep893 := nat_lit 13413969631874048471252078343182274982543678001517444439109287331439446953654401

noncomputable def ep894 := BSN.cos_dyadic_bound_f 3343684497 2147483648 3 2 1048576 389484 ep892 ep71 ep888 ep893 ep74 ep888 14439 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3343684497) qz15 0 2 ep892 ep71 ep888 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3343684497) qz16 0 2 ep893 ep74 ep888 rfl rfl rfl rfl) rfl rfl

noncomputable def ep895 := @Enclosure.Real.IsNear.sin_image qz157 qz456 Bool.false 309640233 1048576 725 1048576 Bool.true 14439 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz157 Bool.false 265978934862703007259 900719925474099200 3359875001961011203 4863800000000000000000 309640233 1048576 725 1048576 (ep886 rfl) rfl) (Enclosure.sfrac_false_div 309640233 1048576) (BSN.sin_reduce3 qz456 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 235290879022128447881216) qz26) 226375608064910080 72057594037927936 Bool.false 14439 1048576 46 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 309640233 1048576 226375608064910080 72057594037927936 46 235290879022128447881216 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 14439 1048576 235290879022128447881216 151115727451828646838272 3343684497 2147483648 389484 389104 (ep894 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep896 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz320 (Real.cos qz157)) (@HMul.hMul Real Real Real qz0 qz320 (@Neg.neg Real Real.instNeg (Real.sin qz157))) Bool.false 91617143475 274877906944 3116949992683 13369511637942272 Bool.false 5046791475 1099511627776 6208753239563 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz320 (Real.cos qz157) 349525 1048576 1 1048576 262119 262144 17762347 25500319744 91617143475 274877906944 3116949992683 13369511637942272 qz324 (@Enclosure.Real.IsNear.recentre' (Real.cos qz157) Bool.false 1048476 1048576 142098776 204002557952 262119 262144 17762347 25500319744 (ep891 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz320 (@Neg.neg Real Real.instNeg (Real.sin qz157)) 349525 1048576 1 1048576 14439 1048576 17762347 25500319744 5046791475 1099511627776 6208753239563 26739023275884544 qz324 (@Enclosure.Real.IsNear.neg (Real.sin qz157) Bool.true 14439 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz157) Bool.true 14439 1048576 142098776 204002557952 14439 1048576 17762347 25500319744 (ep895 rfl rfl) rfl)) rfl)

noncomputable def ep897 := @ep884 91617143475 274877906944 3116949992683 13369511637942272 Bool.false 5046791475 1099511627776 6208753239563 26739023275884544 Bool.true 62401249993669079990272 227014425013 549755813888 34583216684127 13369511637942272 Bool.false 829194108247028103380992 11783557003 17179869184 4319406639649 1671188954742784 EMRow45.d13 (ep885 ep896) rfl rfl

noncomputable abbrev qz158 := (@HMul.hMul Real Real Real qz267 qz446 qz566)

noncomputable def ep898 := @Enclosure.Complex.IsNear.of_eq qz656 (Complex.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz158)))) Bool.true 3102015095 1099511627776 5898108083185 26739023275884544 Bool.true 173841170263 549755813888 2961689938643 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 10 qz148 rfl)

noncomputable def ep899 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz566 134395 1000 0 1 10369917190100709 4503599627370496 125000000072957 24319000000000000000 278733004152716957211 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 10 1 10369917190100709 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz325) Bool.false 43494585150108164161536 18889465931478580854784 1000000000583656 194552000000000000000 10369917190100709 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 10 1 3 20 16 116991 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep189 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep900 := BSN.sin_dyadic_bound_f 19159356 2147483648 1 0 1048576 389484 0 1 1 0 1 1 9355 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 19159356) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 19159356) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz457 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 324487923) qz25)

noncomputable def ep901 := @Enclosure.Real.IsNear.cos_image qz158 qz457 Bool.false 324487923 1048576 363 524288 Bool.true 9355 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 278733004152716957211 900719925474099200 3359875001961011203 4863800000000000000000 324487923 1048576 363 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 324487923 1048576) (BSN.cos_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1348219841421399556096) qz26) 226375608064910080 72057594037927936 Bool.false 9355 1048576 49 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 324487923 1048576 226375608064910080 72057594037927936 49 1348219841421399556096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 9355 1048576 1348219841421399556096 151115727451828646838272 19159356 2147483648 389484 389104 (ep900 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep902 := BSN.cos_dyadic_bound_f 19159356 2147483648 1 0 1048576 389484 0 1 1 0 1 1 1048534 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 19159356) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 19159356) qz16 0 0 rfl) rfl rfl

noncomputable def ep903 := @Enclosure.Real.IsNear.sin_image qz158 qz457 Bool.false 324487923 1048576 363 524288 Bool.false 1048534 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz158 Bool.false 278733004152716957211 900719925474099200 3359875001961011203 4863800000000000000000 324487923 1048576 363 524288 (ep899 rfl) rfl) (Enclosure.sfrac_false_div 324487923 1048576) (BSN.sin_reduce1 qz457 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 1348219841421399556096) qz26) 226375608064910080 72057594037927936 Bool.false 1048534 1048576 49 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 324487923 1048576 226375608064910080 72057594037927936 49 1348219841421399556096 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048534 1048576 1348219841421399556096 151115727451828646838272 19159356 2147483648 389484 389104 (ep902 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep904 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz33 (Real.cos qz158)) (@HMul.hMul Real Real Real qz0 qz33 (@Neg.neg Real Real.instNeg (Real.sin qz158))) Bool.true 3102015095 1099511627776 5898108083185 26739023275884544 Bool.true 173841170263 549755813888 2961689938643 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz33 (Real.cos qz158) 331589 1048576 1 1048576 9355 1048576 8893333 12750159872 3102015095 1099511627776 5898108083185 26739023275884544 qz327 (@Enclosure.Real.IsNear.recentre' (Real.cos qz158) Bool.true 9355 1048576 71146664 102001278976 9355 1048576 8893333 12750159872 (ep901 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz33 (@Neg.neg Real Real.instNeg (Real.sin qz158)) 331589 1048576 1 1048576 524267 524288 8893333 12750159872 173841170263 549755813888 2961689938643 13369511637942272 qz327 (@Enclosure.Real.IsNear.neg (Real.sin qz158) Bool.false 524267 524288 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz158) Bool.false 1048534 1048576 71146664 102001278976 524267 524288 8893333 12750159872 (ep903 rfl rfl) rfl)) rfl)

noncomputable def ep905 := @ep882 3102015095 1099511627776 5898108083185 26739023275884544 Bool.true 173841170263 549755813888 2961689938643 13369511637942272 Bool.true 251310350807920906600448 457130865121 1099511627776 75064541451439 26739023275884544 Bool.false 3491510406768096182272 203232653833 549755813888 37516943055835 13369511637942272 (ep883 (BSN.head_sum_c_succ qz144 9 10 rfl rfl) (ep897 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep898 ep904) rfl rfl

noncomputable abbrev qz159 := (@HMul.hMul Real Real Real qz267 qz446 qz567)

noncomputable def ep906 := @Enclosure.Complex.IsNear.of_eq qz655 (Complex.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz159)))) Bool.true 82585583069 1099511627776 5622060639049 26739023275884544 Bool.true 160531562163 549755813888 1410101121267 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 11 qz148 rfl)

noncomputable def ep907 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz567 134395 1000 0 1 10799156221662949 4503599627370496 125000000072957 24319000000000000000 290270520082078406171 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 11 1 10799156221662949 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz328) Bool.false 45294944137145793642496 18889465931478580854784 1000000000583656 194552000000000000000 10799156221662949 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 11 1 3 22 16 166961 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep204 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep908 := nat_lit 85451404292113719309990188011109041

noncomputable def ep909 := BSN.sin_dyadic_bound_f 540666923 2147483648 2 1 1048576 389484 ep908 ep61 ep908 ep908 ep62 ep908 261217 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 540666923) qz20 0 1 ep908 ep61 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 540666923) qz21 0 1 ep908 ep62 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz458 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 2639995) (@Nat.cast Real Real.instNatCast 8192))

noncomputable def ep910 := @Enclosure.Real.IsNear.cos_image qz159 qz458 Bool.false 2639995 8192 725 1048576 Bool.true 261217 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 290270520082078406171 900719925474099200 3359875001961011203 4863800000000000000000 2639995 8192 725 1048576 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 2639995 8192) (BSN.cos_reduce1 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297234784431730851840) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 261217 1048576 51 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 2639995 8192 226375608064910080 72057594037927936 51 297234784431730851840 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 261217 1048576 297234784431730851840 1180591620717411303424 540666923 2147483648 389484 389104 (ep909 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep911 := BSN.cos_dyadic_bound_f 540666923 2147483648 2 1 1048576 389484 ep908 ep57 ep908 ep908 ep58 ep908 1015518 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 540666923) qz15 0 1 ep908 ep57 ep908 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 540666923) qz16 0 1 ep908 ep58 ep908 rfl rfl rfl rfl) rfl rfl

noncomputable def ep912 := @Enclosure.Real.IsNear.sin_image qz159 qz458 Bool.false 2639995 8192 725 1048576 Bool.false 1015518 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz159 Bool.false 290270520082078406171 900719925474099200 3359875001961011203 4863800000000000000000 2639995 8192 725 1048576 (ep907 rfl) rfl) (Enclosure.sfrac_false_div 2639995 8192) (BSN.sin_reduce1 qz458 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 297234784431730851840) (@Nat.cast Real Real.instNatCast 1180591620717411303424)) 226375608064910080 72057594037927936 Bool.false 1015518 1048576 51 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 2639995 8192 226375608064910080 72057594037927936 51 297234784431730851840 1180591620717411303424 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1015518 1048576 297234784431730851840 1180591620717411303424 540666923 2147483648 389484 389104 (ep911 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep913 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz35 (Real.cos qz159)) (@HMul.hMul Real Real Real qz0 qz35 (@Neg.neg Real Real.instNeg (Real.sin qz159))) Bool.true 82585583069 1099511627776 5622060639049 26739023275884544 Bool.true 160531562163 549755813888 1410101121267 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ft qz35 (Real.cos qz159) 316157 1048576 1 1048576 261217 1048576 17762347 25500319744 82585583069 1099511627776 5622060639049 26739023275884544 qz330 (@Enclosure.Real.IsNear.recentre' (Real.cos qz159) Bool.true 261217 1048576 142098776 204002557952 261217 1048576 17762347 25500319744 (ep910 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz35 (@Neg.neg Real Real.instNeg (Real.sin qz159)) 316157 1048576 1 1048576 507759 524288 17762347 25500319744 160531562163 549755813888 1410101121267 6684755818971136 qz330 (@Enclosure.Real.IsNear.neg (Real.sin qz159) Bool.false 507759 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz159) Bool.false 1015518 1048576 142098776 204002557952 507759 524288 17762347 25500319744 (ep912 rfl rfl) rfl)) rfl)

noncomputable def ep914 := @ep880 82585583069 1099511627776 5622060639049 26739023275884544 Bool.true 160531562163 549755813888 1410101121267 6684755818971136 Bool.true 593424510486868068925440 269858224095 549755813888 10085825261311 3342377909485568 Bool.false 23475173404946947112960 21350545835 274877906944 40337145298369 13369511637942272 (ep881 (BSN.head_sum_c_succ qz144 10 11 rfl rfl) (ep905 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep906 ep913) rfl rfl

noncomputable abbrev qz160 := (@HMul.hMul Real Real Real qz267 qz446 qz568)

noncomputable def ep915 := @Enclosure.Complex.IsNear.of_eq qz654 (Complex.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160)))) Bool.false 46151303499 274877906944 2695729146049 13369511637942272 Bool.true 129096940833 549755813888 1349342621047 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 12 qz148 rfl)

noncomputable def ep916 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz568 134395 1000 0 1 11191020447815397 4503599627370496 125000000072957 24319000000000000000 300803438616830055963 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 12 1 11191020447815397 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz331) Bool.false 46938541828353910898688 18889465931478580854784 1000000000583656 194552000000000000000 11191020447815397 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 12 1 3 24 16 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep214 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep917 := nat_lit 619445645083969220590895384102374656318851256981578535154078499359972581769216

noncomputable def ep918 := nat_lit 300280937337513849987786142729446128971573061532235208366014397851002535936

noncomputable def ep919 := nat_lit 1857736373377232634072710580021665076698610624821671135045503469284215740235776

noncomputable def ep920 := BSN.cos_dyadic_bound_f 2040285628 2147483648 3 2 1048576 389484 ep917 ep71 ep918 ep919 ep74 ep918 609868 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2040285628) qz15 0 2 ep917 ep71 ep918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2040285628) qz16 0 2 ep919 ep74 ep918 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz459 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 350181291) qz25)

noncomputable def ep921 := @Enclosure.Real.IsNear.cos_image qz160 qz459 Bool.false 350181291 1048576 725 1048576 Bool.false 609868 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 300803438616830055963 900719925474099200 3359875001961011203 4863800000000000000000 350181291 1048576 725 1048576 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 350181291 1048576) (BSN.cos_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143572337429530953121792) qz26) 226375608064910080 72057594037927936 Bool.false 609868 1048576 53 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 350181291 1048576 226375608064910080 72057594037927936 53 143572337429530953121792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 609868 1048576 143572337429530953121792 151115727451828646838272 2040285628 2147483648 389484 389104 (ep920 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep922 := nat_lit 1114761936401274585983621462470090824470755004117615575110648487329669845155840

noncomputable def ep923 := nat_lit 2919128426200029845628552176523914008452690082970321934952439157790709876064256

noncomputable def ep924 := BSN.sin_dyadic_bound_f 2040285628 2147483648 3 2 1048576 389484 ep922 ep78 ep918 ep923 ep80 ep918 852978 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2040285628) qz20 0 2 ep922 ep78 ep918 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2040285628) qz21 0 2 ep923 ep80 ep918 rfl rfl rfl rfl) rfl rfl

noncomputable def ep925 := @Enclosure.Real.IsNear.sin_image qz160 qz459 Bool.false 350181291 1048576 725 1048576 Bool.false 852978 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz160 Bool.false 300803438616830055963 900719925474099200 3359875001961011203 4863800000000000000000 350181291 1048576 725 1048576 (ep916 rfl) rfl) (Enclosure.sfrac_false_div 350181291 1048576) (BSN.sin_reduce0 qz459 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 143572337429530953121792) qz26) 226375608064910080 72057594037927936 Bool.false 852978 1048576 53 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 350181291 1048576 226375608064910080 72057594037927936 53 143572337429530953121792 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 852978 1048576 143572337429530953121792 151115727451828646838272 2040285628 2147483648 389484 389104 (ep924 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep926 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz37 (Real.cos qz160)) (@HMul.hMul Real Real Real qz0 qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160))) Bool.false 46151303499 274877906944 2695729146049 13369511637942272 Bool.true 129096940833 549755813888 1349342621047 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz37 (Real.cos qz160) 302697 1048576 1 1048576 152467 262144 17762347 25500319744 46151303499 274877906944 2695729146049 13369511637942272 qz333 (@Enclosure.Real.IsNear.recentre' (Real.cos qz160) Bool.false 609868 1048576 142098776 204002557952 152467 262144 17762347 25500319744 (ep921 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz37 (@Neg.neg Real Real.instNeg (Real.sin qz160)) 302697 1048576 1 1048576 426489 524288 17762347 25500319744 129096940833 549755813888 1349342621047 6684755818971136 qz333 (@Enclosure.Real.IsNear.neg (Real.sin qz160) Bool.false 426489 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz160) Bool.false 852978 1048576 142098776 204002557952 426489 524288 17762347 25500319744 (ep925 rfl rfl) rfl)) rfl)

noncomputable def ep927 := @ep878 46151303499 274877906944 2695729146049 13369511637942272 Bool.true 129096940833 549755813888 1349342621047 6684755818971136 Bool.true 48806116393773661421568 177555617097 549755813888 43039030191293 13369511637942272 Bool.true 23748310186574974287872 86395849163 549755813888 43035830540463 13369511637942272 (ep879 (BSN.head_sum_c_succ qz144 11 12 rfl rfl) (ep914 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep915 ep926) rfl rfl

noncomputable abbrev qz161 := (@HMul.hMul Real Real Real qz267 qz446 qz569)

noncomputable def ep928 := @Enclosure.Complex.IsNear.of_eq qz653 (Complex.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz161)))) Bool.false 199177983771 1099511627776 5182372327691 26739023275884544 Bool.false 230916661053 1099511627776 5185026357437 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 13 qz148 rfl)

noncomputable def ep929 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz569 134395 1000 0 1 11551497052968677 4503599627370496 125000000072957 24319000000000000000 310492689286745069083 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 13 1 11551497052968677 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz334) Bool.false 48450490295254733815808 18889465931478580854784 1000000000583656 194552000000000000000 11551497052968677 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 13 1 3 26 16 254545 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep225 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep930 := nat_lit 5457536504395833424821130403245510801

noncomputable def ep931 := BSN.sin_dyadic_bound_f 1528442701 2147483648 2 1 1048576 389484 ep930 ep61 ep930 ep930 ep62 ep930 684877 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1528442701) qz20 0 1 ep930 ep61 ep930 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1528442701) qz21 0 1 ep930 ep62 ep930 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz460 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 361461063) qz25)

noncomputable def ep932 := @Enclosure.Real.IsNear.cos_image qz161 qz460 Bool.false 361461063 1048576 725 1048576 Bool.false 684877 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 310492689286745069083 900719925474099200 3359875001961011203 4863800000000000000000 361461063 1048576 725 1048576 (ep929 rfl) rfl) (Enclosure.sfrac_false_div 361461063 1048576) (BSN.cos_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107554593446405829820416) qz26) 226375608064910080 72057594037927936 Bool.false 684877 1048576 54 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 361461063 1048576 226375608064910080 72057594037927936 54 107554593446405829820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 684877 1048576 107554593446405829820416 151115727451828646838272 1528442701 2147483648 389484 389104 (ep931 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep933 := nat_lit 195025645828386895597074329323353933935611551790233265674997280878093900968481

noncomputable def ep934 := nat_lit 29784704696813092747086001792718856035976157053111760422992241159407661601

noncomputable def ep935 := nat_lit 585017368075767060605728815966476364094762703056593573504145858151962887582241

noncomputable def ep936 := BSN.cos_dyadic_bound_f 1528442701 2147483648 3 2 1048576 389484 ep933 ep71 ep934 ep935 ep74 ep934 794011 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1528442701) qz15 0 2 ep933 ep71 ep934 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1528442701) qz16 0 2 ep935 ep74 ep934 rfl rfl rfl rfl) rfl rfl

noncomputable def ep937 := @Enclosure.Real.IsNear.sin_image qz161 qz460 Bool.false 361461063 1048576 725 1048576 Bool.true 794011 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz161 Bool.false 310492689286745069083 900719925474099200 3359875001961011203 4863800000000000000000 361461063 1048576 725 1048576 (ep929 rfl) rfl) (Enclosure.sfrac_false_div 361461063 1048576) (BSN.sin_reduce3 qz460 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 107554593446405829820416) qz26) 226375608064910080 72057594037927936 Bool.false 794011 1048576 54 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 361461063 1048576 226375608064910080 72057594037927936 54 107554593446405829820416 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 794011 1048576 107554593446405829820416 151115727451828646838272 1528442701 2147483648 389484 389104 (ep936 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep938 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz39 (Real.cos qz161)) (@HMul.hMul Real Real Real qz0 qz39 (@Neg.neg Real Real.instNeg (Real.sin qz161))) Bool.false 199177983771 1099511627776 5182372327691 26739023275884544 Bool.false 230916661053 1099511627776 5185026357437 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz39 (Real.cos qz161) 290823 1048576 1 1048576 684877 1048576 17762347 25500319744 199177983771 1099511627776 5182372327691 26739023275884544 qz337 (@Enclosure.Real.IsNear.recentre' (Real.cos qz161) Bool.false 684877 1048576 142098776 204002557952 684877 1048576 17762347 25500319744 (ep932 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz39 (@Neg.neg Real Real.instNeg (Real.sin qz161)) 290823 1048576 1 1048576 794011 1048576 17762347 25500319744 230916661053 1099511627776 5185026357437 26739023275884544 qz337 (@Enclosure.Real.IsNear.neg (Real.sin qz161) Bool.true 794011 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz161) Bool.true 794011 1048576 142098776 204002557952 794011 1048576 17762347 25500319744 (ep937 rfl rfl) rfl)) rfl)

noncomputable def ep939 := @ep876 199177983771 1099511627776 5182372327691 26739023275884544 Bool.false 230916661053 1099511627776 5185026357437 26739023275884544 Bool.true 85725210998497685274624 155933250423 1099511627776 91260432710277 26739023275884544 Bool.false 31954536191191548952576 58124962727 1099511627776 91256687438363 26739023275884544 (ep877 (BSN.head_sum_c_succ qz144 12 13 rfl rfl) (ep927 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep928 ep938) rfl rfl

noncomputable abbrev qz162 := (@HMul.hMul Real Real Real qz267 qz446 qz570)

noncomputable def ep940 := @Enclosure.Complex.IsNear.of_eq qz652 (Complex.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162)))) Bool.true 34819912507 137438953472 1250491016029 6684755818971136 Bool.true 93573417943 1099511627776 4985911311087 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 14 qz148 rfl)

noncomputable def ep941 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz570 134395 1000 0 1 11885250371606245 4503599627370496 125000000072957 24319000000000000000 63892728947680851871 180143985094819840 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 14 1 11885250371606245 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz338) Bool.false 49850353174629559828480 18889465931478580854784 1000000000583656 194552000000000000000 11885250371606245 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 14 1 3 28 16 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep236 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep942 := nat_lit 3307071563403300460810667658376601534409029755521323516179601974070020669440000

noncomputable def ep943 := nat_lit 2639921700001442055175629867988123890476042453874980801140705827225600000000

noncomputable def ep944 := nat_lit 8657103745208641729271940466438166103820021481440049716316158313129784115200000

noncomputable def ep945 := BSN.sin_dyadic_bound_f 2677311360 2147483648 3 2 1048576 389484 ep942 ep78 ep943 ep944 ep80 ep943 993992 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2677311360) qz20 0 2 ep942 ep78 ep943 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2677311360) qz21 0 2 ep944 ep80 ep943 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz461 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 185952315) qz17)

noncomputable def ep946 := @Enclosure.Real.IsNear.cos_image qz162 qz461 Bool.false 185952315 524288 725 1048576 Bool.true 993992 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 63892728947680851871 180143985094819840 3359875001961011203 4863800000000000000000 185952315 524288 725 1048576 (ep941 rfl) rfl) (Enclosure.sfrac_false_div 185952315 524288) (BSN.cos_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94199519110290399559680) qz19) 226375608064910080 72057594037927936 Bool.false 993992 1048576 56 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 185952315 524288 226375608064910080 72057594037927936 56 94199519110290399559680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 993992 1048576 94199519110290399559680 75557863725914323419136 2677311360 2147483648 389484 389104 (ep945 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep947 := nat_lit 1838435278201834230252671201261662240845228105269124167122508077073222860800000

noncomputable def ep948 := nat_lit 5510025991205499806647662344049010474754732230899622539765242819565217382400000

noncomputable def ep949 := BSN.cos_dyadic_bound_f 2677311360 2147483648 3 2 1048576 389484 ep947 ep71 ep943 ep948 ep74 ep943 333901 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2677311360) qz15 0 2 ep947 ep71 ep943 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2677311360) qz16 0 2 ep948 ep74 ep943 rfl rfl rfl rfl) rfl rfl

noncomputable def ep950 := @Enclosure.Real.IsNear.sin_image qz162 qz461 Bool.false 185952315 524288 725 1048576 Bool.false 333901 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz162 Bool.false 63892728947680851871 180143985094819840 3359875001961011203 4863800000000000000000 185952315 524288 725 1048576 (ep941 rfl) rfl) (Enclosure.sfrac_false_div 185952315 524288) (BSN.sin_reduce1 qz461 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 94199519110290399559680) qz19) 226375608064910080 72057594037927936 Bool.false 333901 1048576 56 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 185952315 524288 226375608064910080 72057594037927936 56 94199519110290399559680 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 333901 1048576 94199519110290399559680 75557863725914323419136 2677311360 2147483648 389484 389104 (ep949 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep951 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz42 (Real.cos qz162)) (@HMul.hMul Real Real Real qz0 qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162))) Bool.true 34819912507 137438953472 1250491016029 6684755818971136 Bool.true 93573417943 1099511627776 4985911311087 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz42 (Real.cos qz162) 280243 1048576 1 1048576 124249 131072 17762347 25500319744 34819912507 137438953472 1250491016029 6684755818971136 qz340 (@Enclosure.Real.IsNear.recentre' (Real.cos qz162) Bool.true 993992 1048576 142098776 204002557952 124249 131072 17762347 25500319744 (ep946 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz42 (@Neg.neg Real Real.instNeg (Real.sin qz162)) 280243 1048576 1 1048576 333901 1048576 17762347 25500319744 93573417943 1099511627776 4985911311087 26739023275884544 qz340 (@Enclosure.Real.IsNear.neg (Real.sin qz162) Bool.false 333901 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz162) Bool.false 333901 1048576 142098776 204002557952 333901 1048576 17762347 25500319744 (ep950 rfl rfl) rfl)) rfl)

noncomputable def ep952 := @ep874 34819912507 137438953472 1250491016029 6684755818971136 Bool.true 93573417943 1099511627776 4985911311087 26739023275884544 Bool.true 59716201429213892313088 434492550479 1099511627776 96262396774393 26739023275884544 Bool.true 38975988696688797679616 2215528451 68719476736 48121299374725 13369511637942272 (ep875 (BSN.head_sum_c_succ qz144 13 14 rfl rfl) (ep939 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep940 ep951) rfl rfl

noncomputable abbrev qz163 := (@HMul.hMul Real Real Real qz267 qz446 qz571)

noncomputable def ep953 := @Enclosure.Complex.IsNear.of_eq qz651 (Complex.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)))) Bool.false 126128214483 549755813888 1207917999017 6684755818971136 Bool.false 130236438417 1099511627776 4820711690277 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 15 qz148 rfl)

noncomputable def ep954 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz571 134395 1000 0 1 12195965485668069 4503599627370496 125000000072957 24319000000000000000 327815356289272026651 900719925474099200 3359875001961011203 4863800000000000000000 qz149 (BSN.isNear_log_sfrac 15 1 12195965485668069 4503599627370496 125000000072957 24319000000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz341) Bool.false 51153586820399524478976 18889465931478580854784 1000000000583656 194552000000000000000 12195965485668069 4503599627370496 125000000072957 24319000000000000000 (BSN.log_rat_reduce_isNear 15 1 3 30 16 329571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep247 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep955 := nat_lit 1961648104766405416953841381671685809571953330552778429852250281653048932915745

noncomputable def ep956 := nat_lit 929454343811907945761126031423307693308460408852403095780641751568318028321

noncomputable def ep957 := nat_lit 5136144967355366336300257033660682241184997406023896758886534460541160404638241

noncomputable def ep958 := BSN.sin_dyadic_bound_f 2349787059 2147483648 3 2 1048576 389484 ep955 ep78 ep956 ep957 ep80 ep956 931726 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2349787059) qz20 0 2 ep955 ep78 ep956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2349787059) qz21 0 2 ep957 ep80 ep956 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz462 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 190813651) qz17)

noncomputable def ep959 := @Enclosure.Real.IsNear.cos_image qz163 qz462 Bool.false 190813651 524288 725 1048576 Bool.false 931726 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 327815356289272026651 900719925474099200 3359875001961011203 4863800000000000000000 190813651 524288 725 1048576 (ep954 rfl) rfl) (Enclosure.sfrac_false_div 190813651 524288) (BSN.cos_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82675782243405824786432) qz19) 226375608064910080 72057594037927936 Bool.false 931726 1048576 57 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 190813651 524288 226375608064910080 72057594037927936 57 82675782243405824786432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 931726 1048576 82675782243405824786432 75557863725914323419136 2349787059 2147483648 389484 389104 (ep958 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep960 := nat_lit 1090217593467474968505805712498235808737000054933255751293819330585724215188001

noncomputable def ep961 := nat_lit 3268793871714801089625894885431860810824383243982062447689896708254036009507361

noncomputable def ep962 := BSN.cos_dyadic_bound_f 2349787059 2147483648 3 2 1048576 389484 ep960 ep71 ep956 ep961 ep74 ep956 481037 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2349787059) qz15 0 2 ep960 ep71 ep956 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2349787059) qz16 0 2 ep961 ep74 ep956 rfl rfl rfl rfl) rfl rfl

noncomputable def ep963 := @Enclosure.Real.IsNear.sin_image qz163 qz462 Bool.false 190813651 524288 725 1048576 Bool.true 481037 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz163 Bool.false 327815356289272026651 900719925474099200 3359875001961011203 4863800000000000000000 190813651 524288 725 1048576 (ep954 rfl) rfl) (Enclosure.sfrac_false_div 190813651 524288) (BSN.sin_reduce3 qz462 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 82675782243405824786432) qz19) 226375608064910080 72057594037927936 Bool.false 481037 1048576 57 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 190813651 524288 226375608064910080 72057594037927936 57 82675782243405824786432 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 481037 1048576 82675782243405824786432 75557863725914323419136 2349787059 2147483648 389484 389104 (ep962 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep964 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz44 (Real.cos qz163)) (@HMul.hMul Real Real Real qz0 qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163))) Bool.false 126128214483 549755813888 1207917999017 6684755818971136 Bool.false 130236438417 1099511627776 4820711690277 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz44 (Real.cos qz163) 270741 1048576 1 1048576 465863 524288 17762347 25500319744 126128214483 549755813888 1207917999017 6684755818971136 qz343 (@Enclosure.Real.IsNear.recentre' (Real.cos qz163) Bool.false 931726 1048576 142098776 204002557952 465863 524288 17762347 25500319744 (ep959 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz44 (@Neg.neg Real Real.instNeg (Real.sin qz163)) 270741 1048576 1 1048576 481037 1048576 17762347 25500319744 130236438417 1099511627776 4820711690277 26739023275884544 qz343 (@Enclosure.Real.IsNear.neg (Real.sin qz163) Bool.true 481037 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz163) Bool.true 481037 1048576 142098776 204002557952 481037 1048576 17762347 25500319744 (ep963 rfl rfl) rfl)) rfl)

noncomputable def ep965 := @ep872 126128214483 549755813888 1207917999017 6684755818971136 Bool.false 130236438417 1099511627776 4820711690277 26739023275884544 Bool.true 100185367302171780972544 182236121513 1099511627776 101094068770461 26739023275884544 Bool.false 6513780606433478311936 94787983201 1099511627776 101063310439727 26739023275884544 (ep873 (BSN.head_sum_c_succ qz144 14 15 rfl rfl) (ep952 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep953 ep964) rfl rfl

noncomputable abbrev qz164 := (@HMul.hMul Real Real Real qz267 qz446 qz572)

noncomputable def ep966 := @Enclosure.Complex.IsNear.of_eq qz650 (Complex.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)))) Bool.true 92530449711 1099511627776 4664876739631 26739023275884544 Bool.true 258834493197 1099511627776 4680304761869 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 16 qz148 rfl)

noncomputable def ep967 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz572 134395 1000 0 1 3121657384082679 1125899906842624 31250000024319 6079750000000000000 83907028826758328841 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 16 1 3121657384082679 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz344) Bool.false 52372720210750067441664 18889465931478580854784 1000000000778208 194552000000000000000 3121657384082679 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 16 1 4 32 32 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep258 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep968 := nat_lit 295510680696803622432682851398047201

noncomputable def ep969 := BSN.sin_dyadic_bound_f 737298407 2147483648 2 1 1048576 389484 ep968 ep61 ep968 ep968 ep62 ep968 352977 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 737298407) qz20 0 1 ep968 ep61 ep968 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 737298407) qz21 0 1 ep968 ep62 ep968 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz463 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 195361275) qz17)

noncomputable def ep970 := @Enclosure.Real.IsNear.cos_image qz164 qz463 Bool.false 195361275 524288 725 1048576 Bool.true 352977 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 83907028826758328841 225179981368524800 839968750653670401 1215950000000000000000 195361275 524288 725 1048576 (ep967 rfl) rfl) (Enclosure.sfrac_false_div 195361275 524288) (BSN.cos_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25941381494868352696320) qz19) 226375608064910080 72057594037927936 Bool.false 352977 1048576 59 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 195361275 524288 226375608064910080 72057594037927936 59 25941381494868352696320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 352977 1048576 25941381494868352696320 75557863725914323419136 737298407 2147483648 389484 389104 (ep969 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep971 := BSN.cos_dyadic_bound_f 737298407 2147483648 2 1 1048576 389484 ep968 ep57 ep968 ep968 ep58 ep968 987379 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 737298407) qz15 0 1 ep968 ep57 ep968 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 737298407) qz16 0 1 ep968 ep58 ep968 rfl rfl rfl rfl) rfl rfl

noncomputable def ep972 := @Enclosure.Real.IsNear.sin_image qz164 qz463 Bool.false 195361275 524288 725 1048576 Bool.false 987379 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz164 Bool.false 83907028826758328841 225179981368524800 839968750653670401 1215950000000000000000 195361275 524288 725 1048576 (ep967 rfl) rfl) (Enclosure.sfrac_false_div 195361275 524288) (BSN.sin_reduce1 qz463 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 25941381494868352696320) qz19) 226375608064910080 72057594037927936 Bool.false 987379 1048576 59 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 195361275 524288 226375608064910080 72057594037927936 59 25941381494868352696320 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 987379 1048576 25941381494868352696320 75557863725914323419136 737298407 2147483648 389484 389104 (ep971 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep973 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz46 (Real.cos qz164)) (@HMul.hMul Real Real Real qz0 qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164))) Bool.true 92530449711 1099511627776 4664876739631 26739023275884544 Bool.true 258834493197 1099511627776 4680304761869 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz46 (Real.cos qz164) 262143 1048576 1 1048576 352977 1048576 17762347 25500319744 92530449711 1099511627776 4664876739631 26739023275884544 qz346 (@Enclosure.Real.IsNear.recentre' (Real.cos qz164) Bool.true 352977 1048576 142098776 204002557952 352977 1048576 17762347 25500319744 (ep970 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz46 (@Neg.neg Real Real.instNeg (Real.sin qz164)) 262143 1048576 1 1048576 987379 1048576 17762347 25500319744 258834493197 1099511627776 4680304761869 26739023275884544 qz346 (@Enclosure.Real.IsNear.neg (Real.sin qz164) Bool.false 987379 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz164) Bool.false 987379 1048576 142098776 204002557952 987379 1048576 17762347 25500319744 (ep972 rfl rfl) rfl)) rfl)

noncomputable def ep974 := @ep870 92530449711 1099511627776 4664876739631 26739023275884544 Bool.true 258834493197 1099511627776 4680304761869 26739023275884544 Bool.true 302109039984930480717824 34345821403 137438953472 26439736377523 6684755818971136 Bool.true 180371045236673815248896 41011627499 274877906944 26435903800399 6684755818971136 (ep871 (BSN.head_sum_c_succ qz144 15 16 rfl rfl) (ep965 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep966 ep973) rfl rfl

theorem EMRow45.d14 : Enclosure.Complex.IsNear qz156 Bool.true 34345821403 137438953472 26439736377523 6684755818971136 Bool.true 41011627499 274877906944 26435903800399 6684755818971136 := ep869 (BSN.head_sum_c_succ qz144 16 17 rfl rfl) (ep974 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz165 := (BSN.headSumC qz444 25)

noncomputable abbrev qz658 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 24) qz145)

noncomputable def ep975 := @Enclosure.Complex.IsNear.of_eq qz165 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 24) qz658) Bool.false 437138491985 549755813888 34762106517621 6684755818971136 Bool.true 241886317881 1099511627776 138968155301467 26739023275884544

noncomputable def ep976 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 24) qz658 Bool.false 163026446551 274877906944 67608062551879 13369511637942272 Bool.true 136844865387 549755813888 67578741911787 13369511637942272 Bool.false

noncomputable abbrev qz659 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 23) qz145)

noncomputable def ep977 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 24) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 23) qz659) Bool.false 163026446551 274877906944 67608062551879 13369511637942272 Bool.true 136844865387 549755813888 67578741911787 13369511637942272

noncomputable def ep978 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 23) qz659 Bool.false 442868152135 1099511627776 131303904433277 26739023275884544 Bool.true 179980434189 1099511627776 131258113020865 26739023275884544 Bool.false

noncomputable abbrev qz660 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 22) qz145)

noncomputable def ep979 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 23) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 22) qz660) Bool.false 442868152135 1099511627776 131303904433277 26739023275884544 Bool.true 179980434189 1099511627776 131258113020865 26739023275884544

noncomputable def ep980 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 22) qz660 Bool.false 268233918901 1099511627776 127308555876971 26739023275884544 Bool.true 23603206917 1099511627776 127264750500013 26739023275884544 Bool.false

noncomputable abbrev qz661 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 21) qz145)

noncomputable def ep981 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 22) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 21) qz661) Bool.false 268233918901 1099511627776 127308555876971 26739023275884544 Bool.true 23603206917 1099511627776 127264750500013 26739023275884544

noncomputable def ep982 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 21) qz661 Bool.false 94553048271 1099511627776 123201693018521 26739023275884544 Bool.false 141934488729 1099511627776 123159618570707 26739023275884544 Bool.false

noncomputable abbrev qz662 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 20) qz145)

noncomputable def ep983 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 21) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 20) qz662) Bool.false 94553048271 1099511627776 123201693018521 26739023275884544 Bool.false 141934488729 1099511627776 123159618570707 26739023275884544

noncomputable def ep984 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 20) qz662 Bool.true 122669818903 1099511627776 1433908738279 322156906938368 Bool.false 257089248699 1099511627776 1433529364809 322156906938368 Bool.false

noncomputable abbrev qz663 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 19) qz145)

noncomputable def ep985 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 20) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 19) qz663) Bool.true 122669818903 1099511627776 1433908738279 322156906938368 Bool.false 257089248699 1099511627776 1433529364809 322156906938368

noncomputable def ep986 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 19) qz663 Bool.true 5828351851 17179869184 28677589157899 6684755818971136 Bool.false 113095083413 549755813888 57350526601797 13369511637942272 Bool.false

noncomputable abbrev qz664 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 18) qz145)

noncomputable def ep987 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 19) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 18) qz664) Bool.true 5828351851 17179869184 28677589157899 6684755818971136 Bool.false 113095083413 549755813888 57350526601797 13369511637942272

noncomputable def ep988 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 18) qz664 Bool.true 489170298293 1099511627776 110302917137063 26739023275884544 Bool.true 2738658663 549755813888 55141123832537 13369511637942272 Bool.false

noncomputable abbrev qz665 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 17) qz145)

noncomputable def ep989 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 18) (@HAdd.hAdd Complex Complex Complex qz4 qz156 qz665) Bool.true 489170298293 1099511627776 110302917137063 26739023275884544 Bool.true 2738658663 549755813888 55141123832537 13369511637942272

noncomputable def ep990 := @Enclosure.Complex.IsNear.addLitP qz156 qz665 Bool.true 34345821403 137438953472 26439736377523 6684755818971136 Bool.true 41011627499 274877906944 26435903800399 6684755818971136 Bool.true

noncomputable abbrev qz166 := (@HMul.hMul Real Real Real qz267 qz446 qz581)

noncomputable def ep991 := @Enclosure.Complex.IsNear.of_eq qz665 (Complex.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)))) Bool.true 214403727069 1099511627776 4543971626971 26739023275884544 Bool.false 79284596335 549755813888 2269316231739 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 17 qz148 rfl)

noncomputable def ep992 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz581 134395 1000 0 1 3189913004350711 1125899906842624 31250000024319 6079750000000000000 85741671643942760969 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 17 1 3189913004350711 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz347) Bool.false 53517859495200818200576 18889465931478580854784 1000000000778208 194552000000000000000 3189913004350711 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 17 1 4 34 32 31784 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep290 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep993 := nat_lit 124969292211209134781366812663295919169885848981594983692545663054407522123776

noncomputable def ep994 := nat_lit 12231060572433162483936805600034223306413474901354782213786212190713348096

noncomputable def ep995 := nat_lit 374883414512482538019132564378687689063044719994982241513209416738841139675136

noncomputable def ep996 := BSN.cos_dyadic_bound_f 1367517884 2147483648 3 2 1048576 389484 ep993 ep71 ep994 ep995 ep74 ep994 843057 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1367517884) qz15 0 2 ep993 ep71 ep994 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1367517884) qz16 0 2 ep995 ep74 ep994 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz464 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 399265771) qz25)

noncomputable def ep997 := @Enclosure.Real.IsNear.cos_image qz166 qz464 Bool.false 399265771 1048576 363 524288 Bool.true 843057 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 85741671643942760969 225179981368524800 839968750653670401 1215950000000000000000 399265771 1048576 363 524288 (ep992 rfl) rfl) (Enclosure.sfrac_false_div 399265771 1048576) (BSN.cos_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96230516166982423805952) qz26) 226375608064910080 72057594037927936 Bool.false 843057 1048576 60 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 399265771 1048576 226375608064910080 72057594037927936 60 96230516166982423805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 843057 1048576 96230516166982423805952 151115727451828646838272 1367517884 2147483648 389484 389104 (ep996 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep998 := nat_lit 3497293320903061239816351177140551936

noncomputable def ep999 := BSN.sin_dyadic_bound_f 1367517884 2147483648 2 1 1048576 389484 ep998 ep61 ep998 ep998 ep62 ep998 623510 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1367517884) qz20 0 1 ep998 ep61 ep998 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1367517884) qz21 0 1 ep998 ep62 ep998 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1000 := @Enclosure.Real.IsNear.sin_image qz166 qz464 Bool.false 399265771 1048576 363 524288 Bool.true 623510 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz166 Bool.false 85741671643942760969 225179981368524800 839968750653670401 1215950000000000000000 399265771 1048576 363 524288 (ep992 rfl) rfl) (Enclosure.sfrac_false_div 399265771 1048576) (BSN.sin_reduce2 qz464 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 96230516166982423805952) qz26) 226375608064910080 72057594037927936 Bool.false 623510 1048576 60 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 399265771 1048576 226375608064910080 72057594037927936 60 96230516166982423805952 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 623510 1048576 96230516166982423805952 151115727451828646838272 1367517884 2147483648 389484 389104 (ep999 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1001 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz49 (Real.cos qz166)) (@HMul.hMul Real Real Real qz0 qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166))) Bool.true 214403727069 1099511627776 4543971626971 26739023275884544 Bool.false 79284596335 549755813888 2269316231739 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz49 (Real.cos qz166) 254317 1048576 1 1048576 843057 1048576 8893333 12750159872 214403727069 1099511627776 4543971626971 26739023275884544 qz349 (@Enclosure.Real.IsNear.recentre' (Real.cos qz166) Bool.true 843057 1048576 71146664 102001278976 843057 1048576 8893333 12750159872 (ep997 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz49 (@Neg.neg Real Real.instNeg (Real.sin qz166)) 254317 1048576 1 1048576 311755 524288 8893333 12750159872 79284596335 549755813888 2269316231739 13369511637942272 qz349 (@Enclosure.Real.IsNear.neg (Real.sin qz166) Bool.true 311755 524288 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz166) Bool.true 623510 1048576 71146664 102001278976 311755 524288 8893333 12750159872 (ep1000 rfl rfl) rfl)) rfl)

noncomputable def ep1002 := @ep990 214403727069 1099511627776 4543971626971 26739023275884544 Bool.false 79284596335 549755813888 2269316231739 13369511637942272 Bool.true 67231053866975988023296 489170298293 1099511627776 110302917137063 26739023275884544 Bool.true 752796761119493455872 2738658663 549755813888 55141123832537 13369511637942272 EMRow45.d14 (ep991 ep1001) rfl rfl

noncomputable abbrev qz167 := (@HMul.hMul Real Real Real qz267 qz446 qz582)

noncomputable def ep1003 := @Enclosure.Complex.IsNear.of_eq qz664 (Complex.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)))) Bool.false 116155779829 1099511627776 4407439494533 26739023275884544 Bool.false 28958435519 137438953472 552350692315 3342377909485568 (BSN.cpow_neg_s_mk qz147 134395 1000 18 qz148 rfl)

noncomputable def ep1004 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz582 134395 1000 0 1 3254268794313975 1125899906842624 31250000024319 6079750000000000000 3498859636894613361 9007199254740992 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 18 1 3254268794313975 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz350) Bool.false 54597570484265130393600 18889465931478580854784 1000000000778208 194552000000000000000 3254268794313975 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 18 1 4 36 32 61752 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep305 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1005 := nat_lit 992276491043847939491904023869250625

noncomputable def ep1006 := BSN.sin_dyadic_bound_f 998063505 2147483648 2 1 1048576 389484 ep1005 ep61 ep1005 ep1005 ep62 ep1005 469979 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 998063505) qz20 0 1 ep1005 ep61 ep1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 998063505) qz21 0 1 ep1005 ep62 ep1005 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz465 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 203660435) qz17)

noncomputable def ep1007 := @Enclosure.Real.IsNear.cos_image qz167 qz465 Bool.false 203660435 524288 363 524288 Bool.false 469979 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 3498859636894613361 9007199254740992 839968750653670401 1215950000000000000000 203660435 524288 363 524288 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 203660435 524288) (BSN.cos_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35116237755132611133440) qz19) 226375608064910080 72057594037927936 Bool.false 469979 1048576 61 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 203660435 524288 226375608064910080 72057594037927936 61 35116237755132611133440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 469979 1048576 35116237755132611133440 75557863725914323419136 998063505 2147483648 389484 389104 (ep1006 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1008 := BSN.cos_dyadic_bound_f 998063505 2147483648 2 1 1048576 389484 ep1005 ep57 ep1005 ep1005 ep58 ep1005 937352 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 998063505) qz15 0 1 ep1005 ep57 ep1005 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 998063505) qz16 0 1 ep1005 ep58 ep1005 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1009 := @Enclosure.Real.IsNear.sin_image qz167 qz465 Bool.false 203660435 524288 363 524288 Bool.true 937352 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz167 Bool.false 3498859636894613361 9007199254740992 839968750653670401 1215950000000000000000 203660435 524288 363 524288 (ep1004 rfl) rfl) (Enclosure.sfrac_false_div 203660435 524288) (BSN.sin_reduce3 qz465 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 35116237755132611133440) qz19) 226375608064910080 72057594037927936 Bool.false 937352 1048576 61 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 203660435 524288 226375608064910080 72057594037927936 61 35116237755132611133440 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 937352 1048576 35116237755132611133440 75557863725914323419136 998063505 2147483648 389484 389104 (ep1008 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1010 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz51 (Real.cos qz167)) (@HMul.hMul Real Real Real qz0 qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167))) Bool.false 116155779829 1099511627776 4407439494533 26739023275884544 Bool.false 28958435519 137438953472 552350692315 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ff qz51 (Real.cos qz167) 247151 1048576 1 1048576 469979 1048576 8893333 12750159872 116155779829 1099511627776 4407439494533 26739023275884544 qz352 (@Enclosure.Real.IsNear.recentre' (Real.cos qz167) Bool.false 469979 1048576 71146664 102001278976 469979 1048576 8893333 12750159872 (ep1007 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz51 (@Neg.neg Real Real.instNeg (Real.sin qz167)) 247151 1048576 1 1048576 117169 131072 8893333 12750159872 28958435519 137438953472 552350692315 3342377909485568 qz352 (@Enclosure.Real.IsNear.neg (Real.sin qz167) Bool.true 117169 131072 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz167) Bool.true 937352 1048576 71146664 102001278976 117169 131072 8893333 12750159872 (ep1009 rfl rfl) rfl)) rfl)

noncomputable def ep1011 := @ep988 116155779829 1099511627776 4407439494533 26739023275884544 Bool.false 28958435519 137438953472 552350692315 3342377909485568 Bool.true 410133800380433447256064 5828351851 17179869184 28677589157899 6684755818971136 Bool.false 15543669907111265959936 113095083413 549755813888 57350526601797 13369511637942272 (ep989 (BSN.head_sum_c_succ qz144 17 18 rfl rfl) (ep1002 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1003 ep1010) rfl rfl

noncomputable abbrev qz168 := (@HMul.hMul Real Real Real qz267 qz446 qz583)

noncomputable def ep1012 := @Enclosure.Complex.IsNear.of_eq qz663 (Complex.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)))) Bool.false 250344699561 1099511627776 4304068645561 26739023275884544 Bool.false 30899081873 1099511627776 4281884075553 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 19 qz148 rfl)

noncomputable def ep1013 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz583 134395 1000 0 1 3315143513283831 1125899906842624 31250000024319 6079750000000000000 89107742493556093449 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 19 1 3315143513283831 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz353) Bool.false 55618878793361701994496 18889465931478580854784 1000000000778208 194552000000000000000 3315143513283831 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 19 1 4 38 32 90099 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep319 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1014 := nat_lit 6021639914934146433484621404208171283802571063540295553826938143840820490284865

noncomputable def ep1015 := nat_lit 8741084029059970388218098197644283887603400180450055902617909453485255831361

noncomputable def ep1016 := nat_lit 15756809450685238802307369613939500712236328232789569217132980428086982298447681

noncomputable def ep1017 := BSN.sin_dyadic_bound_f 3109536521 2147483648 3 2 1048576 389484 ep1014 ep78 ep1015 ep1016 ep80 ep1015 1040679 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3109536521) qz20 0 2 ep1014 ep78 ep1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3109536521) qz21 0 2 ep1016 ep80 ep1015 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz466 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 103735065) qz41)

noncomputable def ep1018 := @Enclosure.Real.IsNear.cos_image qz168 qz466 Bool.false 103735065 262144 363 524288 Bool.false 1040679 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 89107742493556093449 225179981368524800 839968750653670401 1215950000000000000000 103735065 262144 363 524288 (ep1013 rfl) rfl) (Enclosure.sfrac_false_div 103735065 262144) (BSN.cos_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54703544993619021660160) qz336) 226375608064910080 72057594037927936 Bool.false 1040679 1048576 62 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 103735065 262144 226375608064910080 72057594037927936 62 54703544993619021660160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1040679 1048576 54703544993619021660160 37778931862957161709568 3109536521 2147483648 389484 389104 (ep1017 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1019 := nat_lit 3349240434531885783219553268203492617173696546491475332527240261890893719416641

noncomputable def ep1020 := nat_lit 10030239135537537408882223608215189283745882839113525885776484966765710646587201

noncomputable def ep1021 := BSN.cos_dyadic_bound_f 3109536521 2147483648 3 2 1048576 389484 ep1019 ep71 ep1015 ep1020 ep74 ep1015 128447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3109536521) qz15 0 2 ep1019 ep71 ep1015 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3109536521) qz16 0 2 ep1020 ep74 ep1015 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1022 := @Enclosure.Real.IsNear.sin_image qz168 qz466 Bool.false 103735065 262144 363 524288 Bool.true 128447 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz168 Bool.false 89107742493556093449 225179981368524800 839968750653670401 1215950000000000000000 103735065 262144 363 524288 (ep1013 rfl) rfl) (Enclosure.sfrac_false_div 103735065 262144) (BSN.sin_reduce3 qz466 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 54703544993619021660160) qz336) 226375608064910080 72057594037927936 Bool.false 128447 1048576 62 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 103735065 262144 226375608064910080 72057594037927936 62 54703544993619021660160 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 128447 1048576 54703544993619021660160 37778931862957161709568 3109536521 2147483648 389484 389104 (ep1021 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1023 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz53 (Real.cos qz168)) (@HMul.hMul Real Real Real qz0 qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168))) Bool.false 250344699561 1099511627776 4304068645561 26739023275884544 Bool.false 30899081873 1099511627776 4281884075553 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz53 (Real.cos qz168) 240559 1048576 1 1048576 1040679 1048576 8893333 12750159872 250344699561 1099511627776 4304068645561 26739023275884544 qz355 (@Enclosure.Real.IsNear.recentre' (Real.cos qz168) Bool.false 1040679 1048576 71146664 102001278976 1040679 1048576 8893333 12750159872 (ep1018 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz53 (@Neg.neg Real Real.instNeg (Real.sin qz168)) 240559 1048576 1 1048576 128447 1048576 8893333 12750159872 30899081873 1099511627776 4281884075553 26739023275884544 qz355 (@Enclosure.Real.IsNear.neg (Real.sin qz168) Bool.true 128447 1048576 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz168) Bool.true 128447 1048576 71146664 102001278976 128447 1048576 8893333 12750159872 (ep1022 rfl rfl) rfl)) rfl)

noncomputable def ep1024 := @ep986 250344699561 1099511627776 4304068645561 26739023275884544 Bool.false 30899081873 1099511627776 4281884075553 26739023275884544 Bool.true 2107451441578510385152 122669818903 1099511627776 1433908738279 322156906938368 Bool.false 141336309160373190131712 257089248699 1099511627776 1433529364809 322156906938368 (ep987 (BSN.head_sum_c_succ qz144 18 19 rfl rfl) (ep1011 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1012 ep1023) rfl rfl

noncomputable abbrev qz169 := (@HMul.hMul Real Real Real qz267 qz446 qz584)

noncomputable def ep1025 := @Enclosure.Complex.IsNear.of_eq qz662 (Complex.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)))) Bool.false 108611433587 549755813888 1046816935341 6684755818971136 Bool.true 57577379985 549755813888 522085161445 3342377909485568 (BSN.cpow_neg_s_mk qz147 134395 1000 20 qz148 rfl)

noncomputable def ep1026 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz584 134395 1000 0 1 3372893643545847 1125899906842624 31250000024319 6079750000000000000 90660008244868821513 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 20 1 3372893643545847 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz356) Bool.false 56587765202795681021952 18889465931478580854784 1000000000778208 194552000000000000000 3372893643545847 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 20 1 4 40 32 116991 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep330 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1027 := nat_lit 1200755506775981493160549362647147536

noncomputable def ep1028 := BSN.cos_dyadic_bound_f 1046799838 2147483648 2 1 1048576 389484 ep1027 ep57 ep1027 ep1027 ep58 ep1027 926446 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1046799838) qz15 0 1 ep1027 ep57 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1046799838) qz16 0 1 ep1027 ep58 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz467 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 422168561) qz25)

noncomputable def ep1029 := @Enclosure.Real.IsNear.cos_image qz169 qz467 Bool.false 422168561 1048576 725 1048576 Bool.false 926446 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 90660008244868821513 225179981368524800 839968750653670401 1215950000000000000000 422168561 1048576 725 1048576 (ep1026 rfl) rfl) (Enclosure.sfrac_false_div 422168561 1048576) (BSN.cos_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73661990047017401843712) qz26) 226375608064910080 72057594037927936 Bool.false 926446 1048576 64 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 422168561 1048576 226375608064910080 72057594037927936 64 73661990047017401843712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 926446 1048576 73661990047017401843712 151115727451828646838272 1046799838 2147483648 389484 389104 (ep1028 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1030 := BSN.sin_dyadic_bound_f 1046799838 2147483648 2 1 1048576 389484 ep1027 ep61 ep1027 ep1027 ep62 ep1027 491130 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1046799838) qz20 0 1 ep1027 ep61 ep1027 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1046799838) qz21 0 1 ep1027 ep62 ep1027 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1031 := @Enclosure.Real.IsNear.sin_image qz169 qz467 Bool.false 422168561 1048576 725 1048576 Bool.false 491130 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz169 Bool.false 90660008244868821513 225179981368524800 839968750653670401 1215950000000000000000 422168561 1048576 725 1048576 (ep1026 rfl) rfl) (Enclosure.sfrac_false_div 422168561 1048576) (BSN.sin_reduce0 qz467 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 73661990047017401843712) qz26) 226375608064910080 72057594037927936 Bool.false 491130 1048576 64 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 422168561 1048576 226375608064910080 72057594037927936 64 73661990047017401843712 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 491130 1048576 73661990047017401843712 151115727451828646838272 1046799838 2147483648 389484 389104 (ep1030 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1032 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz55 (Real.cos qz169)) (@HMul.hMul Real Real Real qz0 qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169))) Bool.false 108611433587 549755813888 1046816935341 6684755818971136 Bool.true 57577379985 549755813888 522085161445 3342377909485568 (@Enclosure.Real.IsNear.mulLit_ff qz55 (Real.cos qz169) 234469 1048576 1 1048576 463223 524288 17762347 25500319744 108611433587 549755813888 1046816935341 6684755818971136 qz358 (@Enclosure.Real.IsNear.recentre' (Real.cos qz169) Bool.false 926446 1048576 142098776 204002557952 463223 524288 17762347 25500319744 (ep1029 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz55 (@Neg.neg Real Real.instNeg (Real.sin qz169)) 234469 1048576 1 1048576 245565 524288 17762347 25500319744 57577379985 549755813888 522085161445 3342377909485568 qz358 (@Enclosure.Real.IsNear.neg (Real.sin qz169) Bool.false 245565 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz169) Bool.false 491130 1048576 142098776 204002557952 245565 524288 17762347 25500319744 (ep1031 rfl rfl) rfl)) rfl)

noncomputable def ep1033 := @ep984 108611433587 549755813888 1046816935341 6684755818971136 Bool.true 57577379985 549755813888 522085161445 3342377909485568 Bool.false 51981088007814956187648 94553048271 1099511627776 123201693018521 26739023275884544 Bool.false 78029310369988557668352 141934488729 1099511627776 123159618570707 26739023275884544 (ep985 (BSN.head_sum_c_succ qz144 19 20 rfl rfl) (ep1024 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1025 ep1032) rfl rfl

noncomputable abbrev qz170 := (@HMul.hMul Real Real Real qz267 qz446 qz585)

noncomputable def ep1034 := @Enclosure.Complex.IsNear.of_eq qz661 (Complex.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)))) Bool.false 86840435315 549755813888 2053431429225 13369511637942272 Bool.true 82768847823 549755813888 2052565964653 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 21 qz148 rfl)

noncomputable def ep1035 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz585 134395 1000 0 1 3427826275261687 1125899906842624 31250000024319 6079750000000000000 92136542452758884873 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 21 1 3427826275261687 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz359) Bool.false 57509381830540779323392 18889465931478580854784 1000000000778208 194552000000000000000 3427826275261687 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 21 1 4 42 32 142571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep341 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1036 := nat_lit 255435618394014278666051530715268107967336280064583589192463175019773765509376

noncomputable def ep1037 := nat_lit 51089503308895508799661231273720339537659261148255510935895010627307069696

noncomputable def ep1038 := nat_lit 766204676175425044980555269683256883222933521671454256555517735038066682388736

noncomputable def ep1039 := BSN.cos_dyadic_bound_f 1635089238 2147483648 3 2 1048576 389484 ep1036 ep71 ep1037 ep1038 ep74 ep1037 759035 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1635089238) qz15 0 2 ep1036 ep71 ep1037 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1635089238) qz16 0 2 ep1038 ep74 ep1037 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz468 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 429044209) qz25)

noncomputable def ep1040 := @Enclosure.Real.IsNear.cos_image qz170 qz468 Bool.false 429044209 1048576 363 524288 Bool.false 759035 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 92136542452758884873 225179981368524800 839968750653670401 1215950000000000000000 429044209 1048576 363 524288 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 429044209 1048576) (BSN.cos_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115059176301315068264448) qz26) 226375608064910080 72057594037927936 Bool.false 759035 1048576 65 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 429044209 1048576 226375608064910080 72057594037927936 65 115059176301315068264448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 759035 1048576 115059176301315068264448 151115727451828646838272 1635089238 2147483648 389484 389104 (ep1039 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1041 := nat_lit 7147692166629415553601015792165374736

noncomputable def ep1042 := BSN.sin_dyadic_bound_f 1635089238 2147483648 2 1 1048576 389484 ep1041 ep61 ep1041 ep1041 ep62 ep1041 723447 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1635089238) qz20 0 1 ep1041 ep61 ep1041 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1635089238) qz21 0 1 ep1041 ep62 ep1041 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1043 := @Enclosure.Real.IsNear.sin_image qz170 qz468 Bool.false 429044209 1048576 363 524288 Bool.false 723447 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz170 Bool.false 92136542452758884873 225179981368524800 839968750653670401 1215950000000000000000 429044209 1048576 363 524288 (ep1035 rfl) rfl) (Enclosure.sfrac_false_div 429044209 1048576) (BSN.sin_reduce0 qz468 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 115059176301315068264448) qz26) 226375608064910080 72057594037927936 Bool.false 723447 1048576 65 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 429044209 1048576 226375608064910080 72057594037927936 65 115059176301315068264448 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 723447 1048576 115059176301315068264448 151115727451828646838272 1635089238 2147483648 389484 389104 (ep1042 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1044 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz57 (Real.cos qz170)) (@HMul.hMul Real Real Real qz0 qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170))) Bool.false 86840435315 549755813888 2053431429225 13369511637942272 Bool.true 82768847823 549755813888 2052565964653 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz57 (Real.cos qz170) 114409 524288 1 524288 759035 1048576 8893333 12750159872 86840435315 549755813888 2053431429225 13369511637942272 qz361 (@Enclosure.Real.IsNear.recentre' (Real.cos qz170) Bool.false 759035 1048576 71146664 102001278976 759035 1048576 8893333 12750159872 (ep1040 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz57 (@Neg.neg Real Real.instNeg (Real.sin qz170)) 114409 524288 1 524288 723447 1048576 8893333 12750159872 82768847823 549755813888 2052565964653 13369511637942272 qz361 (@Enclosure.Real.IsNear.neg (Real.sin qz170) Bool.false 723447 1048576 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz170) Bool.false 723447 1048576 71146664 102001278976 723447 1048576 8893333 12750159872 (ep1043 rfl rfl) rfl)) rfl)

noncomputable def ep1045 := @ep982 86840435315 549755813888 2053431429225 13369511637942272 Bool.true 82768847823 549755813888 2052565964653 13369511637942272 Bool.false 147463156397787041497088 268233918901 1099511627776 127308555876971 26739023275884544 Bool.true 12976000229022206263296 23603206917 1099511627776 127264750500013 26739023275884544 (ep983 (BSN.head_sum_c_succ qz144 20 21 rfl rfl) (ep1033 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1034 ep1044) rfl rfl

noncomputable abbrev qz171 := (@HMul.hMul Real Real Real qz267 qz446 qz586)

noncomputable def ep1046 := @Enclosure.Complex.IsNear.of_eq qz660 (Complex.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171)))) Bool.false 87317116617 549755813888 1997674278153 13369511637942272 Bool.true 19547153409 137438953472 998340630213 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 22 qz148 rfl)

noncomputable def ep1047 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz586 134395 1000 0 1 3480203401436407 1125899906842624 31250000024319 6079750000000000000 93544387227209183753 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 22 1 3480203401436407 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz362) Bool.false 58388124189833310502912 18889465931478580854784 1000000000778208 194552000000000000000 3480203401436407 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 22 1 4 44 32 166961 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep355 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1048 := nat_lit 216184610066318635276675245678308071237068890812895560794148283021054051266081

noncomputable def ep1049 := nat_lit 36596959662404116384293716948474525014522046248566625292689842116751175201

noncomputable def ep1050 := nat_lit 648480636279631097597257149601027264661177628346189549131859469378928651447841

noncomputable def ep1051 := BSN.cos_dyadic_bound_f 1568305357 2147483648 3 2 1048576 389484 ep1048 ep71 ep1049 ep1050 ep74 ep1049 781162 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1568305357) qz15 0 2 ep1048 ep71 ep1049 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1568305357) qz16 0 2 ep1050 ep74 ep1049 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz469 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 435599997) qz25)

noncomputable def ep1052 := @Enclosure.Real.IsNear.cos_image qz171 qz469 Bool.false 435599997 1048576 363 524288 Bool.false 781162 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 93544387227209183753 225179981368524800 839968750653670401 1215950000000000000000 435599997 1048576 363 524288 (ep1047 rfl) rfl) (Enclosure.sfrac_false_div 435599997 1048576) (BSN.cos_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110359678497669475467264) qz26) 226375608064910080 72057594037927936 Bool.false 781162 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 435599997 1048576 226375608064910080 72057594037927936 66 110359678497669475467264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 781162 1048576 110359678497669475467264 151115727451828646838272 1568305357 2147483648 389484 389104 (ep1051 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1053 := nat_lit 6049542103531813289787669370426707601

noncomputable def ep1054 := BSN.sin_dyadic_bound_f 1568305357 2147483648 2 1 1048576 389484 ep1053 ep61 ep1053 ep1053 ep62 ep1053 699496 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1568305357) qz20 0 1 ep1053 ep61 ep1053 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1568305357) qz21 0 1 ep1053 ep62 ep1053 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1055 := @Enclosure.Real.IsNear.sin_image qz171 qz469 Bool.false 435599997 1048576 363 524288 Bool.false 699496 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz171 Bool.false 93544387227209183753 225179981368524800 839968750653670401 1215950000000000000000 435599997 1048576 363 524288 (ep1047 rfl) rfl) (Enclosure.sfrac_false_div 435599997 1048576) (BSN.sin_reduce0 qz469 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110359678497669475467264) qz26) 226375608064910080 72057594037927936 Bool.false 699496 1048576 66 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 435599997 1048576 226375608064910080 72057594037927936 66 110359678497669475467264 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 699496 1048576 110359678497669475467264 151115727451828646838272 1568305357 2147483648 389484 389104 (ep1054 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1056 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz59 (Real.cos qz171)) (@HMul.hMul Real Real Real qz0 qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171))) Bool.false 87317116617 549755813888 1997674278153 13369511637942272 Bool.true 19547153409 137438953472 998340630213 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz59 (Real.cos qz171) 223557 1048576 1 1048576 390581 524288 8893333 12750159872 87317116617 549755813888 1997674278153 13369511637942272 qz364 (@Enclosure.Real.IsNear.recentre' (Real.cos qz171) Bool.false 781162 1048576 71146664 102001278976 390581 524288 8893333 12750159872 (ep1052 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz59 (@Neg.neg Real Real.instNeg (Real.sin qz171)) 223557 1048576 1 1048576 87437 131072 8893333 12750159872 19547153409 137438953472 998340630213 6684755818971136 qz364 (@Enclosure.Real.IsNear.neg (Real.sin qz171) Bool.false 87437 131072 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz171) Bool.false 699496 1048576 71146664 102001278976 87437 131072 8893333 12750159872 (ep1055 rfl rfl) rfl)) rfl)

noncomputable def ep1057 := @ep980 87317116617 549755813888 1997674278153 13369511637942272 Bool.true 19547153409 137438953472 998340630213 6684755818971136 Bool.false 243469341422051529850880 442868152135 1099511627776 131303904433277 26739023275884544 Bool.true 24736322520372329054208 179980434189 1099511627776 131258113020865 26739023275884544 (ep981 (BSN.head_sum_c_succ qz144 21 22 rfl rfl) (ep1045 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1046 ep1056) rfl rfl

noncomputable abbrev qz172 := (@HMul.hMul Real Real Real qz267 qz446 qz588)

noncomputable def ep1058 := @Enclosure.Complex.IsNear.of_eq qz659 (Complex.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172)))) Bool.false 209237634069 1099511627776 3912220670481 26739023275884544 Bool.true 93709296585 1099511627776 3899370802709 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 23 qz148 rfl)

noncomputable def ep1059 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz588 134395 1000 0 1 3530250507853047 1125899906842624 31250000024319 6079750000000000000 94889603400582050313 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 23 1 3530250507853047 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz589) Bool.false 59227775304360265777152 18889465931478580854784 1000000000778208 194552000000000000000 3530250507853047 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 23 1 4 46 32 190266 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep369 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1060 := nat_lit 668577810140014496582725611300255601

noncomputable def ep1061 := BSN.cos_dyadic_bound_f 904248901 2147483648 2 1 1048576 389484 ep1060 ep57 ep1060 ep1060 ep58 ep1060 956983 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 904248901) qz15 0 1 ep1060 ep57 ep1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 904248901) qz16 0 1 ep1060 ep58 ep1060 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz470 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 110466037) qz41)

noncomputable def ep1062 := @Enclosure.Real.IsNear.cos_image qz172 qz470 Bool.false 110466037 262144 363 524288 Bool.false 956983 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 94889603400582050313 225179981368524800 839968750653670401 1215950000000000000000 110466037 262144 363 524288 (ep1059 rfl) rfl) (Enclosure.sfrac_false_div 110466037 262144) (BSN.cos_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15907714897286375931904) qz336) 226375608064910080 72057594037927936 Bool.false 956983 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 110466037 262144 226375608064910080 72057594037927936 67 15907714897286375931904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 956983 1048576 15907714897286375931904 37778931862957161709568 904248901 2147483648 389484 389104 (ep1061 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1063 := BSN.sin_dyadic_bound_f 904248901 2147483648 2 1 1048576 389484 ep1060 ep61 ep1060 ep1060 ep62 ep1060 428595 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 904248901) qz20 0 1 ep1060 ep61 ep1060 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 904248901) qz21 0 1 ep1060 ep62 ep1060 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1064 := @Enclosure.Real.IsNear.sin_image qz172 qz470 Bool.false 110466037 262144 363 524288 Bool.false 428595 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz172 Bool.false 94889603400582050313 225179981368524800 839968750653670401 1215950000000000000000 110466037 262144 363 524288 (ep1059 rfl) rfl) (Enclosure.sfrac_false_div 110466037 262144) (BSN.sin_reduce0 qz470 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 15907714897286375931904) qz336) 226375608064910080 72057594037927936 Bool.false 428595 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 110466037 262144 226375608064910080 72057594037927936 67 15907714897286375931904 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 428595 1048576 15907714897286375931904 37778931862957161709568 904248901 2147483648 389484 389104 (ep1063 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1065 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz61 (Real.cos qz172)) (@HMul.hMul Real Real Real qz0 qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172))) Bool.false 209237634069 1099511627776 3912220670481 26739023275884544 Bool.true 93709296585 1099511627776 3899370802709 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz61 (Real.cos qz172) 218643 1048576 1 1048576 956983 1048576 8893333 12750159872 209237634069 1099511627776 3912220670481 26739023275884544 qz366 (@Enclosure.Real.IsNear.recentre' (Real.cos qz172) Bool.false 956983 1048576 71146664 102001278976 956983 1048576 8893333 12750159872 (ep1062 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz61 (@Neg.neg Real Real.instNeg (Real.sin qz172)) 218643 1048576 1 1048576 428595 1048576 8893333 12750159872 93709296585 1099511627776 3899370802709 26739023275884544 qz366 (@Enclosure.Real.IsNear.neg (Real.sin qz172) Bool.false 428595 1048576 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz172) Bool.false 428595 1048576 71146664 102001278976 428595 1048576 8893333 12750159872 (ep1064 rfl rfl) rfl)) rfl)

noncomputable def ep1066 := @ep978 209237634069 1099511627776 3912220670481 26739023275884544 Bool.true 93709296585 1099511627776 3899370802709 26739023275884544 Bool.false 716997894471308284002304 163026446551 274877906944 67608062551879 13369511637942272 Bool.true 300925041388895940378624 136844865387 549755813888 67578741911787 13369511637942272 (ep979 (BSN.head_sum_c_succ qz144 22 23 rfl rfl) (ep1057 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1058 ep1065) rfl rfl

noncomputable abbrev qz173 := (@HMul.hMul Real Real Real qz267 qz446 qz591)

noncomputable def ep1067 := @Enclosure.Complex.IsNear.of_eq qz658 (Complex.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173)))) Bool.false 111085598883 549755813888 1916150483363 13369511637942272 Bool.false 31803412893 1099511627776 3810671477893 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 24 qz148 rfl)

noncomputable def ep1068 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz591 134395 1000 0 1 3578169457974519 1125899906842624 31250000024319 6079750000000000000 96177616860897096201 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 24 1 3578169457974519 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz592) Bool.false 60031721881041427759104 18889465931478580854784 1000000000778208 194552000000000000000 3578169457974519 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 24 1 4 48 32 212580 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep380 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1069 := nat_lit 5705286799517066133649474598534690275436642845691568918903109418018900619198720

noncomputable def ep1070 := nat_lit 7847961162749165429342195339838843344067510501038183095570031839893835120896

noncomputable def ep1071 := nat_lit 14929711585424055510767784203707306879777002912190523443543887471832530650562816

noncomputable def ep1072 := BSN.sin_dyadic_bound_f 3067924062 2147483648 3 2 1048576 389484 ep1069 ep78 ep1070 ep1071 ep80 ep1070 1037994 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3067924062) qz20 0 2 ep1069 ep78 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3067924062) qz21 0 2 ep1071 ep80 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz471 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 55982741) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1073 := @Enclosure.Real.IsNear.cos_image qz173 qz471 Bool.false 55982741 131072 363 524288 Bool.false 1037994 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 96177616860897096201 225179981368524800 839968750653670401 1215950000000000000000 55982741 131072 363 524288 (ep1068 rfl) rfl) (Enclosure.sfrac_false_div 55982741 131072) (BSN.cos_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26985745439992359944192) qz454) 226375608064910080 72057594037927936 Bool.false 1037994 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 55982741 131072 226375608064910080 72057594037927936 67 26985745439992359944192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1037994 1048576 26985745439992359944192 18889465931478580854784 3067924062 2147483648 389484 389104 (ep1072 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1074 := nat_lit 3173091760248480814440526863781422972284387141162444147433091913050453159608576

noncomputable def ep1075 := nat_lit 9503579358419944112462896200664591230165026402485256076108135675471571808583936

noncomputable def ep1076 := BSN.cos_dyadic_bound_f 3067924062 2147483648 3 2 1048576 389484 ep1074 ep71 ep1070 ep1075 ep74 ep1070 148587 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3067924062) qz15 0 2 ep1074 ep71 ep1070 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3067924062) qz16 0 2 ep1075 ep74 ep1070 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1077 := @Enclosure.Real.IsNear.sin_image qz173 qz471 Bool.false 55982741 131072 363 524288 Bool.true 148587 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz173 Bool.false 96177616860897096201 225179981368524800 839968750653670401 1215950000000000000000 55982741 131072 363 524288 (ep1068 rfl) rfl) (Enclosure.sfrac_false_div 55982741 131072) (BSN.sin_reduce3 qz471 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 26985745439992359944192) qz454) 226375608064910080 72057594037927936 Bool.false 148587 1048576 67 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 55982741 131072 226375608064910080 72057594037927936 67 26985745439992359944192 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 148587 1048576 26985745439992359944192 18889465931478580854784 3067924062 2147483648 389484 389104 (ep1076 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1078 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz63 (Real.cos qz173)) (@HMul.hMul Real Real Real qz0 qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173))) Bool.false 111085598883 549755813888 1916150483363 13369511637942272 Bool.false 31803412893 1099511627776 3810671477893 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz63 (Real.cos qz173) 214039 1048576 1 1048576 518997 524288 8893333 12750159872 111085598883 549755813888 1916150483363 13369511637942272 qz368 (@Enclosure.Real.IsNear.recentre' (Real.cos qz173) Bool.false 1037994 1048576 71146664 102001278976 518997 524288 8893333 12750159872 (ep1073 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz63 (@Neg.neg Real Real.instNeg (Real.sin qz173)) 214039 1048576 1 1048576 148587 1048576 8893333 12750159872 31803412893 1099511627776 3810671477893 26739023275884544 qz368 (@Enclosure.Real.IsNear.neg (Real.sin qz173) Bool.true 148587 1048576 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz173) Bool.true 148587 1048576 71146664 102001278976 148587 1048576 8893333 12750159872 (ep1077 rfl rfl) rfl)) rfl)

noncomputable def ep1079 := @ep976 111085598883 549755813888 1916150483363 13369511637942272 Bool.false 31803412893 1099511627776 3810671477893 26739023275884544 Bool.false 120159713721493319843840 437138491985 549755813888 34762106517621 6684755818971136 Bool.true 132978409555040642531328 241886317881 1099511627776 138968155301467 26739023275884544 (ep977 (BSN.head_sum_c_succ qz144 23 24 rfl rfl) (ep1066 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1067 ep1078) rfl rfl

theorem EMRow45.d15 : Enclosure.Complex.IsNear qz165 Bool.false 437138491985 549755813888 34762106517621 6684755818971136 Bool.true 241886317881 1099511627776 138968155301467 26739023275884544 := ep975 (BSN.head_sum_c_succ qz144 24 25 rfl rfl) (ep1079 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable abbrev qz174 := (BSN.headSumC qz444 33)

noncomputable abbrev qz666 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 32) qz145)

noncomputable def ep1080 := @Enclosure.Complex.IsNear.of_eq qz174 (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 32) qz666) Bool.false 826398132489 1099511627776 167162539932163 26739023275884544 Bool.true 26673510891 274877906944 83543596928961 13369511637942272

noncomputable def ep1081 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 32) qz666 Bool.false 694061925899 1099511627776 163852678179185 26739023275884544 Bool.false 35663442895 1099511627776 163776017346847 26739023275884544 Bool.false

noncomputable abbrev qz667 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 31) qz145)

noncomputable def ep1082 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 32) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 31) qz667) Bool.false 694061925899 1099511627776 163852678179185 26739023275884544 Bool.false 35663442895 1099511627776 163776017346847 26739023275884544

noncomputable def ep1083 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 31) qz667 Bool.false 220628664513 274877906944 40120790097773 6684755818971136 Bool.false 47339391661 549755813888 40105803465385 6684755818971136 Bool.true

noncomputable abbrev qz668 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 30) qz145)

noncomputable def ep1084 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 31) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 30) qz668) Bool.false 220628664513 274877906944 40120790097773 6684755818971136 Bool.false 47339391661 549755813888 40105803465385 6684755818971136

noncomputable def ep1085 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 30) qz668 Bool.false 441062631495 549755813888 78538980220271 13369511637942272 Bool.true 414310035 4294967296 78496281552365 13369511637942272 Bool.false

noncomputable abbrev qz669 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 29) qz145)

noncomputable def ep1086 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 30) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 29) qz669) Bool.false 441062631495 549755813888 78538980220271 13369511637942272 Bool.true 414310035 4294967296 78496281552365 13369511637942272

noncomputable def ep1087 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 29) qz669 Bool.false 680500801215 1099511627776 153594165322375 26739023275884544 Bool.true 4618917615 68719476736 76764966612843 13369511637942272 Bool.false

noncomputable abbrev qz670 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 28) qz145)

noncomputable def ep1088 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 29) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 28) qz670) Bool.false 680500801215 1099511627776 153594165322375 26739023275884544 Bool.true 4618917615 68719476736 76764966612843 13369511637942272

noncomputable def ep1089 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 28) qz670 Bool.false 712467267397 1099511627776 1808018860795 322156906938368 Bool.false 131412615319 1099511627776 1806988669865 322156906938368 Bool.true

noncomputable abbrev qz671 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 27) qz145)

noncomputable def ep1090 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 28) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 27) qz671) Bool.false 712467267397 1099511627776 1808018860795 322156906938368 Bool.false 131412615319 1099511627776 1806988669865 322156906938368

noncomputable def ep1091 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 27) qz671 Bool.false 924023249047 1099511627776 146450721423535 26739023275884544 Bool.false 135803761559 1099511627776 146390181218555 26739023275884544 Bool.true

noncomputable abbrev qz672 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 26) qz145)

noncomputable def ep1092 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 27) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.headSumC qz144 26) qz672) Bool.false 924023249047 1099511627776 146450721423535 26739023275884544 Bool.false 135803761559 1099511627776 146390181218555 26739023275884544

noncomputable def ep1093 := @Enclosure.Complex.IsNear.addLitP (BSN.headSumC qz144 26) qz672 Bool.false 62756945065 68719476736 71394265139099 13369511637942272 Bool.true 64404093951 1099511627776 142713784883257 26739023275884544 Bool.true

noncomputable abbrev qz673 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 25) qz145)

noncomputable def ep1094 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 26) (@HAdd.hAdd Complex Complex Complex qz4 qz165 qz673) Bool.false 62756945065 68719476736 71394265139099 13369511637942272 Bool.true 64404093951 1099511627776 142713784883257 26739023275884544

noncomputable def ep1095 := @Enclosure.Complex.IsNear.addLitP qz165 qz673 Bool.false 437138491985 549755813888 34762106517621 6684755818971136 Bool.true 241886317881 1099511627776 138968155301467 26739023275884544 Bool.false

noncomputable abbrev qz175 := (@HMul.hMul Real Real Real qz267 qz446 qz602)

noncomputable def ep1096 := @Enclosure.Complex.IsNear.of_eq qz673 (Complex.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175)))) Bool.false 64917068535 549755813888 1870052103857 13369511637942272 Bool.false 88741111965 549755813888 1872814790895 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 25 qz148 rfl)

noncomputable def ep1097 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz602 134395 1000 0 1 3624129903009015 1125899906842624 31250000024319 6079750000000000000 19482597532595862837 45035996273704960 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 25 1 3624129903009015 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz603) Bool.false 60802810194841294602240 18889465931478580854784 1000000000778208 194552000000000000000 3624129903009015 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 25 1 4 50 32 233982 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep416 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1098 := nat_lit 3383955736501620468042896053046410000

noncomputable def ep1099 := BSN.sin_dyadic_bound_f 1356301270 2147483648 2 1 1048576 389484 ep1098 ep61 ep1098 ep1098 ep62 ep1098 619098 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1356301270) qz20 0 1 ep1098 ep61 ep1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1356301270) qz21 0 1 ep1098 ep62 ep1098 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz472 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 113403643) qz41)

noncomputable def ep1100 := @Enclosure.Real.IsNear.cos_image qz175 qz472 Bool.false 113403643 262144 725 1048576 Bool.false 619098 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 19482597532595862837 45035996273704960 839968750653670401 1215950000000000000000 113403643 262144 725 1048576 (ep1097 rfl) rfl) (Enclosure.sfrac_false_div 113403643 262144) (BSN.cos_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23860304276074524573696) qz336) 226375608064910080 72057594037927936 Bool.false 619098 1048576 68 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 113403643 262144 226375608064910080 72057594037927936 68 23860304276074524573696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 619098 1048576 23860304276074524573696 37778931862957161709568 1356301270 2147483648 389484 389104 (ep1099 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1101 := BSN.cos_dyadic_bound_f 1356301270 2147483648 2 1 1048576 389484 ep1098 ep57 ep1098 ep1098 ep58 ep1098 846302 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 1356301270) qz15 0 1 ep1098 ep57 ep1098 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 1356301270) qz16 0 1 ep1098 ep58 ep1098 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1102 := @Enclosure.Real.IsNear.sin_image qz175 qz472 Bool.false 113403643 262144 725 1048576 Bool.true 846302 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz175 Bool.false 19482597532595862837 45035996273704960 839968750653670401 1215950000000000000000 113403643 262144 725 1048576 (ep1097 rfl) rfl) (Enclosure.sfrac_false_div 113403643 262144) (BSN.sin_reduce3 qz472 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23860304276074524573696) qz336) 226375608064910080 72057594037927936 Bool.false 846302 1048576 68 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 113403643 262144 226375608064910080 72057594037927936 68 23860304276074524573696 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 846302 1048576 23860304276074524573696 37778931862957161709568 1356301270 2147483648 389484 389104 (ep1101 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1103 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz66 (Real.cos qz175)) (@HMul.hMul Real Real Real qz0 qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175))) Bool.false 64917068535 549755813888 1870052103857 13369511637942272 Bool.false 88741111965 549755813888 1872814790895 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz66 (Real.cos qz175) 209715 1048576 1 1048576 309549 524288 17762347 25500319744 64917068535 549755813888 1870052103857 13369511637942272 qz370 (@Enclosure.Real.IsNear.recentre' (Real.cos qz175) Bool.false 619098 1048576 142098776 204002557952 309549 524288 17762347 25500319744 (ep1100 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz66 (@Neg.neg Real Real.instNeg (Real.sin qz175)) 209715 1048576 1 1048576 423151 524288 17762347 25500319744 88741111965 549755813888 1872814790895 13369511637942272 qz370 (@Enclosure.Real.IsNear.neg (Real.sin qz175) Bool.true 423151 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz175) Bool.true 846302 1048576 142098776 204002557952 423151 524288 17762347 25500319744 (ep1102 rfl rfl) rfl)) rfl)

noncomputable def ep1104 := @ep1095 64917068535 549755813888 1870052103857 13369511637942272 Bool.false 88741111965 549755813888 1872814790895 13369511637942272 Bool.false 276007963290668640501760 62756945065 68719476736 71394265139099 13369511637942272 Bool.true 35406525087751222591488 64404093951 1099511627776 142713784883257 26739023275884544 EMRow45.d15 (ep1096 ep1103) rfl rfl

noncomputable abbrev qz176 := (@HMul.hMul Real Real Real qz267 qz446 qz605)

noncomputable def ep1105 := @Enclosure.Complex.IsNear.of_eq qz672 (Complex.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176)))) Bool.true 80087871993 1099511627776 3662191145337 26739023275884544 Bool.false 100103927755 549755813888 1838198167649 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 26 qz148 rfl)

noncomputable def ep1106 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz605 134395 1000 0 1 3668288609262839 1125899906842624 31250000024319 6079750000000000000 98599929528375849481 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 26 1 3668288609262839 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz606) Bool.false 61543670347942250676224 18889465931478580854784 1000000000778208 194552000000000000000 3668288609262839 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 26 1 4 52 32 254545 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep427 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1107 := nat_lit 1527028816903968246822274067998872182520161529296331263895564764072570496597121

noncomputable def ep1108 := nat_lit 1822216035947627337852170596919286750148988827419189082666186730625562688641

noncomputable def ep1109 := nat_lit 4577442018640009485791117862802777974060186610234155413521361918756460364414081

noncomputable def ep1110 := BSN.cos_dyadic_bound_f 2556083183 2147483648 3 2 1048576 389484 ep1107 ep71 ep1108 ep1109 ep74 ep1108 389451 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2556083183) qz15 0 2 ep1107 ep71 ep1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2556083183) qz16 0 2 ep1109 ep74 ep1108 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz473 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 459141701) qz25)

noncomputable def ep1111 := @Enclosure.Real.IsNear.cos_image qz176 qz473 Bool.false 459141701 1048576 725 1048576 Bool.true 389451 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 98599929528375849481 225179981368524800 839968750653670401 1215950000000000000000 459141701 1048576 725 1048576 (ep1106 rfl) rfl) (Enclosure.sfrac_false_div 459141701 1048576) (BSN.cos_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179868363652001832108032) qz26) 226375608064910080 72057594037927936 Bool.false 389451 1048576 69 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 459141701 1048576 226375608064910080 72057594037927936 69 179868363652001832108032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 389451 1048576 179868363652001832108032 151115727451828646838272 2556083183 2147483648 389484 389104 (ep1110 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1112 := nat_lit 2747194097598384742409811585920434499136171561671460923745883625946126443723905

noncomputable def ep1113 := nat_lit 7192081905842330547764412544063268652523065251038004684629188051342651679685761

noncomputable def ep1114 := BSN.sin_dyadic_bound_f 2556083183 2147483648 3 2 1048576 389484 ep1112 ep78 ep1108 ep1113 ep80 ep1108 973570 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2556083183) qz20 0 2 ep1112 ep78 ep1108 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2556083183) qz21 0 2 ep1113 ep80 ep1108 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1115 := @Enclosure.Real.IsNear.sin_image qz176 qz473 Bool.false 459141701 1048576 725 1048576 Bool.true 973570 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz176 Bool.false 98599929528375849481 225179981368524800 839968750653670401 1215950000000000000000 459141701 1048576 725 1048576 (ep1106 rfl) rfl) (Enclosure.sfrac_false_div 459141701 1048576) (BSN.sin_reduce2 qz473 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 179868363652001832108032) qz26) 226375608064910080 72057594037927936 Bool.false 973570 1048576 69 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q2 459141701 1048576 226375608064910080 72057594037927936 69 179868363652001832108032 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 973570 1048576 179868363652001832108032 151115727451828646838272 2556083183 2147483648 389484 389104 (ep1114 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1116 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz68 (Real.cos qz176)) (@HMul.hMul Real Real Real qz0 qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176))) Bool.true 80087871993 1099511627776 3662191145337 26739023275884544 Bool.false 100103927755 549755813888 1838198167649 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ft qz68 (Real.cos qz176) 205643 1048576 1 1048576 389451 1048576 17762347 25500319744 80087871993 1099511627776 3662191145337 26739023275884544 qz372 (@Enclosure.Real.IsNear.recentre' (Real.cos qz176) Bool.true 389451 1048576 142098776 204002557952 389451 1048576 17762347 25500319744 (ep1111 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz68 (@Neg.neg Real Real.instNeg (Real.sin qz176)) 205643 1048576 1 1048576 486785 524288 17762347 25500319744 100103927755 549755813888 1838198167649 13369511637942272 qz372 (@Enclosure.Real.IsNear.neg (Real.sin qz176) Bool.true 486785 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz176) Bool.true 973570 1048576 142098776 204002557952 486785 524288 17762347 25500319744 (ep1115 rfl rfl) rfl)) rfl)

noncomputable def ep1117 := @ep1093 80087871993 1099511627776 3662191145337 26739023275884544 Bool.false 100103927755 549755813888 1838198167649 13369511637942272 Bool.false 63498394166408450670592 924023249047 1099511627776 146450721423535 26739023275884544 Bool.false 74658907464919932731392 135803761559 1099511627776 146390181218555 26739023275884544 (ep1094 (BSN.head_sum_c_succ qz144 25 26 rfl rfl) (ep1104 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1105 ep1116) rfl rfl

noncomputable abbrev qz177 := (@HMul.hMul Real Real Real qz267 qz446 qz608)

noncomputable def ep1118 := @Enclosure.Complex.IsNear.of_eq qz671 (Complex.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177)))) Bool.true 105777990825 549755813888 1807422011225 13369511637942272 Bool.true 17152915 4294967296 224367398765 1671188954742784 (BSN.cpow_neg_s_mk qz147 134395 1000 27 qz148 rfl)

noncomputable def ep1119 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz608 134395 1000 0 1 3710780868205815 1125899906842624 31250000024319 6079750000000000000 19948415791300820277 45035996273704960 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 27 1 3710780868205815 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz609) Bool.false 62256572154556490711040 18889465931478580854784 1000000000778208 194552000000000000000 3710780868205815 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 27 1 4 54 32 274332 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep441 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1120 := nat_lit 7910837568026247170220456865625778160141930703038303624162239288500157584111425

noncomputable def ep1121 := nat_lit 15072522289578490140417748951730464920388863601010744536157614739274981046081

noncomputable def ep1122 := nat_lit 20694457165885615509397663054526617285738712728793920667366371522208253227169601

noncomputable def ep1123 := BSN.sin_dyadic_bound_f 3328689161 2147483648 3 2 1048576 389484 ep1120 ep78 ep1121 ep1122 ep80 ep1121 1048350 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3328689161) qz20 0 2 ep1120 ep78 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3328689161) qz21 0 2 ep1122 ep80 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz474 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 58057531) (@Nat.cast Real Real.instNatCast 131072))

noncomputable def ep1124 := @Enclosure.Real.IsNear.cos_image qz177 qz474 Bool.false 58057531 131072 363 524288 Bool.true 1048350 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 19948415791300820277 45035996273704960 839968750653670401 1215950000000000000000 58057531 131072 363 524288 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 58057531 131072) (BSN.cos_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29279459505058424553472) qz454) 226375608064910080 72057594037927936 Bool.false 1048350 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 58057531 131072 226375608064910080 72057594037927936 70 29279459505058424553472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048350 1048576 29279459505058424553472 18889465931478580854784 3328689161 2147483648 389484 389104 (ep1123 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1125 := nat_lit 4401608658809949979073772813770645851154578774399506788772869655717543093860161

noncomputable def ep1126 := nat_lit 13174680931850692956940482943408476623622958595996498877246293737674079319488321

noncomputable def ep1127 := BSN.cos_dyadic_bound_f 3328689161 2147483648 3 2 1048576 389484 ep1125 ep71 ep1121 ep1126 ep74 ep1121 21760 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3328689161) qz15 0 2 ep1125 ep71 ep1121 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3328689161) qz16 0 2 ep1126 ep74 ep1121 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1128 := @Enclosure.Real.IsNear.sin_image qz177 qz474 Bool.false 58057531 131072 363 524288 Bool.false 21760 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz177 Bool.false 19948415791300820277 45035996273704960 839968750653670401 1215950000000000000000 58057531 131072 363 524288 (ep1119 rfl) rfl) (Enclosure.sfrac_false_div 58057531 131072) (BSN.sin_reduce1 qz474 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 29279459505058424553472) qz454) 226375608064910080 72057594037927936 Bool.false 21760 1048576 70 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 58057531 131072 226375608064910080 72057594037927936 70 29279459505058424553472 18889465931478580854784 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 21760 1048576 29279459505058424553472 18889465931478580854784 3328689161 2147483648 389484 389104 (ep1127 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1129 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz70 (Real.cos qz177)) (@HMul.hMul Real Real Real qz0 qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177))) Bool.true 105777990825 549755813888 1807422011225 13369511637942272 Bool.true 17152915 4294967296 224367398765 1671188954742784 (@Enclosure.Real.IsNear.mulLit_ft qz70 (Real.cos qz177) 201799 1048576 1 1048576 524175 524288 8893333 12750159872 105777990825 549755813888 1807422011225 13369511637942272 qz374 (@Enclosure.Real.IsNear.recentre' (Real.cos qz177) Bool.true 1048350 1048576 71146664 102001278976 524175 524288 8893333 12750159872 (ep1124 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz70 (@Neg.neg Real Real.instNeg (Real.sin qz177)) 201799 1048576 1 1048576 85 4096 8893333 12750159872 17152915 4294967296 224367398765 1671188954742784 qz374 (@Enclosure.Real.IsNear.neg (Real.sin qz177) Bool.false 85 4096 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz177) Bool.false 21760 1048576 71146664 102001278976 85 4096 8893333 12750159872 (ep1128 rfl rfl) rfl)) rfl)

noncomputable def ep1130 := @ep1091 105777990825 549755813888 1807422011225 13369511637942272 Bool.true 17152915 4294967296 224367398765 1671188954742784 Bool.false 391683022456397062209536 712467267397 1099511627776 1808018860795 322156906938368 Bool.false 564412885076933607424 131412615319 1099511627776 1806988669865 322156906938368 (ep1092 (BSN.head_sum_c_succ qz144 26 27 rfl rfl) (ep1117 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1118 ep1129) rfl rfl

noncomputable abbrev qz178 := (@HMul.hMul Real Real Real qz267 qz446 qz611)

noncomputable def ep1131 := @Enclosure.Complex.IsNear.of_eq qz670 (Complex.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178)))) Bool.true 15983233091 549755813888 1764299938195 13369511637942272 Bool.true 205315297159 1099511627776 3549873626891 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 28 qz148 rfl)

noncomputable def ep1132 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz611 134395 1000 0 1 3751726938922231 1125899906842624 31250000024319 6079750000000000000 100842668391290647049 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 28 1 3751726938922231 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz612) Bool.false 62943533227317076688896 18889465931478580854784 1000000000778208 194552000000000000000 3751726938922231 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 28 1 4 56 32 293399 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep456 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1133 := nat_lit 12104070391532880420852990555979776

noncomputable def ep1134 := BSN.sin_dyadic_bound_f 331690368 2147483648 2 1 1048576 389484 ep1133 ep61 ep1133 ep1133 ep62 ep1133 161314 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 331690368) qz20 0 1 ep1133 ep61 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 331690368) qz21 0 1 ep1133 ep62 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz475 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 469585267) qz25)

noncomputable def ep1135 := @Enclosure.Real.IsNear.cos_image qz178 qz475 Bool.false 469585267 1048576 363 524288 Bool.true 161314 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 100842668391290647049 225179981368524800 839968750653670401 1215950000000000000000 469585267 1048576 363 524288 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 469585267 1048576) (BSN.cos_reduce1 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23340634708717573505024) qz26) 226375608064910080 72057594037927936 Bool.false 161314 1048576 71 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 469585267 1048576 226375608064910080 72057594037927936 71 23340634708717573505024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 161314 1048576 23340634708717573505024 151115727451828646838272 331690368 2147483648 389484 389104 (ep1134 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1136 := BSN.cos_dyadic_bound_f 331690368 2147483648 2 1 1048576 389484 ep1133 ep57 ep1133 ep1133 ep58 ep1133 1036093 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 331690368) qz15 0 1 ep1133 ep57 ep1133 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 331690368) qz16 0 1 ep1133 ep58 ep1133 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1137 := @Enclosure.Real.IsNear.sin_image qz178 qz475 Bool.false 469585267 1048576 363 524288 Bool.false 1036093 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz178 Bool.false 100842668391290647049 225179981368524800 839968750653670401 1215950000000000000000 469585267 1048576 363 524288 (ep1132 rfl) rfl) (Enclosure.sfrac_false_div 469585267 1048576) (BSN.sin_reduce1 qz475 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 23340634708717573505024) qz26) 226375608064910080 72057594037927936 Bool.false 1036093 1048576 71 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 469585267 1048576 226375608064910080 72057594037927936 71 23340634708717573505024 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1036093 1048576 23340634708717573505024 151115727451828646838272 331690368 2147483648 389484 389104 (ep1136 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1138 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz72 (Real.cos qz178)) (@HMul.hMul Real Real Real qz0 qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178))) Bool.true 15983233091 549755813888 1764299938195 13369511637942272 Bool.true 205315297159 1099511627776 3549873626891 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz72 (Real.cos qz178) 198163 1048576 1 1048576 80657 524288 8893333 12750159872 15983233091 549755813888 1764299938195 13369511637942272 qz376 (@Enclosure.Real.IsNear.recentre' (Real.cos qz178) Bool.true 161314 1048576 71146664 102001278976 80657 524288 8893333 12750159872 (ep1135 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz72 (@Neg.neg Real Real.instNeg (Real.sin qz178)) 198163 1048576 1 1048576 1036093 1048576 8893333 12750159872 205315297159 1099511627776 3549873626891 26739023275884544 qz376 (@Enclosure.Real.IsNear.neg (Real.sin qz178) Bool.false 1036093 1048576 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz178) Bool.false 1036093 1048576 71146664 102001278976 1036093 1048576 8893333 12750159872 (ep1137 rfl rfl) rfl)) rfl)

noncomputable def ep1139 := @ep1089 15983233091 549755813888 1764299938195 13369511637942272 Bool.true 205315297159 1099511627776 3549873626891 26739023275884544 Bool.false 374109271823388424273920 680500801215 1099511627776 153594165322375 26739023275884544 Bool.true 81256858006910234787840 4618917615 68719476736 76764966612843 13369511637942272 (ep1090 (BSN.head_sum_c_succ qz144 27 28 rfl rfl) (ep1130 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1131 ep1138) rfl rfl

noncomputable abbrev qz179 := (@HMul.hMul Real Real Real qz267 qz446 qz613)

noncomputable def ep1140 := @Enclosure.Complex.IsNear.of_eq qz669 (Complex.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)))) Bool.false 201624461775 1099511627776 3483795118167 26739023275884544 Bool.true 2010042945 68719476736 865657469761 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 29 qz148 rfl)

noncomputable def ep1141 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz613 134395 1000 0 1 3791236343078135 1125899906842624 31250000024319 6079750000000000000 20380928333119438133 45035996273704960 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 29 1 3791236343078135 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz614) Bool.false 63606391034871975772160 18889465931478580854784 1000000000778208 194552000000000000000 3791236343078135 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 29 1 4 58 32 311797 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep471 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1142 := nat_lit 13313065735614842383659819577370896

noncomputable def ep1143 := BSN.cos_dyadic_bound_f 339679642 2147483648 2 1 1048576 389484 ep1142 ep57 ep1142 ep1142 ep58 ep1142 1035485 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 339679642) qz15 0 1 ep1142 ep57 ep1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 339679642) qz16 0 1 ep1142 ep58 ep1142 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz476 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 237265233) qz17)

noncomputable def ep1144 := @Enclosure.Real.IsNear.cos_image qz179 qz476 Bool.false 237265233 524288 725 1048576 Bool.false 1035485 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 20380928333119438133 45035996273704960 839968750653670401 1215950000000000000000 237265233 524288 725 1048576 (ep1141 rfl) rfl) (Enclosure.sfrac_false_div 237265233 524288) (BSN.cos_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951414929719249862656) qz19) 226375608064910080 72057594037927936 Bool.false 1035485 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 237265233 524288 226375608064910080 72057594037927936 72 11951414929719249862656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1035485 1048576 11951414929719249862656 75557863725914323419136 339679642 2147483648 389484 389104 (ep1143 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1145 := BSN.sin_dyadic_bound_f 339679642 2147483648 2 1 1048576 389484 ep1142 ep61 ep1142 ep1142 ep62 ep1142 165168 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 339679642) qz20 0 1 ep1142 ep61 ep1142 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 339679642) qz21 0 1 ep1142 ep62 ep1142 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1146 := @Enclosure.Real.IsNear.sin_image qz179 qz476 Bool.false 237265233 524288 725 1048576 Bool.false 165168 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz179 Bool.false 20380928333119438133 45035996273704960 839968750653670401 1215950000000000000000 237265233 524288 725 1048576 (ep1141 rfl) rfl) (Enclosure.sfrac_false_div 237265233 524288) (BSN.sin_reduce0 qz476 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 11951414929719249862656) qz19) 226375608064910080 72057594037927936 Bool.false 165168 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 237265233 524288 226375608064910080 72057594037927936 72 11951414929719249862656 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 165168 1048576 11951414929719249862656 75557863725914323419136 339679642 2147483648 389484 389104 (ep1145 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1147 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz377 (Real.cos qz179)) (@HMul.hMul Real Real Real qz0 qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179))) Bool.false 201624461775 1099511627776 3483795118167 26739023275884544 Bool.true 2010042945 68719476736 865657469761 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ff qz377 (Real.cos qz179) 194715 1048576 1 1048576 1035485 1048576 17762347 25500319744 201624461775 1099511627776 3483795118167 26739023275884544 qz381 (@Enclosure.Real.IsNear.recentre' (Real.cos qz179) Bool.false 1035485 1048576 142098776 204002557952 1035485 1048576 17762347 25500319744 (ep1144 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz377 (@Neg.neg Real Real.instNeg (Real.sin qz179)) 194715 1048576 1 1048576 10323 65536 17762347 25500319744 2010042945 68719476736 865657469761 6684755818971136 qz381 (@Enclosure.Real.IsNear.neg (Real.sin qz179) Bool.false 10323 65536 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz179) Bool.false 165168 1048576 142098776 204002557952 10323 65536 17762347 25500319744 (ep1146 rfl rfl) rfl)) rfl)

noncomputable def ep1148 := @ep1087 201624461775 1099511627776 3483795118167 26739023275884544 Bool.true 2010042945 68719476736 865657469761 6684755818971136 Bool.false 969906983812466988810240 441062631495 549755813888 78538980220271 13369511637942272 Bool.true 455538700986781532160 414310035 4294967296 78496281552365 13369511637942272 (ep1088 (BSN.head_sum_c_succ qz144 28 29 rfl rfl) (ep1139 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1140 ep1147) rfl rfl

noncomputable abbrev qz180 := (@HMul.hMul Real Real Real qz267 qz446 qz615)

noncomputable def ep1149 := @Enclosure.Complex.IsNear.of_eq qz668 (Complex.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)))) Bool.false 194697531 549755813888 1702599975275 13369511637942272 Bool.false 100371076141 549755813888 1715325378405 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 30 qz148 rfl)

noncomputable def ep1150 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz615 134395 1000 0 1 3829405717437687 1125899906842624 31250000024319 6079750000000000000 102930596279007588873 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 30 1 3829405717437687 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz616) Bool.false 64246766873087041339392 18889465931478580854784 1000000000778208 194552000000000000000 3829405717437687 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 30 1 4 60 32 329571 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep486 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1151 := BSN.sin_dyadic_bound_f 4166068 2147483648 1 0 1048576 389484 0 1 1 0 1 1 2034 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.sinEvenP 4166068) qz20 0 0 rfl) (@BSN.binarySplit_of_le (BSN.sinOddP 4166068) qz21 0 0 rfl) rfl rfl

noncomputable abbrev qz477 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 479307939) qz25)

noncomputable def ep1152 := @Enclosure.Real.IsNear.cos_image qz180 qz477 Bool.false 479307939 1048576 363 524288 Bool.false 2034 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 102930596279007588873 225179981368524800 839968750653670401 1215950000000000000000 479307939 1048576 363 524288 (ep1150 rfl) rfl) (Enclosure.sfrac_false_div 479307939 1048576) (BSN.cos_reduce3 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293160974948423958528) qz26) 226375608064910080 72057594037927936 Bool.false 2034 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 479307939 1048576 226375608064910080 72057594037927936 72 293160974948423958528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 2034 1048576 293160974948423958528 151115727451828646838272 4166068 2147483648 389484 389104 (ep1151 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1153 := BSN.cos_dyadic_bound_f 4166068 2147483648 1 0 1048576 389484 0 1 1 0 1 1 1048574 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.cosEvenP 4166068) qz15 0 0 rfl) (@BSN.binarySplit_of_le (BSN.cosOddP 4166068) qz16 0 0 rfl) rfl rfl

noncomputable def ep1154 := @Enclosure.Real.IsNear.sin_image qz180 qz477 Bool.false 479307939 1048576 363 524288 Bool.true 1048574 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz180 Bool.false 102930596279007588873 225179981368524800 839968750653670401 1215950000000000000000 479307939 1048576 363 524288 (ep1150 rfl) rfl) (Enclosure.sfrac_false_div 479307939 1048576) (BSN.sin_reduce3 qz477 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 293160974948423958528) qz26) 226375608064910080 72057594037927936 Bool.false 1048574 1048576 72 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 479307939 1048576 226375608064910080 72057594037927936 72 293160974948423958528 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1048574 1048576 293160974948423958528 151115727451828646838272 4166068 2147483648 389484 389104 (ep1153 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1155 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz382 (Real.cos qz180)) (@HMul.hMul Real Real Real qz0 qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180))) Bool.false 194697531 549755813888 1702599975275 13369511637942272 Bool.false 100371076141 549755813888 1715325378405 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz382 (Real.cos qz180) 191443 1048576 1 1048576 1017 524288 8893333 12750159872 194697531 549755813888 1702599975275 13369511637942272 qz386 (@Enclosure.Real.IsNear.recentre' (Real.cos qz180) Bool.false 2034 1048576 71146664 102001278976 1017 524288 8893333 12750159872 (ep1152 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz382 (@Neg.neg Real Real.instNeg (Real.sin qz180)) 191443 1048576 1 1048576 524287 524288 8893333 12750159872 100371076141 549755813888 1715325378405 13369511637942272 qz386 (@Enclosure.Real.IsNear.neg (Real.sin qz180) Bool.true 524287 524288 8893333 12750159872 (@Enclosure.Real.IsNear.recentre' (Real.sin qz180) Bool.true 1048574 1048576 71146664 102001278976 524287 524288 8893333 12750159872 (ep1154 rfl rfl) rfl)) rfl)

noncomputable def ep1156 := @ep1085 194697531 549755813888 1702599975275 13369511637942272 Bool.false 100371076141 549755813888 1715325378405 13369511637942272 Bool.false 242583782052733636313088 220628664513 274877906944 40120790097773 6684755818971136 Bool.false 203321138996530118656 47339391661 549755813888 40105803465385 6684755818971136 (ep1086 (BSN.head_sum_c_succ qz144 29 30 rfl rfl) (ep1148 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1149 ep1155) rfl rfl

noncomputable abbrev qz181 := (@HMul.hMul Real Real Real qz267 qz446 qz617)

noncomputable def ep1157 := @Enclosure.Complex.IsNear.of_eq qz667 (Complex.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181)))) Bool.true 188452732153 1099511627776 3369517788093 26739023275884544 Bool.true 59015340427 1099511627776 3352803485307 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 31 qz148 rfl)

noncomputable def ep1158 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz617 134395 1000 0 1 3866325256314103 1125899906842624 31250000024319 6079750000000000000 103922956564466774537 225179981368524800 839968750653670401 1215950000000000000000 qz149 (BSN.isNear_log_sfrac 31 1 3866325256314103 1125899906842624 31250000024319 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz618) Bool.false 64866173951437069877248 18889465931478580854784 1000000000778208 194552000000000000000 3866325256314103 1125899906842624 31250000024319 6079750000000000000 (BSN.log_rat_reduce_isNear 31 1 4 62 32 346763 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep501 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1159 := nat_lit 3531229889242360801629603332998414993536330495945770849651021576194556491626625

noncomputable def ep1160 := nat_lit 3009600758332819345884864574784647738966626876434032698517842879093372516481

noncomputable def ep1161 := nat_lit 9243586546787929915803242758065245077208252950629459029478884763467211065424001

noncomputable def ep1162 := BSN.sin_dyadic_bound_f 2721533039 2147483648 3 2 1048576 389484 ep1159 ep78 ep1160 ep1161 ep80 ep1160 1000657 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2721533039) qz20 0 2 ep1159 ep78 ep1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2721533039) qz21 0 2 ep1161 ep80 ep1160 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz478 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 483928977) qz25)

noncomputable def ep1163 := @Enclosure.Real.IsNear.cos_image qz181 qz478 Bool.false 483928977 1048576 725 1048576 Bool.true 1000657 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 103922956564466774537 225179981368524800 839968750653670401 1215950000000000000000 483928977 1048576 725 1048576 (ep1158 rfl) rfl) (Enclosure.sfrac_false_div 483928977 1048576) (BSN.cos_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191510862246082986901504) qz26) 226375608064910080 72057594037927936 Bool.false 1000657 1048576 73 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 483928977 1048576 226375608064910080 72057594037927936 73 191510862246082986901504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1000657 1048576 191510862246082986901504 151115727451828646838272 2721533039 2147483648 389484 389104 (ep1162 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1164 := nat_lit 1963131983249459476170172902587912617626390998581621153227686583609906216466561

noncomputable def ep1165 := nat_lit 5883376748231712789818748978614168557401239741991995394286024065071531904366721

noncomputable def ep1166 := BSN.cos_dyadic_bound_f 2721533039 2147483648 3 2 1048576 389484 ep1164 ep71 ep1160 ep1165 ep74 ep1160 313363 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2721533039) qz15 0 2 ep1164 ep71 ep1160 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2721533039) qz16 0 2 ep1165 ep74 ep1160 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1167 := @Enclosure.Real.IsNear.sin_image qz181 qz478 Bool.false 483928977 1048576 725 1048576 Bool.false 313363 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz181 Bool.false 103922956564466774537 225179981368524800 839968750653670401 1215950000000000000000 483928977 1048576 725 1048576 (ep1158 rfl) rfl) (Enclosure.sfrac_false_div 483928977 1048576) (BSN.sin_reduce1 qz478 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 191510862246082986901504) qz26) 226375608064910080 72057594037927936 Bool.false 313363 1048576 73 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 483928977 1048576 226375608064910080 72057594037927936 73 191510862246082986901504 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 313363 1048576 191510862246082986901504 151115727451828646838272 2721533039 2147483648 389484 389104 (ep1166 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1168 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz387 (Real.cos qz181)) (@HMul.hMul Real Real Real qz0 qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181))) Bool.true 188452732153 1099511627776 3369517788093 26739023275884544 Bool.true 59015340427 1099511627776 3352803485307 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ft qz387 (Real.cos qz181) 188329 1048576 1 1048576 1000657 1048576 17762347 25500319744 188452732153 1099511627776 3369517788093 26739023275884544 qz391 (@Enclosure.Real.IsNear.recentre' (Real.cos qz181) Bool.true 1000657 1048576 142098776 204002557952 1000657 1048576 17762347 25500319744 (ep1163 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz387 (@Neg.neg Real Real.instNeg (Real.sin qz181)) 188329 1048576 1 1048576 313363 1048576 17762347 25500319744 59015340427 1099511627776 3352803485307 26739023275884544 qz391 (@Enclosure.Real.IsNear.neg (Real.sin qz181) Bool.false 313363 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz181) Bool.false 313363 1048576 142098776 204002557952 313363 1048576 17762347 25500319744 (ep1167 rfl rfl) rfl)) rfl)

noncomputable def ep1169 := @ep1083 188452732153 1099511627776 3369517788093 26739023275884544 Bool.true 59015340427 1099511627776 3352803485307 26739023275884544 Bool.false 190782289480638745542656 694061925899 1099511627776 163852678179185 26739023275884544 Bool.false 19606185074788935925760 35663442895 1099511627776 163776017346847 26739023275884544 (ep1084 (BSN.head_sum_c_succ qz144 30 31 rfl rfl) (ep1156 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1157 ep1168) rfl rfl

noncomputable abbrev qz182 := (@HMul.hMul Real Real Real qz267 qz446 qz619)

noncomputable def ep1170 := @Enclosure.Complex.IsNear.of_eq qz666 (Complex.mk (@HMul.hMul Real Real Real qz0 qz392 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz392 (@Neg.neg Real Real.instNeg (Real.sin qz182)))) Bool.false 66168103295 549755813888 1654930876489 13369511637942272 Bool.true 142357486459 1099511627776 3311176511075 26739023275884544 (BSN.cpow_neg_s_mk qz147 134395 1000 32 qz148 rfl)

noncomputable def ep1171 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz619 134395 1000 0 1 15608286920413395 4503599627370496 25000000024319 4863800000000000000 83907028826758328841 180143985094819840 671975000653670401 972760000000000000000 qz149 (BSN.isNear_log_sfrac 32 1 15608286920413395 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz620) Bool.false 65465900263437584302080 18889465931478580854784 1000000000972760 194552000000000000000 15608286920413395 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 32 1 5 64 64 0 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep512 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1172 := nat_lit 346789038638298243478378924257900482697056079941561285272135498441947793021761

noncomputable def ep1173 := nat_lit 94153697608168481417722555938128513018694193893433986872688532506902223681

noncomputable def ep1174 := nat_lit 1040178808519678393472301327661825191065130851436896987842661118260829574617921

noncomputable def ep1175 := BSN.cos_dyadic_bound_f 1764938889 2147483648 3 2 1048576 389484 ep1172 ep71 ep1173 ep1174 ep74 ep1173 713930 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 1764938889) qz15 0 2 ep1172 ep71 ep1173 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 1764938889) qz16 0 2 ep1174 ep74 ep1173 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz479 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 122100797) qz41)

noncomputable def ep1176 := @Enclosure.Real.IsNear.cos_image qz182 qz479 Bool.false 122100797 262144 725 1048576 Bool.false 713930 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 83907028826758328841 180143985094819840 671975000653670401 972760000000000000000 122100797 262144 725 1048576 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 122100797 262144) (BSN.cos_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31049133298833176920064) qz336) 226375608064910080 72057594037927936 Bool.false 713930 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 122100797 262144 226375608064910080 72057594037927936 74 31049133298833176920064 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 713930 1048576 31049133298833176920064 37778931862957161709568 1764938889 2147483648 389484 389104 (ep1175 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1177 := nat_lit 9703282826351527171985524921639771041

noncomputable def ep1178 := BSN.sin_dyadic_bound_f 1764938889 2147483648 2 1 1048576 389484 ep1177 ep61 ep1177 ep1177 ep62 ep1177 767993 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 1764938889) qz20 0 1 ep1177 ep61 ep1177 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 1764938889) qz21 0 1 ep1177 ep62 ep1177 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1179 := @Enclosure.Real.IsNear.sin_image qz182 qz479 Bool.false 122100797 262144 725 1048576 Bool.false 767993 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz182 Bool.false 83907028826758328841 180143985094819840 671975000653670401 972760000000000000000 122100797 262144 725 1048576 (ep1171 rfl) rfl) (Enclosure.sfrac_false_div 122100797 262144) (BSN.sin_reduce0 qz479 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 31049133298833176920064) qz336) 226375608064910080 72057594037927936 Bool.false 767993 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q0 122100797 262144 226375608064910080 72057594037927936 74 31049133298833176920064 37778931862957161709568 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 767993 1048576 31049133298833176920064 37778931862957161709568 1764938889 2147483648 389484 389104 (ep1178 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1180 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz392 (Real.cos qz182)) (@HMul.hMul Real Real Real qz0 qz392 (@Neg.neg Real Real.instNeg (Real.sin qz182))) Bool.false 66168103295 549755813888 1654930876489 13369511637942272 Bool.true 142357486459 1099511627776 3311176511075 26739023275884544 (@Enclosure.Real.IsNear.mulLit_ff qz392 (Real.cos qz182) 185363 1048576 1 1048576 356965 524288 17762347 25500319744 66168103295 549755813888 1654930876489 13369511637942272 qz396 (@Enclosure.Real.IsNear.recentre' (Real.cos qz182) Bool.false 713930 1048576 142098776 204002557952 356965 524288 17762347 25500319744 (ep1176 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz392 (@Neg.neg Real Real.instNeg (Real.sin qz182)) 185363 1048576 1 1048576 767993 1048576 17762347 25500319744 142357486459 1099511627776 3311176511075 26739023275884544 qz396 (@Enclosure.Real.IsNear.neg (Real.sin qz182) Bool.false 767993 1048576 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz182) Bool.false 767993 1048576 142098776 204002557952 767993 1048576 17762347 25500319744 (ep1179 rfl rfl) rfl)) rfl)

noncomputable def ep1181 := @ep1081 66168103295 549755813888 1654930876489 13369511637942272 Bool.true 142357486459 1099511627776 3311176511075 26739023275884544 Bool.false 454317177922013450207232 826398132489 1099511627776 167162539932163 26739023275884544 Bool.true 117311341513057096433664 26673510891 274877906944 83543596928961 13369511637942272 (ep1082 (BSN.head_sum_c_succ qz144 31 32 rfl rfl) (ep1169 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1170 ep1180) rfl rfl

theorem EMRow45.d16 : Enclosure.Complex.IsNear qz174 Bool.false 826398132489 1099511627776 167162539932163 26739023275884544 Bool.true 26673510891 274877906944 83543596928961 13369511637942272 := ep1080 (BSN.head_sum_c_succ qz144 32 33 rfl rfl) (ep1181 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1182 := nat_lit 4092675679815921132770198584431

noncomputable def ep1183 := nat_lit 5664229978825380207818230988800

noncomputable def ep1184 := nat_lit 248652445662460955395784691334801129

noncomputable def ep1185 := nat_lit 37015508894431695811720901585115545600

noncomputable abbrev qz674 := (@HAdd.hAdd Complex Complex Complex qz687 (@HAdd.hAdd Complex Complex Complex qz687 qz690 (@HMul.hMul Complex Complex Complex qz689 Complex.I (@HDiv.hDiv Complex Complex Complex qz691 (↑qz694) (2 : Complex)))) (@Nat.cast Complex Complex.instNatCast 2))

noncomputable abbrev qz480 := qz674

noncomputable abbrev qz183 := (Complex.Stirling.logGammaStirling 1 qz480)

noncomputable abbrev qz675 := (@HAdd.hAdd Complex Complex Complex qz687 qz690 (@HMul.hMul Complex Complex Complex qz689 Complex.I (@HDiv.hDiv Complex Complex Complex qz691 (↑qz694) (2 : Complex))))

noncomputable abbrev qz481 := qz675

noncomputable abbrev qz184 := qz481

noncomputable abbrev qz185 := (@HMul.hMul Real Real Real qz267 (@HDiv.hDiv Real Real Real qz270 qz446 (2 : Real)) (Real.log Real.pi))

noncomputable def ep1186 := Complex.re (@HMul.hMul Complex Complex Complex qz78 (Complex.exp (@HMul.hMul Complex Complex Complex qz78 Complex.I ↑(@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185))) (zetaApproximant qz144 1 34))

noncomputable def ep1187 := @Enclosure.Real.IsNear.of_eq ep1186 (@HSub.hSub Real Real Real qz401 (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.im (zetaApproximant qz144 1 34))))

noncomputable def ep1188 := nat_lit 327409248395177552061775989903

noncomputable def ep1189 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.im (zetaApproximant qz144 1 34))) ep1188

noncomputable def ep1190 := nat_lit 453138398306030416625458479104

noncomputable def ep1191 := nat_lit 8983281285933023128763810340547764479

noncomputable def ep1192 := nat_lit 1339961421978427388384296637381182750720

noncomputable def ep1193 := nat_lit 120149752403463995997421287

noncomputable def ep1194 := nat_lit 11328459957650760415636461977600

noncomputable def ep1195 := nat_lit 44843117620158641408988714430090977

noncomputable def ep1196 := nat_lit 3349903554946068470960741593452956876800

noncomputable def ep1197 := nat_lit 3709097004675661360809561885078762978242582628500533986459648

noncomputable def ep1198 := @Enclosure.Real.IsNear.mulLit_ff (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.re (zetaApproximant qz144 1 34)) 1048575 1048576 9153421

noncomputable def ep1199 := nat_lit 7806052223140394155443721

noncomputable def ep1200 := nat_lit 10803661306048164764057600

noncomputable def ep1201 := nat_lit 211582203812754506503187337

noncomputable def ep1202 := nat_lit 32841779912723164862139596800

noncomputable def ep1203 := @Enclosure.Real.IsNear.recentre' (Real.cos (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) Bool.false 1048575 1048576 73227368

noncomputable abbrev qz482 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72472121) qz17)

noncomputable def ep1204 := @Enclosure.Real.IsNear.cos_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185) qz482 Bool.false 72472121 524288 371

noncomputable def ep1205 := nat_lit 5390654968635026226880909

noncomputable def ep1206 := nat_lit 15300191846400000000000000000

noncomputable def ep1207 := @Enclosure.Real.IsNear.recentre' (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185) Bool.false 373518470054623139393 2702159776422297600 ep1205 ep1206

noncomputable def ep1208 := nat_lit 1468632562635026226880909

noncomputable def ep1209 := @Enclosure.Real.IsNear.subLit_ff_p (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185 581376620753832728129 2702159776422297600 ep1208 ep1206 2016489459 26214400

noncomputable def ep1210 := nat_lit 9791562581399912825303859200

noncomputable def ep1211 := nat_lit 1275015987200000000000000000

noncomputable def ep1212 := @Enclosure.Complex.IsNear.im_isNear (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j)))) Bool.true 11899253825930946781 112589990684262400 228768723733300484752561 ep1211 Bool.false 581376620753832728129 2702159776422297600

noncomputable def ep1213 := nat_lit 1389989362619726035034509

noncomputable def ep1214 := @Enclosure.Complex.IsNear.subLitP qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))) Bool.true 10951758219515819881 112589990684262400 225491923718000292906161 ep1211 Bool.false 589805394407509505729 2702159776422297600 ep1213

noncomputable def ep1215 := nat_lit 13397368774112390199040140686393344

noncomputable def ep1216 := nat_lit 163642970786804952856560551145242624

noncomputable abbrev qz483 := (@HSub.hSub Complex Complex Complex qz623 qz674 qz626)

noncomputable abbrev qz484 := (Complex.log qz674)

noncomputable abbrev qz186 := (@HSub.hSub Complex Complex Complex qz398 (@HMul.hMul Complex Complex Complex qz397 qz483 qz484) qz480)

noncomputable abbrev qz187 := qz480

noncomputable def ep1217 := @Enclosure.Complex.IsNear.of_eq qz183 (@HAdd.hAdd Complex Complex Complex qz4 (@HAdd.hAdd Complex Complex Complex qz4 qz186 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k)))))) Bool.true 10951758219515819881

noncomputable def ep1218 := @Enclosure.Complex.IsNear.addLitP (@HAdd.hAdd Complex Complex Complex qz4 qz186 qz84) (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) Bool.true 10951762889422763881 112589990684262400

noncomputable def ep1219 := nat_lit 752599094184314165496345788416

noncomputable def ep1220 := nat_lit 810622361595083079652857484410880

noncomputable def ep1221 := @ep1218 3440732849979043751 19455200000000000000000 Bool.false 196602913890758704363 900719925474099200 110464844241316757 1215950000000000000000 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800 Bool.true ep1219 10951758219515819881 112589990684262400 225491923718000292906161 ep1211 Bool.false ep1220

noncomputable def ep1222 := @Enclosure.Complex.IsNear.addLitP qz186 qz84 Bool.true 11055226074603026281 112589990684262400 3403625000857950001 19455200000000000000000

noncomputable def ep1223 := nat_lit 1435469465442420507410432

noncomputable def ep1224 := @ep1222 Bool.false 196602913890758704363 900719925474099200 110464844241316757 1215950000000000000000 Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 Bool.true ep1223 10951762889422763881 112589990684262400 3440732849979043751 19455200000000000000000 Bool.false 196602913890758704363 196602913890758704363 900719925474099200

noncomputable abbrev qz188 := (@HMul.hMul Complex Complex Complex qz397 qz483 qz484)

noncomputable def ep1225 := @Enclosure.Complex.IsNear.subLitP qz188 qz187 Bool.true 10801898595563435881 112589990684262400 3403625000857950001 19455200000000000000000 Bool.false 51425808216560897071

noncomputable def ep1226 := @ep1225 180143985094819840 110464844241316757 1215950000000000000000 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 Bool.true 44220904298412105124000 11055226074603026281 112589990684262400 3403625000857950001 19455200000000000000000 Bool.false 157282331112606963490400 196602913890758704363 900719925474099200 110464844241316757 1215950000000000000000

noncomputable abbrev qz189 := qz483

noncomputable abbrev qz190 := qz484

noncomputable def ep1227 := @Enclosure.Complex.IsNear.mul qz189 qz190 Bool.true 10801898595563435881 112589990684262400 3403625000857950001 19455200000000000000000 Bool.false 51425808216560897071 180143985094819840 110464844241316757

noncomputable abbrev qz191 := (Complex.re qz483)

noncomputable abbrev qz192 := (Complex.re qz484)

noncomputable abbrev qz193 := (Complex.im qz483)

noncomputable abbrev qz194 := (Complex.im qz484)

noncomputable def ep1228 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 qz191 qz192) (@HMul.hMul Real Real Real qz0 qz193 qz194) 66332107173224515 9007199254740992 109375000510699 48638000000000000000 23262099870457484637 225179981368524800

noncomputable def ep1229 := nat_lit 194589705959493495642287548508667904

noncomputable def ep1230 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz192 7000 4000 0 1 9476015310460645 2251799813685248 15625000072957 12159500000000000000

noncomputable def ep1231 := @Enclosure.Complex.IsNear.re_isNear qz189 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable abbrev qz676 := (Enclosure.sfrac Bool.false 268790 4000)

noncomputable abbrev qz485 := qz676

noncomputable def ep1232 := @Enclosure.Complex.IsNear.of_eq qz189 (Complex.mk (Enclosure.sfrac Bool.false 7000 4000) qz485) Bool.false 7000 4000 0 1 Bool.false 268790 4000 0

noncomputable abbrev qz486 := (Complex.log (Complex.mk qz630 qz676))

noncomputable def ep1233 := @Enclosure.Complex.IsNear.of_eq qz190 qz486 Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1234 := BSN.log_dyadic_bound 6793064100 137865064100 2 1 57020327697891326430000 1048576 389104 46145719866708810000 46145719866708810000 103417 144658128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6793064100) (BSN.artanhQ 137865064100) 0 1 46145719866708810000 57020327697891326430000 46145719866708810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable abbrev qz677 := (Real.log (Enclosure.sfrac Bool.false 72329064100 16000000))

noncomputable def ep1235 := @Enclosure.Real.IsNear.mulLit_ff qz98 qz677 1 2 0 1 9476015310460645 1125899906842624 15625000072957 6079750000000000000 9476015310460645 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 72329064100 16000000 9476015310460645 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72329064100) qz632)) Bool.false 317962311365810601328640 37778931862957161709568 1000000004669248 389104000000000000000 9476015310460645 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 72329064100 16000000 12 144658128200 131072000000 103417 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep1234 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1236 := BSN.arctan_dyadic_bound_f 9000 268790 1 0 1048576 389104 0 1 1 0 1 1 35096 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 9000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 9000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz487 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 9000) (@Nat.cast Real Real.instNatCast 268790)))

noncomputable def ep1237 := @Enclosure.Real.IsNear.subLit_ff_p qz99 qz487 884279719003555 562949953421312 1 2000000000000000 35096 1048576 1 389104 907477199068597321728 865437697476003 562949953421312 125000000024319 48638000000000000000 qz100 (ep1236 rfl) rfl rfl

noncomputable abbrev qz488 := (Complex.mk qz630 qz676)

noncomputable abbrev qz489 := (Real.arctan (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 268790) (@Nat.cast Real Real.instNatCast 9000)))

noncomputable def ep1238 := @Enclosure.Complex.IsNear.re_isNear qz190 Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (ep1233 (@congrArg Complex Complex qz187 qz488 Complex.log (BSN.w_shift_mk qz147 Bool.false 134395 1000 2 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz486 Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz486) (@HMul.hMul Real Real Real qz0 qz98 qz677) Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 9000 268790 4000 72329064100 16000000 rfl rfl rfl) (ep1235 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz486) qz489 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 9000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz489 (@HSub.hSub Real Real Real qz401 qz99 qz487) Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 268790 9000 rfl rfl) ep1237))))

noncomputable def ep1239 := @Enclosure.Real.IsNear.mulLit_ff qz193 qz194 268790 4000 0 1 865437697476003 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1240 := @Enclosure.Complex.IsNear.im_isNear qz189 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable def ep1241 := @Enclosure.Complex.IsNear.im_isNear qz190 Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (ep1233 (@congrArg Complex Complex qz187 qz488 Complex.log (BSN.w_shift_mk qz147 Bool.false 134395 1000 2 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz486 Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz486) (@HMul.hMul Real Real Real qz0 qz98 qz677) Bool.false 9476015310460645 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 9000 268790 4000 72329064100 16000000 rfl rfl rfl) (ep1235 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz486) qz489 Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 9000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq qz489 (@HSub.hSub Real Real Real qz401 qz99 qz487) Bool.false 865437697476003 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 268790 9000 rfl rfl) ep1237))))

noncomputable abbrev qz195 := (@ep1232 1 (BSN.w_sub_half_mk qz446 Bool.false 134395 1000 2 qz447 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7000 4000) qz485 Bool.false 7000 4000 0 1 Bool.false 268790 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 7000 4000) (Enclosure.Real.IsNear.const Bool.false 268790 4000)))

noncomputable def ep1242 := @ep1228 3359875000653670401 19455200000000000000000 ep1229 10801898595563435881 112589990684262400 3403625000857950001 19455200000000000000000 (@ep1230 66332107173224515 9007199254740992 109375000510699 48638000000000000000 (ep1231 qz195) ep1238 rfl) (@ep1239 23262099870457484637 225179981368524800 3359875000653670401 19455200000000000000000 (ep1240 qz195) ep1241 rfl) rfl

noncomputable def ep1243 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz191 qz194) (@HMul.hMul Real Real Real qz0 qz193 qz192) 6058063882332021 2251799813685248 875000000170233 194552000000000000000 50941163105974335391 180143985094819840

noncomputable def ep1244 := nat_lit 115800625360665123756371969319108608

noncomputable def ep1245 := @Enclosure.Real.IsNear.mulLit_ff qz191 qz194 7000 4000 0 1 865437697476003 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1246 := @Enclosure.Real.IsNear.mulLit_ff qz193 qz192 268790 4000 0 1 9476015310460645 2251799813685248 15625000072957 12159500000000000000

noncomputable def ep1247 := @ep1243 419984376961011203 4863800000000000000000 ep1244 51425808216560897071 180143985094819840 110464844241316757 1215950000000000000000 (@ep1245 6058063882332021 2251799813685248 875000000170233 194552000000000000000 (ep1231 qz195) ep1241 rfl) (@ep1246 50941163105974335391 180143985094819840 419984376961011203 4863800000000000000000 (ep1240 qz195) ep1238 rfl) rfl

noncomputable def ep1248 := @Enclosure.Complex.IsNear.of_eq qz187 qz488 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 (BSN.w_shift_mk qz147 Bool.false 134395 1000 2 qz148 rfl)

noncomputable abbrev qz490 := (ep1248 (@Enclosure.Complex.IsNear.mk qz630 qz676 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1 (Enclosure.Real.IsNear.const Bool.false 9000 4000) (Enclosure.Real.IsNear.const Bool.false 268790 4000)))

noncomputable abbrev qz196 := qz490

noncomputable def ep1249 := ep1226 (@ep1227 1215950000000000000000 (ep1242 rfl) (ep1247 rfl)) qz196 rfl rfl rfl rfl rfl rfl

noncomputable def ep1250 := @ep1224 110464844241316757 1215950000000000000000 (ep1249 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@Enclosure.Complex.IsNear.mul qz103 (↑qz2) Bool.false 120447 131072 1 524288 Bool.false 0 1 0 1 (@ep594 131072 1 524288 (ep596 rfl) (ep598 rfl) rfl rfl) (@ep599 1 0 1 (ep601 rfl) (ep603 rfl) rfl rfl))

noncomputable abbrev qz491 := (@HPow.hPow Complex Int Complex qz628 qz674 (@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@OfNat.ofNat Int 1 (@instOfNat 1)) (@HMul.hMul Int Int Int (@instHMul Int Int.instMul) (@OfNat.ofNat Int 2 (@instOfNat 2)) (@Nat.cast Int instNatCastInt 1))))

noncomputable abbrev qz197 := qz491

noncomputable def ep1251 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz197)) Bool.false 2850285 68719476736 3 68719476736

noncomputable def ep1252 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz197) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1253 := @ep1252 0 1 0 1 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800 Bool.false 2850285 2850285 68719476736 3 68719476736 Bool.true 5107520701 5107520701 4123168604160 26879

noncomputable def ep1254 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (@HSub.hSub Complex Complex Complex qz79 (@HMul.hMul Complex Complex Complex qz78 (2 : Complex) (@Nat.cast Complex Complex.instNatCast k)) (1 : Complex)))) (@HPow.hPow Complex Int Complex qz87 qz187 (@HSub.hSub Int Int Int qz408 qz89 (@HMul.hMul Int Int Int qz409 qz90 (@Nat.cast Int instNatCastInt k))))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1255 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106) qz197 Bool.false 2850285 68719476736 3 68719476736 Bool.true 5107520701 4123168604160 26879 20615843020800

noncomputable abbrev qz198 := (Complex.re qz491)

noncomputable abbrev qz199 := (Complex.im qz491)

noncomputable def ep1256 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz198) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz199) 2850285 68719476736 3 68719476736 0 1 0

noncomputable def ep1257 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz198 1 12 0 1 8550855 17179869184 9 17179869184 2850285

noncomputable def ep1258 := @Enclosure.Complex.IsNear.re_isNear qz197 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879 1717986918400

noncomputable abbrev qz492 := (@HPow.hPow Complex Nat Complex qz633 qz674 1)

noncomputable abbrev qz200 := (@Inv.inv Complex Complex.instInv qz492)

noncomputable def ep1259 := @Enclosure.Complex.IsNear.of_eq qz197 qz200 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879

noncomputable def ep1260 := @Enclosure.Complex.IsNear.of_parts qz200 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879

noncomputable abbrev qz201 := (Complex.re qz492)

noncomputable abbrev qz202 := qz492

noncomputable def ep1261 := @Enclosure.Real.IsNear.mulLit_ff qz201 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202)) 9000 4000 0 1 950095 4294967296 1 4294967296

noncomputable def ep1262 := @Enclosure.Complex.IsNear.re_isNear qz202 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable def ep1263 := @Enclosure.Complex.IsNear.of_eq qz202 qz187 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0

noncomputable def ep1264 := @Enclosure.Real.IsNear.recentre' (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202)) Bool.false 950095 4294967296 1 4294967296 950095 4294967296 1

noncomputable abbrev qz203 := (Complex.im qz492)

noncomputable def ep1265 := @Enclosure.Real.IsNear.of_eq (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 qz201 qz201) (@HMul.hMul Real Real Real qz0 qz203 qz203)) Bool.false 723290641 160000 0 1

noncomputable def ep1266 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 qz201 qz201) (@HMul.hMul Real Real Real qz0 qz203 qz203) 81 16 0 1 722480641 160000

noncomputable def ep1267 := @Enclosure.Real.IsNear.mulLit_ff qz201 qz201 9000 4000 0 1 9000 4000 0 1

noncomputable def ep1268 := @Enclosure.Real.IsNear.mulLit_ff qz203 qz203 268790 4000 0 1 268790 4000 0 1

noncomputable def ep1269 := @Enclosure.Complex.IsNear.im_isNear qz202 Bool.false 9000 4000 0 1 Bool.false 268790 4000 0 1

noncomputable abbrev qz204 := (ep1262 (@ep1263 1 (BSN.pow_one_c qz480) qz490))

noncomputable abbrev qz205 := (ep1269 (@ep1263 1 (BSN.pow_one_c qz480) qz490))

noncomputable def ep1270 := @ep1266 0 1 11572650256 723290641 160000 0 1 (@ep1267 81 16 0 1 qz204 qz204 rfl) (@ep1268 722480641 160000 0 1 qz205 qz205 rfl)

noncomputable def ep1271 := @Enclosure.Real.IsNear.inv_image (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202) 723290641 160000 0 1 475047 475048 2147483648 (ep1265 (Enclosure.Complex.normSq_eq_mul_add_mul qz202) (ep1270 rfl rfl)) rfl

noncomputable def ep1272 := @Enclosure.Real.IsNear.of_eq (Complex.re qz200) (@HMul.hMul Real Real Real qz0 qz201 (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202))) Bool.false 8550855 17179869184 9 17179869184 (Enclosure.Complex.inv_re_eq_mul qz202) (@ep1261 8550855 17179869184 9 17179869184 qz204 (@ep1264 4294967296 (ep1271 rfl rfl rfl rfl rfl) rfl) rfl)

noncomputable def ep1273 := @Enclosure.Real.IsNear.of_eq (Complex.im qz200) (@HMul.hMul Real Real Real qz0 (@Neg.neg Real Real.instNeg qz203) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202))) Bool.true 5107520701 343597383680 26879 1717986918400 (Enclosure.Complex.inv_im_eq_mul qz202)

noncomputable def ep1274 := @Enclosure.Real.IsNear.mulLit_tf (@Neg.neg Real Real.instNeg qz203) (@Inv.inv Real Real.instInv (@DFunLike.coe qz112 Complex (fun (x : Complex) => Real) qz113 Complex.normSq qz202)) 268790 4000 0 1 950095 4294967296 1

noncomputable def ep1275 := @ep1274 4294967296 5107520701 343597383680 26879 1717986918400 (@Enclosure.Real.IsNear.neg qz203 Bool.false 268790 4000 0 1 qz205) (@ep1264 4294967296 (ep1271 rfl rfl rfl rfl rfl) rfl) rfl

noncomputable def ep1276 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz199 0 1 0 1 5107520701 343597383680 26879 1717986918400 0

noncomputable def ep1277 := @Enclosure.Complex.IsNear.im_isNear qz197 Bool.false 8550855 17179869184 9 17179869184 Bool.true 5107520701 343597383680 26879 1717986918400

noncomputable abbrev qz206 := (@ep1259 1717986918400 (BSN.zpow_one_sub_two_mul qz480 1 1 rfl rfl) (@ep1260 1717986918400 ep1272 (ep1273 ep1275)))

noncomputable def ep1278 := @ep1256 1 2850285 2850285 68719476736 3 68719476736 (@ep1257 68719476736 3 68719476736 ep613 (ep1258 qz206) rfl) (@ep1276 1 0 1 ep633 (ep1277 qz206) rfl) rfl

noncomputable def ep1279 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz199) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz198) 5107520701 4123168604160 26879 20615843020800 0 1 0

noncomputable def ep1280 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz199 1 12 0 1 5107520701 343597383680 26879 1717986918400 5107520701

noncomputable def ep1281 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 (@Rat.cast Complex Complex.instRatCast (bernoulli qz105)) qz106)) qz198 0 1 0 1 8550855 17179869184 9 17179869184 0

noncomputable def ep1282 := @ep1279 1 5107520701 5107520701 4123168604160 26879 20615843020800 (@ep1280 4123168604160 26879 20615843020800 ep613 (ep1277 qz206) rfl) (@ep1281 1 0 1 ep633 (ep1258 qz206) rfl) rfl

noncomputable def ep1283 := @ep1253 20615843020800 (@ep1254 0 1 0 1 (BSN.stirling_sum_base qz187) qz119) (ep1255 (ep1278 rfl) (ep1282 rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1284 := @ep1221 589805394407509505729 2702159776422297600 ep1213 ep1206 (ep1250 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1251 Bool.true 5107520701 4123168604160 26879 20615843020800 (BSN.stirling_sum_succ qz187 0 1 rfl) (ep1283 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl

noncomputable def ep1285 := @Enclosure.Complex.IsNear.of_eq (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))) (BSN.logSumC qz147 2) Bool.false 9474956064151269 1125899906842624 15625000072957 6079750000000000000 Bool.false 877997255591331 281474976710656

noncomputable abbrev qz207 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz481 qz417))

noncomputable def ep1286 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 2) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz147 1) qz207) Bool.false 9474956064151269 1125899906842624 15625000072957 6079750000000000000 Bool.false 877997255591331 281474976710656 125000000024319 24319000000000000000

noncomputable def ep1287 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz147 1) qz207 Bool.false 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000 Bool.false

noncomputable def ep1288 := nat_lit 42671408599863476461920451559424

noncomputable def ep1289 := nat_lit 988537028278359106810275692544

noncomputable abbrev qz208 := (Complex.log (@HAdd.hAdd Complex Complex Complex qz272 qz481 (@Nat.cast Complex Complex.instNatCast 0)))

noncomputable def ep1290 := @Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 1) (@HAdd.hAdd Complex Complex Complex qz4 (BSN.logSumC qz147 0) qz208) Bool.false 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1291 := @Enclosure.Complex.IsNear.addLitP (BSN.logSumC qz147 0) qz208 Bool.false 0 1 0 1 Bool.false 0 1 0 1 Bool.false

noncomputable abbrev qz493 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz676))

noncomputable def ep1292 := @Enclosure.Complex.IsNear.of_eq qz208 qz493 Bool.false 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1293 := BSN.log_dyadic_bound 6713064100 137785064100 2 1 56954171667123326430000 1048576 389104 45065229610708810000 45065229610708810000 102256 144498128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6713064100) (BSN.artanhQ 137785064100) 0 1 45065229610708810000 56954171667123326430000 45065229610708810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1294 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 72249064100 16000000)) 1 2 0 1 9474768696202981 1125899906842624 15625000072957 6079750000000000000 9474768696202981 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 72249064100 16000000 9474768696202981 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72249064100) qz632)) Bool.false 317920481932471584161792 37778931862957161709568 1000000004669248 389104000000000000000 9474768696202981 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 72249064100 16000000 12 144498128200 131072000000 102256 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep1293 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1295 := BSN.arctan_dyadic_bound_f 1000 268790 1 0 1048576 389104 0 1 1 0 1 1 3901 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 1000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 1000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable abbrev qz494 := (@Nat.cast Real Real.instNatCast 268790)

noncomputable def ep1296 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz494)) 884279719003555 562949953421312 1 2000000000000000 3901 1048576 1 389104 925038422865575149568 882185385575843 562949953421312 125000000024319 48638000000000000000 qz100 (ep1295 rfl) rfl rfl

noncomputable abbrev qz209 := (@HAdd.hAdd Complex Complex Complex qz272 qz481 (@Nat.cast Complex Complex.instNatCast 0))

noncomputable abbrev qz495 := (Complex.mk (Enclosure.sfrac Bool.false 1000 4000) qz676)

noncomputable def ep1297 := @ep1291 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000 Bool.false 9474768696202981 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 882185385575843 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Complex.IsNear.of_eq (BSN.logSumC qz147 0) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false 0 1 0 1 (BSN.log_sum_c_base qz147) qz119) (ep1292 (@congrArg Complex Complex qz209 qz495 Complex.log (BSN.w_shift_mk qz147 Bool.false 134395 1000 0 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz493 Bool.false 9474768696202981 2251799813685248 15625000072957 12159500000000000000 Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz493) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 72249064100 16000000))) Bool.false 9474768696202981 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 1000 268790 4000 72249064100 16000000 rfl rfl rfl) (ep1294 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz493) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz494 qz423)) Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 1000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz494 qz423)) (@HSub.hSub Real Real Real qz401 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz423 qz494))) Bool.false 882185385575843 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 268790 1000 rfl rfl) ep1296)))) rfl rfl

noncomputable abbrev qz496 := (Complex.log (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz676))

noncomputable def ep1298 := @Enclosure.Complex.IsNear.of_eq qz207 qz496 Bool.false 9475143432099557 2251799813685248 15625000072957 12159500000000000000 Bool.false 873809125606819 562949953421312 125000000024319 48638000000000000000

noncomputable def ep1299 := BSN.log_dyadic_bound 6737064100 137809064100 2 1 56974014444353726430000 1048576 389104 45388032687508810000 45388032687508810000 102605 144546128200 131072000000 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.artanhP 6737064100) (BSN.artanhQ 137809064100) 0 1 45388032687508810000 56974014444353726430000 45388032687508810000 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1300 := @Enclosure.Real.IsNear.mulLit_ff qz98 (Real.log (Enclosure.sfrac Bool.false 72273064100 16000000)) 1 2 0 1 9475143432099557 1125899906842624 15625000072957 6079750000000000000 9475143432099557 2251799813685248 15625000072957 12159500000000000000 qz412 (BSN.isNear_log_sfrac 72273064100 16000000 9475143432099557 1125899906842624 15625000072957 6079750000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 72273064100) qz632)) Bool.false 317933055982631202586624 37778931862957161709568 1000000004669248 389104000000000000000 9475143432099557 1125899906842624 15625000072957 6079750000000000000 (BSN.log_rat_reduce_isNear 72273064100 16000000 12 144546128200 131072000000 102605 1048576 24973259072661432 36028797018963968 389104 1000000000000000 rfl rfl rfl rfl (ep1299 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1301 := BSN.arctan_dyadic_bound_f 5000 268790 1 0 1048576 389104 0 1 1 0 1 1 19503 rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_le (BSN.arctanEvenP 5000) (BSN.arctanEvenQ 268790) 0 0 rfl) (@BSN.binarySplit_of_le (BSN.arctanOddP 5000) (BSN.arctanOddQ 268790) 0 0 rfl) rfl rfl rfl

noncomputable def ep1302 := @Enclosure.Real.IsNear.subLit_ff_p qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz494)) 884279719003555 562949953421312 1 2000000000000000 19503 1048576 1 389104 916255277692295839744 873809125606819 562949953421312 125000000024319 48638000000000000000 qz100 (ep1301 rfl) rfl rfl

noncomputable abbrev qz210 := (@HAdd.hAdd Complex Complex Complex qz272 qz481 qz417)

noncomputable abbrev qz497 := (Complex.mk (Enclosure.sfrac Bool.false 5000 4000) qz676)

noncomputable def ep1303 := @ep1287 9475143432099557 2251799813685248 15625000072957 12159500000000000000 Bool.false 873809125606819 562949953421312 125000000024319 48638000000000000000 Bool.false ep1288 9474956064151269 1125899906842624 15625000072957 6079750000000000000 Bool.false ep1289 877997255591331 281474976710656 125000000024319 24319000000000000000 (ep1290 (BSN.log_sum_c_succ qz147 0 1 rfl) (ep1297 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (ep1298 (@congrArg Complex Complex qz210 qz497 Complex.log (BSN.w_shift_mk qz147 Bool.false 134395 1000 1 qz148 rfl)) (@Enclosure.Complex.IsNear.of_parts qz496 Bool.false 9475143432099557 2251799813685248 15625000072957 12159500000000000000 Bool.false 873809125606819 562949953421312 125000000024319 48638000000000000000 (@Enclosure.Real.IsNear.of_eq (Complex.re qz496) (@HMul.hMul Real Real Real qz0 qz98 (Real.log (Enclosure.sfrac Bool.false 72273064100 16000000))) Bool.false 9475143432099557 2251799813685248 15625000072957 12159500000000000000 (Enclosure.clog_re_eq 5000 268790 4000 72273064100 16000000 rfl rfl rfl) (ep1300 rfl)) (@Enclosure.Real.IsNear.of_eq (Complex.im qz496) (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz494 qz427)) Bool.false 873809125606819 562949953421312 125000000024319 48638000000000000000 (Enclosure.clog_im_eq 5000 268790 4000 rfl rfl) (@Enclosure.Real.IsNear.of_eq (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz494 qz427)) (@HSub.hSub Real Real Real qz401 qz99 (Real.arctan (@HDiv.hDiv Real Real Real qz1 qz427 qz494))) Bool.false 873809125606819 562949953421312 125000000024319 48638000000000000000 (BSN.arctan_recip 268790 5000 rfl rfl) ep1302)))) rfl rfl

noncomputable def ep1304 := @ep1214 ep1206 Bool.false 9474956064151269 1125899906842624 15625000072957 6079750000000000000 Bool.false 877997255591331 281474976710656 125000000024319 24319000000000000000 Bool.true ep1215 11899253825930946781 112589990684262400 228768723733300484752561 ep1211 Bool.false ep1216 581376620753832728129 2702159776422297600 ep1208 ep1206 (@ep1217 112589990684262400 225491923718000292906161 ep1211 Bool.false 589805394407509505729 2702159776422297600 ep1213 ep1206 (BSN.logGammaStirling_unfold 1 qz187) (ep1284 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) (@ep1285 125000000024319 24319000000000000000 (BSN.log_sum_c_eq qz147 2) (ep1286 (BSN.log_sum_c_succ qz147 1 2 rfl) (ep1303 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)))

noncomputable abbrev qz211 := (@HDiv.hDiv Real Real Real qz270 qz446 (2 : Real))

noncomputable def ep1305 := @Enclosure.Real.IsNear.mulLit_ff qz211 (Real.log Real.pi) 134395 2000 0 1 75021 65536 1 262144 2016489459 26214400 26879 104857600 (@Enclosure.Real.IsNear.of_eq qz211 (Enclosure.sfrac Bool.false 134395 2000) Bool.false 134395 2000 0 1 (BSN.t_half_eq qz147 Bool.false 134395 1000 qz148) (Enclosure.Real.IsNear.const Bool.false 134395 2000)) EMRow45.d5 rfl

noncomputable def ep1306 := @ep1209 26879 104857600 ep1210 373518470054623139393 2702159776422297600 ep1205 ep1206 (@ep1212 ep1208 ep1206 (ep1304 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) ep1305 rfl rfl

noncomputable def ep1307 := nat_lit 8333861765039413646945467217050976014855209411807293884791919175550245444788480

noncomputable def ep1308 := nat_lit 16724196880350348788331395272153705671371194477876794629532630551193871196416

noncomputable def ep1309 := nat_lit 21799703542058849463009401404692878801152852239864445364102449772215376563937536

noncomputable def ep1310 := BSN.sin_dyadic_bound_f 3372237542 2147483648 3 2 1048576 389484 ep1307 ep78 ep1308 ep1309 ep80 ep1308 1048575 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 3372237542) qz20 0 2 ep1307 ep78 ep1308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 3372237542) qz21 0 2 ep1309 ep80 ep1308 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1311 := @ep1204 1048576 Bool.false 1048575 1048576 1 194552 (@ep1207 72472121 524288 371 1048576 ep1306 rfl) (Enclosure.sfrac_false_div 72472121 524288) (BSN.cos_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118650060472388820140032) qz19) 226375608064910080 72057594037927936 Bool.false 1048575 1048576 21 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 72472121 524288 226375608064910080 72057594037927936 21 118650060472388820140032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 1048575 1048576 118650060472388820140032 75557863725914323419136 3372237542 2147483648 389484 389104 (ep1310 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1312 := nat_lit 21607322612096329528115200

noncomputable def ep1313 := nat_lit 3384101880620914539994882037

noncomputable def ep1314 := nat_lit 525468478603570637794233548800

noncomputable abbrev qz498 := (@HPow.hPow Complex Complex Complex qz535 qz634 qz643)

noncomputable abbrev qz212 := qz498

noncomputable abbrev qz213 := (@HAdd.hAdd Complex Complex Complex qz272 (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz444 (1 : Complex))) qz405)

noncomputable def ep1315 := @Enclosure.Complex.IsNear.of_eq (zetaApproximant qz144 1 34) (@HAdd.hAdd Complex Complex Complex qz4 (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz145) (@HMul.hMul Complex Complex Complex qz78 qz212 (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) Bool.false ep1199 ep1200 ep1201

noncomputable def ep1316 := @Enclosure.Complex.IsNear.addLitP (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz145) (@HMul.hMul Complex Complex Complex qz78 qz212 (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) Bool.false 27275594137 34359738368 85205478432973 13369511637942272

noncomputable def ep1317 := nat_lit 2277657331603356263831137

noncomputable def ep1318 := nat_lit 36345195316536344661019637

noncomputable def ep1319 := nat_lit 268213912074048698513442576508387328

noncomputable def ep1320 := nat_lit 66318298113461880793240074281025536

noncomputable def ep1321 := @ep1316 Bool.false 9873867035 137438953472 10647135315357 1671188954742784 Bool.true 770156298046127979314679 ep1200 ep1317 ep1202 Bool.true 1069780645344334767861537 ep1312 ep1318 ep1314 Bool.false ep1319 ep1199 ep1200 ep1201 ep1202 Bool.false ep1320 482529126118329301194463 ep1312

noncomputable def ep1322 := @Enclosure.Complex.IsNear.of_eq (∑ n ∈ @Finset.Ico Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 34, @HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast n) qz145) (BSN.headSumC qz144 34) Bool.false 27275594137 34359738368 85205478432973 13369511637942272 Bool.false 9873867035 137438953472 10647135315357

noncomputable abbrev qz678 := (@HPow.hPow Complex Complex Complex qz6 (@Nat.cast Complex Complex.instNatCast 33) qz145)

noncomputable def ep1323 := @Enclosure.Complex.IsNear.of_eq (BSN.headSumC qz144 34) (@HAdd.hAdd Complex Complex Complex qz4 qz174 qz678) Bool.false 27275594137 34359738368 85205478432973 13369511637942272 Bool.false 9873867035 137438953472 10647135315357 1671188954742784

noncomputable def ep1324 := @Enclosure.Complex.IsNear.addLitP qz174 qz678 Bool.false 826398132489 1099511627776 167162539932163 26739023275884544 Bool.true 26673510891 274877906944 83543596928961 13369511637942272 Bool.false

noncomputable abbrev qz214 := (@HMul.hMul Real Real Real qz267 qz446 qz636)

noncomputable def ep1325 := @Enclosure.Complex.IsNear.of_eq qz678 (Complex.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214)))) Bool.false 46420879895 1099511627776 3248416933783 26739023275884544 Bool.false 46421244961 274877906944 1633485593895 13369511637942272 (BSN.cpow_neg_s_mk qz147 134395 1000 33 qz148 rfl)

noncomputable def ep1326 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz636 134395 1000 0 1 15746868335186131 4503599627370496 25000000024319 4863800000000000000 423260073981468015149 900719925474099200 671975000653670401 972760000000000000000 qz149 (BSN.isNear_log_sfrac 33 1 15746868335186131 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' (Real.log qz637) Bool.false 66047152845744529997824 18889465931478580854784 1000000000972760 194552000000000000000 15746868335186131 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 33 1 5 66 64 16133 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep683 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1327 := nat_lit 76599265946382501927957292357186576

noncomputable def ep1328 := BSN.sin_dyadic_bound_f 526085282 2147483648 2 1 1048576 389484 ep1327 ep61 ep1327 ep1327 ep62 ep1327 254315 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 526085282) qz20 0 1 ep1327 ep61 ep1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 526085282) qz21 0 1 ep1327 ep62 ep1327 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz499 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 492739577) qz25)

noncomputable def ep1329 := @Enclosure.Real.IsNear.cos_image qz214 qz499 Bool.false 492739577 1048576 725 1048576 Bool.false 254315 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 423260073981468015149 900719925474099200 671975000653670401 972760000000000000000 492739577 1048576 725 1048576 (ep1326 rfl) rfl) (Enclosure.sfrac_false_div 492739577 1048576) (BSN.cos_reduce3 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37019960693591820468224) qz26) 226375608064910080 72057594037927936 Bool.false 254315 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 492739577 1048576 226375608064910080 72057594037927936 74 37019960693591820468224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 254315 1048576 37019960693591820468224 151115727451828646838272 526085282 2147483648 389484 389104 (ep1328 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1330 := BSN.cos_dyadic_bound_f 526085282 2147483648 2 1 1048576 389484 ep1327 ep57 ep1327 ep1327 ep58 ep1327 1017268 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.cosEvenP 526085282) qz15 0 1 ep1327 ep57 ep1327 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.cosOddP 526085282) qz16 0 1 ep1327 ep58 ep1327 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1331 := @Enclosure.Real.IsNear.sin_image qz214 qz499 Bool.false 492739577 1048576 725 1048576 Bool.true 1017268 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz214 Bool.false 423260073981468015149 900719925474099200 671975000653670401 972760000000000000000 492739577 1048576 725 1048576 (ep1326 rfl) rfl) (Enclosure.sfrac_false_div 492739577 1048576) (BSN.sin_reduce3 qz499 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 37019960693591820468224) qz26) 226375608064910080 72057594037927936 Bool.false 1017268 1048576 74 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 492739577 1048576 226375608064910080 72057594037927936 74 37019960693591820468224 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1017268 1048576 37019960693591820468224 151115727451828646838272 526085282 2147483648 389484 389104 (ep1330 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1332 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz432 (Real.cos qz214)) (@HMul.hMul Real Real Real qz0 qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214))) Bool.false 46420879895 1099511627776 3248416933783 26739023275884544 Bool.false 46421244961 274877906944 1633485593895 13369511637942272 (@Enclosure.Real.IsNear.mulLit_ff qz432 (Real.cos qz214) 182533 1048576 1 1048576 254315 1048576 17762347 25500319744 46420879895 1099511627776 3248416933783 26739023275884544 qz436 (@Enclosure.Real.IsNear.recentre' (Real.cos qz214) Bool.false 254315 1048576 142098776 204002557952 254315 1048576 17762347 25500319744 (ep1329 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ff qz432 (@Neg.neg Real Real.instNeg (Real.sin qz214)) 182533 1048576 1 1048576 254317 262144 17762347 25500319744 46421244961 274877906944 1633485593895 13369511637942272 qz436 (@Enclosure.Real.IsNear.neg (Real.sin qz214) Bool.true 254317 262144 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' (Real.sin qz214) Bool.true 1017268 1048576 142098776 204002557952 254317 262144 17762347 25500319744 (ep1331 rfl rfl) rfl)) rfl)

noncomputable def ep1333 := @ep1324 46420879895 1099511627776 3248416933783 26739023275884544 Bool.false 46421244961 274877906944 1633485593895 13369511637942272 Bool.false 959674653060172542377984 27275594137 34359738368 85205478432973 13369511637942272 Bool.false 5428215808048318382080 9873867035 137438953472 10647135315357 1671188954742784 EMRow45.d16 (ep1325 ep1332) rfl rfl

noncomputable def ep1334 := @Enclosure.Complex.IsNear.mul qz212 (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.true 770156298046127979314679 ep1200 ep1317 ep1202 Bool.true

noncomputable abbrev qz215 := (Complex.re qz498)

noncomputable abbrev qz216 := (Complex.im qz498)

noncomputable def ep1335 := @Enclosure.Real.IsNear.subLit_tt_n (@HMul.hMul Real Real Real qz0 qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 979338032952706827231 12710189771821370310656 316288245317642168273027

noncomputable def ep1336 := nat_lit 5254684786035706377942335488

noncomputable def ep1337 := nat_lit 131367119650892659448558387200

noncomputable def ep1338 := nat_lit 9788832702129706646622155680136140432210919424

noncomputable def ep1339 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 169341552549 1099511627776 3217103601249 26739023275884544 294943792169

noncomputable abbrev qz217 := (@HMul.hMul Real Real Real qz267 qz446 qz638)

noncomputable abbrev qz218 := (Real.sin (@HMul.hMul Real Real Real qz267 qz446 qz638))

noncomputable abbrev qz679 := (@Neg.neg Real Real.instNeg qz218)

noncomputable def ep1340 := @Enclosure.Complex.IsNear.of_eq qz212 (Complex.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz437 qz679)) Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (BSN.cpow_neg_s_mk qz147 134395 1000 34 qz148 rfl)

noncomputable def ep1341 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz135 134395 1000 0 1 15881309401485523 4503599627370496 25000000024319 4863800000000000000 426873715402529372717 900719925474099200 671975000653670401 972760000000000000000 qz149 (BSN.isNear_log_sfrac 34 1 15881309401485523 4503599627370496 25000000024319 4863800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false 66611039547888335060992 18889465931478580854784 1000000000972760 194552000000000000000 15881309401485523 4503599627370496 25000000024319 4863800000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 31784 524288 24973259072661432 36028797018963968 194552 1000000000000000 rfl rfl rfl rfl (ep706 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1342 := nat_lit 2117680155047012354104671279970965088577712406772779689992944890226315643224320

noncomputable def ep1343 := nat_lit 1083113256466201429842567568483147864399771236245199578368514846847238308096

noncomputable def ep1344 := nat_lit 5544551556041229934625822528622602516399266197641454579235592355126407346422016

noncomputable def ep1345 := BSN.sin_dyadic_bound_f 2395158366 2147483648 3 2 1048576 389484 ep1342 ep78 ep1343 ep1344 ep80 ep1343 941681 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.sinEvenP 2395158366) qz20 0 2 ep1342 ep78 ep1343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.sinOddP 2395158366) qz21 0 2 ep1344 ep80 ep1343 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz500 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 496946409) qz25)

noncomputable def ep1346 := @Enclosure.Real.IsNear.cos_image qz217 qz500 Bool.false 496946409 1048576 725 1048576 Bool.true 941681 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 426873715402529372717 900719925474099200 671975000653670401 972760000000000000000 496946409 1048576 725 1048576 (ep1341 rfl) rfl) (Enclosure.sfrac_false_div 496946409 1048576) (BSN.cos_reduce1 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168544286372578426093568) qz26) 226375608064910080 72057594037927936 Bool.false 941681 1048576 75 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 496946409 1048576 226375608064910080 72057594037927936 75 168544286372578426093568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 941681 1048576 168544286372578426093568 151115727451828646838272 2395158366 2147483648 389484 389104 (ep1345 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1347 := nat_lit 1176970358695658508471414074458750892705129013200986583142022056724329685483776

noncomputable def ep1348 := nat_lit 3528744849574043122554557088239286382386587497130469350269329140479294579835136

noncomputable def ep1349 := BSN.cos_dyadic_bound_f 2395158366 2147483648 3 2 1048576 389484 ep1347 ep71 ep1343 ep1348 ep74 ep1343 461246 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 2395158366) qz15 0 2 ep1347 ep71 ep1343 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 2395158366) qz16 0 2 ep1348 ep74 ep1343 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1350 := @Enclosure.Real.IsNear.sin_image qz217 qz500 Bool.false 496946409 1048576 725 1048576 Bool.false 461246 1048576 1 194552 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 426873715402529372717 900719925474099200 671975000653670401 972760000000000000000 496946409 1048576 725 1048576 (ep1341 rfl) rfl) (Enclosure.sfrac_false_div 496946409 1048576) (BSN.sin_reduce1 qz500 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 168544286372578426093568) qz26) 226375608064910080 72057594037927936 Bool.false 461246 1048576 75 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q1 496946409 1048576 226375608064910080 72057594037927936 75 168544286372578426093568 151115727451828646838272 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 461246 1048576 168544286372578426093568 151115727451828646838272 2395158366 2147483648 389484 389104 (ep1349 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1351 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz437 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz437 qz679) Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (@Enclosure.Real.IsNear.mulLit_ft qz437 (Real.cos qz217) 179829 1048576 1 1048576 941681 1048576 17762347 25500319744 169341552549 1099511627776 3217103601249 26739023275884544 qz442 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 941681 1048576 142098776 204002557952 941681 1048576 17762347 25500319744 (ep1346 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz437 qz679 179829 1048576 1 1048576 230623 524288 17762347 25500319744 41472703467 549755813888 801354975621 6684755818971136 qz442 (@Enclosure.Real.IsNear.neg qz218 Bool.false 230623 524288 17762347 25500319744 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 461246 1048576 142098776 204002557952 230623 524288 17762347 25500319744 (ep1350 rfl rfl) rfl)) rfl)

noncomputable def ep1352 := @ep1339 589552363056 0 1 979338032952706827231 12710189771821370310656 316288245317642168273027 ep1336 (@Enclosure.Complex.IsNear.re_isNear qz212 Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (ep1340 ep1351))

noncomputable def ep1353 := @Enclosure.Complex.IsNear.re_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 294943792169 589552363056 0 1 Bool.false

noncomputable def ep1354 := @Enclosure.Complex.IsNear.addLitP qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) Bool.false 721130641 1444981282 0 1 Bool.true 182777200

noncomputable def ep1355 := @ep1354 722490641 0 1 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1 Bool.false 589887584338 294943792169 589552363056 0 1 Bool.false 4505206419439 4505206419439 58955236305600 0 1

noncomputable abbrev qz219 := (@HDiv.hDiv Complex Complex Complex qz406 qz430 (@HSub.hSub Complex Complex Complex qz398 qz444 (1 : Complex)))

noncomputable def ep1356 := @Enclosure.Complex.IsNear.addLitP qz219 qz103 Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1

noncomputable def ep1357 := @Enclosure.Complex.IsNear.of_eq qz219 (Complex.mk (Enclosure.sfrac Bool.true 68000000 72249064100) (Enclosure.sfrac Bool.true 18277720000 72249064100)) Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1

noncomputable def ep1358 := @ep1356 Bool.false 1 2 0 1 Bool.false 0 1 0 1 Bool.false 72113064100 721130641 1444981282 0 1 Bool.true 18277720000 182777200 722490641 0 1 (ep1357 (BSN.N_div_s_sub_one_mk qz147 134395 1000 34 qz148 rfl rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 68000000 72249064100) (Enclosure.sfrac Bool.true 18277720000 72249064100) Bool.true 68000000 72249064100 0 1 Bool.true 18277720000 72249064100 0 1 (Enclosure.Real.IsNear.const Bool.true 68000000 72249064100) (Enclosure.Real.IsNear.const Bool.true 18277720000 72249064100))) qz104 rfl

noncomputable def ep1359 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HAdd.hAdd Complex Complex Complex qz4 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138)) Bool.false 1 816 0 1

noncomputable def ep1360 := @Enclosure.Complex.IsNear.addLitP (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1361 := @ep1360 0 1 0 1 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1 Bool.false 1 1 816 0 1 Bool.false 26879 26879 81600 0

noncomputable def ep1362 := @Enclosure.Complex.IsNear.of_eq (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 0, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (Complex.mk qz10 qz10) Bool.false 0 1 0 1 Bool.false

noncomputable def ep1363 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz138 Bool.false 1 816 0 1 Bool.false 26879 81600 0 1

noncomputable def ep1364 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) 1 816 0 1 0 1 0

noncomputable def ep1365 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 1 24 0 1 1 34 0 1 1

noncomputable def ep1366 := @Enclosure.Real.IsNear.subLit_ff_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) 1 24 0 1 0 1 0 1 1

noncomputable def ep1367 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 1 2 0 1 1 24 0

noncomputable def ep1368 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz144 Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 (BSN.ascPochhammer_one_eval qz144)

noncomputable def ep1369 := ep1368 (@Enclosure.Complex.IsNear.of_eq qz144 (Complex.mk qz98 qz147) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_crit_mk qz147 Bool.false 134395 1000 qz148) (@Enclosure.Complex.IsNear.mk qz98 qz147 Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 qz412 qz149))

noncomputable def ep1370 := @ep1367 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1371 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 134395 1000 0 1 0 1 0

noncomputable def ep1372 := @ep1371 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1373 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) 26879 2400 0 1 0 1 0 1 26879

noncomputable def ep1374 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 1 12 0 1 134395 1000 0 1 26879 2400 0

noncomputable def ep1375 := @ep1374 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1376 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) 0 1 0 1 1 2 0 1 0 1 0

noncomputable def ep1377 := @ep1376 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) Bool.false 1 12 0 1 Bool.false 0 1 0 1 ep730) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1378 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 (@ep1366 1 24 0 1 (ep1370 rfl) (ep1372 rfl) rfl rfl) (@ep1373 26879 2400 0 1 (ep1375 rfl) (ep1377 rfl) rfl rfl)

noncomputable def ep1379 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 ep1378

noncomputable def ep1380 := @ep1365 816 0 1 ep1379 qz141

noncomputable def ep1381 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 26879 2400 0 1 0 1 0 1 0

noncomputable def ep1382 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) Bool.false 1 24 0 1 Bool.false 26879 2400 0 1 ep1378

noncomputable def ep1383 := @ep1381 1 0 1 ep1382 qz142

noncomputable def ep1384 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139) 0 1 0 1 26879 81600 0

noncomputable def ep1385 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz140 1 24 0 1 0 1 0 1 0

noncomputable def ep1386 := @ep1385 1 0 1 ep1379 qz142

noncomputable def ep1387 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz105)) ↑qz137) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)))) qz139 26879 2400 0 1 1 34 0 1 26879

noncomputable def ep1388 := @ep1387 81600 0 1 ep1382 qz141

noncomputable def ep1389 := @ep1361 1 (@ep1362 0 1 0 1 (BSN.bern_sum_base qz144 34) qz119) (ep1363 (@ep1364 1 1 1 816 0 1 (ep1380 rfl) (ep1383 rfl) rfl rfl) (@ep1384 1 26879 26879 81600 0 1 (ep1386 rfl) (ep1388 rfl) rfl rfl)) rfl rfl rfl rfl rfl

noncomputable def ep1390 := ep1355 (ep1358 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl) (@ep1359 Bool.false 26879 81600 0 1 (BSN.bern_sum_succ qz144 34 0 1 1 rfl rfl) (ep1389 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)) rfl rfl rfl rfl

noncomputable def ep1391 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 41472703467 549755813888 801354975621 6684755818971136 4505206419439

noncomputable def ep1392 := @ep1391 58955236305600 0 1 62281029963672823831671 ep1200 1203423193472370848498873 ep1337 (@Enclosure.Complex.IsNear.im_isNear qz212 Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (ep1340 ep1351))

noncomputable def ep1393 := @Enclosure.Complex.IsNear.im_isNear (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))) Bool.false 294943792169 589552363056 0 1 Bool.false

noncomputable def ep1394 := nat_lit 1271018977182137031065600

noncomputable def ep1395 := nat_lit 4831238598782439899426437

noncomputable def ep1396 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) (@HMul.hMul Real Real Real qz0 qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1))))))) 14959189208265128501961 ep1394 ep1395

noncomputable def ep1397 := nat_lit 1313671196508926594485583872

noncomputable def ep1398 := nat_lit 6798557508274014300136809765053059645241819136

noncomputable def ep1399 := @Enclosure.Real.IsNear.mulLit_tf qz215 (Complex.im (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 169341552549 1099511627776 3217103601249 26739023275884544 4505206419439

noncomputable def ep1400 := @ep1399 58955236305600 0 1 14959189208265128501961 ep1394 ep1395 ep1314 (@Enclosure.Complex.IsNear.re_isNear qz212 Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (ep1340 ep1351))

noncomputable def ep1401 := @Enclosure.Real.IsNear.mulLit_tf qz216 (Complex.re (@HAdd.hAdd Complex Complex Complex qz4 qz213 (∑ k ∈ @Finset.Icc Nat Nat.instPreorder Nat.instLocallyFiniteOrder 1 1, @HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli (@HMul.hMul Nat Nat Nat qz86 2 k))) ↑(@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat qz86 2 k)))) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))) (@Inv.inv Complex Complex.instInv (@HPow.hPow Complex Nat Complex qz128 qz129 (@HSub.hSub Nat Nat Nat qz127 (@HMul.hMul Nat Nat Nat qz86 2 k) 1)))))) 41472703467 549755813888 801354975621 6684755818971136 294943792169

noncomputable def ep1402 := @ep1401 589552363056 0 1 4077372144019137916641 108036613060481647640576 78784891794384761903983 ep1397 (@Enclosure.Complex.IsNear.im_isNear qz212 Bool.true 169341552549 1099511627776 3217103601249 26739023275884544 Bool.true 41472703467 549755813888 801354975621 6684755818971136 (ep1340 ep1351))

noncomputable abbrev qz680 := (ep1390 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl)

noncomputable def ep1403 := @ep1334 1069780645344334767861537 ep1312 ep1318 ep1314 (@ep1335 ep1336 62281029963672823831671 ep1200 1203423193472370848498873 ep1337 ep1338 770156298046127979314679 ep1200 ep1317 ep1202 (ep1352 (@ep1353 4505206419439 58955236305600 0 1 qz680) rfl) (ep1392 (@ep1393 4505206419439 58955236305600 0 1 qz680) rfl) rfl rfl) (@ep1396 ep1314 4077372144019137916641 108036613060481647640576 78784891794384761903983 ep1397 ep1398 1069780645344334767861537 ep1312 ep1318 ep1314 (ep1400 (@ep1393 4505206419439 58955236305600 0 1 qz680) rfl) (ep1402 (@ep1353 4505206419439 58955236305600 0 1 qz680) rfl) rfl rfl)

noncomputable def ep1404 := @ep1321 ep1313 ep1314 (@ep1322 1671188954742784 (BSN.head_sum_c_eq qz144 34) (ep1323 (BSN.head_sum_c_succ qz144 33 34 rfl rfl) (ep1333 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))) ep1403 rfl rfl rfl

noncomputable def ep1405 := @Enclosure.Complex.IsNear.re_isNear (zetaApproximant qz144 1 34) Bool.false ep1199 ep1200 ep1201 ep1202 Bool.false 482529126118329301194463 ep1312 ep1313 ep1314 (@ep1315 ep1202 Bool.false 482529126118329301194463 ep1312 ep1313 ep1314 (BSN.zetaApproximant_eq_folded' qz144 1 34 rfl) (ep1404 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

noncomputable def ep1406 := @Enclosure.Real.IsNear.mulLit_tf (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) (Complex.im (zetaApproximant qz144 1 34)) 249 524288 9153421

noncomputable def ep1407 := @Enclosure.Real.IsNear.recentre' (Real.sin (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185)) Bool.true 498 1048576 73227368

noncomputable def ep1408 := @Enclosure.Real.IsNear.sin_image (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185) qz482 Bool.false 72472121 524288 371

noncomputable def ep1409 := nat_lit 4637356179190941069986740185149277210773503537438664066941969599995111412080896

noncomputable def ep1410 := nat_lit 13878620143812122512383557764903524220977768223360238611566843538882946493849856

noncomputable def ep1411 := BSN.cos_dyadic_bound_f 3372237542 2147483648 3 2 1048576 389484 ep1409 ep71 ep1308 ep1410 ep74 ep1308 498 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 3372237542) qz15 0 2 ep1409 ep71 ep1308 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 3372237542) qz16 0 2 ep1410 ep74 ep1308 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1412 := @ep1408 1048576 Bool.true 498 1048576 1 194552 (@ep1207 72472121 524288 371 1048576 ep1306 rfl) (Enclosure.sfrac_false_div 72472121 524288) (BSN.sin_reduce3 qz482 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 118650060472388820140032) qz19) 226375608064910080 72057594037927936 Bool.false 498 1048576 21 1000000000000000 389104 194552 (BSN.sin_reduce_arg_pos_rat_q3 72472121 524288 226375608064910080 72057594037927936 21 118650060472388820140032 75557863725914323419136 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 498 1048576 118650060472388820140032 75557863725914323419136 3372237542 2147483648 389484 389104 (ep1411 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1413 := @Enclosure.Complex.IsNear.im_isNear (zetaApproximant qz144 1 34) Bool.false ep1199 ep1200 ep1201 ep1202 Bool.false 482529126118329301194463 ep1312 ep1313 ep1314 (@ep1315 ep1202 Bool.false 482529126118329301194463 ep1312 ep1313 ep1314 (BSN.zetaApproximant_eq_folded' qz144 1 34 rfl) (ep1404 rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl))

theorem EMRow45.d17 : Enclosure.Real.IsNear (hardyZApproximantEM 1 34 qz147) Bool.false ep1182 ep1183 ep1184 ep1185 := @Enclosure.Real.IsNear.of_eq (hardyZApproximantEM 1 34 qz147) ep1186 Bool.false ep1182 ep1183 ep1184 ep1185 (@Eq.refl Real ep1186) (@ep1187 Bool.false ep1182 ep1183 ep1184 ep1185 (BSN.re_exp_mul (@HSub.hSub Real Real Real qz401 (Complex.im (@HSub.hSub Complex Complex Complex qz79 qz183 (∑ j ∈ Finset.range 2, Complex.log (@HAdd.hAdd Complex Complex Complex qz4 qz184 (@Nat.cast Complex Complex.instNatCast j))))) qz185) (zetaApproximant qz144 1 34)) (@ep1189 ep1190 ep1191 ep1192 ep1193 ep1194 ep1195 ep1196 ep1197 ep1182 ep1183 ep1184 ep1185 (@ep1198 25500319744 ep1199 ep1200 ep1201 ep1202 ep1188 ep1190 ep1191 ep1192 (@ep1203 204002557952 1048575 1048576 9153421 25500319744 (ep1311 rfl rfl) rfl) ep1405 rfl) (@ep1406 25500319744 482529126118329301194463 ep1312 ep1313 ep1314 ep1193 ep1194 ep1195 ep1196 (@ep1407 204002557952 249 524288 9153421 25500319744 (ep1412 rfl rfl) rfl) ep1413 rfl) rfl rfl))

theorem EMRow45.d18 : @Eq Nat (Nat.mul (BSN.factNat (Nat.succ (Nat.mul 2 1))) (Nat.pow 4 (Nat.mul 2 1))) 96 := @Eq.refl Nat 96

theorem EMRow45.d19 : @Eq Nat (Nat.mul (Nat.mul 2 1) (Nat.pow (Nat.succ (Nat.mul 4 2)) (Nat.mul 2 1))) 162 := @Eq.refl Nat 162

theorem EMRow45.d20 : @Eq Nat (BSN.factNat (Nat.mul 2 2)) 24 := @Eq.refl Nat 24

theorem EMRow45.d21 : @Eq Nat (Nat.pow 34 (Nat.succ (Nat.mul 2 3))) 52523350144 := @Eq.refl Nat 52523350144

noncomputable abbrev qz681 := (@HAdd.hAdd Complex Complex Complex qz687 qz686 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz501 := qz681

noncomputable abbrev qz220 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz501) (@HAdd.hAdd Real Real Real qz421 (Complex.re qz271) qz288))

noncomputable abbrev qz221 := (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)

noncomputable abbrev qz222 := (@Nat.cast Real Real.instNatCast (Nat.factorial (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat) 2 2)))

noncomputable abbrev qz502 := (@HPow.hPow Complex Complex Complex qz535 qz634 (@HSub.hSub Complex Complex Complex qz623 qz536 qz542))

noncomputable abbrev qz223 := qz502

noncomputable def ep1414 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) 6412223815 206158430208 59948651 618475290624 268048086322497237 504403158265495552 117066384535

noncomputable def ep1415 := nat_lit 58494718640295730685648306176

noncomputable def ep1416 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34)) 26561 1769472 1 1769472 2172735 1048576 6689 1048576 6412223815 206158430208

noncomputable abbrev qz224 := (@HMul.hMul Real Real Real qz267 (2 : Real) Real.pi)

noncomputable abbrev qz682 := (@instHPow Real Nat (@NPow.toPow Real (@Monoid.toNPow Real Real.instMonoid)))

noncomputable abbrev qz503 := (@Inv.inv Real Real.instInv (@HPow.hPow Real Nat Real qz682 qz224 2))

noncomputable def ep1417 := @Enclosure.Real.IsNear.mulLit_ff (Enclosure.sfrac Bool.false 96 162) qz503 96 162 0 1 26561 1048576 1 1048576 26561 1769472 1 1769472

noncomputable def ep1418 := nat_lit 781950621441006189802102638025

noncomputable def ep1419 := nat_lit 19807040628566084398385987584

noncomputable def ep1420 := nat_lit 26986075409044041160201671

noncomputable def ep1421 := nat_lit 1073741824000000000000000000000000000000

noncomputable abbrev qz504 := (@HPow.hPow Real Nat Real qz682 qz224 1)

noncomputable def ep1422 := @Enclosure.Real.IsNear.mulLit_ff qz504 qz224 884279719003555 140737488355328 1 500000000000000 884279719003555 140737488355328 1 500000000000000 ep1418 ep1419 ep1420 ep1421

noncomputable def ep1423 := ep1422 (@Enclosure.Real.IsNear.of_eq qz504 qz224 Bool.false 884279719003555 140737488355328 1 500000000000000 (BSN.pow_one_r qz224) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269)) (@Enclosure.Real.IsNear.of_eq qz224 qz268 Bool.false 884279719003555 140737488355328 1 500000000000000 BSN.two_pi_eq qz269) rfl

noncomputable abbrev qz505 := (@HPow.hPow Real Nat Real qz682 qz224 2)

noncomputable def ep1424 := @Enclosure.Real.IsNear.inv_image qz505 ep1418 ep1419 ep1420 ep1421 13280 13281 524288 (@Enclosure.Real.IsNear.of_eq qz505 (@HMul.hMul Real Real Real qz0 qz504 qz224) Bool.false ep1418 ep1419 ep1420 ep1421 (BSN.pow_succ_r qz224 1 2 rfl) ep1423) rfl rfl rfl

noncomputable def ep1425 := ep1417 (Enclosure.Real.IsNear.const Bool.false 96 162) (@Enclosure.Real.IsNear.recentre' qz503 Bool.false 26561 1048576 1 1048576 26561 1048576 1 1048576 (ep1424 rfl rfl rfl) rfl)

noncomputable def ep1426 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))))) Bool.false 2172735 1048576 6689 1048576

noncomputable def ep1427 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))))) Bool.false 2172735 1048576 6689 1048576

noncomputable def ep1428 := nat_lit 5818076173619241209975446770746229981184333

noncomputable def ep1429 := nat_lit 1355069354786339147698750560239878144000000

noncomputable def ep1430 := nat_lit 3339353175254601763141651254410489302242598383778009148529947

noncomputable def ep1431 := nat_lit 126321523616048639630436773311057080390107916342474571776000000

noncomputable def ep1432 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34)))) ep1428 ep1429 ep1430 ep1431 1083023 1089712

noncomputable def ep1433 := nat_lit 25474125689797202285744871842394837585912017663778961

noncomputable def ep1434 := nat_lit 5933124054509287375883398629378014553000902656000000

noncomputable def ep1435 := nat_lit 12996521875276729174382897554879870839375321385776743905699

noncomputable def ep1436 := nat_lit 493443451625189998556393645746316720273859048212791296000000

noncomputable def ep1437 := nat_lit 474173362430618082245198108692931894784371034849

noncomputable def ep1438 := nat_lit 23732496218037149503533594517512058212003610624000000

noncomputable def ep1439 := nat_lit 720210304927005558801734138896609844853888765833100510059

noncomputable def ep1440 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34))) ep1433 ep1434 ep1435 ep1436 ep1437 ep1438 ep1439

noncomputable def ep1441 := nat_lit 7430677859767567037084516077121004728829877431910268928000000

noncomputable def ep1442 := nat_lit 604567404920297740206306800787150800583139984542320971746508391014769763537044982936381714079940608000000

noncomputable def ep1443 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz5 1 34)) (Complex.re (zetaApproximant qz5 1 34)) ep542 ep543 ep544 ep545 ep542 ep543 ep544 ep545 ep1433

noncomputable def ep1444 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz5 1 34)) (Complex.im (zetaApproximant qz5 1 34)) 688602470537695705590543 ep666 ep667 ep668 688602470537695705590543 ep666 ep667 ep668 ep1437

noncomputable def ep1445 := @ep1414 1008806316530991104 ep1415 851210186960753791 1513209474796486656 881103630854479 9079256848778919936 (@ep1416 59948651 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz503) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow45.d18 EMRow45.d19 rfl) (ep1425 rfl)) (ep1426 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz5 1 34)) (@ep1427 2172735 1048576 6689 1048576 (@ep1432 524288 (@ep1440 ep1441 ep1442 ep1428 ep1429 ep1430 ep1431 (@ep1443 ep1434 ep1435 ep1436 ep768 ep768 rfl) (@ep1444 ep1438 ep1439 ep1441 ep774 ep774 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz225 := (@Norm.norm Complex Complex.instNorm qz501)

noncomputable abbrev qz683 := (Enclosure.sfrac Bool.false 2 7)

noncomputable def ep1446 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz225 qz683) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) Bool.false 268048086322497237 504403158265495552 117066384535 1008806316530991104 (BSN.zrb_shape_eq qz225 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) qz12 3)

noncomputable def ep1447 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz225 qz683) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) 138816021 3670016 1 3670016 1930959297 137438953472 1631 549755813888

noncomputable def ep1448 := @Enclosure.Real.IsNear.mulLit_ff qz225 qz683 138816021 1048576 1 1048576 2 7 0 1 138816021 3670016

noncomputable abbrev qz506 := (Complex.re qz681)

noncomputable abbrev qz507 := (Complex.im qz681)

noncomputable abbrev qz226 := (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz267 qz506 qz506) (@HMul.hMul Real Real Real qz267 qz507 qz507))

noncomputable abbrev qz227 := qz501

noncomputable def ep1449 := @Enclosure.Real.IsNear.of_eq qz225 (Real.sqrt qz226) Bool.false 138816021 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz227)

noncomputable def ep1450 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz226) Bool.false 138816021 1048576 1 1048576 138816021

noncomputable def ep1451 := @Enclosure.Real.IsNear.sqrt_image qz226 17525860921 1000000 0 1 69408010 69408011 524288

noncomputable abbrev qz228 := (@HMul.hMul Real Real Real qz267 qz506 qz506)

noncomputable abbrev qz229 := (@HMul.hMul Real Real Real qz267 qz507 qz507)

noncomputable def ep1452 := @Enclosure.Real.IsNear.addLit_ff qz228 qz229 49 4 0 1 17513610921 1000000 0 1

noncomputable abbrev qz230 := qz506

noncomputable def ep1453 := @Enclosure.Real.IsNear.mulLit_ff qz230 qz230 7 2 0 1 7 2 0 1 49 4

noncomputable abbrev qz508 := (Enclosure.sfrac Bool.false 7 2)

noncomputable def ep1454 := @Enclosure.Complex.IsNear.of_eq qz227 (Complex.mk qz508 qz12) Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 132339 1000 3 qz13)

noncomputable abbrev qz509 := (ep1454 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz12 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz18))

noncomputable def ep1455 := @ep1453 0 1 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz509)

noncomputable def ep1456 := ep1455 (@Enclosure.Complex.IsNear.re_isNear qz227 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz509)

noncomputable abbrev qz231 := qz507

noncomputable def ep1457 := @Enclosure.Real.IsNear.mulLit_ff qz231 qz231 132339 1000 0 1 132339 1000 0 1 17513610921 1000000

noncomputable def ep1458 := @ep1457 0 1 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz509)

noncomputable def ep1459 := ep1458 (@Enclosure.Complex.IsNear.im_isNear qz227 Bool.false 7 2 0 1 Bool.false 132339 1000 0 1 qz509)

noncomputable def ep1460 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 1930959297 137438953472

noncomputable def ep1461 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))))) Bool.false 15447674376 1099511627776

noncomputable def ep1462 := nat_lit 166168365940566709797903870692499323551455617420612360932019067481

noncomputable def ep1463 := nat_lit 841824943102600080885322463644579019321817144754176000000000000000000

noncomputable def ep1464 := nat_lit 1447298087091563497189999483473529010381802613604152773301515785742823910617931

noncomputable def ep1465 := nat_lit 17364992116519456492989301251620827677087906884636317833149549515898880000000000000000000

noncomputable def ep1466 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) ep1462 ep1463 ep1464 ep1465

noncomputable def ep1467 := nat_lit 44637241612171245390965578291186211946970090514196502775269081

noncomputable def ep1468 := nat_lit 233840261972944466912589573234605283144949206876160000000000000000

noncomputable def ep1469 := nat_lit 1749452948185147023005371545728734987888012089687247678683174222215667712309789

noncomputable def ep1470 := nat_lit 21706240145649320616236626564526034596359883605795397291436936894873600000000000000000000

noncomputable def ep1471 := nat_lit 5474296136750226390427788844228960542363291569504950941050375881

noncomputable def ep1472 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223))) ep1467 ep1468 ep1469 ep1470 ep1471

noncomputable def ep1473 := nat_lit 79559547572409797976170411484235033452321569757257717258294013283816234616833

noncomputable def ep1474 := nat_lit 28941653527532427488315502086034712795146511474393863055249249193164800000000000000000000

noncomputable def ep1475 := nat_lit 38856854223158222124833881736136335565546829699508296125113983083897914951755965148299336210901412085429196250152960000000000000000

noncomputable def ep1476 := nat_lit 6681110806757454564688733054491

noncomputable def ep1477 := nat_lit 483570327845851669882470400000000

noncomputable def ep1478 := nat_lit 429725270002370625136741591347441667

noncomputable def ep1479 := nat_lit 147330377538541998457687861824061440000000000

noncomputable def ep1480 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1476 ep1477 ep1478 ep1479 ep1476 ep1477 ep1478

noncomputable def ep1481 := nat_lit 73988486514796519322022162598109

noncomputable def ep1482 := nat_lit 29014219670751100192948224000000000

noncomputable def ep1483 := nat_lit 158821016657992548255063849593594263

noncomputable def ep1484 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1476 ep1477 ep1478 ep1479 Bool.true ep1481 ep1482 ep1483

noncomputable def ep1485 := nat_lit 294660755077083996915375723648122880000000000

noncomputable def ep1486 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223 Bool.false ep1476 ep1477 ep1478 ep1479 Bool.true ep1481 ep1482 ep1483 ep1485

noncomputable def ep1487 := nat_lit 4100971449920574368795083879

noncomputable def ep1488 := nat_lit 58028439341502200385896448000000

noncomputable def ep1489 := nat_lit 8825788689918408623143220192653

noncomputable def ep1490 := nat_lit 589321510154167993830751447296245760000000

noncomputable def ep1491 := nat_lit 629558022078761814165189883139

noncomputable def ep1492 := nat_lit 45334718235548594051481600000000

noncomputable def ep1493 := nat_lit 142506274276630340993651928766426139

noncomputable abbrev qz232 := (Complex.re qz502)

noncomputable abbrev qz233 := (Complex.im qz502)

noncomputable def ep1494 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) ep1487 ep1488 ep1489 ep1490 ep1491 ep1492 ep1493

noncomputable def ep1495 := nat_lit 49110125846180666152562620608020480000000000

noncomputable def ep1496 := nat_lit 36346353110979354518622583997172697209859189832650063872000000

noncomputable def ep1497 := nat_lit 1227753146154516653814065515200512

noncomputable def ep1498 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 52539582763 480000000 0 1 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 ep1487

noncomputable def ep1499 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 52539582763 480000000 0 1 0 1 0 1 52539582763

noncomputable def ep1500 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 157618748289 2000000 0 1 52539582763 480000000 0

noncomputable def ep1501 := @Enclosure.Complex.IsNear.of_eq (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (Complex.mk (Enclosure.sfrac Bool.true 1 720) qz10) Bool.true 1 720 0 1 Bool.false 0 1 0 1 (BSN.bern_coeff_mk 2 1 30 24 Bool.true BSN.bern_real_2 EMRow45.d20 rfl) (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.true 1 720) qz10 Bool.true 1 720 0 1 Bool.false 0 1 0 1 (Enclosure.Real.IsNear.const Bool.true 1 720) qz22)

noncomputable abbrev qz510 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 qz543)

noncomputable abbrev qz234 := qz510

noncomputable def ep1502 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1

noncomputable abbrev qz235 := (Complex.re qz510)

noncomputable abbrev qz236 := (Complex.im qz510)

noncomputable def ep1503 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) 17512860921 400000 0 1 17513610921 500000 0 1

noncomputable def ep1504 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 17512860921 1000000 0 1 5 2 0 1 17512860921 400000

noncomputable abbrev qz511 := (@HAdd.hAdd Complex Complex Complex qz534 qz533 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz237 := qz511

noncomputable def ep1505 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1

noncomputable abbrev qz238 := (Complex.re qz511)

noncomputable abbrev qz239 := (Complex.im qz511)

noncomputable def ep1506 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) 3 4 0 1 17513610921 1000000 0 1

noncomputable def ep1507 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1508 := @ep1507 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable abbrev qz512 := (Enclosure.sfrac Bool.false 3 2)

noncomputable def ep1509 := @Enclosure.Complex.IsNear.of_eq qz237 (Complex.mk qz512 qz12) Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 132339 1000 1 qz13)

noncomputable abbrev qz513 := (ep1509 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz12 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz18))

noncomputable def ep1510 := ep1508 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz513)

noncomputable def ep1511 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 132339 1000 0 1 132339 1000 0 1 17513610921 1000000

noncomputable def ep1512 := @ep1511 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep1513 := ep1512 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz513)

noncomputable def ep1514 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) qz237 Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 (@ep1506 70051443684 17512860921 1000000 0 1 (ep1510 rfl) (ep1513 rfl) rfl rfl)

noncomputable def ep1515 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238) 132339 2000 0 1 397017 2000 0 1

noncomputable def ep1516 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz239 1 2 0 1 132339 1000 0 1 132339 2000

noncomputable def ep1517 := @ep1516 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep1518 := ep1517 (@Enclosure.Complex.IsNear.im_isNear qz237 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz513)

noncomputable def ep1519 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1))) qz238 132339 1000 0 1 3 2 0 1 397017 2000

noncomputable def ep1520 := @ep1519 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 132339 1000 0 1 ep732)

noncomputable def ep1521 := ep1520 (@Enclosure.Complex.IsNear.re_isNear qz237 Bool.false 3 2 0 1 Bool.false 132339 1000 0 1 qz513)

noncomputable abbrev qz240 := (ep1505 (BSN.ascPochhammer_succ_eval_c 1 2 qz271 rfl) (ep1514 (@ep1515 1058712000 132339 500 0 1 (ep1518 rfl) (ep1521 rfl) rfl rfl)))

noncomputable def ep1522 := @ep1504 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz240)

noncomputable abbrev qz514 := (Enclosure.sfrac Bool.false 5 2)

noncomputable def ep1523 := @Enclosure.Complex.IsNear.of_eq qz234 (Complex.mk qz514 qz12) Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 (BSN.s_add_nat_mk qz12 Bool.false 132339 1000 2 qz13)

noncomputable abbrev qz515 := (ep1523 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz12 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz18))

noncomputable def ep1524 := ep1522 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz515)

noncomputable def ep1525 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 132339 500 0 1 132339 1000 0 1 17513610921 500000

noncomputable def ep1526 := @ep1525 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz240)

noncomputable def ep1527 := ep1526 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz515)

noncomputable def ep1528 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) qz234 Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 (@ep1503 15761874828900000 157618748289 2000000 0 1 (ep1524 rfl) (ep1527 rfl) rfl rfl)

noncomputable def ep1529 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235) 2317634501424219 1000000000 0 1 132339 200 0 1

noncomputable def ep1530 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz236 17512860921 1000000 0 1 132339 1000 0 1 2317634501424219 1000000000

noncomputable def ep1531 := @ep1530 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz240)

noncomputable def ep1532 := ep1531 (@Enclosure.Complex.IsNear.im_isNear qz234 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz515)

noncomputable def ep1533 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2))) qz235 132339 500 0 1 5 2 0 1 132339 200

noncomputable def ep1534 := @ep1533 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 17512860921 1000000 0 1 Bool.false 132339 500 0 1 qz240)

noncomputable def ep1535 := ep1534 (@Enclosure.Complex.IsNear.re_isNear qz234 Bool.false 5 2 0 1 Bool.false 132339 1000 0 1 qz515)

noncomputable abbrev qz241 := (ep1502 (BSN.ascPochhammer_succ_eval_c 2 3 qz271 rfl) (ep1528 (@ep1529 463394561284843800 2316972806424219 1000000000 0 1 (ep1532 rfl) (ep1535 rfl) rfl rfl)))

noncomputable def ep1536 := @ep1500 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz241)

noncomputable def ep1537 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 2316972806424219 1000000000 0 1 0 1 0

noncomputable def ep1538 := @ep1537 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz241)

noncomputable def ep1539 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) 772324268808073 240000000000 0 1 0 1 0 1 772324268808073

noncomputable def ep1540 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 2316972806424219 1000000000 0 1 772324268808073 240000000000 0

noncomputable def ep1541 := @ep1540 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz241)

noncomputable def ep1542 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 157618748289 2000000 0 1 0 1 0

noncomputable def ep1543 := @ep1542 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 157618748289 2000000 0 1 Bool.true 2316972806424219 1000000000 0 1 qz241)

noncomputable def ep1544 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 (@ep1499 52539582763 480000000 0 1 (ep1536 rfl) (ep1538 rfl) rfl rfl) (@ep1539 772324268808073 240000000000 0 1 (ep1541 rfl) (ep1543 rfl) rfl rfl)

noncomputable def ep1545 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 ep1544

noncomputable def ep1546 := nat_lit 613876573077258326907032757600256

noncomputable def ep1547 := @Enclosure.Complex.IsNear.re_isNear qz223 Bool.true 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 Bool.true 20378681840801075 4722366482869645213696 553548347625642069129 ep1546

noncomputable abbrev qz684 := (@Nat.cast Real Real.instNatCast 52523350144)

noncomputable abbrev qz242 := (@Inv.inv Real Real.instInv (Real.sqrt qz684))

noncomputable def ep1548 := @Enclosure.Complex.IsNear.of_eq qz223 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz242 qz640)) Bool.true 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 Bool.true 20378681840801075 4722366482869645213696 553548347625642069129

noncomputable def ep1549 := @Enclosure.Real.IsNear.inv_image (Real.sqrt qz684) 251985781586464421 1099511627776 1 1099511627776 2398797 2398798 549755813888 (@Enclosure.Real.IsNear.of_eq (Real.sqrt qz684) (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz684 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_natCast_div_one 52523350144) (@Enclosure.Real.IsNear.recentre' (Real.sqrt (@HDiv.hDiv Real Real Real qz1 qz684 qz14)) Bool.false 251985781586464421 1099511627776 1 1099511627776 251985781586464421 1099511627776 1 1099511627776 (BSN.sqrt_enclosure 52523350144 1 125992890793232210 125992890793232211 549755813888 rfl rfl rfl rfl rfl) rfl)) rfl rfl rfl rfl

noncomputable def ep1550 := nat_lit 406229439800000000000000000

noncomputable def ep1551 := nat_lit 69846766182031428999891124224

noncomputable def ep1552 := nat_lit 259986841472000000000000000

noncomputable def ep1553 := BSN.log_dyadic_bound 2 66 4 3 8678664751680 549755813888 259986841472 2657927616 960 33328738308 68 64 rfl rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.artanhP 2) (BSN.artanhQ 66) 0 3 2657927616 8678664751680 960 rfl rfl rfl rfl) rfl rfl rfl

noncomputable def ep1554 := @Enclosure.Real.IsNear.mulLit_ff qz12 qz135 132339 1000 0 1 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 2101717470796724520009 4503599627370496000 207048487489168461 ep1550 qz18 (BSN.isNear_log_sfrac 34 1 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false ep1551 ep1419 1001299934207360 ep1552 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 33328738308 549755813888 24973259072661432 36028797018963968 259986841472 1000000000000000 rfl rfl rfl rfl (ep1553 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1555 := nat_lit 23533364378146355070392860672

noncomputable def ep1556 := nat_lit 158456325028528675187087900672

noncomputable def ep1557 := nat_lit 12508835313762184541296672880610778953562410208944324342016

noncomputable def ep1558 := nat_lit 3085321044977261329040567217295032196842629748062962243778641920

noncomputable def ep1559 := nat_lit 21597247314840829303283970521065225377898408236440735706450493440

noncomputable def ep1560 := BSN.sin_dyadic_bound_f 334429222137748 2251799813685248 2 1 1099511627776 520481469744 ep1557 ep1558 ep1557 ep1557 ep1559 ep1557 162695875414 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base (BSN.sinEvenP 334429222137748) (BSN.sinEvenQ 2251799813685248) 0 1 ep1557 ep1558 ep1557 rfl rfl rfl rfl) (@BSN.binarySplit_of_base (BSN.sinOddP 334429222137748) (BSN.sinOddQ 2251799813685248) 0 1 ep1557 ep1559 ep1557 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz516 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 513114616893731) (@Nat.cast Real Real.instNatCast 1099511627776))

noncomputable def ep1561 := @Enclosure.Real.IsNear.cos_image qz133 qz516 Bool.false 513114616893731 1099511627776 561 1099511627776 Bool.true 162695875414 1099511627776 1 259986841472 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2101717470796724520009 4503599627370496000 207048487489168461 ep1550 513114616893731 1099511627776 561 1099511627776 (ep1554 rfl) rfl) (Enclosure.sfrac_false_div 513114616893731 1099511627776) (BSN.cos_reduce1 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1555) (@Nat.cast Real Real.instNatCast ep1556)) 226375608064910080 72057594037927936 Bool.false 162695875414 1099511627776 74 1000000000000000 519973682944 259986841472 (BSN.sin_reduce_arg_pos_rat_q1 513114616893731 1099511627776 226375608064910080 72057594037927936 74 ep1555 ep1556 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 162695875414 1099511627776 ep1555 ep1556 334429222137748 2251799813685248 520481469744 519973682944 (ep1560 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1562 := nat_lit 540312976254833872026002729700965920045500638798267214456526442620944849123439409197599332272141482567243570909164391694336

noncomputable def ep1563 := nat_lit 26653776661622823509741225219881328325881276817119818761557039425464041502648073463671628964929320285054877668848941806827601920

noncomputable def ep1564 := nat_lit 156470960906823889779969982351778709213276291452905694943352892631337805720179340009102691342613111861579951342944256

noncomputable def ep1565 := nat_lit 1620938615822579802430228629162933056579083489842218737558189441157049284694706787234117978611041762475506989567590489194496

noncomputable def ep1566 := nat_lit 1199419949773027057938355134894659774664657456770391844270066774145881867619163305865223303421819412827469495098202381307242086400

noncomputable def ep1567 := BSN.cos_dyadic_bound_f 334429222137748 2251799813685248 3 2 1099511627776 520481469744 ep1562 ep1563 ep1564 ep1565 ep1566 ep1564 1087407868160 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base2 (BSN.cosEvenP 334429222137748) (BSN.cosEvenQ 2251799813685248) 0 2 ep1562 ep1563 ep1564 rfl rfl rfl rfl) (@BSN.binarySplit_of_base2 (BSN.cosOddP 334429222137748) (BSN.cosOddQ 2251799813685248) 0 2 ep1565 ep1566 ep1564 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1568 := @Enclosure.Real.IsNear.sin_image qz133 qz516 Bool.false 513114616893731 1099511627776 561 1099511627776 Bool.false 1087407868160 1099511627776 1 259986841472 (@Enclosure.Real.IsNear.recentre' qz133 Bool.false 2101717470796724520009 4503599627370496000 207048487489168461 ep1550 513114616893731 1099511627776 561 1099511627776 (ep1554 rfl) rfl) (Enclosure.sfrac_false_div 513114616893731 1099511627776) (BSN.sin_reduce1 qz516 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1555) (@Nat.cast Real Real.instNatCast ep1556)) 226375608064910080 72057594037927936 Bool.false 1087407868160 1099511627776 74 1000000000000000 519973682944 259986841472 (BSN.sin_reduce_arg_pos_rat_q1 513114616893731 1099511627776 226375608064910080 72057594037927936 74 ep1555 ep1556 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 1087407868160 1099511627776 ep1555 ep1556 334429222137748 2251799813685248 520481469744 519973682944 (ep1567 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable abbrev qz517 := (@Enclosure.Real.IsNear.recentre' qz242 Bool.false 4797595 1099511627776 1 1099511627776 4797595 1099511627776 1 1099511627776 (ep1549 rfl rfl) rfl)

noncomputable def ep1569 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz133)) (@HMul.hMul Real Real Real qz0 qz242 qz640) Bool.true 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 Bool.true 20378681840801075 4722366482869645213696 553548347625642069129 ep1546 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz133) 4797595 1099511627776 1 1099511627776 81347937707 549755813888 1148063513231 2233269963025152999424 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 qz517 (@Enclosure.Real.IsNear.recentre' (Real.cos qz133) Bool.true 162695875414 1099511627776 146952129693568 285858555267219583926272 81347937707 549755813888 1148063513231 2233269963025152999424 (ep1561 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz640 4797595 1099511627776 1 1099511627776 4247686985 4294967296 1148063513231 2233269963025152999424 20378681840801075 4722366482869645213696 553548347625642069129 ep1546 qz517 (@Enclosure.Real.IsNear.neg qz134 Bool.false 4247686985 4294967296 1148063513231 2233269963025152999424 (@Enclosure.Real.IsNear.recentre' qz134 Bool.false 1087407868160 1099511627776 146952129693568 285858555267219583926272 4247686985 4294967296 1148063513231 2233269963025152999424 (ep1568 rfl rfl) rfl)) rfl)

noncomputable def ep1570 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 772324268808073 240000000000 0 1 20378681840801075 4722366482869645213696 553548347625642069129 ep1546 ep1491

noncomputable def ep1571 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 52539582763 480000000 0 1 Bool.false 772324268808073 240000000000 0 1 ep1544

noncomputable def ep1572 := @Enclosure.Complex.IsNear.im_isNear qz223 Bool.true 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 Bool.true 20378681840801075 4722366482869645213696 553548347625642069129 ep1546

noncomputable def ep1573 := nat_lit 42827497647024530807274809

noncomputable def ep1574 := nat_lit 90669436471097188102963200000

noncomputable def ep1575 := nat_lit 9694399741133105344005887607809

noncomputable def ep1576 := nat_lit 98220251692361332305125241216040960000000

noncomputable def ep1577 := nat_lit 60283687267748669463694223718109

noncomputable def ep1578 := nat_lit 129737817434593232223046186770167263

noncomputable def ep1579 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232) ep1573 ep1574 ep1575 ep1576 ep1577 ep1482 ep1578

noncomputable def ep1580 := nat_lit 6708494377645974010805503841783441948429156349513616588800000

noncomputable def ep1581 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz233 52539582763 480000000 0 1 20378681840801075 4722366482869645213696 553548347625642069129 ep1546 ep1573

noncomputable def ep1582 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3)))) qz232 772324268808073 240000000000 0 1 390274459203414665 604462909807314587353088 167983608277411029031 ep1497 ep1577

noncomputable abbrev qz518 := (@ep1548 ep1546 (BSN.cpow_neg_s_sub_mk qz12 132339 1000 34 3 52523350144 qz13 rfl EMRow45.d21) ep1569)

noncomputable def ep1583 := ep1486 (@ep1494 ep1495 ep1496 ep1476 ep1477 ep1478 ep1479 (@ep1498 ep1488 ep1489 ep1490 ep1545 (ep1547 qz518) rfl) (@ep1570 ep1492 ep1493 ep1495 ep1571 (ep1572 qz518) rfl) rfl rfl) (@ep1579 ep1485 ep1580 ep1481 ep1482 ep1483 ep1485 (@ep1581 ep1574 ep1575 ep1576 ep1545 (ep1572 qz518) rfl) (@ep1582 ep1482 ep1578 ep1485 ep1571 (ep1547 qz518) rfl) rfl rfl)

noncomputable def ep1584 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) ep1481 ep1482 ep1483 ep1485 ep1481 ep1482 ep1483

noncomputable def ep1585 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223) Bool.false ep1476 ep1477 ep1478 ep1479 Bool.true ep1481 ep1482 ep1483

noncomputable def ep1586 := @ep1447 268048086322497237 504403158265495552 117066384535 1008806316530991104 (@ep1448 1 3670016 (ep1449 (@ep1450 1048576 1 1048576 (ep1451 (@ep1452 70103443684 17525860921 1000000 0 1 (ep1456 rfl) (ep1459 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1460 1631 549755813888 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)) (@ep1461 3262 1099511627776 1930959297 137438953472 1631 549755813888 (@ep1466 7723835557 7723838819 549755813888 (@ep1472 ep1463 ep1473 ep1474 ep1475 ep1462 ep1463 ep1464 ep1465 (@ep1480 ep1479 ep1467 ep1468 ep1469 ep1470 (@ep1484 ep1485 ep1583) (@ep1484 ep1485 ep1583) rfl) (@ep1584 ep1485 ep1471 ep1463 ep1473 ep1474 (@ep1585 ep1485 ep1583) (@ep1585 ep1485 ep1583) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow45.d22 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 851210186960753791 1513209474796486656 881103630854479 9079256848778919936 := ep1445 (ep1446 ep1586) rfl rfl

noncomputable abbrev qz685 := (@HAdd.hAdd Complex Complex Complex qz687 qz693 (@Nat.cast Complex Complex.instNatCast 3))

noncomputable abbrev qz519 := qz685

noncomputable abbrev qz243 := (@HDiv.hDiv Real Real Real qz270 (@Norm.norm Complex Complex.instNorm qz519) (@HAdd.hAdd Real Real Real qz421 (Complex.re qz444) qz288))

noncomputable abbrev qz520 := (@HPow.hPow Complex Complex Complex qz535 qz634 (@HSub.hSub Complex Complex Complex qz623 qz643 qz542))

noncomputable abbrev qz244 := qz520

noncomputable def ep1587 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) 6710769455 618475290624 62434297 618475290624 285092544980445871 504403158265495552 63133341113

noncomputable def ep1588 := nat_lit 179707627919010670794625777664

noncomputable def ep1589 := @Enclosure.Real.IsNear.mulLit_ff (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34)) 26561 1769472 1 1769472 757965 1048576 7023 1048576 6710769455 618475290624

noncomputable def ep1590 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 34)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 34)) (Complex.im (zetaApproximant qz144 1 34))))) Bool.false 757965 1048576 7023 1048576

noncomputable def ep1591 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 34)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 34)) (Complex.im (zetaApproximant qz144 1 34))))) Bool.false 757965 1048576 7023 1048576

noncomputable def ep1592 := nat_lit 337679999925608556546333561131133230447413

noncomputable def ep1593 := nat_lit 646204066833316044195101180251540029440000

noncomputable def ep1594 := nat_lit 2672945333885562325405692056977033492513482936984942739043

noncomputable def ep1595 := nat_lit 276117122005951173178747874936287320382780101239441981440000

noncomputable def ep1596 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 34)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 34)) (Complex.im (zetaApproximant qz144 1 34)))) ep1592 ep1593 ep1594 ep1595 375471 382494

noncomputable def ep1597 := nat_lit 60934451310395089947415042245766321694898398325841

noncomputable def ep1598 := nat_lit 116719097615802337231525745194947924276816117760000

noncomputable def ep1599 := nat_lit 40344857027320348374244856320836105648454306932584205939

noncomputable def ep1600 := nat_lit 4314330031342987080917935545879489380980939081866280960000

noncomputable def ep1601 := nat_lit 232834357552518544585111798379845942758541858369

noncomputable def ep1602 := nat_lit 466876390463209348926102980779791697107264471040000

noncomputable def ep1603 := nat_lit 90874484137060029454021252443522731012407293299553558947

noncomputable def ep1604 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (zetaApproximant qz144 1 34)) (Complex.re (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 (Complex.im (zetaApproximant qz144 1 34)) (Complex.im (zetaApproximant qz144 1 34))) ep1597 ep1598 ep1599 ep1600 ep1601 ep1602 ep1603

noncomputable def ep1605 := nat_lit 28476032898760921623200227139963952067501841678119089852802531245329726145481710623409718773678080000

noncomputable def ep1606 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (zetaApproximant qz144 1 34)) (Complex.re (zetaApproximant qz144 1 34)) ep1199 ep1200 ep1201 ep1202 ep1199 ep1200 ep1201 ep1202 ep1597

noncomputable def ep1607 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (zetaApproximant qz144 1 34)) (Complex.im (zetaApproximant qz144 1 34)) 482529126118329301194463 ep1312 ep1313 ep1314 482529126118329301194463 ep1312 ep1313 ep1314 ep1601

noncomputable def ep1608 := @ep1587 504403158265495552 ep1588 2615090167368335399 4539628424389459968 458837937947521 4539628424389459968 (@ep1589 62434297 618475290624 (@Enclosure.Real.IsNear.of_eq (riemannSiegelThetaStirlingErrorBound 1 2) (@HMul.hMul Real Real Real qz0 (Enclosure.sfrac Bool.false 96 162) qz503) Bool.false 26561 1769472 1 1769472 (BSN.theta_err_eq 1 2 96 162 EMRow45.d18 EMRow45.d19 rfl) (ep1425 rfl)) (ep1590 (BSN.norm_eq_sqrt_mul_add (zetaApproximant qz144 1 34)) (@ep1591 757965 1048576 7023 1048576 (@ep1596 524288 (@ep1604 ep1595 ep1605 ep1592 ep1593 ep1594 ep1595 (@ep1606 ep1598 ep1599 ep1600 ep1405 ep1405 rfl) (@ep1607 ep1602 ep1603 ep1595 ep1413 ep1413 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl)

noncomputable abbrev qz245 := (@Norm.norm Complex Complex.instNorm qz519)

noncomputable def ep1609 := @Enclosure.Real.IsNear.of_eq (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (@HMul.hMul Real Real Real qz0 qz245 qz683) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) Bool.false 285092544980445871 504403158265495552 63133341113 504403158265495552 (BSN.zrb_shape_eq qz245 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) qz147 3)

noncomputable def ep1610 := @Enclosure.Real.IsNear.mulLit_ff (@HMul.hMul Real Real Real qz0 qz245 qz683) (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) 140971151 3670016 1 3670016 2022346721 137438953472 867 274877906944

noncomputable def ep1611 := @Enclosure.Real.IsNear.mulLit_ff qz245 qz683 140971151 1048576 1 1048576 2 7 0 1 140971151 3670016

noncomputable abbrev qz521 := (Complex.re qz685)

noncomputable abbrev qz522 := (Complex.im qz685)

noncomputable abbrev qz246 := (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz267 qz521 qz521) (@HMul.hMul Real Real Real qz267 qz522 qz522))

noncomputable abbrev qz247 := qz519

noncomputable def ep1612 := @Enclosure.Real.IsNear.of_eq qz245 (Real.sqrt qz246) Bool.false 140971151 1048576 1 1048576 (BSN.norm_eq_sqrt_mul_add qz247)

noncomputable def ep1613 := @Enclosure.Real.IsNear.recentre' (Real.sqrt qz246) Bool.false 140971151 1048576 1 1048576 140971151

noncomputable def ep1614 := @Enclosure.Real.IsNear.sqrt_image qz246 722970641 40000 0 1 70485575 70485576 524288

noncomputable abbrev qz248 := (@HMul.hMul Real Real Real qz267 qz521 qz521)

noncomputable abbrev qz249 := (@HMul.hMul Real Real Real qz267 qz522 qz522)

noncomputable def ep1615 := @Enclosure.Real.IsNear.addLit_ff qz248 qz249 49 4 0 1 722480641 40000 0 1

noncomputable abbrev qz250 := qz521

noncomputable def ep1616 := @Enclosure.Real.IsNear.mulLit_ff qz250 qz250 7 2 0 1 7 2 0 1 49 4

noncomputable def ep1617 := @Enclosure.Complex.IsNear.of_eq qz247 (Complex.mk qz508 qz147) Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 134395 1000 3 qz148)

noncomputable abbrev qz523 := (ep1617 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 7 2) qz147 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 7 2) qz149))

noncomputable def ep1618 := @ep1616 0 1 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz523)

noncomputable def ep1619 := ep1618 (@Enclosure.Complex.IsNear.re_isNear qz247 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz523)

noncomputable abbrev qz251 := qz522

noncomputable def ep1620 := @Enclosure.Real.IsNear.mulLit_ff qz251 qz251 134395 1000 0 1 134395 1000 0 1 722480641 40000

noncomputable def ep1621 := @ep1620 0 1 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz523)

noncomputable def ep1622 := ep1621 (@Enclosure.Complex.IsNear.im_isNear qz247 Bool.false 7 2 0 1 Bool.false 134395 1000 0 1 qz523)

noncomputable def ep1623 := @Enclosure.Real.IsNear.of_eq (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 2022346721 137438953472

noncomputable def ep1624 := @Enclosure.Real.IsNear.recentre' (Real.sqrt (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))))) Bool.false 16178773768 1099511627776

noncomputable def ep1625 := nat_lit 671917261749927789706375953476909059879463891907219762852341

noncomputable def ep1626 := nat_lit 3103303470253424938175652729979376096827946722421794406400000000

noncomputable def ep1627 := nat_lit 6187464801869975992531344835681717910503199791966155694999083549125162361809

noncomputable def ep1628 := nat_lit 66681569727434712933078916806223978280017562437003460479294270141051699200000000000000

noncomputable def ep1629 := @Enclosure.Real.IsNear.sqrt_image (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) ep1625 ep1626 ep1627 ep1628

noncomputable def ep1630 := nat_lit 70383988274947993004159486473084039439465272201450070625982081

noncomputable def ep1631 := nat_lit 1939564668908390586359782956237110060517466701513621504000000000000

noncomputable def ep1632 := nat_lit 1163283714375039159494306963167661781102876130215848668351531392829129429117

noncomputable def ep1633 := nat_lit 87391075079689218890581371112496030746299915060140570289182761

noncomputable def ep1634 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244))) ep1630 ep1631 ep1632 ep1628 ep1633

noncomputable def ep1635 := nat_lit 484891167227097646589945739059277515129366675378405376000000000000

noncomputable def ep1636 := nat_lit 1256045271873734208259259468128514032350080915437576756661888039074008233173

noncomputable def ep1637 := nat_lit 16670392431858678233269729201555994570004390609250865119823567535262924800000000000000

noncomputable def ep1638 := nat_lit 203629215831223610601890244190127700354666385441815102994437635590003827994921301141166602701678576633091205365760000000000000000

noncomputable def ep1639 := nat_lit 8389516569799954391419687500991

noncomputable def ep1640 := nat_lit 1392682544196052809261514752000000

noncomputable def ep1641 := nat_lit 6826644093886822598518280714515693

noncomputable def ep1642 := nat_lit 4714572081233343950646011578369966080000000

noncomputable def ep1643 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1639 ep1640 ep1641 ep1642 ep1639 ep1640 ep1641

noncomputable def ep1644 := nat_lit 9348319371934680478660111424819

noncomputable def ep1645 := nat_lit 696341272098026404630757376000000

noncomputable def ep1646 := nat_lit 6615007004423958533592649615078661

noncomputable def ep1647 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1639 ep1640 ep1641 ep1642 Bool.true ep1644 ep1645 ep1646

noncomputable def ep1648 := nat_lit 2357286040616671975323005789184983040000000

noncomputable def ep1649 := @Enclosure.Complex.IsNear.mul (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244 Bool.false ep1639 ep1640 ep1641 ep1642 Bool.true ep1644 ep1645 ep1646 ep1648

noncomputable def ep1650 := nat_lit 1026848703425425793688112733

noncomputable def ep1651 := nat_lit 2321137573660088015435857920000

noncomputable def ep1652 := nat_lit 726579105903357005269637286227

noncomputable def ep1653 := nat_lit 7857620135388906584410019297283276800000

noncomputable def ep1654 := nat_lit 9005625791855209867632555140791

noncomputable def ep1655 := nat_lit 6390696630344808395356498342779493

noncomputable abbrev qz252 := (Complex.re qz520)

noncomputable abbrev qz253 := (Complex.im qz520)

noncomputable def ep1656 := @Enclosure.Real.IsNear.subLit_tt_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) ep1650 ep1651 ep1652 ep1653 ep1654 ep1640 ep1655

noncomputable def ep1657 := nat_lit 19473222135006570574636083553709982326431510564096935198720000

noncomputable def ep1658 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 2167391923 19200000 0 1 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 ep1650

noncomputable def ep1659 := @Enclosure.Real.IsNear.subLit_ft (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) 2167391923 19200000 0 1 0 1 0 1 2167391923

noncomputable def ep1660 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 6502175769 80000 0 1 2167391923 19200000 0

noncomputable abbrev qz524 := (@HAdd.hAdd Complex Complex Complex qz534 qz642 qz543)

noncomputable abbrev qz254 := qz524

noncomputable def ep1661 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) qz254) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1

noncomputable abbrev qz255 := (Complex.re qz524)

noncomputable abbrev qz256 := (Complex.im qz524)

noncomputable def ep1662 := @Enclosure.Real.IsNear.subLit_tf (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) 722450641 16000 0 1 722480641 20000 0 1

noncomputable def ep1663 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 722450641 40000 0 1 5 2 0 1 722450641 16000

noncomputable abbrev qz525 := (@HAdd.hAdd Complex Complex Complex qz534 qz642 (@Nat.cast Complex Complex.instNatCast 1))

noncomputable abbrev qz257 := qz525

noncomputable def ep1664 := @Enclosure.Complex.IsNear.of_eq (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) (@HMul.hMul Complex Complex Complex qz78 (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz257) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1

noncomputable abbrev qz258 := (Complex.re qz525)

noncomputable abbrev qz259 := (Complex.im qz525)

noncomputable def ep1665 := @Enclosure.Real.IsNear.subLit_ff_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) 3 4 0 1 722480641 40000 0 1

noncomputable def ep1666 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 1 2 0 1 3 2 0 1 3 4

noncomputable def ep1667 := @ep1666 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1668 := @Enclosure.Complex.IsNear.of_eq qz257 (Complex.mk qz512 qz147) Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 134395 1000 1 qz148)

noncomputable abbrev qz526 := (ep1668 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 3 2) qz147 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 3 2) qz149))

noncomputable def ep1669 := ep1667 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz526)

noncomputable def ep1670 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 134395 1000 0 1 134395 1000 0 1 722480641 40000

noncomputable def ep1671 := @ep1670 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1672 := ep1671 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz526)

noncomputable def ep1673 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) qz257 Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 (@ep1665 2889802564 722450641 40000 0 1 (ep1669 rfl) (ep1672 rfl) rfl rfl)

noncomputable def ep1674 := @Enclosure.Real.IsNear.addLit_ff (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz259) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz258) 26879 400 0 1 80637 400 0 1

noncomputable def ep1675 := @Enclosure.Real.IsNear.mulLit_ff (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz259 1 2 0 1 134395 1000 0 1 26879 400

noncomputable def ep1676 := @ep1675 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1677 := ep1676 (@Enclosure.Complex.IsNear.im_isNear qz257 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz526)

noncomputable def ep1678 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1))) qz258 134395 1000 0 1 3 2 0 1 80637 400

noncomputable def ep1679 := @ep1678 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 1)) Bool.false 1 2 0 1 Bool.false 134395 1000 0 1 ep1369)

noncomputable def ep1680 := ep1679 (@Enclosure.Complex.IsNear.re_isNear qz257 Bool.false 3 2 0 1 Bool.false 134395 1000 0 1 qz526)

noncomputable abbrev qz260 := (ep1664 (BSN.ascPochhammer_succ_eval_c 1 2 qz444 rfl) (ep1673 (@ep1674 43006400 26879 100 0 1 (ep1677 rfl) (ep1680 rfl) rfl rfl)))

noncomputable def ep1681 := @ep1663 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz260)

noncomputable def ep1682 := @Enclosure.Complex.IsNear.of_eq qz254 (Complex.mk qz514 qz147) Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 (BSN.s_add_nat_mk qz147 Bool.false 134395 1000 2 qz148)

noncomputable abbrev qz527 := (ep1682 (@Enclosure.Complex.IsNear.mk (Enclosure.sfrac Bool.false 5 2) qz147 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 (Enclosure.Real.IsNear.const Bool.false 5 2) qz149))

noncomputable def ep1683 := ep1681 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz527)

noncomputable def ep1684 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 26879 100 0 1 134395 1000 0 1 722480641 20000

noncomputable def ep1685 := @ep1684 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz260)

noncomputable def ep1686 := ep1685 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz527)

noncomputable def ep1687 := @Enclosure.Complex.IsNear.mul (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) qz254 Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 (@ep1662 26008703076000 6502175769 80000 0 1 (ep1683 rfl) (ep1686 rfl) rfl rfl)

noncomputable def ep1688 := @Enclosure.Real.IsNear.addLit_tf_n (@HMul.hMul Real Real Real qz0 (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz256) (@HMul.hMul Real Real Real qz0 (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz255) 19418750779439 8000000 0 1 26879 40 0 1

noncomputable def ep1689 := @Enclosure.Real.IsNear.mulLit_tf (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz256 722450641 40000 0 1 134395 1000 0 1 19418750779439 8000000

noncomputable def ep1690 := @ep1689 0 1 (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz260)

noncomputable def ep1691 := ep1690 (@Enclosure.Complex.IsNear.im_isNear qz254 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz527)

noncomputable def ep1692 := @Enclosure.Real.IsNear.mulLit_ff (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2))) qz255 26879 100 0 1 5 2 0 1 26879 40

noncomputable def ep1693 := @ep1692 0 1 (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 2)) Bool.true 722450641 40000 0 1 Bool.false 26879 100 0 1 qz260)

noncomputable def ep1694 := ep1693 (@Enclosure.Complex.IsNear.re_isNear qz254 Bool.false 5 2 0 1 Bool.false 134395 1000 0 1 qz527)

noncomputable abbrev qz261 := (ep1661 (BSN.ascPochhammer_succ_eval_c 2 3 qz444 rfl) (ep1687 (@ep1688 776534999177560 19413374979439 8000000 0 1 (ep1691 rfl) (ep1694 rfl) rfl rfl)))

noncomputable def ep1695 := @ep1660 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz261)

noncomputable def ep1696 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 19413374979439 8000000 0 1 0 1 0

noncomputable def ep1697 := @ep1696 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz261)

noncomputable def ep1698 := @Enclosure.Real.IsNear.addLit_ft_p (@HMul.hMul Real Real Real qz0 (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) (@HMul.hMul Real Real Real qz0 (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) 19413374979439 5760000000 0 1 0 1 0 1 19413374979439

noncomputable def ep1699 := @Enclosure.Real.IsNear.mulLit_tt (Complex.re (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.im (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 1 720 0 1 19413374979439 8000000 0 1 19413374979439 5760000000 0

noncomputable def ep1700 := @ep1699 1 (@Enclosure.Complex.IsNear.re_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.im_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz261)

noncomputable def ep1701 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222)) (Complex.re (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) 0 1 0 1 6502175769 80000 0 1 0 1 0

noncomputable def ep1702 := @ep1701 1 (@Enclosure.Complex.IsNear.im_isNear (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) Bool.true 1 720 0 1 Bool.false 0 1 0 1 ep1501) (@Enclosure.Complex.IsNear.re_isNear (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.true 6502175769 80000 0 1 Bool.true 19413374979439 8000000 0 1 qz261)

noncomputable def ep1703 := @Enclosure.Complex.IsNear.mul (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 (@ep1659 2167391923 19200000 0 1 (ep1695 rfl) (ep1697 rfl) rfl rfl) (@ep1698 19413374979439 5760000000 0 1 (ep1700 rfl) (ep1702 rfl) rfl rfl)

noncomputable def ep1704 := @Enclosure.Complex.IsNear.re_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 ep1703

noncomputable def ep1705 := nat_lit 1208925819614629174706176

noncomputable def ep1706 := nat_lit 2455506292309033307628131030401024

noncomputable def ep1707 := @Enclosure.Complex.IsNear.re_isNear qz244 Bool.true 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 Bool.true 2319438480272802845 ep1705 987571193125351799361 ep1706

noncomputable def ep1708 := @Enclosure.Complex.IsNear.of_eq qz244 (Complex.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz679)) Bool.true 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 Bool.true 2319438480272802845 ep1705 987571193125351799361

noncomputable def ep1709 := nat_lit 81245887960000000000000000

noncomputable def ep1710 := @Enclosure.Real.IsNear.mulLit_ff qz147 qz135 134395 1000 0 1 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 426873891275777800749 900719925474099200 42053032705561921 ep1709 qz149 (BSN.isNear_log_sfrac 34 1 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 Bool.false (@Enclosure.Real.IsNear.recentre' qz440 Bool.false ep1551 ep1419 1001299934207360 ep1552 15881315944632531 4503599627370496 1564531147199 406229439800000000000000 (BSN.log_rat_reduce_isNear 34 1 5 68 64 33328738308 549755813888 24973259072661432 36028797018963968 259986841472 1000000000000000 rfl rfl rfl rfl (ep1553 rfl) BSN.log2_near_15 rfl rfl rfl rfl) rfl))

noncomputable def ep1711 := nat_lit 44190630322832227223958716416

noncomputable def ep1712 := nat_lit 39614081257132168796771975168

noncomputable def ep1713 := nat_lit 1366473480156877520560434627386473959222572799332134238565904305797750428409878187854105230261546261041095926551122289080188432762396285577244490032287305433115737907273410260468678776351358976

noncomputable def ep1714 := nat_lit 105837034526088297993462992180381389879322393587938448256862118304383601140722304680429244037940156116138104563485128823993096599821236196995637140025443129138277048165837662434864861216033996800

noncomputable def ep1715 := nat_lit 63113845819722983328389535891318938613418131660410640366809424432228232728800249662742968415898767924313233759375367624938968758726914871671754225218288725500983263835391242969207013376

noncomputable def ep1716 := nat_lit 6830205397036939842468492625056669534183545357137008820057620913733027412302781336044324852140166003365060461220463070377320837047874452416088942399607671094427147463759057574500442425561972736

noncomputable def ep1717 := nat_lit 3704296208413090429771204726313348645776283775577845688990174140653426039925280663815023541327905464064833659721979508839758380993743266894847299900890509519839696685804318185220270142561189888000

noncomputable def ep1718 := BSN.sin_dyadic_bound_f 2511946509163876 2251799813685248 4 3 1099511627776 520481469744 ep1713 ep1714 ep1715 ep1716 ep1717 ep1715 987518920418 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.sinEvenP 2511946509163876) (BSN.sinEvenQ 2251799813685248) 0 3 ep1713 ep1714 ep1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.sinOddP 2511946509163876) (BSN.sinOddQ 2251799813685248) 0 3 ep1716 ep1717 ep1715 rfl rfl rfl rfl) rfl rfl

noncomputable abbrev qz528 := (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast 130271573265313) (@Nat.cast Real Real.instNatCast 274877906944))

noncomputable def ep1719 := @Enclosure.Real.IsNear.cos_image qz217 qz528 Bool.false 130271573265313 274877906944 285 549755813888 Bool.true 987518920418 1099511627776 1 259986841472 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 426873891275777800749 900719925474099200 42053032705561921 ep1709 130271573265313 274877906944 285 549755813888 (ep1710 rfl) rfl) (Enclosure.sfrac_false_div 130271573265313 274877906944) (BSN.cos_reduce1 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1711) (@Nat.cast Real Real.instNatCast ep1712)) 226375608064910080 72057594037927936 Bool.false 987518920418 1099511627776 75 1000000000000000 519973682944 259986841472 (BSN.sin_reduce_arg_pos_rat_q1 130271573265313 274877906944 226375608064910080 72057594037927936 75 ep1711 ep1712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.sin_arg_round Bool.false 987518920418 1099511627776 ep1711 ep1712 2511946509163876 2251799813685248 520481469744 519973682944 (ep1718 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1720 := nat_lit 525781958937751309147878345483318620270012450030870145605404602422113589213666191045191660477739152905535004061782259150920054165993385309052636487551396406597422949152997277154580500217593856

noncomputable def ep1721 := nat_lit 8141310348160638307189460936952414606101722583687572942835547561875661626209408052340711079841550470472161889498856063384084353832402784384279780001957163779867465243525974033451143170464153600

noncomputable def ep1722 := nat_lit 3187785272098610121398547989694344851163400959725167278863279305243408309341510333345753422595852971643055790241913164023064750332323735403917315992368586698980219996883918216480144450146795520

noncomputable def ep1723 := nat_lit 740859241682618085954240945262669729155256755115569137798034828130685207985056132763004708265581092812966731944395901767951676198748653378969459980178101903967939337160863637044054028512237977600

noncomputable def ep1724 := BSN.cos_dyadic_bound_f 2511946509163876 2251799813685248 4 3 1099511627776 520481469744 ep1720 ep1721 ep1715 ep1722 ep1723 ep1715 483458582951 rfl rfl rfl rfl rfl rfl rfl rfl (@BSN.binarySplit_of_base3 (BSN.cosEvenP 2511946509163876) (BSN.cosEvenQ 2251799813685248) 0 3 ep1720 ep1721 ep1715 rfl rfl rfl rfl) (@BSN.binarySplit_of_base3 (BSN.cosOddP 2511946509163876) (BSN.cosOddQ 2251799813685248) 0 3 ep1722 ep1723 ep1715 rfl rfl rfl rfl) rfl rfl

noncomputable def ep1725 := @Enclosure.Real.IsNear.sin_image qz217 qz528 Bool.false 130271573265313 274877906944 285 549755813888 Bool.false 483458582951 1099511627776 1 259986841472 (@Enclosure.Real.IsNear.recentre' qz217 Bool.false 426873891275777800749 900719925474099200 42053032705561921 ep1709 130271573265313 274877906944 285 549755813888 (ep1710 rfl) rfl) (Enclosure.sfrac_false_div 130271573265313 274877906944) (BSN.sin_reduce1 qz528 (@HDiv.hDiv Real Real Real qz1 (@Nat.cast Real Real.instNatCast ep1711) (@Nat.cast Real Real.instNatCast ep1712)) 226375608064910080 72057594037927936 Bool.false 483458582951 1099511627776 75 1000000000000000 519973682944 259986841472 (BSN.sin_reduce_arg_pos_rat_q1 130271573265313 274877906944 226375608064910080 72057594037927936 75 ep1711 ep1712 rfl rfl rfl rfl) BSN.pi_near_15 (@BSN.cos_arg_round Bool.false 483458582951 1099511627776 ep1711 ep1712 2511946509163876 2251799813685248 520481469744 519973682944 (ep1724 rfl rfl) rfl) rfl rfl rfl rfl)

noncomputable def ep1726 := @Enclosure.Complex.IsNear.mk (@HMul.hMul Real Real Real qz0 qz242 (Real.cos qz217)) (@HMul.hMul Real Real Real qz0 qz242 qz679) Bool.true 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 Bool.true 2319438480272802845 ep1705 987571193125351799361 ep1706 (@Enclosure.Real.IsNear.mulLit_ft qz242 (Real.cos qz217) 4797595 1099511627776 1 1099511627776 493759460209 549755813888 583171919011 1116634981512576499712 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 qz517 (@Enclosure.Real.IsNear.recentre' (Real.cos qz217) Bool.true 987518920418 1099511627776 74646005633408 142929277633609791963136 493759460209 549755813888 583171919011 1116634981512576499712 (ep1719 rfl rfl) rfl) rfl) (@Enclosure.Real.IsNear.mulLit_ft qz242 qz679 4797595 1099511627776 1 1099511627776 483458582951 1099511627776 583171919011 1116634981512576499712 2319438480272802845 ep1705 987571193125351799361 ep1706 qz517 (@Enclosure.Real.IsNear.neg qz218 Bool.false 483458582951 1099511627776 583171919011 1116634981512576499712 (@Enclosure.Real.IsNear.recentre' qz218 Bool.false 483458582951 1099511627776 74646005633408 142929277633609791963136 483458582951 1099511627776 583171919011 1116634981512576499712 (ep1725 rfl rfl) rfl)) rfl)

noncomputable def ep1727 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 19413374979439 5760000000 0 1 2319438480272802845 ep1705 987571193125351799361 ep1706 ep1654

noncomputable def ep1728 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) Bool.false 2167391923 19200000 0 1 Bool.false 19413374979439 5760000000 0 1 ep1703

noncomputable def ep1729 := @Enclosure.Complex.IsNear.im_isNear qz244 Bool.true 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 Bool.true 2319438480272802845 ep1705 987571193125351799361 ep1706

noncomputable def ep1730 := nat_lit 1005426445607733544564884187

noncomputable def ep1731 := nat_lit 4642275147320176030871715840000

noncomputable def ep1732 := nat_lit 713484609122453538822849320401

noncomputable def ep1733 := nat_lit 15715240270777813168820038594566553600000

noncomputable def ep1734 := nat_lit 9197505405093520446975378796769

noncomputable def ep1735 := nat_lit 6507984313055590502769222217018511

noncomputable def ep1736 := @Enclosure.Real.IsNear.addLit_tt (@HMul.hMul Real Real Real qz0 (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253) (@HMul.hMul Real Real Real qz0 (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252) ep1730 ep1731 ep1732 ep1733 ep1734 ep1645 ep1735

noncomputable def ep1737 := nat_lit 43397470689544124285297116616558209287335991993749691432960000

noncomputable def ep1738 := @Enclosure.Real.IsNear.mulLit_ft (Complex.re (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz253 2167391923 19200000 0 1 2319438480272802845 ep1705 987571193125351799361 ep1706 ep1730

noncomputable def ep1739 := @Enclosure.Real.IsNear.mulLit_ft (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3)))) qz252 19413374979439 5760000000 0 1 2368857917501397355 604462909807314587353088 1005695967849221802147 ep1497 ep1734

noncomputable abbrev qz529 := (@ep1708 ep1706 (BSN.cpow_neg_s_sub_mk qz147 134395 1000 34 3 52523350144 qz148 rfl EMRow45.d21) ep1726)

noncomputable def ep1740 := ep1649 (@ep1656 ep1642 ep1657 ep1639 ep1640 ep1641 ep1642 (@ep1658 ep1651 ep1652 ep1653 ep1704 (ep1707 qz529) rfl) (@ep1727 ep1640 ep1655 ep1642 ep1728 (ep1729 qz529) rfl) rfl rfl) (@ep1736 ep1648 ep1737 ep1644 ep1645 ep1646 ep1648 (@ep1738 ep1731 ep1732 ep1733 ep1704 (ep1729 qz529) rfl) (@ep1739 ep1645 ep1735 ep1648 ep1728 (ep1707 qz529) rfl) rfl rfl)

noncomputable def ep1741 := @Enclosure.Real.IsNear.mulLit_tt (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (Complex.im (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) ep1644 ep1645 ep1646 ep1648 ep1644 ep1645 ep1646

noncomputable def ep1742 := @Enclosure.Complex.IsNear.im_isNear (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244) Bool.false ep1639 ep1640 ep1641 ep1642 Bool.true ep1644 ep1645 ep1646

noncomputable def ep1743 := @ep1610 285092544980445871 504403158265495552 63133341113 504403158265495552 (@ep1611 1 3670016 (ep1612 (@ep1613 1048576 1 1048576 (ep1614 (@ep1615 2891882564 722970641 40000 0 1 (ep1619 rfl) (ep1622 rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) (Enclosure.Real.IsNear.const Bool.false 2 7) rfl) (@ep1623 867 274877906944 (BSN.norm_eq_sqrt_mul_add (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)) (@ep1624 3468 1099511627776 2022346721 137438953472 867 274877906944 (@ep1629 8089385150 8089388618 549755813888 (@ep1634 ep1635 ep1636 ep1637 ep1638 ep1625 ep1626 ep1627 ep1628 (@ep1643 ep1642 ep1630 ep1631 ep1632 ep1628 (@ep1647 ep1648 ep1740) (@ep1647 ep1648 ep1740) rfl) (@ep1741 ep1648 ep1633 ep1635 ep1636 ep1637 (@ep1742 ep1648 ep1740) (@ep1742 ep1648 ep1740) rfl) rfl rfl) rfl rfl rfl rfl rfl rfl) rfl)) rfl

theorem EMRow45.d23 : Enclosure.Real.IsNear (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 2615090167368335399 4539628424389459968 458837937947521 4539628424389459968 := ep1608 (ep1609 ep1743) rfl rfl

noncomputable def EMRow45.d24 := fun (I J : @NonemptyInterval Real Real.instLE) => @LE.le Real Real.instLE (@Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE I)) (@Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE J))

noncomputable abbrev qz530 := (EMRow45.d3 qz545 qz649 (@Enclosure.dec_le_dec qz545 qz649 132339 1000 134395 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz649) rfl rfl rfl) 34 34 1 1)

noncomputable abbrev qz262 := qz530

noncomputable def ep1744 := @Zeta.Certificates.ZIntervalEM.Certificate.mk qz262 (@Enclosure.dec_nonneg qz12 132339 1000 qz13) (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 34 rfl)

noncomputable abbrev qz263 := (Zeta.Certificates.ZIntervalEM.fstVal qz530)

noncomputable def ep1745 := @Enclosure.Real.IsNear.neg_val qz263 ep525 ep526

noncomputable def ep1746 := @Enclosure.Real.IsNear.of_eq qz263 (hardyZApproximantEM 1 34 qz12) Bool.true

noncomputable abbrev qz264 := (Zeta.Certificates.ZIntervalEM.sndVal qz530)

noncomputable def ep1747 := BSN.mul_neg_of_neg_pos_r qz263 qz264 (@ep1745 ep527 ep528 (@ep1746 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 34 qz12)) EMRow45.d12) rfl rfl rfl)

noncomputable def ep1748 := @Enclosure.Real.IsNear.pos_val qz264 ep1182 ep1183

noncomputable def ep1749 := @Enclosure.Real.IsNear.of_eq qz264 (hardyZApproximantEM 1 34 qz147) Bool.false

noncomputable def ep1750 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz263) (BSN.hardyZErrorBoundStrong 1 34 qz12)

noncomputable def ep1751 := @Enclosure.norm_gt_of_isNear qz263 (BSN.hardyZErrorBoundStrong 1 34 qz12) Bool.true

noncomputable def ep1752 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 34 qz12) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))) Bool.false 851210186960753791 1513209474796486656 881103630854479 9079256848778919936 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz5 1 34))) (@HMul.hMul Real Real Real qz0 qz220 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz5 (@ascPochhammer Complex Complex.instSemiring 3))) qz223)))))

noncomputable def ep1753 := BSN.gt_trans_le (@Norm.norm Real Real.norm qz264) (BSN.hardyZErrorBoundStrong 1 34 qz147)

noncomputable def ep1754 := @Enclosure.norm_gt_of_isNear qz264 (BSN.hardyZErrorBoundStrong 1 34 qz147) Bool.false

noncomputable def ep1755 := @Enclosure.Real.IsNear.of_eq (BSN.hardyZErrorBoundStrong 1 34 qz147) (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))) Bool.false 2615090167368335399 4539628424389459968 458837937947521 4539628424389459968 (@Eq.refl Real (@HAdd.hAdd Real Real Real qz421 (@HMul.hMul Real Real Real qz0 (riemannSiegelThetaStirlingErrorBound 1 2) (@Norm.norm Complex Complex.instNorm (zetaApproximant qz144 1 34))) (@HMul.hMul Real Real Real qz0 qz243 (@Norm.norm Complex Complex.instNorm (@HMul.hMul Complex Complex Complex qz78 (@HMul.hMul Complex Complex Complex qz78 (@HDiv.hDiv Complex Complex Complex qz85 ↑(@Rat.cast Real Real.instRatCast (bernoulli qz221)) ↑qz222) (@Polynomial.eval Complex Complex.instSemiring qz144 (@ascPochhammer Complex Complex.instSemiring 3))) qz244)))))

noncomputable def ep1756 := @List.cons EMRow45.d0 (@PSigma.mk Zeta.Certificates.ZIntervalEM Zeta.Certificates.ZIntervalEM.Certificate qz262 (ep1744 (@Enclosure.pos_of_ble 1 rfl) (@Enclosure.pos_of_ble 34 rfl) (ep1747 (@ep1748 ep1184 ep1185 (@ep1749 ep1182 ep1183 ep1184 ep1185 (@Eq.refl Real (hardyZApproximantEM 1 34 qz147)) EMRow45.d17) rfl rfl rfl)) (ep1750 (hardyZErrorBoundEM 1 34 qz12) (BSN.hardyZErrorBoundEM_le_strong 1 34 qz12 rfl) (@ep1751 Bool.false ep525 ep526 ep527 ep528 851210186960753791 1513209474796486656 881103630854479 9079256848778919936 (@ep1746 ep525 ep526 ep527 ep528 (@Eq.refl Real (hardyZApproximantEM 1 34 qz12)) EMRow45.d12) (ep1752 EMRow45.d22) rfl rfl rfl rfl rfl)) (ep1753 (hardyZErrorBoundEM 1 34 qz147) (BSN.hardyZErrorBoundEM_le_strong 1 34 qz147 rfl) (@ep1754 Bool.false ep1182 ep1183 ep1184 ep1185 2615090167368335399 4539628424389459968 458837937947521 4539628424389459968 (@ep1749 ep1182 ep1183 ep1184 ep1185 (@Eq.refl Real (hardyZApproximantEM 1 34 qz147)) EMRow45.d17) (ep1755 EMRow45.d23) rfl rfl rfl rfl rfl)))) (@List.nil EMRow45.d0)

noncomputable abbrev qz531 := (@Enclosure.dec_le_dec qz545 qz649 132339 1000 134395 1000 (@Eq.refl Real qz545) (@Eq.refl Real qz649) rfl rfl rfl)

noncomputable abbrev qz265 := (Zeta.Certificates.CertifiedZeroIntervals.intervals (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1756 (@List.IsChain.singleton EMRow45.d1 EMRow45.d24 (EMRow45.d2 qz277 qz446 qz531))))

noncomputable abbrev qz532 := (@NonemptyInterval Real Real.instLE)

noncomputable def ep1757 := And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz265)) (@Option.some Real qz12))

noncomputable def ep1758 := ep1757 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz265)) (@Option.some Real qz147))

noncomputable def ep1759 := @And.intro (@Eq Nat (@List.length qz532 qz265) 1) ep1758

noncomputable def ep1760 := @And.intro (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 qz265)) (@Option.some Real qz12))

noncomputable def ep1761 := @ep1760 (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 qz265)) (@Option.some Real qz147))

noncomputable abbrev qz266 := (Zeta.Certificates.CertifiedZeroIntervals.ofCertifiedEM ep1756 (@List.IsChain.singleton EMRow45.d1 EMRow45.d24 (EMRow45.d2 qz277 qz446 qz531)))

theorem EMRow45.d25 : Zeta.Certificates.BatchSpec 1 132339 1000 134395 1000 := @Exists.intro Zeta.Certificates.CertifiedZeroIntervals (fun (C : Zeta.Certificates.CertifiedZeroIntervals) => And (@Eq Nat (@List.length qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C)) 1) (And (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.fst Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.head? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz12)) (@Eq (Option Real) (@Option.map qz532 Real (fun (x : @NonemptyInterval Real Real.instLE) => @Prod.snd Real Real (@NonemptyInterval.toProd Real Real.instLE x)) (@List.getLast? qz532 (Zeta.Certificates.CertifiedZeroIntervals.intervals C))) (@Option.some Real qz147)))) qz266 (ep1759 (@Eq.refl Nat 1) (ep1761 (@Eq.refl (Option Real) (@Option.some Real qz12)) (@Eq.refl (Option Real) (@Option.some Real qz147))))

theorem solution : Zeta.Certificates.BatchSpec 1 132339 1000 134395 1000 := EMRow45.d25
#print axioms solution
#check solution
